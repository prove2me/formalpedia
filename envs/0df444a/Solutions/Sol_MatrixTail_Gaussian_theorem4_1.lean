-- Prove2me | solution 1 for MatrixTail.Gaussian.theorem4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T03:27:13.44651+00:00
-- url     : https://prove2.me/submissions/e0f4d4b1-de20-4a17-ac38-88b542257045

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

/-
Apache-2.0. Independent proof of the complete native matrix Gaussian/Rademacher tail theorem.
Credit: prior accepted vebis supports display2_4 and lemma4_3_rademacher informed the mission history; no accepted source code was copied.
This construction proves scalar secant, matrix moments, actual Gaussian/sign integration, trace MGF, and both native tails.
-/

-- BEGIN GTProof.TraceBasics
section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian.GTFresh

noncomputable def rtrace {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace A).re

noncomputable def series {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℂ := ∑ i, x i • A i

@[simp] theorem rtrace_zero {d : ℕ} : rtrace (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  simp [rtrace]

@[simp] theorem rtrace_one {d : ℕ} : rtrace (1 : Matrix (Fin d) (Fin d) ℂ) = d := by
  simp [rtrace]

theorem rtrace_add {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (A + B) = rtrace A + rtrace B := by simp [rtrace]

theorem rtrace_sub {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (A - B) = rtrace A - rtrace B := by simp [rtrace]

theorem rtrace_smul {d : ℕ} (a : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (a • A) = a * rtrace A := by simp [rtrace]

theorem rtrace_sum {ι : Type*} {d : ℕ} (s : Finset ι)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    rtrace (∑ i ∈ s, A i) = ∑ i ∈ s, rtrace (A i) := by simp [rtrace]

theorem rtrace_mul_comm {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (A * B) = rtrace (B * A) := by
  exact congrArg Complex.re (Matrix.trace_mul_comm A B)

theorem rtrace_conj {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    rtrace ((U : Matrix (Fin d) (Fin d) ℂ) * A * star (U : Matrix (Fin d) (Fin d) ℂ)) = rtrace A := by
  rw [rtrace_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

theorem rtrace_diagonal {d : ℕ} (a : Fin d → ℝ) :
    rtrace (Matrix.diagonal (fun i => (a i : ℂ))) = ∑ i, a i := by
  simp [rtrace]

theorem series_hermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (x : Fin n → ℝ) : (series A x).IsHermitian := by
  unfold series
  apply Finset.sum_induction
  · exact fun _ _ ha hb => ha.add hb
  · exact Matrix.isHermitian_zero
  · intro i _
    exact (hA i).smul (by rfl)

theorem series_neg {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℝ) : series A (-x) = -series A x := by
  simp [series, Finset.sum_neg_distrib]

theorem continuous_series {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    Continuous (series A) := by unfold series; fun_prop

theorem continuous_rtrace {d : ℕ} :
    Continuous (rtrace (d := d)) := by unfold rtrace Matrix.trace Matrix.diag; fun_prop

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceBasics

-- BEGIN GTProof.SpectralTrace
section

open scoped MatrixOrder ComplexOrder

namespace MatrixTail.Gaussian.GTFresh

theorem rtrace_cfc {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    rtrace (cfc f A) = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, rtrace_conj]
  exact rtrace_diagonal _

theorem rtrace_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (m : ℕ) :
    rtrace (A ^ m) = ∑ i, hA.eigenvalues i ^ m := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, rtrace_conj, Matrix.diagonal_pow]
  change rtrace (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ m)) = _
  simpa only [Complex.ofReal_pow]
    using rtrace_diagonal (fun i => hA.eigenvalues i ^ m)

theorem rtrace_even_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (p : ℕ) : 0 ≤ rtrace (A ^ (2 * p)) := by
  rw [rtrace_pow A hA]
  exact Finset.sum_nonneg (fun i _ => by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _)

theorem rtrace_mexp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    rtrace (MatrixTail.Master.mexp A) = ∑ i, Real.exp (hA.eigenvalues i) :=
  rtrace_cfc A hA Real.exp

theorem rtrace_mexp_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : 0 ≤ rtrace (MatrixTail.Master.mexp A) := by
  rw [rtrace_mexp A hA]
  exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.SpectralTrace

-- BEGIN GTProof.TraceCosh
section

namespace MatrixTail.Gaussian.GTFresh

theorem hasSum_rtrace_cosh {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    HasSum (fun p : ℕ => rtrace (A^(2*p)) / ((2*p).factorial : ℝ))
      (rtrace (cfc Real.cosh A)) := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ => Real.hasSum_cosh (hA.eigenvalues i))
  rw [rtrace_cfc A hA]
  convert h using 1
  ext p
  rw [rtrace_pow A hA, Finset.sum_div]

theorem rtrace_cosh_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : 0 ≤ rtrace (cfc Real.cosh A) := by
  rw [rtrace_cfc A hA]
  exact Finset.sum_nonneg (fun i _ => (Real.cosh_pos _).le)

theorem rtrace_cosh_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    rtrace (cfc Real.cosh A) =
      (rtrace (MatrixTail.Master.mexp A) + rtrace (MatrixTail.Master.mexp (-A)))/2 := by
  have hn : cfc Real.exp (-A) = cfc (fun t : ℝ => Real.exp (-t)) A :=
    (cfc_comp_neg Real.exp A (ha := hA)).symm
  rw [MatrixTail.Master.mexp, MatrixTail.Master.mexp, hn]
  rw [rtrace_cfc A hA, rtrace_cfc A hA, rtrace_cfc A hA]
  simp only [Real.cosh_eq]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

theorem rtrace_exp_le_cosh {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    rtrace (MatrixTail.Master.mexp A) ≤ 2*rtrace (cfc Real.cosh A) := by
  rw [rtrace_cosh_eq A hA]
  have h := rtrace_mexp_nonneg (-A) hA.neg
  linarith

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceCosh

-- BEGIN GTProof.PolynomialFunctions
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory

def IsPoly {ι : Type*} (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ p : MvPolynomial ι ℝ, ∀ x, MvPolynomial.eval x p = f x

variable {ι : Type*} {f g : (ι → ℝ) → ℝ}

theorem isPoly_const (a : ℝ) : IsPoly (fun _ : ι → ℝ => a) :=
  ⟨MvPolynomial.C a, fun _ => MvPolynomial.eval_C _⟩

theorem isPoly_coordinate (i : ι) : IsPoly (fun x : ι → ℝ => x i) :=
  ⟨MvPolynomial.X i, fun _ => MvPolynomial.eval_X _⟩

theorem IsPoly.add (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x + g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun x => by simp [hp, hq]⟩

theorem IsPoly.mul (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x * g x) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun x => by simp [hp, hq]⟩

theorem IsPoly.neg (hf : IsPoly f) : IsPoly (fun x => -f x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun x => by simp [hp]⟩

theorem IsPoly.sub (hf : IsPoly f) (hg : IsPoly g) : IsPoly (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem IsPoly.pow (hf : IsPoly f) (k : ℕ) : IsPoly (fun x => f x ^ k) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p ^ k, fun x => by simp [hp]⟩

theorem IsPoly.finset_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → ℝ) → ℝ)
    (hF : ∀ i ∈ s, IsPoly (F i)) : IsPoly (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPoly_const (ι := ι) 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hF a (Finset.mem_insert_self a s)).add (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem IsPoly.fintype_sum {κ : Type*} [Fintype κ] (F : κ → (ι → ℝ) → ℝ)
    (hF : ∀ i, IsPoly (F i)) : IsPoly (fun x => ∑ i, F i x) :=
  IsPoly.finset_sum Finset.univ F (fun i _ => hF i)

theorem IsPoly.continuous (hf : IsPoly f) : Continuous f := by
  obtain ⟨p, hp⟩ := hf
  exact p.continuous_eval.congr hp

theorem integrable_mvPolynomial_eval [Fintype ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x ^ k) (μ i)) (p : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x p) (Measure.pi μ) := by
  classical
  simp_rw [MvPolynomial.eval_eq']
  apply integrable_finsetSum
  intro d _
  exact (Integrable.fintype_prod (fun i => hμ i (d i))).const_mul (p.coeff d)

theorem IsPoly.integrable [Fintype ι] (hf : IsPoly f) (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x ^ k) (μ i)) :
    Integrable f (Measure.pi μ) := by
  obtain ⟨p, hp⟩ := hf
  exact (integrable_mvPolynomial_eval μ hμ p).congr (Filter.Eventually.of_forall hp)

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.PolynomialFunctions

-- BEGIN GTProof.MatrixPolynomials
section

namespace MatrixTail.Gaussian.GTFresh

def IsMatPoly {n d : ℕ} (F : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j, IsPoly (fun x => (F x i j).re) ∧ IsPoly (fun x => (F x i j).im)

theorem isMatPoly_const {n d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    IsMatPoly (fun _ : Fin n → ℝ => A) :=
  fun i j => ⟨isPoly_const (A i j).re, isPoly_const (A i j).im⟩

theorem IsMatPoly.mul {n d : ℕ} {F G : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℂ}
    (hF : IsMatPoly F) (hG : IsMatPoly G) : IsMatPoly (fun x => F x * G x) := by
  intro i j
  constructor
  · simp only [Matrix.mul_apply, Complex.re_sum, Complex.mul_re]
    exact IsPoly.fintype_sum _ (fun k => ((hF i k).1.mul (hG k j).1).sub
      ((hF i k).2.mul (hG k j).2))
  · simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im]
    exact IsPoly.fintype_sum _ (fun k => ((hF i k).1.mul (hG k j).2).add
      ((hF i k).2.mul (hG k j).1))

theorem IsMatPoly.pow {n d : ℕ} {F : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℂ}
    (hF : IsMatPoly F) (m : ℕ) : IsMatPoly (fun x => F x ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using isMatPoly_const (n := n) (1 : Matrix (Fin d) (Fin d) ℂ)
  | succ m ih => simpa only [pow_succ] using ih.mul hF

theorem IsMatPoly.rtrace {n d : ℕ} {F : (Fin n → ℝ) → Matrix (Fin d) (Fin d) ℂ}
    (hF : IsMatPoly F) : IsPoly (fun x => rtrace (F x)) := by
  change IsPoly (fun x => (∑ i, F x i i).re)
  simp only [Complex.re_sum]
  exact IsPoly.fintype_sum _ (fun i => (hF i i).1)

theorem series_isMatPoly {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    IsMatPoly (series A) := by
  intro i j
  constructor
  · simp only [series, Matrix.sum_apply, Matrix.smul_apply, Complex.re_sum, Complex.smul_re,
      smul_eq_mul]
    exact IsPoly.fintype_sum _ (fun k => (isPoly_coordinate k).mul (isPoly_const _))
  · simp only [series, Matrix.sum_apply, Matrix.smul_apply, Complex.im_sum, Complex.smul_im,
      smul_eq_mul]
    exact IsPoly.fintype_sum _ (fun k => (isPoly_coordinate k).mul (isPoly_const _))

theorem series_trace_power_isPoly {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (m : ℕ) : IsPoly (fun x => rtrace (series A x ^ m)) :=
  ((series_isMatPoly A).pow m).rtrace

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.MatrixPolynomials

-- BEGIN GTProof.TraceSeries
section

open MeasureTheory

namespace MatrixTail.Gaussian.GTFresh

theorem real_hasSum_exp (x : ℝ) : HasSum (fun m : ℕ => x^m/(m.factorial : ℝ)) (Real.exp x) := by
  simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x

theorem rtrace_smul_pow {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) (m : ℕ) :
    rtrace ((t•A)^m) = t^m*rtrace (A^m) := by
  rw [smul_pow, rtrace_smul]

theorem hasSum_rtrace_exp {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    HasSum (fun m : ℕ => rtrace (A^m)/(m.factorial : ℝ))
      (rtrace (MatrixTail.Master.mexp A)) := by
  have h := hasSum_sum (s := Finset.univ) (fun i _ => real_hasSum_exp (hA.eigenvalues i))
  rw [rtrace_mexp A hA]
  convert h using 1
  ext m
  rw [rtrace_pow A hA, Finset.sum_div]

theorem hasSum_scaled_cosh {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (t : ℝ) :
    HasSum (fun p : ℕ => t^(2*p)*rtrace (A^(2*p))/((2*p).factorial : ℝ))
      (rtrace (cfc Real.cosh (t•A))) := by
  simpa only [rtrace_smul_pow] using hasSum_rtrace_cosh (t•A) (hA.smul (by rfl))

theorem measurable_series_exp {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (t : ℝ) :
    Measurable (fun x => rtrace (MatrixTail.Master.mexp (t•series A x))) := by
  have he (x : Fin n → ℝ) := hasSum_rtrace_exp (t•series A x)
    ((series_hermitian A hA x).smul (by rfl))
  have hm : Measurable (fun x : Fin n → ℝ => ∑' m : ℕ,
      t^m*rtrace (series A x^m)/(m.factorial : ℝ)) := by
    apply Measurable.tsum
    intro m
    exact (measurable_const.mul (series_trace_power_isPoly A m).continuous.measurable).div_const _
  convert hm using 1
  funext x
  simpa only [rtrace_smul_pow] using (he x).tsum_eq.symm

theorem measurable_series_cosh {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (t : ℝ) :
    Measurable (fun x => rtrace (cfc Real.cosh (t•series A x))) := by
  have hm : Measurable (fun x : Fin n → ℝ => ∑' p : ℕ,
      t^(2*p)*rtrace (series A x^(2*p))/((2*p).factorial : ℝ)) := by
    apply Measurable.tsum
    intro p
    exact (measurable_const.mul (series_trace_power_isPoly A (2*p)).continuous.measurable).div_const _
  convert hm using 1
  funext x
  exact (hasSum_scaled_cosh (series A x) (series_hermitian A hA x) t).tsum_eq.symm

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceSeries

-- BEGIN GTProof.NonnegativeSeries
section

open MeasureTheory
open scoped ENNReal

namespace MatrixTail.Gaussian.GTFresh

theorem integrable_nonnegative_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (F : Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hpos : ∀ n x, 0 ≤ f n x) (hs : ∀ x, HasSum (fun n => f n x) (F x))
    (hi : Summable (fun n => ∫ x, f n x ∂μ)) : Integrable F μ := by
  have hF : F = fun x => ∑' n, f n x := funext (fun x => (hs x).tsum_eq.symm)
  have hm : AEStronglyMeasurable F μ := by
    rw [hF]
    exact (AEMeasurable.tsum (fun n => (hf n).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  refine ⟨hm, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => (hs x).nonneg (hpos · x)))).2 ?_⟩
  have he (x : Ω) : ENNReal.ofReal (F x) = ∑' n, ENNReal.ofReal (f n x) := by
    rw [← (hs x).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (hpos · x) (hs x).summable
  simp_rw [he]
  rw [lintegral_tsum (fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _) (Filter.Eventually.of_forall (hpos _))]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hpos n)) hi]
  exact ENNReal.ofReal_lt_top

theorem integral_nonnegative_series {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (F : Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hpos : ∀ n x, 0 ≤ f n x) (hs : ∀ x, HasSum (fun n => f n x) (F x))
    (hi : Summable (fun n => ∫ x, f n x ∂μ)) :
    HasSum (fun n => ∫ x, f n x ∂μ) (∫ x, F x ∂μ) := by
  have hn : Summable (fun n => ∫ x, ‖f n x‖ ∂μ) := by
    simpa only [Real.norm_of_nonneg (hpos _ _)] using hi
  have h := hasSum_integral_of_summable_integral_norm hf hn
  simpa only [funext (fun x => (hs x).tsum_eq)] using h

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.NonnegativeSeries

-- BEGIN GTProof.CoshMomentBound
section

open MeasureTheory

namespace MatrixTail.Gaussian.GTFresh

theorem cosh_bound_of_normalized_moments {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (v : ℝ)
    (hb : ∀ p, (∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ) / ((2*p).factorial : ℝ) ≤
      d*(v/2)^p/(p.factorial : ℝ)) (t : ℝ) :
    Integrable (fun x => rtrace (cfc Real.cosh (t•series A x))) (Measure.pi μ) ∧
      (∫ x, rtrace (cfc Real.cosh (t•series A x)) ∂Measure.pi μ) ≤
        d*Real.exp (t^2*v/2) := by
  let f := fun (p : ℕ) (x : Fin n → ℝ) =>
    t^(2*p)*rtrace (series A x^(2*p))/((2*p).factorial : ℝ)
  have hf p : Integrable (f p) (Measure.pi μ) :=
    (((series_trace_power_isPoly A (2*p)).integrable μ hμ).const_mul _).div_const _
  have hp p x : 0 ≤ f p x := by
    dsimp [f]
    apply div_nonneg
    · apply mul_nonneg
      · rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
      · exact rtrace_even_nonneg _ (series_hermitian A hA x) p
    · positivity
  have hs x := hasSum_scaled_cosh (series A x) (series_hermitian A hA x) t
  have he p : (∫ x, f p x ∂Measure.pi μ) =
      t^(2*p)*((∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ)/((2*p).factorial : ℝ)) := by
    dsimp [f]
    rw [integral_div, integral_const_mul]
    ring
  have hle p : (∫ x, f p x ∂Measure.pi μ) ≤
      (d:ℝ)*((t^2*v/2)^p/(p.factorial : ℝ)) := by
    rw [he]
    have ht : 0 ≤ t^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    have h := mul_le_mul_of_nonneg_left (hb p) ht
    calc
      _ ≤ t^(2*p) * (d*(v/2)^p/(p.factorial : ℝ)) := h
      _ = _ := by simp only [div_eq_mul_inv, mul_pow, pow_mul]; ring
  have hmajor := (real_hasSum_exp (t^2*v/2)).mul_left (d:ℝ)
  have hi : Summable (fun p => ∫ x, f p x ∂Measure.pi μ) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg (hp p)) hle hmajor.summable
  refine ⟨integrable_nonnegative_series (Measure.pi μ) f _ hf hp hs hi, ?_⟩
  have heq := integral_nonnegative_series (Measure.pi μ) f _ hf hp hs hi
  rw [← heq.tsum_eq, ← hmajor.tsum_eq]
  exact hi.tsum_le_tsum hle hmajor.summable

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.CoshMomentBound

-- BEGIN GTProof.SignLaw
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory
open scoped ENNReal

def signLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1)

instance signLaw_probability : IsProbabilityMeasure signLaw := by
  constructor
  simp only [signLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.add_halves 1

theorem integrable_signLaw (f : ℝ → ℝ) : Integrable f signLaw := by
  have h₁ : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by finiteness)
  have h₂ : Integrable f (Measure.dirac (-1 : ℝ)) := integrable_dirac (by finiteness)
  exact (integrable_add_measure).mpr
    ⟨h₁.smul_measure (by norm_num), h₂.smul_measure (by norm_num)⟩

theorem integral_signLaw (f : ℝ → ℝ) :
    (∫ x, f x ∂signLaw) = (f 1 + f (-1)) / 2 := by
  have h₁ : Integrable f (Measure.dirac (1 : ℝ)) := integrable_dirac (by finiteness)
  have h₂ : Integrable f (Measure.dirac (-1 : ℝ)) := integrable_dirac (by finiteness)
  rw [signLaw, integral_add_measure (h₁.smul_measure (by norm_num))
    (h₂.smul_measure (by norm_num))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  norm_num
  ring

theorem rademacher_map_eq_signLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → ℝ}
    (hξ : IsRademacher P ξ) : P.map ξ = signLaw := by
  have hp : P {ω | ξ ω = 1} = (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] using hξ.2.1
  have hn : P {ω | ξ ω = -1} = (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by norm_num)).mp
    simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] using hξ.2.2
  have hm₁ : MeasurableSet {ω | ξ ω = 1} := hξ.1 (measurableSet_singleton _)
  have hm₂ : MeasurableSet {ω | ξ ω = -1} := hξ.1 (measurableSet_singleton _)
  have hd : Disjoint {ω | ξ ω = 1} {ω | ξ ω = -1} := by
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    change ξ ω = 1 at h₁
    change ξ ω = -1 at h₂
    linarith
  have hu : P ({ω | ξ ω = 1} ∪ {ω | ξ ω = -1}) = 1 := by
    rw [measure_union hd hm₂, hp, hn]
    exact ENNReal.add_halves 1
  have hae : ∀ᵐ ω ∂P, ξ ω = (1 : ℝ) ∨ ξ ω = -1 := by
    rw [ae_iff]
    change P ({ω | ξ ω = 1} ∪ {ω | ξ ω = -1})ᶜ = 0
    rw [measure_compl (hm₁.union hm₂) (measure_ne_top _ _), hu, measure_univ]
    simp
  have he := (Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hξ.1.aemeasurable
    (show (1 : ℝ) ≠ -1 by norm_num)).mp hae
  change P.map ξ = P {ω | ξ ω = 1} • Measure.dirac 1 +
    P {ω | ξ ω = -1} • Measure.dirac (-1) at he
  simpa only [hp, hn, signLaw] using he

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.SignLaw

-- BEGIN GTProof.GaussianPolynomial
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem gaussian_integrable_pow (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have hm : MemLp (fun x : ℝ => x) (k : ℝ≥0∞) (gaussianReal 0 1) := by
    change MemLp id (k : ℝ≥0∞) (gaussianReal 0 1)
    exact memLp_id_gaussianReal' _ (by simp)
  exact hm.integrable_norm_pow'.mono' (by fun_prop) (Filter.Eventually.of_forall (fun x => by
    simp only [norm_pow]; exact le_rfl))

theorem gaussian_integrable_polynomial (p : Polynomial ℝ) :
    Integrable (fun x => p.eval x) (gaussianReal 0 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    exact (hp.add hq).congr (Filter.Eventually.of_forall (fun x => by
      change p.eval x + q.eval x = (p + q).eval x
      rw [Polynomial.eval_add]))
  | monomial k a =>
    simpa only [Polynomial.eval_monomial] using (gaussian_integrable_pow k).const_mul a

theorem gaussian_integrable_density_mul {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0)] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using h

theorem gaussian_density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hfun : gaussianPDFReal 0 1 = fun t : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    funext t
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [hfun]
  have h := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq] at h
  apply h.congr_deriv
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

theorem gaussian_polynomial_stein (p : Polynomial ℝ) :
    (∫ x : ℝ, x * p.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, p.derivative.eval x ∂gaussianReal 0 1 := by
  have hp := gaussian_integrable_density_mul (gaussian_integrable_polynomial p)
  have hpd := gaussian_integrable_density_mul (gaussian_integrable_polynomial p.derivative)
  have hxp : Integrable (fun x => gaussianPDFReal 0 1 x * (x * p.eval x)) := by
    exact (gaussian_integrable_density_mul (gaussian_integrable_polynomial (Polynomial.X * p))).congr
      (Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [Polynomial.eval_mul, Polynomial.eval_X]))
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => p.eval x) (v := gaussianPDFReal 0 1)
    (u' := fun x => p.derivative.eval x) (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x) (fun x _ => gaussian_density_hasDerivAt x)
    (hxp.neg.congr (Filter.Eventually.of_forall (fun x => by dsimp; ring)))
    (hpd.congr (Filter.Eventually.of_forall (fun x => by dsimp; ring)))
    (hp.congr (Filter.Eventually.of_forall (fun x => by dsimp; ring)))
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have he : (fun x => p.eval x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(gaussianPDFReal 0 1 x * (x * p.eval x)) := by funext x; ring
  have he' : (fun x => p.derivative.eval x * gaussianPDFReal 0 1 x) =
      fun x => gaussianPDFReal 0 1 x * p.derivative.eval x := by funext x; ring
  rw [he, he', integral_neg] at hibp
  linarith

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.GaussianPolynomial

-- BEGIN GTProof.ProductSymmetry
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory

theorem signLaw_map_neg : signLaw.map (fun x => -x) = signLaw := by
  rw [signLaw, Measure.map_add _ _ measurable_neg]
  simp only [Measure.map_smul, Measure.map_dirac, neg_neg]
  exact add_comm _ _

theorem product_neg_preserving {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ.map (fun x => -x) = μ) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => -x i)
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => μ)) :=
  measurePreserving_pi (fun _ => μ) (fun _ => μ)
    (fun _ => ⟨measurable_neg, hμ⟩)

theorem gaussian_product_neg_preserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => -x i)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
  product_neg_preserving _ (by simpa using (gaussianReal_map_neg (μ := 0) (v := 1)))

theorem sign_product_neg_preserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ℝ => fun i => -x i)
      (Measure.pi (fun _ : Fin n => signLaw))
      (Measure.pi (fun _ : Fin n => signLaw)) :=
  product_neg_preserving _ signLaw_map_neg

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.ProductSymmetry

-- BEGIN GTProof.TraceMGF
section

open MeasureTheory

namespace MatrixTail.Gaussian.GTFresh

theorem exp_bound_of_symmetric_moments {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (v : ℝ)
    (hb : ∀ p, (∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ) / ((2*p).factorial : ℝ) ≤
      d*(v/2)^p/(p.factorial : ℝ))
    (hn : MeasurePreserving (fun x : Fin n → ℝ => -x) (Measure.pi μ) (Measure.pi μ))
    (t : ℝ) :
    Integrable (fun x => rtrace (MatrixTail.Master.mexp (t•series A x))) (Measure.pi μ) ∧
      (∫ x, rtrace (MatrixTail.Master.mexp (t•series A x)) ∂Measure.pi μ) ≤
        d*Real.exp (t^2*v/2) := by
  obtain ⟨hc, hbound⟩ := cosh_bound_of_normalized_moments A hA μ hμ v hb t
  have hi : Integrable (fun x => rtrace (MatrixTail.Master.mexp (t•series A x))) (Measure.pi μ) := by
    apply (hc.const_mul 2).mono' (measurable_series_exp A hA t).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (rtrace_mexp_nonneg _ ((series_hermitian A hA x).smul (by rfl)))]
    exact rtrace_exp_le_cosh _ ((series_hermitian A hA x).smul (by rfl))
  have hneg := hn.integrable_comp_of_integrable hi
  have heq := hn.integral_comp measurableEmbedding_neg
    (fun x => rtrace (MatrixTail.Master.mexp (t•series A x)))
  change Integrable (fun x => rtrace (MatrixTail.Master.mexp (t•series A (-x)))) (Measure.pi μ) at hneg
  simp only [series_neg, smul_neg] at hneg heq
  have hc_eq : (∫ x, rtrace (cfc Real.cosh (t•series A x)) ∂Measure.pi μ) =
      (∫ x, rtrace (MatrixTail.Master.mexp (t•series A x)) ∂Measure.pi μ) := by
    have hpoint (x : Fin n → ℝ) := rtrace_cosh_eq (t•series A x)
      ((series_hermitian A hA x).smul (show IsSelfAdjoint t from rfl))
    simp_rw [hpoint]
    rw [integral_div, integral_add hi hneg, heq]
    ring
  exact ⟨hi, hc_eq ▸ hbound⟩

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceMGF

-- BEGIN GTProof.TraceOverlap
section

namespace MatrixTail.Gaussian.GTFresh

theorem rtrace_diagonal_overlap {d : ℕ} (a b : Fin d → ℝ)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (Matrix.diagonal (fun i => (a i : ℂ)) * U *
      Matrix.diagonal (fun i => (b i : ℂ)) * star U) =
      ∑ i, ∑ j, a i * b j * Complex.normSq (U i j) := by
  simp only [rtrace, Matrix.trace, Matrix.diag, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, ((Matrix.diagonal (fun i => (a i : ℂ)) * U *
    Matrix.diagonal (fun i => (b i : ℂ))) i j) * star (U i j)).re = _
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [RCLike.star_def, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem rtrace_conj_product {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (B C : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (((U : Matrix (Fin d) (Fin d) ℂ) * B * star (U : Matrix (Fin d) (Fin d) ℂ)) *
      ((V : Matrix (Fin d) (Fin d) ℂ) * C * star (V : Matrix (Fin d) (Fin d) ℂ))) =
      rtrace (B * (star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ)) * C *
        star (star (U : Matrix (Fin d) (Fin d) ℂ) * (V : Matrix (Fin d) (Fin d) ℂ))) := by
  simp only [star_mul, star_star, mul_assoc]
  rw [rtrace_mul_comm (U : Matrix (Fin d) (Fin d) ℂ)]
  simp only [mul_assoc]

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceOverlap

-- BEGIN GTProof.MixedSpectral
section

namespace MatrixTail.Gaussian.GTFresh

noncomputable def overlap {d : ℕ} {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (i j : Fin d) : ℝ :=
  Complex.normSq ((star (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    (hC.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) i j)

theorem overlap_nonneg {d : ℕ} {B C : Matrix (Fin d) (Fin d) ℂ}
    (hB : B.IsHermitian) (hC : C.IsHermitian) (i j : Fin d) :
    0 ≤ overlap hB hC i j := Complex.normSq_nonneg _

theorem spectral_power {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (r : ℕ) :
    B ^ r = (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
      Matrix.diagonal (fun i => ((hB.eigenvalues i ^ r : ℝ) : ℂ)) *
        star (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.diagonal_pow]
  congr 2
  ext i j
  simp [Matrix.diagonal_apply]

theorem rtrace_mixed_pow {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (r s : ℕ) :
    rtrace (B ^ r * C ^ s) =
      ∑ i, ∑ j, (hB.eigenvalues i ^ r) * (hC.eigenvalues j ^ s) * overlap hB hC i j := by
  rw [spectral_power B hB r, spectral_power C hC s, rtrace_conj_product,
    rtrace_diagonal_overlap]
  rfl

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.MixedSpectral

-- BEGIN GTProof.SecantAlgebra
section

namespace MatrixTail.Gaussian.GTFresh

theorem rtrace_cycle {d : ℕ} (A B C : Matrix (Fin d) (Fin d) ℂ) :
    rtrace (A * B * C) = rtrace (C * A * B) :=
  congrArg Complex.re (Matrix.trace_mul_cycle A B C)

theorem secant_trace_expand {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    rtrace ((B-C)*(B^m-C^m)) =
      rtrace (B^(m+1)*C^0) - rtrace (B^1*C^m) -
        rtrace (B^m*C^1) + rtrace (B^0*C^(m+1)) := by
  simp only [pow_zero, pow_one, mul_one, one_mul, sub_mul, mul_sub, rtrace_sub]
  rw [pow_succ', pow_succ', rtrace_mul_comm C (B^m)]
  ring

theorem square_trace_expand {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ) (r : ℕ) :
    rtrace ((B-C)^2*(B^r+C^r)) =
      rtrace (B^(r+2)*C^0) + rtrace (B^2*C^r) + rtrace (B^r*C^2) +
        rtrace (B^0*C^(r+2)) - 2*rtrace (B^(r+1)*C^1) -
          2*rtrace (B^1*C^(r+1)) := by
  have hex : (B-C)^2*(B^r+C^r) =
      B*B*B^r + B*B*C^r - B*C*B^r - B*C*C^r - C*B*B^r - C*B*C^r +
        C*C*B^r + C*C*C^r := by noncomm_ring
  have h1 : rtrace (B*C*B^r) = rtrace (B^(r+1)*C) := by
    rw [rtrace_cycle, ← pow_succ]
  have h2 : rtrace (C*B*B^r) = rtrace (B^(r+1)*C) := by
    rw [mul_assoc, ← pow_succ', rtrace_mul_comm]
  have h3 : rtrace (B*C*C^r) = rtrace (B*C^(r+1)) := by
    rw [mul_assoc, ← pow_succ']
  have h4 : rtrace (C*B*C^r) = rtrace (B*C^(r+1)) := by
    rw [rtrace_cycle, ← pow_succ, rtrace_mul_comm]
  have h5 : rtrace (C*C*B^r) = rtrace (B^r*C^2) := by
    rw [rtrace_mul_comm, pow_two]
  have h6 (A : Matrix (Fin d) (Fin d) ℂ) : A*A*A^r = A^(r+2) := by
    rw [← pow_two, ← pow_add]
    congr 1
    omega
  rw [hex]
  simp only [rtrace_add, rtrace_sub, h1, h2, h3, h4, h5, h6,
    pow_zero, pow_one, mul_one, one_mul, pow_two]
  ring

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.SecantAlgebra

-- BEGIN GTProof.ScalarSecant
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory Set

theorem odd_power_secant (p : ℕ) (a b : ℝ) :
    (a - b) * (a ^ (2 * p + 1) - b ^ (2 * p + 1)) ≤
      ((2 * p + 1 : ℕ) : ℝ) / 2 * (a - b) ^ 2 * (a ^ (2 * p) + b ^ (2 * p)) := by
  let m : ℝ := (2 * p + 1 : ℕ)
  let F : ℝ → ℝ := fun t => (a - b) * (b + t * (a - b)) ^ (2 * p + 1)
  let f : ℝ → ℝ := fun t => m * (a - b) ^ 2 * (b + t * (a - b)) ^ (2 * p)
  let g : ℝ → ℝ := fun t => m * (a - b) ^ 2 * ((1 - t) * b ^ (2 * p) + t * a ^ (2 * p))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hd (t : ℝ) : HasDerivAt F (f t) t := by
    have h := (((hasDerivAt_id t).mul_const (a - b)).const_add b).pow (2 * p + 1)
    have h' := h.const_mul (a - b)
    apply h'.congr_deriv
    dsimp [f, m]
    ring
  have he : (∫ t in (0 : ℝ)..1, f t) = F 1 - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hf.intervalIntegrable (μ := volume) 0 1)
  have hfg : (∫ t in (0 : ℝ)..1, f t) ≤ ∫ t in (0 : ℝ)..1, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hf.intervalIntegrable (μ := volume) 0 1)
      (hg.intervalIntegrable (μ := volume) 0 1)
    intro t ht
    have hc := (show Even (2 * p) from even_two_mul p).convexOn_pow (𝕜 := ℝ)
    have hb := hc.2 (mem_univ b) (mem_univ a) (by linarith [ht.2] : 0 ≤ 1 - t)
      ht.1 (by ring : (1 - t) + t = 1)
    have hh : (b + t * (a - b)) ^ (2 * p) ≤ (1 - t) * b ^ (2 * p) + t * a ^ (2 * p) := by
      simpa only [smul_eq_mul, show (1 - t) * b + t * a = b + t * (a - b) by ring] using hb
    exact mul_le_mul_of_nonneg_left hh (by dsimp [m]; positivity)
  have hge : (∫ t in (0 : ℝ)..1, g t) =
      m / 2 * (a - b) ^ 2 * (a ^ (2 * p) + b ^ (2 * p)) := by
    have hg' : g = fun t => m * (a - b) ^ 2 * b ^ (2 * p) +
        (m * (a - b) ^ 2 * (a ^ (2 * p) - b ^ (2 * p))) * t := by
      funext t; dsimp [g]; ring
    have hi := intervalIntegral.integral_add ((show Continuous (fun _ : ℝ => m * (a - b) ^ 2 * b ^ (2 * p)) from continuous_const).intervalIntegrable (μ := volume) 0 1)
      ((show Continuous (fun t : ℝ => m * (a - b) ^ 2 * (a ^ (2 * p) - b ^ (2 * p)) * t) by fun_prop).intervalIntegrable (μ := volume) 0 1)
    rw [hg', hi, intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    norm_num
    ring
  rw [he, hge] at hfg
  dsimp [F, m] at hfg ⊢
  simp only [one_mul, zero_mul, add_zero] at hfg
  rw [show b + (a - b) = a by ring] at hfg
  nlinarith

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.ScalarSecant

-- BEGIN GTProof.MatrixSecant
section

namespace MatrixTail.Gaussian.GTFresh

theorem secant_trace_spectral {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (m : ℕ) :
    rtrace ((B-C)*(B^m-C^m)) = ∑ i, ∑ j,
      ((hB.eigenvalues i - hC.eigenvalues j) *
        (hB.eigenvalues i ^ m - hC.eigenvalues j ^ m)) * overlap hB hC i j := by
  rw [secant_trace_expand]
  simp_rw [rtrace_mixed_pow B C hB hC]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero, pow_succ]
  ring

theorem square_trace_spectral {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (r : ℕ) :
    rtrace ((B-C)^2*(B^r+C^r)) = ∑ i, ∑ j,
      ((hB.eigenvalues i - hC.eigenvalues j)^2 *
        (hB.eigenvalues i ^ r + hC.eigenvalues j ^ r)) * overlap hB hC i j := by
  rw [square_trace_expand]
  simp_rw [rtrace_mixed_pow B C hB hC]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero, pow_succ]
  ring

theorem matrix_odd_power_secant {d : ℕ} (B C : Matrix (Fin d) (Fin d) ℂ)
    (hB : B.IsHermitian) (hC : C.IsHermitian) (p : ℕ) :
    rtrace ((B-C)*(B^(2*p+1)-C^(2*p+1))) ≤
      ((2*p+1 : ℕ) : ℝ)/2 * rtrace ((B-C)^2*(B^(2*p)+C^(2*p))) := by
  rw [secant_trace_spectral B C hB hC, square_trace_spectral B C hB hC]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_right
    (odd_power_secant p (hB.eigenvalues i) (hC.eigenvalues j))
    (overlap_nonneg hB hC i j)
  convert h using 1
  ring

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.MatrixSecant

-- BEGIN GTProof.MomentAlgebra
section

namespace MatrixTail.Gaussian.GTFresh

theorem rademacher_trace_step {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (hA : A.IsHermitian) (p : ℕ) :
    (rtrace (A*(H+A)^(2*p+1))-rtrace (A*(H-A)^(2*p+1)))/2 ≤
      ((2*p+1 : ℕ):ℝ) *
        (rtrace (A^2*(H+A)^(2*p))+rtrace (A^2*(H-A)^(2*p)))/2 := by
  have h := matrix_odd_power_secant (H+A) (H-A) (hH.add hA) (hH.sub hA) p
  have hd : H+A-(H-A) = (2:ℝ) • A := by module
  have hs : ((2:ℝ) • A)^2 = (4:ℝ) • A^2 := by
    simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
    norm_num
  rw [hd, hs, smul_mul_assoc, rtrace_smul, smul_mul_assoc, rtrace_smul,
    mul_sub, rtrace_sub, mul_add, rtrace_add] at h
  linarith

theorem trace_series_power_step {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n → ℝ) (m : ℕ) :
    rtrace (series A x ^ (m+1)) = ∑ i, x i * rtrace (A i * series A x ^ m) := by
  rw [pow_succ']
  conv_lhs => arg 1; lhs; unfold series
  rw [Finset.sum_mul, rtrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, rtrace_smul]

theorem trace_variance_sum {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (H : Matrix (Fin d) (Fin d) ℂ) :
    ∑ i, rtrace (A i ^ 2 * H) = rtrace ((∑ i, A i ^ 2) * H) := by
  rw [Finset.sum_mul, rtrace_sum]

theorem trace_coefficient_isPoly {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (m : ℕ) :
    IsPoly (fun x => rtrace (B*series A x ^ m)) :=
  ((isMatPoly_const B).mul ((series_isMatPoly A).pow m)).rtrace

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.MomentAlgebra

-- BEGIN GTProof.VarianceOrder
section

open scoped Matrix.Norms.L2Operator

namespace MatrixTail.Gaussian.GTFresh

theorem eigenvalue_le_specNorm {d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (hV : V.IsHermitian) (i : Fin d) : hV.eigenvalues i ≤ specNorm V := by
  let : Nonempty (Fin d) := ⟨i⟩
  have h := spectrum.norm_le_norm_of_mem (hV.eigenvalues_mem_spectrum_real i)
  have he : |hV.eigenvalues i| ≤ specNorm V := by
    simpa only [Real.norm_eq_abs, specNorm, Matrix.cstar_norm_def] using h
  exact (le_abs_self _).trans he

theorem rtrace_mul_even_le {d : ℕ} (V H : Matrix (Fin d) (Fin d) ℂ)
    (hV : V.IsHermitian) (hH : H.IsHermitian) (p : ℕ) :
    rtrace (V * H^(2*p)) ≤ specNorm V * rtrace (H^(2*p)) := by
  have hleft := rtrace_mixed_pow V H hV hH 1 (2*p)
  have hright := rtrace_mixed_pow V H hV hH 0 (2*p)
  simp only [pow_one] at hleft
  simp only [pow_zero, one_mul] at hright
  rw [hleft, hright]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ hH.eigenvalues j ^ (2*p) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have h := mul_le_mul_of_nonneg_right (eigenvalue_le_specNorm V hV i)
    (mul_nonneg hp (overlap_nonneg hV hH i j))
  simpa only [mul_assoc] using h

theorem variance_hermitian {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ i, (A i).IsHermitian) : (∑ i, A i ^ 2).IsHermitian := by
  exact isSelfAdjoint_sum _ (fun i _ => (hA i).pow 2)

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.VarianceOrder

-- BEGIN GTProof.MomentRecurrence
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh

theorem normalized_moment_bound (T : ℕ → ℝ) (d v : ℝ) (hv : 0 ≤ v)
    (hzero : T 0 = d) (hstep : ∀ p, T (p + 1) ≤ (2 * p + 1 : ℕ) * v * T p)
    (p : ℕ) :
    T p / (Nat.factorial (2 * p) : ℝ) ≤
      d * (v / 2) ^ p / (Nat.factorial p : ℝ) := by
  induction p with
  | zero => simpa using le_of_eq hzero
  | succ p ih =>
    have hf : (0 : ℝ) < (Nat.factorial (2 * p) : ℝ) := by positivity
    have hg : (0 : ℝ) < (Nat.factorial p : ℝ) := by positivity
    have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have he : (Nat.factorial (2 * (p + 1)) : ℝ) =
        (2 * (p : ℝ) + 2) * (2 * (p : ℝ) + 1) * (Nat.factorial (2 * p) : ℝ) := by
      have hn : 2 * (p + 1) = (2 * p + 1) + 1 := by omega
      rw [hn, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    have hodd : (0 : ℝ) < 2 * (p : ℝ) + 1 := by positivity
    have heven : (0 : ℝ) < 2 * (p : ℝ) + 2 := by positivity
    have hr : ((2 * p + 1 : ℕ) : ℝ) * v * T p /
        (Nat.factorial (2 * (p + 1)) : ℝ) =
        ((v / 2) / ((p : ℝ) + 1)) * (T p / (Nat.factorial (2 * p) : ℝ)) := by
      rw [he]
      push_cast
      field_simp [ne_of_gt hf, ne_of_gt hp, ne_of_gt hodd, ne_of_gt heven]
    have hs : ((v / 2) / ((p : ℝ) + 1)) *
        (d * (v / 2) ^ p / (Nat.factorial p : ℝ)) =
        d * (v / 2) ^ (p + 1) / (Nat.factorial (p + 1) : ℝ) := by
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp [ne_of_gt hg, ne_of_gt hp]
    calc
      T (p + 1) / (Nat.factorial (2 * (p + 1)) : ℝ) ≤
          ((2 * p + 1 : ℕ) : ℝ) * v * T p /
            (Nat.factorial (2 * (p + 1)) : ℝ) :=
        div_le_div_of_nonneg_right (hstep p) (by positivity)
      _ = ((v / 2) / ((p : ℝ) + 1)) *
          (T p / (Nat.factorial (2 * p) : ℝ)) := hr
      _ ≤ ((v / 2) / ((p : ℝ) + 1)) *
          (d * (v / 2) ^ p / (Nat.factorial p : ℝ)) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := hs

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.MomentRecurrence

-- BEGIN GTProof.ProductMomentRecurrence
section

open MeasureTheory

namespace MatrixTail.Gaussian.GTFresh

theorem product_moment_recurrence {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i)) (p : ℕ)
    (hc : ∀ i, (∫ x, x i * rtrace (A i * series A x^(2*p+1)) ∂Measure.pi μ) ≤
      ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace (A i^2*series A x^(2*p)) ∂Measure.pi μ) :
    (∫ x, rtrace (series A x^(2*(p+1))) ∂Measure.pi μ) ≤
      ((2*p+1 : ℕ):ℝ) * specNorm (∑ i, A i^2) *
        ∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ := by
  have hi i := ((isPoly_coordinate i).mul (trace_coefficient_isPoly A (A i) (2*p+1))).integrable μ hμ
  have hq i := (trace_coefficient_isPoly A (A i^2) (2*p)).integrable μ hμ
  have hv := (trace_coefficient_isPoly A (∑ i, A i^2) (2*p)).integrable μ hμ
  have hp := (series_trace_power_isPoly A (2*p)).integrable μ hμ
  rw [show 2*(p+1)=(2*p+1)+1 by omega]
  simp_rw [trace_series_power_step]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ ≤ ∑ i, ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace (A i^2*series A x^(2*p)) ∂Measure.pi μ :=
      Finset.sum_le_sum (fun i _ => hc i)
    _ = ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace ((∑ i, A i^2)*series A x^(2*p)) ∂Measure.pi μ := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => hq i)]
      simp_rw [trace_variance_sum]
    _ ≤ ((2*p+1 : ℕ):ℝ) * (specNorm (∑ i, A i^2) *
        ∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← integral_const_mul]
      exact integral_mono hv (hp.const_mul _) (fun x =>
        rtrace_mul_even_le _ _ (variance_hermitian A hA) (series_hermitian A hA x) p)
    _ = _ := by ring

theorem product_normalized_moments {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i k, Integrable (fun x : ℝ => x^k) (μ i))
    (hc : ∀ p i, (∫ x, x i * rtrace (A i * series A x^(2*p+1)) ∂Measure.pi μ) ≤
      ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace (A i^2*series A x^(2*p)) ∂Measure.pi μ) (p : ℕ) :
    (∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ) / ((2*p).factorial : ℝ) ≤
      d * (specNorm (∑ i, A i^2)/2)^p / (p.factorial : ℝ) := by
  apply normalized_moment_bound (fun p => ∫ x, rtrace (series A x^(2*p)) ∂Measure.pi μ)
    (d : ℝ) (specNorm (∑ i, A i^2)) (norm_nonneg _)
  · simp
  · intro j
    exact product_moment_recurrence A hA μ hμ j (hc j)

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.ProductMomentRecurrence

-- BEGIN GTProof.PolynomialSections
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh

theorem IsPoly.section_polynomial {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : IsPoly f) (i : Fin (n + 1)) (x : Fin n → ℝ) :
    ∃ p : Polynomial ℝ, ∀ t, p.eval t = f (i.insertNth t x) := by
  obtain ⟨p, hp⟩ := hf
  let v : Fin (n + 1) → Polynomial ℝ := i.insertNth Polynomial.X (fun j => Polynomial.C (x j))
  refine ⟨MvPolynomial.eval₂Hom Polynomial.C v p, fun t => ?_⟩
  have he : (Polynomial.evalRingHom t).comp (MvPolynomial.eval₂Hom Polynomial.C v) =
      MvPolynomial.eval (i.insertNth t x) := by
    ext r
    · simp
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      change (v r).eval t = (Fin.insertNth (α := fun _ => ℝ) i t x) r
      refine i.succAboveCases ?_ (fun k => ?_) r
      · simp [v]
      · simp [v]
  have hh := congrArg (fun h : MvPolynomial (Fin (n + 1)) ℝ →+* ℝ => h p) he
  exact hh.trans (hp _)

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.PolynomialSections

-- BEGIN GTProof.ProductCoordinateIntegral
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory

theorem integral_pi_insert {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f (Measure.pi μ)) :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ x : Fin n → ℝ, ∫ t : ℝ, f (i.insertNth t x) ∂μ i
        ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hm := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (fun z => f (e z))
      ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) :=
    (hm.integrable_comp_emb e.measurableEmbedding).mpr hf
  rw [← hm.integral_comp' f, integral_prod_symm _ hi]
  rfl

theorem integrable_integral_pi_insert {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : Integrable f (Measure.pi μ)) :
    Integrable (fun x : Fin n → ℝ => ∫ t : ℝ, f (i.insertNth t x) ∂μ i)
      (Measure.pi (fun j => μ (i.succAbove j))) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hm := (measurePreserving_piFinSuccAbove μ i).symm
  have hi : Integrable (fun z => f (e z))
      ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) :=
    (hm.integrable_comp_emb e.measurableEmbedding).mpr hf
  exact hi.integral_prod_right

theorem gaussian_coordinate_stein {n : ℕ} (i : Fin (n + 1))
    (f g : (Fin (n + 1) → ℝ) → ℝ) (hf : IsPoly f)
    (hg : Integrable g (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hd : ∀ x : Fin n → ℝ, ∀ t : ℝ,
      HasDerivAt (fun u => f (i.insertNth u x)) (g (i.insertNth t x)) t) :
    (∫ x, x i * f x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ x, g x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hi := ((isPoly_coordinate i).mul hf).integrable
    (fun _ => gaussianReal 0 1) (fun _ k => gaussian_integrable_pow k)
  rw [integral_pi_insert _ i _ hi, integral_pi_insert _ i _ hg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    obtain ⟨p, hp⟩ := hf.section_polynomial i x
    have hg' (t : ℝ) : p.derivative.eval t = g (i.insertNth t x) :=
      ((p.hasDerivAt t).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => (hp t).symm))).unique (hd x t)
    simpa only [Fin.insertNth_apply_same, ← hp, ← hg'] using gaussian_polynomial_stein p)

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.ProductCoordinateIntegral

-- BEGIN GTProof.PolynomialDerivative
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh

theorem polynomial_coordinate_hasDerivAt {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (i : Fin (n + 1))
    (x : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun u => MvPolynomial.eval (i.insertNth u x) p)
      (MvPolynomial.eval (i.insertNth t x) (MvPolynomial.pderiv i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    have h := (hp.add hq).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u => by
        exact map_add _ p q))
    exact h.congr_deriv (by simp only [map_add])
  | mul_X p j hp =>
    have hj : HasDerivAt (fun u : ℝ => (Fin.insertNth (α := fun _ => ℝ) i u x) j)
        (if j = i then (1 : ℝ) else 0) t := by
      refine i.succAboveCases ?_ (fun k => ?_) j
      · simp only [Fin.insertNth_apply_same]
        exact hasDerivAt_id t
      · simpa using hasDerivAt_const t (x k)
    have he : (fun u : ℝ => MvPolynomial.eval (i.insertNth u x) (p * MvPolynomial.X j)) =
        (fun u : ℝ => MvPolynomial.eval (i.insertNth u x) p *
          (Fin.insertNth (α := fun _ => ℝ) i u x) j) := by
      funext u
      simp only [map_mul, MvPolynomial.eval_X]
    have h := (hp.mul hj).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun u => congrFun he u))
    apply h.congr_deriv
    by_cases hji : j = i
    · subst j
      simp [mul_comm, add_comm]
    · simp [MvPolynomial.pderiv_X_of_ne hji, hji, mul_comm]


theorem IsPoly.coordinate_derivative {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : IsPoly f) (i : Fin (n + 1)) :
    ∃ g : (Fin (n + 1) → ℝ) → ℝ, IsPoly g ∧
      ∀ x : Fin n → ℝ, ∀ t : ℝ,
        HasDerivAt (fun u => f (i.insertNth u x)) (g (i.insertNth t x)) t := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun x => MvPolynomial.eval x (MvPolynomial.pderiv i p),
    ⟨MvPolynomial.pderiv i p, fun _ => rfl⟩, fun x t => ?_⟩
  exact (polynomial_coordinate_hasDerivAt p i x t).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => (hp (i.insertNth u x)).symm))

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.PolynomialDerivative

-- BEGIN GTProof.CoordinateSeries
section

namespace MatrixTail.Gaussian.GTFresh

theorem series_insert {n d : ℕ} (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ)
    (i : Fin (n+1)) (x : Fin n → ℝ) (t : ℝ) :
    series A (i.insertNth t x) = t • A i +
      ∑ j, x j • A (i.succAbove j) := by
  unfold series
  rw [Fin.sum_univ_succAbove _ i]
  simp

theorem series_insert_add {n d : ℕ} (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ)
    (i : Fin (n+1)) (x : Fin n → ℝ) (t u : ℝ) :
    series A (i.insertNth (t+u) x) = series A (i.insertNth t x) + u • A i := by
  rw [series_insert, series_insert, add_smul]
  abel

theorem series_insert_one {n d : ℕ} (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ)
    (i : Fin (n+1)) (x : Fin n → ℝ) :
    series A (i.insertNth 1 x) = series A (i.insertNth 0 x) + A i := by
  simpa using series_insert_add A i x 0 1

theorem series_insert_neg_one {n d : ℕ} (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ)
    (i : Fin (n+1)) (x : Fin n → ℝ) :
    series A (i.insertNth (-1) x) = series A (i.insertNth 0 x) - A i := by
  simpa [sub_eq_add_neg] using series_insert_add A i x 0 (-1)

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.CoordinateSeries

-- BEGIN GTProof.TraceDerivativeBound
section

open Filter
open scoped Topology

namespace MatrixTail.Gaussian.GTFresh

theorem trace_slope_bound {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (hA : A.IsHermitian) (p : ℕ) (t : ℝ) (ht : 0 < t) :
    (rtrace (A * (H+t•A)^(2*p+1)) - rtrace (A*H^(2*p+1))) / t ≤
      ((2*p+1 : ℕ) : ℝ)/2 * rtrace (A^2*((H+t•A)^(2*p)+H^(2*p))) := by
  have h := matrix_odd_power_secant (H+t•A) H (hH.add (hA.smul (by rfl))) hH p
  have hs : (t • A)^2 = t^2 • A^2 := by
    simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show H+t•A-H=t•A by abel, hs, smul_mul_assoc, rtrace_smul,
    smul_mul_assoc, rtrace_smul, mul_sub, rtrace_sub] at h
  apply (div_le_iff₀ ht).2
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith only [h]

theorem trace_derivative_bound {d : ℕ} (H A : Matrix (Fin d) (Fin d) ℂ)
    (hH : H.IsHermitian) (hA : A.IsHermitian) (p : ℕ) (f' : ℝ)
    (hf : HasDerivAt (fun t : ℝ => rtrace (A*(H+t•A)^(2*p+1))) f' 0) :
    f' ≤ ((2*p+1 : ℕ) : ℝ) * rtrace (A^2*H^(2*p)) := by
  have hl := hf.tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, ← div_eq_inv_mul] at hl
  have hc : Continuous (fun t : ℝ => ((2*p+1 : ℕ) : ℝ)/2 *
      rtrace (A^2*((H+t•A)^(2*p)+H^(2*p)))) := by
    apply Continuous.mul continuous_const
    exact continuous_rtrace.comp (by fun_prop)
  have hr := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (rtrace (A*(H+t•A)^(2*p+1))-rtrace (A*H^(2*p+1)))/t ≤
      ((2*p+1 : ℕ):ℝ)/2*rtrace (A^2*((H+t•A)^(2*p)+H^(2*p))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact trace_slope_bound H A hH hA p t ht
  have hh := le_of_tendsto_of_tendsto hl hr hb
  simp only [zero_smul, add_zero, mul_add, rtrace_add] at hh
  linarith

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.TraceDerivativeBound

-- BEGIN GTProof.GaussianMomentStep
section

open MeasureTheory ProbabilityTheory

namespace MatrixTail.Gaussian.GTFresh

theorem gaussian_trace_coordinate_bound {n d : ℕ}
    (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (i : Fin (n+1)) (p : ℕ) :
    (∫ x, x i * rtrace (A i * series A x ^ (2*p+1))
      ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) ≤
      ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace (A i ^ 2 * series A x ^ (2*p))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hf := trace_coefficient_isPoly A (A i) (2*p+1)
  obtain ⟨g, hg, hd⟩ := hf.coordinate_derivative i
  have hgi : Integrable g μ := hg.integrable _ (fun _ k => gaussian_integrable_pow k)
  rw [gaussian_coordinate_stein i _ g hf hgi hd]
  have hqi := (trace_coefficient_isPoly A (A i ^ 2) (2*p)).integrable
    (fun _ => gaussianReal 0 1) (fun _ k => gaussian_integrable_pow k)
  rw [← integral_const_mul]
  apply integral_mono hgi (hqi.const_mul _)
  intro y
  have bound (x : Fin n → ℝ) (t : ℝ) :
      g (i.insertNth t x) ≤ ((2*p+1 : ℕ):ℝ) *
        rtrace (A i ^ 2 * series A (i.insertNth t x) ^ (2*p)) := by
    have hi : HasDerivAt (fun u : ℝ => t+u) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add t
    have hdt : HasDerivAt (fun u => rtrace (A i * series A (i.insertNth u x)^(2*p+1)))
        (g (i.insertNth t x)) (t+0) := by simpa only [add_zero] using hd x t
    have hs := hdt.comp 0 hi
    have hs' : HasDerivAt
        (fun u : ℝ => rtrace (A i * (series A (i.insertNth t x)+u•A i)^(2*p+1)))
        (g (i.insertNth t x)) 0 := by
      simpa only [Function.comp_def, add_zero, mul_one, series_insert_add] using hs
    exact trace_derivative_bound _ _ (series_hermitian A hA _) (hA i) p _ hs'
  simpa using bound (i.removeNth y) (y i)

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.GaussianMomentStep

-- BEGIN GTProof.SignCoordinateIntegral
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory

theorem sign_coordinate_integral {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => signLaw))) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (n + 1) => signLaw)) =
      ∫ x : Fin n → ℝ, (f (i.insertNth 1 x) + f (i.insertNth (-1) x)) / 2
        ∂Measure.pi (fun _ : Fin n => signLaw) := by
  rw [integral_pi_insert _ i _ hf]
  simp_rw [integral_signLaw]

theorem integrable_sign_coordinate_average {n : ℕ} (i : Fin (n + 1))
    (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => signLaw))) :
    Integrable (fun x : Fin n → ℝ =>
      (f (i.insertNth 1 x) + f (i.insertNth (-1) x)) / 2)
      (Measure.pi (fun _ : Fin n => signLaw)) := by
  simpa only [integral_signLaw] using integrable_integral_pi_insert
    (fun _ : Fin (n + 1) => signLaw) i f hf

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.SignCoordinateIntegral

-- BEGIN GTProof.SignMomentStep
section

open MeasureTheory

namespace MatrixTail.Gaussian.GTFresh

theorem sign_trace_coordinate_bound {n d : ℕ}
    (A : Fin (n+1) → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (i : Fin (n+1)) (p : ℕ) :
    (∫ x, x i * rtrace (A i * series A x ^ (2*p+1))
      ∂Measure.pi (fun _ : Fin (n+1) => signLaw)) ≤
      ((2*p+1 : ℕ):ℝ) * ∫ x, rtrace (A i ^ 2 * series A x ^ (2*p))
        ∂Measure.pi (fun _ : Fin (n+1) => signLaw) := by
  let f := fun x => x i * rtrace (A i * series A x ^ (2*p+1))
  let g := fun x => ((2*p+1 : ℕ):ℝ) * rtrace (A i ^ 2 * series A x ^ (2*p))
  have hf := ((isPoly_coordinate i).mul (trace_coefficient_isPoly A (A i) (2*p+1))).integrable
    (fun _ => signLaw) (fun _ _ => integrable_signLaw _)
  have hg := ((isPoly_const ((2*p+1 : ℕ):ℝ)).mul
    (trace_coefficient_isPoly A (A i ^ 2) (2*p))).integrable
    (fun _ => signLaw) (fun _ _ => integrable_signLaw _)
  rw [← integral_const_mul]
  change (∫ x, f x ∂Measure.pi (fun _ : Fin (n+1) => signLaw)) ≤ ∫ x, g x ∂_
  rw [sign_coordinate_integral i f hf, sign_coordinate_integral i g hg]
  apply integral_mono (integrable_sign_coordinate_average i f hf)
    (integrable_sign_coordinate_average i g hg)
  intro x
  have h := rademacher_trace_step (series A (i.insertNth 0 x)) (A i)
    (series_hermitian A hA _) (hA i) p
  dsimp [f, g]
  simp only [Fin.insertNth_apply_same, one_mul, neg_one_mul,
    series_insert_one, series_insert_neg_one]
  nlinarith [h]

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.SignMomentStep

-- BEGIN GTProof.NativeMoments
section

open MeasureTheory ProbabilityTheory

namespace MatrixTail.Gaussian.GTFresh

theorem gaussian_normalized_moments {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    (∫ x, rtrace (series A x^(2*p)) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) /
      ((2*p).factorial : ℝ) ≤ d * (specNorm (∑ i, A i^2)/2)^p / (p.factorial : ℝ) := by
  apply product_normalized_moments A hA _ (fun _ k => gaussian_integrable_pow k)
  intro j i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact gaussian_trace_coordinate_bound A hA i j

theorem sign_normalized_moments {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian) (p : ℕ) :
    (∫ x, rtrace (series A x^(2*p)) ∂Measure.pi (fun _ : Fin n => signLaw)) /
      ((2*p).factorial : ℝ) ≤ d * (specNorm (∑ i, A i^2)/2)^p / (p.factorial : ℝ) := by
  apply product_normalized_moments A hA _ (fun _ _ => integrable_signLaw _)
  intro j i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact sign_trace_coordinate_bound A hA i j

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.NativeMoments

-- BEGIN GTProof.NativeJointLaw
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem gaussian_joint_law {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hi : iIndepFun ξ P) (hξ : ∀ i, IsStdGaussian P (ξ i)) :
    P.map (fun ω i => ξ i ω) = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hξ i).1.aemeasurable) hi]
  simp_rw [(fun i => (hξ i).2)]

theorem rademacher_joint_law {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hi : iIndepFun ξ P) (hξ : ∀ i, IsRademacher P (ξ i)) :
    P.map (fun ω i => ξ i ω) = Measure.pi (fun _ : Fin n => signLaw) := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (hξ i).1.aemeasurable) hi]
  simp_rw [fun i => rademacher_map_eq_signLaw P (hξ i)]

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.NativeJointLaw

-- BEGIN GTProof.NativeMGF
section

open MeasureTheory ProbabilityTheory

namespace MatrixTail.Gaussian.GTFresh

theorem native_trace_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n d : ℕ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hind : iIndepFun ξ P)
    (hlaw : (∀ i, IsStdGaussian P (ξ i)) ∨ (∀ i, IsRademacher P (ξ i))) (t : ℝ) :
    Integrable (fun ω => rtrace (MatrixTail.Master.mexp (t•series A (fun i => ξ i ω)))) P ∧
      (∫ ω, rtrace (MatrixTail.Master.mexp (t•series A (fun i => ξ i ω))) ∂P) ≤
        d*Real.exp (t^2*specNorm (∑ i, A i^2)/2) := by
  have transport (μ : Measure (Fin n → ℝ))
      (hm : P.map (fun ω i => ξ i ω) = μ)
      (hξ : Measurable (fun ω i => ξ i ω))
      (hb : Integrable (fun x => rtrace (MatrixTail.Master.mexp (t•series A x))) μ ∧
        (∫ x, rtrace (MatrixTail.Master.mexp (t•series A x)) ∂μ) ≤
          d*Real.exp (t^2*specNorm (∑ i, A i^2)/2)) :
      Integrable (fun ω => rtrace (MatrixTail.Master.mexp (t•series A (fun i => ξ i ω)))) P ∧
      (∫ ω, rtrace (MatrixTail.Master.mexp (t•series A (fun i => ξ i ω))) ∂P) ≤
        d*Real.exp (t^2*specNorm (∑ i, A i^2)/2) := by
    have hp : MeasurePreserving (fun ω i => ξ i ω) P μ := ⟨hξ, hm⟩
    refine ⟨hp.integrable_comp_of_integrable hb.1, ?_⟩
    have he := integral_map (μ := P) hξ.aemeasurable (measurable_series_exp A hA t).aestronglyMeasurable
    rw [hm] at he
    rw [← he]
    exact hb.2
  rcases hlaw with hg | hs
  · apply transport _ (gaussian_joint_law P ξ hind hg) (measurable_pi_lambda _ (fun i => (hg i).1))
    exact exp_bound_of_symmetric_moments A hA (fun _ => gaussianReal 0 1)
      (fun _ k => gaussian_integrable_pow k) _ (gaussian_normalized_moments A hA)
      (gaussian_product_neg_preserving n) t
  · apply transport _ (rademacher_joint_law P ξ hind hs) (measurable_pi_lambda _ (fun i => (hs i).1))
    exact exp_bound_of_symmetric_moments A hA (fun _ => signLaw)
      (fun _ _ => integrable_signLaw _) _ (sign_normalized_moments A hA)
      (sign_product_neg_preserving n) t

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.NativeMGF

-- BEGIN GTProof.SpectralTail
section

open scoped Matrix.Norms.L2Operator

namespace MatrixTail.Gaussian.GTFresh

theorem spectrum_real_finite {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) : (spectrum ℝ X).Finite := by
  rw [hX.spectrum_real_eq_range_eigenvalues]
  exact Set.finite_range _

theorem eigenvalue_le_lambdaMax {d : ℕ} (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (i : Fin d) :
    hX.eigenvalues i ≤ MatrixTail.Master.lambdaMax X :=
  le_csSup (spectrum_real_finite X hX).bddAbove (hX.eigenvalues_mem_spectrum_real i)

theorem lambdaMax_eq_eigenvalue {d : ℕ} [NeZero d]
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    ∃ i, MatrixTail.Master.lambdaMax X = hX.eigenvalues i := by
  have hn : (spectrum ℝ X).Nonempty :=
    ⟨hX.eigenvalues 0, hX.eigenvalues_mem_spectrum_real 0⟩
  have hm := hn.csSup_mem (spectrum_real_finite X hX)
  rw [hX.spectrum_real_eq_range_eigenvalues] at hm
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, ?_⟩
  simpa only [MatrixTail.Master.lambdaMax, hX.spectrum_real_eq_range_eigenvalues] using hi.symm

theorem exp_lambdaMax_le_trace {d : ℕ} [NeZero d]
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) (θ : ℝ) :
    Real.exp (θ * MatrixTail.Master.lambdaMax X) ≤
      rtrace (MatrixTail.Master.mexp (θ • X)) := by
  obtain ⟨i, hi⟩ := lambdaMax_eq_eigenvalue X hX
  have he : cfc (fun t : ℝ => Real.exp (θ * t)) X = cfc Real.exp (θ • X) :=
    cfc_comp_const_mul θ Real.exp X (ha := hX)
  change Real.exp (θ * MatrixTail.Master.lambdaMax X) ≤ rtrace (cfc Real.exp (θ • X))
  rw [← he, rtrace_cfc X hX, hi]
  exact Finset.single_le_sum (fun j _ => (Real.exp_pos (θ * hX.eigenvalues j)).le)
    (Finset.mem_univ i)

theorem specNorm_le_max_lambdaMax {d : ℕ} [NeZero d]
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) :
    specNorm X ≤ max (MatrixTail.Master.lambdaMax X) (MatrixTail.Master.lambdaMax (-X)) := by
  let c := max (MatrixTail.Master.lambdaMax X) (MatrixTail.Master.lambdaMax (-X))
  have hb (x : ℝ) (hx : x ∈ spectrum ℝ X) : |x| ≤ c := by
    have hx' : -x ∈ spectrum ℝ (-X) := by
      rw [← spectrum.neg_eq, Set.mem_neg]
      simpa only [neg_neg] using hx
    have h₁ := le_csSup (spectrum_real_finite X hX).bddAbove hx
    have h₂ := le_csSup (spectrum_real_finite (-X) hX.neg).bddAbove hx'
    apply abs_le.mpr
    constructor
    · have h := le_max_right (MatrixTail.Master.lambdaMax X)
        (MatrixTail.Master.lambdaMax (-X))
      change -x ≤ MatrixTail.Master.lambdaMax (-X) at h₂
      dsimp [c]
      linarith
    · exact h₁.trans (le_max_left _ _)
  have hc : 0 ≤ c := (abs_nonneg (hX.eigenvalues 0)).trans
    (hb _ (hX.eigenvalues_mem_spectrum_real 0))
  have hh : ‖cfc (fun x : ℝ => x) X‖ ≤ c :=
    norm_cfc_le hc (fun x hx => by simpa only [Real.norm_eq_abs] using hb x hx)
  have hid : cfc (fun x : ℝ => x) X = X := cfc_id (R := ℝ) X (ha := hX)
  rw [hid] at hh
  simpa only [Matrix.cstar_norm_def, specNorm] using hh

theorem specNorm_event_union {d : ℕ} [NeZero d]
    (X : Matrix (Fin d) (Fin d) ℂ) (hX : X.IsHermitian) (t : ℝ)
    (ht : t ≤ specNorm X) :
    t ≤ MatrixTail.Master.lambdaMax X ∨ t ≤ MatrixTail.Master.lambdaMax (-X) := by
  exact le_max_iff.mp (ht.trans (specNorm_le_max_lambdaMax X hX))

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.SpectralTail

-- BEGIN GTProof.OuterMarkov
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory

theorem outer_markov_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : Integrable f P) (hn : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (E : Set Ω) (a : ℝ) (ha : 0 < a) (hE : ∀ ω ∈ E, a ≤ f ω) :
    P.real E ≤ (∫ ω, f ω ∂P) / a := by
  have hm := mul_meas_ge_le_integral_of_nonneg hn hf a
  have hs : E ⊆ {ω | a ≤ f ω} := hE
  have hmono := measureReal_mono (μ := P) hs
  apply (le_div_iff₀ ha).mpr
  calc
    P.real E * a ≤ P.real {ω | a ≤ f ω} * a := mul_le_mul_of_nonneg_right hmono ha.le
    _ = a * P.real {ω | a ≤ f ω} := mul_comm _ _
    _ ≤ _ := hm

theorem outer_exponential_markov {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : Integrable f P) (hn : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (E : Set Ω) (u B : ℝ) (hE : ∀ ω ∈ E, Real.exp u ≤ f ω)
    (hB : (∫ ω, f ω ∂P) ≤ B) :
    P.real E ≤ Real.exp (-u) * B := by
  calc
    P.real E ≤ (∫ ω, f ω ∂P) / Real.exp u :=
      outer_markov_real P f hf hn E _ (Real.exp_pos u) hE
    _ ≤ B / Real.exp u := div_le_div_of_nonneg_right hB (Real.exp_pos u).le
    _ = Real.exp (-u) * B := by rw [Real.exp_neg]; ring

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.OuterMarkov

-- BEGIN GTProof.NativeTail
section

noncomputable section
namespace MatrixTail.Gaussian.GTFresh
open MeasureTheory ProbabilityTheory

theorem native_lambda_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n d : ℕ} [NeZero d]
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hind : iIndepFun ξ P)
    (hlaw : (∀ i, IsStdGaussian P (ξ i)) ∨ (∀ i, IsRademacher P (ξ i)))
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (series A (fun i => ξ i ω))} ≤
      d * Real.exp (-t ^ 2 / (2 * specNorm (∑ i, A i ^ 2))) := by
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  let v := specNorm (∑ i, A i ^ 2)
  have hv : 0 ≤ v := norm_nonneg _
  change _ ≤ d * Real.exp (-t ^ 2 / (2 * v))
  by_cases hv0 : v = 0
  · simp only [hv0, mul_zero, div_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hd
  by_cases ht0 : t = 0
  · simp only [ht0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      neg_zero, zero_div, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hd
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let θ := t / v
  have hθ : 0 < θ := div_pos htp hvp
  let f := fun ω => rtrace (MatrixTail.Master.mexp (θ • series A (fun i => ξ i ω)))
  have hm := native_trace_mgf P A hA ξ hind hlaw θ
  have hn : ∀ᵐ ω ∂P, 0 ≤ f ω := Filter.Eventually.of_forall (fun ω =>
    rtrace_mexp_nonneg _ ((series_hermitian A hA _).smul (by rfl)))
  have he : ∀ ω ∈ {ω | t ≤ MatrixTail.Master.lambdaMax (series A (fun i => ξ i ω))},
      Real.exp (θ * t) ≤ f ω := by
    intro ω hω
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ.le)).trans
      (exp_lambdaMax_le_trace _ (series_hermitian A hA _) θ)
  have hb := outer_exponential_markov P f hm.1 hn _ (θ * t)
    (d * Real.exp (θ ^ 2 * v / 2)) he hm.2
  calc
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (series A (fun i => ξ i ω))} ≤
        Real.exp (-(θ * t)) * (d * Real.exp (θ ^ 2 * v / 2)) := hb
    _ = d * Real.exp (-t ^ 2 / (2 * v)) := by
      rw [← mul_assoc, mul_comm (Real.exp (-(θ * t))) (d : ℝ), mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      dsimp [θ]
      field_simp
      ring

theorem native_norm_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n d : ℕ} [NeZero d]
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ i, (A i).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hind : iIndepFun ξ P)
    (hlaw : (∀ i, IsStdGaussian P (ξ i)) ∨ (∀ i, IsRademacher P (ξ i)))
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ specNorm (series A (fun i => ξ i ω))} ≤
      2 * d * Real.exp (-t ^ 2 / (2 * specNorm (∑ i, A i ^ 2))) := by
  have hp := native_lambda_tail P A hA ξ hind hlaw t ht
  have hn := native_lambda_tail P (fun i => -A i) (fun i => (hA i).neg) ξ hind hlaw t ht
  have hneg (x : Fin n → ℝ) : series (fun i => -A i) x = -series A x := by
    simp only [series, smul_neg, Finset.sum_neg_distrib]
  simp only [hneg, neg_sq] at hn
  have hs : {ω | t ≤ specNorm (series A (fun i => ξ i ω))} ⊆
      {ω | t ≤ MatrixTail.Master.lambdaMax (series A (fun i => ξ i ω))} ∪
      {ω | t ≤ MatrixTail.Master.lambdaMax (-series A (fun i => ξ i ω))} := by
    intro ω hω
    exact specNorm_event_union _ (series_hermitian A hA _) t hω
  have hu := (measureReal_mono (μ := P) hs).trans (measureReal_union_le _ _)
  linarith

end MatrixTail.Gaussian.GTFresh
end
end
-- END GTProof.NativeTail

-- BEGIN GTProof.NativeConclusion
section

open MeasureTheory ProbabilityTheory

namespace MatrixTail.Gaussian.GTFresh

theorem native_theorem4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hAherm : ∀ k, (A k).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hindep : iIndepFun ξ P)
    (hlaw : (∀ k, IsStdGaussian P (ξ k)) ∨ (∀ k, IsRademacher P (ξ k))) :
    ∀ t : ℝ, 0 ≤ t →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, ξ k ω • A k)} ≤
          d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) ∧
        P.real {ω | t ≤ specNorm (∑ k, ξ k ω • A k)} ≤
          2 * d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) := by
  intro t ht
  exact ⟨native_lambda_tail P A hAherm ξ hindep hlaw t ht,
    native_norm_tail P A hAherm ξ hindep hlaw t ht⟩

end MatrixTail.Gaussian.GTFresh
end
-- END GTProof.NativeConclusion

-- BEGIN GTProof.FinalRoot
section

open MeasureTheory ProbabilityTheory

namespace MatrixTail.Gaussian

/-- **Theorem 4.1** (Matrix Gaussian and Rademacher Series), Tropp, arXiv:1004.4389v7, p. 14, displays
(4.2)–(4.4). Let `A₀, …, A_{n-1}` be fixed self-adjoint `d × d` matrices and `ξ₀, …, ξ_{n-1}` independent
scalar random variables that are either all standard normal or all Rademacher. With the variance parameter
`σ² := ‖Σ_k A_k²‖` (4.2), for all `t ≥ 0`:
* (4.3) `P{λmax(Σ_k ξ_k A_k) ≥ t} ≤ d · e^{−t²/2σ²}`;
* (4.4) `P{‖Σ_k ξ_k A_k‖ ≥ t} ≤ 2d · e^{−t²/2σ²}`.

Formalization Note.
* Complex Hermitian matrices; `‖·‖` is the spectral norm `specNorm`; `[NeZero d]` (at `d = 0` the right
  sides vanish while the probability at `t = 0` is `1`).
* "Gaussian or Rademacher" is the disjunction of two universal statements: the paper's sequence is all
  standard normal or all Rademacher, never a mixture.
* σ² is the norm of the sum, `specNorm (∑ k, A k ^ 2)`, not the sum of the norms.
* Boundary `σ² = 0`: Lean's `x / 0 = 0` makes the right sides `d` and `2d`, which are valid (and, at
  `t = 0`, the paper's values); for `t > 0` the paper's convention `e^{−∞} = 0` would give `0`, so at this
  degenerate point (all `A_k = 0`) the Lean bound is the trivial one. No positivity hypothesis is added. -/
theorem theorem4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hAherm : ∀ k, (A k).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hindep : iIndepFun ξ P)
    (hlaw : (∀ k, IsStdGaussian P (ξ k)) ∨ (∀ k, IsRademacher P (ξ k))) :
    ∀ t : ℝ, 0 ≤ t →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, ξ k ω • A k)} ≤
          d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) ∧
        P.real {ω | t ≤ specNorm (∑ k, ξ k ω • A k)} ≤
          2 * d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) := by
  exact GTFresh.native_theorem4_1 P A hAherm ξ hindep hlaw

end MatrixTail.Gaussian
end
-- END GTProof.FinalRoot

open MeasureTheory ProbabilityTheory
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hAherm : ∀ k, (A k).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hindep : iIndepFun ξ P)
    (hlaw : (∀ k, MatrixTail.Gaussian.IsStdGaussian P (ξ k)) ∨ (∀ k, MatrixTail.Gaussian.IsRademacher P (ξ k))) :
    ∀ t : ℝ, 0 ≤ t →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, ξ k ω • A k)} ≤
          d * Real.exp (-t ^ 2 / (2 * MatrixTail.Gaussian.specNorm (∑ k, A k ^ 2))) ∧
        P.real {ω | t ≤ MatrixTail.Gaussian.specNorm (∑ k, ξ k ω • A k)} ≤
          2 * d * Real.exp (-t ^ 2 / (2 * MatrixTail.Gaussian.specNorm (∑ k, A k ^ 2))) := by
  exact MatrixTail.Gaussian.theorem4_1 P A hAherm ξ hindep hlaw
