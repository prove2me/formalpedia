-- Prove2me | solution 1 for MasulloAudit.mellin_kernel_projection_limit
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:55:14.40682+00:00
-- url     : https://prove2.me/submissions/182d09a7-047c-431e-b00d-d458d41d1ebb

import Mathlib
import Theorems.Thm_MasulloAudit_window_mellin_evaluation_bounded
section

open MeasureTheory Set Polynomial
open scoped SchwartzMap ContDiff

noncomputable section
namespace MasulloWindow

private lemma polynomial_exp_bound (p : ℂ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, ‖p.eval (x : ℂ)‖ ≤ K * Real.exp |x| := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
    refine ⟨‖a‖ * (n.factorial : ℝ), by positivity, ?_⟩
    intro x
    simp only [Polynomial.eval_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) n)
    calc
      _ ≤ ‖a‖ * (Real.exp |x| * n.factorial) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = _ := by ring
  | add p q hp hq =>
    obtain ⟨K, hK, hp⟩ := hp
    obtain ⟨L, hL, hq⟩ := hq
    refine ⟨K+L, by positivity, fun x => ?_⟩
    rw [Polynomial.eval_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hp x) (hq x))

private lemma exponential_polynomial_derivative (q : ℂ[X]) (n : ℕ) :
    ∃ p : ℂ[X], iteratedDeriv n (fun x : ℝ => Complex.exp (q.eval (x : ℂ))) =
      fun x : ℝ => p.eval (x : ℂ) * Complex.exp (q.eval (x : ℂ)) := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.derivative+p*q.derivative, ?_⟩
    rw [iteratedDeriv_succ, hp]
    funext x
    have h := ((p.hasDerivAt (x : ℂ)).mul ((q.hasDerivAt (x : ℂ)).cexp)).comp_ofReal
    convert h.deriv using 1 <;> simp [Polynomial.eval_add, Polynomial.eval_mul]; ring

private lemma quadratic_schwartz (b c : ℂ) (hb : b.re < 0) :
    ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = Complex.exp (b*x^2 + c*x) := by
  let q : ℂ[X] := C b * X^2 + C c * X
  have hq (x : ℝ) : q.eval (x : ℂ) = b*x^2+c*x := by simp [q]
  let g : ℝ → ℂ := fun x => Complex.exp (q.eval (x : ℂ))
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hg : ContDiff ℝ ∞ g := by dsimp [g]; simp_rw [hq]; fun_prop
  refine ⟨⟨g,hg,?_⟩,fun x => by change Complex.exp (q.eval _) = _; rw [hq]⟩
  intro k n
  obtain ⟨p,hp⟩ := exponential_polynomial_derivative q n
  obtain ⟨K,hK,hP⟩ := polynomial_exp_bound (X^k*p)
  let L : ℝ := 1+|c.re|
  refine ⟨K*Real.exp (L^2/(-4*b.re)),fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖x‖^k * ‖iteratedDeriv n (fun x : ℝ => Complex.exp (q.eval (x : ℂ))) x‖ ≤ _
  rw [hp, norm_mul, ← mul_assoc, Real.norm_eq_abs]
  have hpx := hP x
  simp [Polynomial.eval_mul, norm_pow, Real.norm_eq_abs] at hpx
  have hreal : (q.eval (x : ℂ)).re = b.re*x^2+c.re*x := by
    rw [hq, ← Complex.ofReal_pow]; simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hquad : |x| + (b.re*x^2+c.re*x) ≤ L^2/(-4*b.re) := by
    have hcx := (le_abs_self (c.re*x)).trans_eq (abs_mul _ _)
    apply (le_div_iff₀ (by linarith : 0 < -4*b.re)).mpr
    have hlin : |x|+(b.re*x^2+c.re*x) ≤ b.re*x^2+L*|x| := by dsimp [L]; linarith
    apply (mul_le_mul_of_nonneg_right hlin (by linarith : 0 ≤ -4*b.re)).trans
    nlinarith [sq_nonneg (2*b.re*|x|+L), sq_abs x,
      show b.re^2*|x|^2 = b.re^2*x^2 by rw [sq_abs]]
  rw [Complex.norm_exp, hreal]
  calc
    _ ≤ K * Real.exp |x| * Real.exp (b.re*x^2+c.re*x) :=
      mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
    _ = K * Real.exp (|x|+(b.re*x^2+c.re*x)) := by rw [Real.exp_add |x| _]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad) hK



private lemma hasMellin_log_equiv (f : ℝ → ℂ) (s y : ℂ) :
    HasMellin (fun t : ℝ => f (Real.log t)) s y ↔
      Integrable (fun x : ℝ => Complex.exp (s*x) * f x) ∧
      (∫ x : ℝ, Complex.exp (s*x) * f x) = y := by
  have hder : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have himage : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hkey (x : ℝ) : |Real.exp x| • (((Real.exp x : ℝ) : ℂ) ^ (s-1) • f (Real.log (Real.exp x))) =
      Complex.exp (s*x) * f x := by
    rw [abs_of_pos (Real.exp_pos _), Real.log_exp, Complex.real_smul, smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_nonneg _), Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
      ← Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hder Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder Real.exp_injective.injOn]
  simp only [hkey, integrableOn_univ, setIntegral_univ]

private def quadCoeff (c : ℂ) := -(4*c)⁻¹
private def quadNormal (c : ℂ) := ((Real.pi:ℂ) / (-quadCoeff c)) ^ (1/2:ℂ)
private def quadTest (c : ℂ) (x : ℝ) := (quadNormal c)⁻¹ * Complex.exp (quadCoeff c*x^2)

private lemma quadCoeff_re_neg {c : ℂ} (hc : 0 < c.re) : (quadCoeff c).re < 0 := by
  simp [quadCoeff, Complex.inv_re, Complex.mul_re]
  exact div_pos hc (Complex.normSq_pos.mpr (fun h => by simp [h] at hc))

private lemma quadTest_hasMellin {c : ℂ} (hc : 0 < c.re) (s : ℂ) :
    HasMellin (fun t : ℝ => quadTest c (Real.log t)) s (Complex.exp (c*s^2)) := by
  rw [hasMellin_log_equiv]
  have hb := quadCoeff_re_neg hc
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  have hb0 : quadCoeff c ≠ 0 := fun h => by simp [h] at hb
  have hnorm : quadNormal c ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr (Or.inl ?_)
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (neg_ne_zero.mpr hb0)
  have he (x : ℝ) : Complex.exp (s*x)*quadTest c x =
      (quadNormal c)⁻¹ * Complex.exp (quadCoeff c*x^2 + s*x + 0) := by
    dsimp [quadTest]; rw [add_zero, Complex.exp_add]; ring
  simp_rw [he]
  refine ⟨(integrable_cexp_quadratic' hb s 0).const_mul _, ?_⟩
  rw [integral_const_mul, integral_cexp_quadratic hb, ← mul_assoc]
  change (quadNormal c)⁻¹ * quadNormal c * _ = _
  rw [inv_mul_cancel₀ hnorm, one_mul]
  congr 1
  dsimp [quadCoeff]; field_simp; ring

private lemma gaussianTilt (s : ℂ) : ∃ g : 𝓢(ℝ,ℂ),
    ∀ x : ℝ, g x = Complex.exp (s*x)*quadTest 1 x := by
  obtain ⟨g,hg⟩ := quadratic_schwartz (quadCoeff 1) s (quadCoeff_re_neg (c:=1) (by simp))
  refine ⟨(quadNormal 1)⁻¹ • g,fun x => ?_⟩
  change (quadNormal 1)⁻¹ * g x = _
  rw [hg, Complex.exp_add]; dsimp [quadTest]; ring

private def momentLog (x : ℝ) : ℂ := (x:ℂ)/2 * quadTest 1 x

private lemma momentTilt (s : ℂ) : ∃ g : 𝓢(ℝ, ℂ),
    ∀ x : ℝ, g x = Complex.exp (s*x) * momentLog x := by
  obtain ⟨g,hg⟩ := gaussianTilt s
  refine ⟨(2:ℂ)⁻¹ • (SchwartzMap.smulLeftCLM ℂ (Complex.ofReal) g),fun x => ?_⟩
  change (2:ℂ)⁻¹ * (SchwartzMap.smulLeftCLM ℂ Complex.ofReal g) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal, smul_eq_mul, hg]
  dsimp [momentLog]; ring

private lemma gaussianTilt_derivative (s : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (s*y)*quadTest 1 y)
      (s * (Complex.exp (s*x)*quadTest 1 x) - Complex.exp (s*x)*momentLog x) x := by
  let b : ℂ := quadCoeff 1
  have hb : b = -(1/4:ℂ) := by norm_num [b,quadCoeff]
  have hq := ((((hasDerivAt_id (x:ℂ)).pow 2).const_mul b).add
    ((hasDerivAt_id (x:ℂ)).const_mul s)).cexp.comp_ofReal
  have h := hq.const_mul ((quadNormal 1)⁻¹)
  convert! h using 1 <;> try rfl
  · funext y
    dsimp [quadTest,b]; rw [Complex.exp_add]; ring
  · dsimp [momentLog,quadTest,b,id]; rw [Complex.exp_add, show quadCoeff 1 = -(1/4:ℂ) from hb]; ring

private lemma moment_hasMellin (s : ℂ) :
    HasMellin (fun t : ℝ => momentLog (Real.log t)) s (s * Complex.exp (s^2)) := by
  rw [hasMellin_log_equiv]
  obtain ⟨g,hg⟩ := momentTilt s
  have hM : Integrable (fun x : ℝ => Complex.exp (s*x)*momentLog x) := by
    simpa only [← funext hg] using g.integrable
  have hH := (hasMellin_log_equiv (quadTest 1) s _).mp (quadTest_hasMellin (c:=1) (by simp) s)
  have hs := hH.1.const_mul s
  have hz := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable (gaussianTilt_derivative s)
    (hs.sub hM) hH.1
  rw [integral_sub hs hM, integral_const_mul, hH.2, one_mul, sub_eq_zero] at hz
  exact ⟨hM,hz.symm⟩

/-- A genuine exponentially Schwartz norm-line test whose entire Mellin transform has just one
zero, of analytic order one. -/
theorem exists_singleZero_mellin :
    ∃ φ : ℝ → ℂ,
      (∀ a : ℝ, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = Complex.exp ((a : ℂ)*x) * φ (Real.exp x)) ∧
      (∀ s : ℂ, HasMellin φ s (s * Complex.exp (s^2))) ∧
      (∀ s : ℂ, mellin φ s = 0 ↔ s = 0) ∧ analyticOrderAt (mellin φ) 0 = 1 := by
  let φ := fun t : ℝ => momentLog (Real.log t)
  have hM (s : ℂ) : HasMellin φ s (s * Complex.exp (s^2)) := moment_hasMellin s
  have he : mellin φ = id * (fun s : ℂ => Complex.exp (s^2)) := funext fun s => (hM s).2
  refine ⟨φ, ?_, hM, fun s => by simp [(hM s).2], ?_⟩
  · intro a
    simpa only [φ, Real.log_exp] using momentTilt (a : ℂ)
  · rw [he, analyticOrderAt_mul (by fun_prop) (by fun_prop), analyticOrderAt_id,
      show analyticOrderAt (fun s : ℂ => Complex.exp (s^2)) 0 = 0 from
        analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _)), add_zero]

end MasulloWindow

end
end

section

open Set Filter
open scoped Topology InnerProductSpace

namespace MasulloWindow
noncomputable section
variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Orthogonality to all rows is the common kernel of the represented functionals. -/
theorem mem_kernel_of_closed_span_iff (v : ι → H) (s : Set ι) (x : H) :
    x ∈ (Submodule.span 𝕜 (v '' s)).topologicalClosureᗮ ↔ ∀ i ∈ s, inner 𝕜 (v i) x = 0 := by
  rw [Submodule.orthogonal_closure]
  have he : v '' s = Set.range (fun i : s => v i.val) := by ext; simp
  rw [he, Submodule.span_range_eq_iSup, ← Submodule.iInf_orthogonal]
  simp only [Submodule.mem_iInf,Submodule.mem_orthogonal_singleton_iff_inner_right,Subtype.forall]

variable [CompleteSpace H]

/-- Finite-rank Riesz spans converge strongly to the closed span of all represented rows.
The complementary limits are the actual common kernel and are the identity exactly when all
represented functionals vanish. -/
theorem projection_limits (v : ι → H) (F : ℕ → Finset ι) (hF : Monotone F)
    (hex : ∀ i : ι, ∃ n : ℕ, i ∈ F n) :
    let U (n : ℕ) := (Submodule.span 𝕜 (v '' (F n : Set ι))).topologicalClosure
    let V := (Submodule.span 𝕜 (Set.range v)).topologicalClosure
    (∀ n : ℕ, ∀ x : H, x ∈ (U n)ᗮ ↔ ∀ i ∈ F n, inner 𝕜 (v i) x = 0) ∧
      (∀ x : H, x ∈ Vᗮ ↔ ∀ i : ι, inner 𝕜 (v i) x = 0) ∧
      (∀ x : H, Tendsto (fun n : ℕ => (U n).starProjection x) atTop (𝓝 (V.starProjection x))) ∧
      (∀ x : H, Tendsto (fun n : ℕ => (U n)ᗮ.starProjection x) atTop (𝓝 (Vᗮ.starProjection x))) ∧
      ((∀ x : H, Tendsto (fun n : ℕ => (U n)ᗮ.starProjection x) atTop (𝓝 x)) ↔ ∀ i : ι, v i = 0) := by
  classical
  intro U V
  have hUV : (⨆ n, U n).topologicalClosure = V := by
    apply le_antisymm
    · apply (iSup U).topologicalClosure_minimal _ (Submodule.isClosed_topologicalClosure _)
      apply iSup_le
      intro n
      exact Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_subset_range v _))
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      obtain ⟨n,hi⟩ := hex i
      exact (le_iSup U n) ((Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨i,hi,rfl⟩))
  have hmono : Monotone U := fun _ _ h => Submodule.topologicalClosure_mono <|
    Submodule.span_mono (Set.image_mono (show (↑(F _) : Set ι) ⊆ ↑(F _) from hF h))
  have hP (x : H) : Tendsto (fun n : ℕ => (U n).starProjection x) atTop (𝓝 (V.starProjection x)) := by
    have h := Submodule.starProjection_tendsto_closure_iSup U hmono x
    convert! h using 2
    congr 2
    exact hUV.symm
  have hQ (x : H) : Tendsto (fun n : ℕ => (U n)ᗮ.starProjection x) atTop (𝓝 (Vᗮ.starProjection x)) := by
    simpa only [Submodule.starProjection_orthogonal_val] using! (tendsto_const_nhds (x:=x)).sub (hP x)
  have hker (x : H) : x ∈ Vᗮ ↔ ∀ i : ι, inner 𝕜 (v i) x = 0 := by
    simpa only [Set.image_univ,Set.mem_univ,forall_const] using mem_kernel_of_closed_span_iff (𝕜:=𝕜) v Set.univ x
  refine ⟨fun n x => mem_kernel_of_closed_span_iff _ _ _,hker,hP,hQ,?_⟩
  constructor
  · intro h i
    have him : Vᗮ.starProjection (v i) = v i := tendsto_nhds_unique (hQ _) (h _)
    have hz := (hker (v i)).mp (Submodule.starProjection_eq_self_iff.mp him) i
    exact inner_self_eq_zero.mp hz
  · intro hz x
    have hx : x ∈ Vᗮ := (hker x).mpr (by simp [hz])
    simpa only [Submodule.starProjection_eq_self_iff.mpr hx] using hQ x

end
end MasulloWindow

end

section

open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal

namespace MasulloAudit.WindowWeighted
noncomputable section

def density (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2*|x|))
abbrev μ : Measure ℝ := volume.withDensity density
abbrev H := Lp ℂ 2 μ

/-- The Riesz vector representing the Mellin evaluation at zero in the width-one window. -/
def weight (x : ℝ) : ℂ := (Real.exp (-2*|x|) : ℝ)

private theorem measurable_density : Measurable density := by
  unfold density
  fun_prop

private theorem density_finite : ∀ᵐ x : ℝ, density x < ⊤ :=
  ae_of_all _ fun _ => ENNReal.ofReal_lt_top

/-- The strictly positive exponential density preserves null sets in both directions. -/
theorem ae_weighted_iff {p : ℝ → Prop} : (∀ᵐ x ∂μ, p x) ↔ ∀ᵐ x, p x := by
  rw [ae_withDensity_iff measurable_density]
  simp only [density, ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _), ne_eq,
    not_false_eq_true, true_implies]

private theorem scalar_cancel (x : ℝ) : Real.exp (2*|x|) * Real.exp (-2*|x|) = 1 := by
  rw [←Real.exp_add,show 2*|x| + -2*|x|=0 by ring,Real.exp_zero]

private theorem laplace_mass :
    Integrable (fun x : ℝ => Real.exp (-2*|x|)) ∧ (∫ x : ℝ, Real.exp (-2*|x|)) = 1 := by
  obtain ⟨hI,hV,_⟩ := MasulloAudit.window_mellin_evaluation_bounded 1 (by norm_num) 0 (by norm_num)
  norm_num at hI hV
  simpa only [neg_mul] using And.intro hI hV

theorem weight_mem : MemLp weight 2 μ := by
  have hc : Continuous weight := by unfold weight; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  rw [integrable_withDensity_iff_integrable_smul' measurable_density density_finite]
  apply laplace_mass.1.congr
  filter_upwards with x
  simp only [density, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, weight,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),pow_two]
  rw [←mul_assoc,scalar_cancel,one_mul]

def vector : H := weight_mem.toLp weight

theorem vector_ae : (vector : ℝ → ℂ) =ᵐ[μ] weight := weight_mem.coeFn_toLp

theorem vector_ae_volume : (vector : ℝ → ℂ) =ᵐ[volume] weight := ae_weighted_iff.mp vector_ae

private theorem cancel_inner (x : ℝ) (v : ℂ) :
    (density x).toReal • ⟪weight x,v⟫_ℂ = v := by
  simp only [density, ENNReal.toReal_ofReal (Real.exp_nonneg _), Complex.real_smul, RCLike.inner_apply,
    weight, Complex.conj_ofReal]
  rw [mul_left_comm,← Complex.ofReal_mul,scalar_cancel,Complex.ofReal_one,mul_one]

private theorem ae_cancel_inner (u : H) :
    (fun x : ℝ => (density x).toReal • ⟪vector x,u x⟫_ℂ) =ᵐ[volume] (u : ℝ→ℂ) := by
  filter_upwards [vector_ae_volume] with x hx
  rw [hx]
  exact cancel_inner x (u x)

theorem integrable_volume (u : H) : Integrable (u : ℝ→ℂ) (volume : Measure ℝ) := by
  have hi := L2.integrable_inner (𝕜:=ℂ) vector u
  rw [integrable_withDensity_iff_integrable_smul' measurable_density density_finite] at hi
  exact hi.congr (ae_cancel_inner u)

theorem eval_is_inner (u : H) : ⟪vector,u⟫_ℂ = ∫ x : ℝ, u x := by
  rw [L2.inner_def,integral_withDensity_eq_integral_toReal_smul measurable_density density_finite]
  exact integral_congr_ae (ae_cancel_inner u)

theorem vector_self : ⟪vector,vector⟫_ℂ = 1 := by
  rw [eval_is_inner,integral_congr_ae vector_ae_volume]
  change (∫ x : ℝ, ((Real.exp (-2*|x|):ℝ):ℂ)) = 1
  rw [integral_complex_ofReal,laplace_mass.2,Complex.ofReal_one]

end
end MasulloAudit.WindowWeighted

end

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace SchwartzMap
local notation "W" => Lp ℂ 2 (Measure.withDensity (volume : Measure ℝ) (fun x : ℝ => ENNReal.ofReal (Real.exp (2*|x|))))

theorem solution :
    (∃ (φ : ℝ → ℂ) (v : W),
      (∀ a : ℝ, ∃ g : 𝓢(ℝ,ℂ), ∀ x : ℝ, g x = Complex.exp ((a:ℂ)*x) * φ (Real.exp x)) ∧
      (∀ s : ℂ, HasMellin φ s (s * Complex.exp (s^2))) ∧
      (∀ s : ℂ, mellin φ s = 0 ↔ s = 0) ∧ analyticOrderAt (mellin φ) 0 = 1 ∧
      (v : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => ((Real.exp (-2*|x|):ℝ):ℂ)) ∧
      ⟪v,v⟫_ℂ = 1 ∧
      (∀ u : W, ⟪v,u⟫_ℂ = ∫ x : ℝ, u x) ∧
      (let K := (ℂ ∙ v)ᗮ
       (∀ T : ℝ, 0 < T → ∀ u : W, u ∈ K ↔
         ∀ s : ℂ, mellin φ s = 0 → |s.im| ≤ T →
           ∀ j : ℕ, j < analyticOrderNatAt (mellin φ) s →
             (∫ x : ℝ, ((x:ℂ)^j * Complex.exp (s*x)) * u x) = 0) ∧
       K.starProjection v = 0 ∧
       ¬ Tendsto (fun _ : ℝ => K.starProjection v) atTop (𝓝 v))) ∧
    (∀ (ι : Type) (v : ι → W) (F : ℕ → Finset ι), Monotone F → (∀ i, ∃ n, i ∈ F n) →
      let U (n : ℕ) := (Submodule.span ℂ (v '' (F n : Set ι))).topologicalClosure
      let V := (Submodule.span ℂ (Set.range v)).topologicalClosure
      (∀ u : W, u ∈ Vᗮ ↔ ∀ i, ⟪v i,u⟫_ℂ = 0) ∧
      (∀ u : W, Tendsto (fun n => (U n).starProjection u) atTop (𝓝 (V.starProjection u))) ∧
      (∀ u : W, Tendsto (fun n => (U n)ᗮ.starProjection u) atTop (𝓝 (Vᗮ.starProjection u))) ∧
      ((∀ u : W, Tendsto (fun n => (U n)ᗮ.starProjection u) atTop (𝓝 u)) ↔ ∀ i, v i = 0)) := by
  classical
  constructor
  · obtain ⟨φ,hφ,hM,hzero,horder⟩ := MasulloWindow.exists_singleZero_mellin
    let v : W := MasulloAudit.WindowWeighted.vector
    have hv := MasulloAudit.WindowWeighted.vector_ae_volume
    have hinner (u : W) : ⟪v,u⟫_ℂ = ∫ x : ℝ, u x := MasulloAudit.WindowWeighted.eval_is_inner u
    have hself : ⟪v,v⟫_ℂ = 1 := MasulloAudit.WindowWeighted.vector_self
    refine ⟨φ,v,hφ,hM,hzero,horder,hv,hself,hinner,?_,?_,?_⟩
    · intro T hT u
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hinner]
      have hord : analyticOrderNatAt (mellin φ) 0 = 1 := by simp [analyticOrderNatAt,horder]
      constructor
      · intro he s hs _ j hj
        obtain rfl := (hzero s).mp hs
        rw [hord] at hj
        have : j = 0 := by omega
        simpa [this] using he
      · intro h
        simpa using h 0 ((hzero 0).mpr rfl) (by simpa using hT.le) 0 (by omega)
    · exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero v
    · intro h
      have h0 : (0:W) = v := by
        simpa only [Submodule.starProjection_orthogonalComplement_singleton_eq_zero,
          tendsto_const_nhds_iff] using h
      rw [←h0] at hself
      simp at hself
  · intro ι v F hF hcov
    exact (MasulloWindow.projection_limits (𝕜:=ℂ) v F hF hcov).2
