-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:16:26.752403+00:00
-- url     : https://prove2.me/submissions/280b38a9-9485-4085-af3b-9ecd7d874099

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B271
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_siteLaw_shear_buffered_score_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CorrelationDerivative
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteWeightedTest_real {Ω T : Type*} [Fintype T]
    (ψ : T → Ω) (w : T → ℝ) (v : Ω → ℝ) :
    (finiteWeightedTest ψ (fun t => (w t : ℂ)) (fun x => (v x : ℂ))).re =
      𝔼 t, w t * v (ψ t) := by
  change (𝔼 t, (w t : ℂ) * (v (ψ t) : ℂ)).re = _
  rw [expect_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_productive_good_path {H : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (productive bad : Finset H) (err : H → ℝ)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (herr : ∀ h, 0 ≤ err h)
    (hproductive : τ ≤ p.mass productive) (hbad : p.mass bad ≤ τ / 4)
    (hmean : p.mean err ≤ τ * r / 4) :
    ∃ h ∈ productive, h ∉ bad ∧ err h ≤ r := by
  classical
  by_contra! hnone
  have hpoint (h : H) : r * (if h ∈ productive then (1 : ℝ) else 0) ≤
      r * (if h ∈ bad then (1 : ℝ) else 0) + err h := by
    by_cases hp : h ∈ productive
    · by_cases hb : h ∈ bad
      · simp only [hp, hb, ite_true, mul_one]
        linarith [herr h]
      · simpa only [hp, hb, ite_true, ite_false, mul_one, mul_zero, zero_add] using
          (hnone h hp hb).le
    · simp only [hp, ite_false, mul_zero]
      exact add_nonneg (mul_nonneg hr.le (by split_ifs <;> norm_num)) (herr h)
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const_mul, p.mean_const_mul, p.mean_indicator, p.mean_indicator] at h
  have hp := mul_le_mul_of_nonneg_left hproductive hr.le
  have hb := mul_le_mul_of_nonneg_left hbad hr.le
  nlinarith [mul_pos hτ hr]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.BufferedScalarScoreBound
namespace OAI

section

namespace Erdos3

theorem abs_bufferedScalarScore_le_one {Ω : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ)
    (hf : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1) (u : Ω) :
    |bufferedScalarScore χ x T f lam u| ≤ 1 := by
  have hdiff : |f u - lam| ≤ 1 := abs_le.mpr ⟨by linarith [(hf u).1, hlam.2],
    by linarith [(hf u).2, hlam.1]⟩
  unfold bufferedScalarScore
  rw [abs_mul, abs_mul, abs_of_nonneg (χ.nonneg _), abs_of_nonneg (hT u _).1]
  exact (mul_le_of_le_one_left (hT u _).1
    ((mul_le_of_le_one_left (χ.nonneg _) hdiff).trans (χ.le_one _))).trans (hT u _).2

theorem norm_bufferedWeightedPatchScore_le_exp
    {Ω σ : Type*} {m s d : ℕ} {w : σ ⊕ Fin m → ℕ}
    (B : WeightedParameterPatch (σ ⊕ Fin m) w s d)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (point : Ω → σ → ℝ)
    (f : Ω → ℝ) (lam : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hf : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (u : Ω) :
    ‖(bufferedScalarScore χ x
      (fun u b => B.value (Sum.elim (point u) (fun i => (b i : ℝ)))) f lam u : ℂ)‖ ≤
        Real.exp p := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_bufferedScalarScore_le_one χ x _ f lam hf hlam
    (fun u b => B.value_mem_Icc _) u).trans (Real.one_le_exp hp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem finite_model_test_difference_weighted
    {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I]
    (A B : V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) :
    ‖A v - B v‖ ≤ (∑ i, ‖c i‖ * ‖A (J i) - B (J i)‖) + ‖A e‖ + ‖B e‖ := by
  have hid : A v - B v = (∑ i, c i * (A (J i) - B (J i))) + (A e - B e) := by
    rw [hmodel, map_add, map_add, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [hid]
  have hsum : ‖∑ i, c i * (A (J i) - B (J i))‖ ≤
      ∑ i, ‖c i‖ * ‖A (J i) - B (J i)‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun i => c i * (A (J i) - B (J i)))
  exact (norm_add_le _ _).trans ((add_le_add hsum (norm_sub_le _ _)).trans_eq (by ring))

theorem exists_productive_averaged_model_transfer
    {H V I : Type*} [Fintype H] [AddCommGroup V] [Module ℂ V] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.mass productive)
    (hmean : law.mean (fun h =>
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖) ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, ρ ≤ (B h v).re) :
    ∃ h ∈ productive, ρ / 2 ≤ (A h v).re := by
  let err := fun h => (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖
  have herr : ∀ h, 0 ≤ err h := by intro h; dsimp only [err]; positivity
  obtain ⟨h, hp, _, he⟩ := exists_productive_good_path law productive ∅ err
    hτ (show 0 < ρ / 2 by positivity) herr hmass
    (by simp only [FiniteProbabilityWeights.mass, Finset.sum_empty]; positivity)
    (by dsimp only [err]; convert hmean using 1; ring)
  refine ⟨h, hp, ?_⟩
  have hd := (finite_model_test_difference_weighted (A h) (B h) v e J c hmodel).trans he
  have hre := (neg_le_abs ((A h v - B h v).re)).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re] at hre
  linarith [hscore h hp]

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ModelTransferPrecision
namespace OAI

section

namespace Erdos3

private theorem two_pow_le_exp_nat (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h n
  simpa only [← Real.exp_nat_mul, mul_one] using hp

theorem model_transfer_residual_precision {ρ τ R T u : ℝ}
    (hT : 0 ≤ T) (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) :
    Real.exp (-u) ≤ τ * ρ / 32 ∧ Real.exp (-u) ≤ ρ / 8 := by
  have h32 : (32 : ℝ) ≤ Real.exp 6 := by
    have h := two_pow_le_exp_nat 6
    norm_num at h
    linarith
  have hprod : Real.exp (-T - R) ≤ τ * ρ := by
    rw [show -T - R = -T + (-R) by ring, Real.exp_add]
    exact mul_le_mul hτ hρ (Real.exp_nonneg _) ((Real.exp_pos _).le.trans hτ)
  have ha : Real.exp (-u) * 32 ≤ τ * ρ := by
    calc
      _ ≤ Real.exp (-u) * Real.exp 6 := mul_le_mul_of_nonneg_left h32 (Real.exp_nonneg _)
      _ = Real.exp (-u + 6) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-T - R) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ τ * ρ := hprod
  have hb : Real.exp (-u) * 8 ≤ ρ := by
    calc
      _ ≤ Real.exp (-u) * Real.exp 6 := mul_le_mul_of_nonneg_left (by linarith : (8 : ℝ) ≤ Real.exp 6) (Real.exp_nonneg _)
      _ = Real.exp (-u + 6) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ ρ := hρ
  exact ⟨(le_div_iff₀ (by norm_num)).mpr ha, (le_div_iff₀ (by norm_num)).mpr hb⟩

theorem model_transfer_atom_precision {ρ M R Q E : ℝ}
    (hρ : Real.exp (-R) ≤ ρ) (hM : M ≤ Real.exp Q) (hE : Q + R + 8 ≤ E) :
    M * (2 * Real.exp (-E)) ≤ ρ / 8 := by
  have h16 : (16 : ℝ) ≤ Real.exp 8 := by
    have h := two_pow_le_exp_nat 8
    norm_num at h
    linarith
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  calc
    _ ≤ Real.exp Q * (2 * Real.exp (-E)) * 8 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by norm_num)
    _ = Real.exp (Q - E) * 16 := by rw [Real.exp_sub, Real.exp_neg]; ring
    _ ≤ Real.exp (Q - E) * Real.exp 8 := mul_le_mul_of_nonneg_left h16 (Real.exp_nonneg _)
    _ = Real.exp (Q - E + 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-R) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ ρ := hρ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedWeightedLawModeledTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finiteProbabilityTest_real {Ω U : Type*} [Fintype U]
    (law : FiniteProbabilityWeights U) (ψ : U → Ω) (v : Ω → ℝ) :
    (finiteProbabilityTest law ψ (fun x => (v x : ℂ))).re =
      law.mean (fun u => v (ψ u)) := by
  change (law.complexMean (fun u => (v (ψ u) : ℂ))).re = _
  rw [law.complexMean_ofReal, Complex.ofReal_re]

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedModelErrorBudget
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem restricted_model_error_mean_le
    {H Ω I : Type*} [Fintype H] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (A B : H → (Ω → ℂ) →ₗ[ℂ] ℂ) (J : I → Ω → ℂ) (c : I → ℂ) (e : Ω → ℂ)
    {M η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ h ∈ productive, ∀ i, ‖A h (J i) - B h (J i)‖ ≤ η)
    (hambient : ∀ h ∈ productive, ‖A h e‖ ≤ ε)
    (hlocal : law.mean (fun h => if h ∈ productive then ‖B h e‖ else 0) ≤ ε) :
    law.mean (fun h => if h ∈ productive then
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ else 0) ≤
        M * η + 2 * ε := by
  have hM : 0 ≤ M := (Finset.sum_nonneg (fun i _ => norm_nonneg (c i))).trans hc
  have hb := law.mean_mono (fun h => show
      (if h ∈ productive then
        (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ else 0) ≤
      M * η + ε + (if h ∈ productive then ‖B h e‖ else 0) from by
    by_cases hh : h ∈ productive
    · simp only [if_pos hh]
      have ha : (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) ≤ M * η := by
        calc
          _ ≤ ∑ i, ‖c i‖ * η := Finset.sum_le_sum
            (fun i _ => mul_le_mul_of_nonneg_left (hatom h hh i) (norm_nonneg _))
          _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul _ _ _).symm
          _ ≤ M * η := mul_le_mul_of_nonneg_right hc hη
      linarith [hambient h hh]
    · simp only [if_neg hh, add_zero]
      exact add_nonneg (mul_nonneg hM hη) hε)
  rw [law.mean_add, law.mean_const] at hb
  linarith

theorem restricted_model_exponential_error_budget {ρ τ R T Q E u : ℝ}
    (hT : 0 ≤ T) (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E) :
    Real.exp Q * Real.exp (-E) + 2 * Real.exp (-u) ≤ τ * ρ / 8 := by
  have hprod : Real.exp (-(T + R)) ≤ τ * ρ := by
    rw [neg_add, Real.exp_add]
    exact mul_le_mul hτ hρ (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hτ)
  have ha := model_transfer_atom_precision hprod (le_refl (Real.exp Q)) hE
  have he := (model_transfer_residual_precision hT hρ hτ hu).1
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteProbabilityMeanConjugate
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators

theorem complexMean_star {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (f : Ω → ℂ) :
    law.complexMean (fun x => star (f x)) = star (law.complexMean f) := by
  simp only [complexMean, Complex.star_def, map_sum, map_mul, Complex.conj_ofReal]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FiniteLawForecastModelTransfer
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_finiteLaw_forecast_model_transfer
    {H Ω U I : Type*} [Fintype H] [Fintype Ω] [Fintype U] [Fintype I]
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → Ω)
    (forecast : H → Ω → ℝ) (v : Ω → ℝ)
    (models : I → Ω → ℂ) (coeff : I → ℂ) (err : Ω → ℂ)
    (hmodel : (fun u => (v u : ℂ)) = (∑ i, coeff i • models i) + err)
    {τ ρ R T Q E u : ℝ} (hT : 0 ≤ T)
    (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E)
    (hc : (∑ i, ‖coeff i‖) ≤ Real.exp Q)
    (hmass : τ ≤ law.mass productive)
    (hatom : ∀ h ∈ productive, ∀ i,
      ‖(𝔼 x, (forecast h x : ℂ) * models i x) -
        (localLaw h).complexMean (fun a => models i (ψ h a))‖ ≤ Real.exp (-E))
    (hambient : ∀ h ∈ productive,
      ‖𝔼 x, (forecast h x : ℂ) * err x‖ ≤ Real.exp (-u))
    (hlocal : law.mean (fun h => if h ∈ productive then
      ‖(localLaw h).complexMean (fun a => err (ψ h a))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => v (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 x, forecast h x * v x := by
  let A₀ := fun h => finiteWeightedTest id (fun x => (forecast h x : ℂ))
  let B₀ := fun h => finiteProbabilityTest (localLaw h) (ψ h)
  have hb := restricted_model_error_mean_le law productive A₀ B₀ models coeff err
    (Real.exp_nonneg (-E)) (Real.exp_nonneg (-u)) hc hatom hambient hlocal
  have hbudget := restricted_model_exponential_error_budget hT hρ hτ hu hE
  let A := fun h => if h ∈ productive then A₀ h else 0
  let B := fun h => if h ∈ productive then B₀ h else 0
  have he : law.mean (fun h =>
      (∑ i, ‖coeff i‖ * ‖A h (models i) - B h (models i)‖) +
      ‖A h err‖ + ‖B h err‖) ≤ τ * ρ / 8 := by
    apply le_trans _ (hb.trans hbudget)
    apply law.mean_mono
    intro h
    by_cases hh : h ∈ productive
    · simp only [A, B, if_pos hh, le_refl]
    · simp [A, B, hh]
  have hs : ∀ h ∈ productive, ρ ≤ (B h (fun x => (v x : ℂ))).re := by
    intro h hh
    simpa only [B, B₀, if_pos hh, finiteProbabilityTest_real] using hscore h hh
  obtain ⟨h, hh, htransfer⟩ := exists_productive_averaged_model_transfer law productive
    A B (fun x => (v x : ℂ)) err models coeff hmodel
    ((Real.exp_pos _).trans_le hτ) ((Real.exp_pos _).trans_le hρ) hmass he hs
  exact ⟨h, hh, by simpa only [A, A₀, if_pos hh, finiteWeightedTest_real, id_eq] using htransfer⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer
namespace OAI

section

namespace Erdos3

open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem NativeSampleModel.exists_constant_of_degree_zero
    {σ Ω : Type*} {w : σ → ℕ} {p : ℝ} {sample : Ω → σ → ℤ} {f : Ω → ℂ}
    (F : NativeSampleModel w 0 p sample f) :
    ∃ c : ℂ, ‖c‖ ≤ 1 ∧ ∀ x, f x = c := by
  let c := F.test.observable (QuotientGroup.mk (1 : F.model.RealGroup))
  refine ⟨c, (F.test.norm_le _).trans F.norm, ?_⟩
  intro x
  rw [F.eval, RationalFilteredNilmanifold.Niltest.eval_step_zero]

namespace VectorPolynomial.NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem absorb_degree_zero {Ω : Type*} {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {g : Ω → ℂ} (G : NativeSampleModel w 0 budget sample g) :
    ∃ W' : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ∀ u, star (W.eval N poly (sample u)) * g u = star (W'.eval N poly (sample u)) := by
  obtain ⟨c, hc, hg⟩ := G.exists_constant_of_degree_zero
  refine ⟨W.scaleMask (star c) (by simpa only [norm_star] using hc), ?_⟩
  intro u
  rw [scaleMask_eval, star_mul, star_star, hg u]

end VectorPolynomial.NormalizedPolynomialTwist

namespace VectorPolynomial

theorem twistedNativeSampleFunctions_degree_zero
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ) {f : Ω → ℂ}
    (hf : f ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) u =>
        W.eval N poly (sample u))) :
    f = 0 ∨ ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      f = fun u => star (W.eval N poly (sample u)) := by
  rcases hf with hzero | ⟨W, g, ⟨G⟩, hf⟩
  · exact Or.inl hzero
  · obtain ⟨W', hW'⟩ := W.absorb_degree_zero N poly sample w budget G
    exact Or.inr ⟨W', hf.trans (funext hW')⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem degreeZero_finiteLaw_model_atom_comparison
    {X Ω T : Type*} [Fintype X] [Fintype Ω] [Fintype T]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (budget : ℝ)
    (left : FiniteProbabilityWeights Ω) (right : FiniteProbabilityWeights T)
    (ψ : T → Ω) (a : Ω → ℝ)
    {η : ℝ} (hη : 0 ≤ η)
    (hcompare : ∀ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ‖left.complexMean (fun x => (a x : ℂ) * W.eval N poly (sample x)) -
        right.complexMean (fun t => W.eval N poly (sample (ψ t)))‖ ≤ η)
    {f : Ω → ℂ}
    (hf : f ∈ twistedNativeSampleFunctions w 0 budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) x =>
        W.eval N poly (sample x))) :
    ‖left.complexMean (fun x => (a x : ℂ) * f x) -
      right.complexMean (fun t => f (ψ t))‖ ≤ η := by
  rcases twistedNativeSampleFunctions_degree_zero N poly sample w budget hf with rfl | ⟨W, rfl⟩
  · simpa only [Pi.zero_apply, mul_zero, FiniteProbabilityWeights.complexMean,
      Finset.sum_const_zero, sub_zero, norm_zero] using hη
  · have hleft : left.complexMean (fun x => (a x : ℂ) * star (W.eval N poly (sample x))) =
        star (left.complexMean (fun x => (a x : ℂ) * W.eval N poly (sample x))) := by
      rw [← FiniteProbabilityWeights.complexMean_star]
      congr 1
      funext x
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      exact mul_comm _ _
    rw [hleft, FiniteProbabilityWeights.complexMean_star, ← star_sub, norm_star]
    exact hcompare W

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_finiteLaw_degreeZero_forecast_transfer
    {H X U I F : Type*} [Fintype H] [Fintype X] [DecidableEq X]
    [Fintype U] [Fintype I]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (budget : ℝ)
    (law : FiniteProbabilityWeights H) (productive : Finset H)
    (localLaw : H → FiniteProbabilityWeights U) (ψ : H → U → integerBox N)
    (forecast : F → integerBox N → ℂ) (select : H → F)
    (hreal : ∀ h ∈ productive, ∀ x, ((forecast (select h) x).re : ℂ) = forecast (select h) x)
    (v : integerBox N → ℝ) (models : I → integerBox N → ℂ)
    (coeff : I → ℂ) (err : integerBox N → ℂ)
    (hmodels : ∀ i, models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 budget
      (fun x : integerBox N => x.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
        (x : integerBox N) => W.eval N poly x.val))
    (hmodel : (fun x => (v x : ℂ)) = (∑ i, coeff i • models i) + err)
    {τ ρ R T Q E u : ℝ} (hT : 0 ≤ T)
    (hρ : Real.exp (-R) ≤ ρ) (hτ : Real.exp (-T) ≤ τ)
    (hu : R + T + 6 ≤ u) (hE : Q + (T + R) + 8 ≤ E)
    (hc : (∑ i, ‖coeff i‖) ≤ Real.exp Q) (hmass : τ ≤ law.mass productive)
    (hcompare : ∀ h ∈ productive,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ‖(localLaw h).complexMean (fun a => W.eval N poly (ψ h a).val) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).complexMean
          (fun x => W.eval N poly x.val * forecast (select h) x)‖ ≤ Real.exp (-E))
    (hforecast : ∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
      err (forecast f)‖ ≤ Real.exp (-u))
    (hlocal : law.mean (fun h => if h ∈ productive then
      ‖(localLaw h).complexMean (fun a => err (ψ h a))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ h ∈ productive, ρ ≤ (localLaw h).mean (fun a => v (ψ h a))) :
    ∃ h ∈ productive, ρ / 2 ≤ 𝔼 x, (forecast (select h) x).re * v x := by
  let : Nonempty (integerBox N) := hN.to_subtype
  apply exists_finiteLaw_forecast_model_transfer law productive localLaw ψ
    (fun h x => (forecast (select h) x).re) v models coeff err hmodel
    hT hρ hτ hu hE hc hmass ?_ ?_ hlocal hscore
  · intro h hh i
    have hatom := degreeZero_finiteLaw_model_atom_comparison N poly
      (fun x : integerBox N => x.val) (1 : X → ℕ) budget
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hN)
      (localLaw h) (ψ h) (fun x => (forecast (select h) x).re)
      (Real.exp_nonneg (-E)) (fun W => ?_) (hmodels i)
    · simpa only [FiniteProbabilityWeights.uniformFinset,
        FiniteProbabilityWeights.uniform_complexMean] using hatom
    · simpa only [hreal h hh, mul_comm, norm_sub_rev] using hcompare h hh W
  · intro h hh
    have he := hforecast (select h)
    have hstar (x : integerBox N) : star (forecast (select h) x) = forecast (select h) x := by
      rw [← hreal h hh x]
      simp only [Complex.star_def, Complex.conj_ofReal]
    simpa only [FiniteProbabilityWeights.correlation_eq_complexMean,
      FiniteProbabilityWeights.uniformFinset, FiniteProbabilityWeights.uniform_complexMean,
      hstar, hreal h hh, mul_comm] using he

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual
namespace OAI


namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)
    {sliceBudget testBudget : ℝ}
    (hbudget : 0 ≤ sliceBudget) (hcost : outputCost ≤ sliceBudget)
    (htest : 2 ≤ testBudget)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp sliceBudget)

theorem retainedResidualPacket_expect (z : out.retained) (err : A.Site → ℂ) :
    (𝔼 site ∈ (out.retainedResidualPacket hbudget hcost htest hshort z).slice.subtypeSites,
      err site) = (out.siteLaw z).complexMean err := by
  let C := P.chart ⟨z.val, out.subset z.property⟩
  have he : (Subtype.instDecidableEq : DecidableEq C.Variables) = Classical.decEq _ :=
    Subsingleton.elim _ _
  let signal : (LayerSamplerVariables G I n B → ℤ) → ℂ :=
    Function.extend Subtype.val err (fun _ => 0)
  have heval (site : A.Site) : signal site.val = err site :=
    Subtype.val_injective.extend_apply _ _ site
  have hleft :
      (𝔼 site ∈ (out.retainedResidualPacket hbudget hcost htest hshort z).slice.subtypeSites,
        signal site.val) =
      𝔼 u ∈ (out.slice z).integerPoints, signal (C.parameter u) := by
    rw [ResidueBoxSlice.expect_subtypeSites]
    change (𝔼 x ∈ ((out.slice z).freezeShort C.keep C.fixedNatural C.fixedNatural_lt).integerPoints,
      signal x) = _
    rw [ResidueBoxSlice.expect_freezeShort]
    simp only [C.frozenLongExtension_fixedNatural]
    congr 1
    exact congrArg (fun dec : DecidableEq C.Variables =>
      @ResidueBoxSlice.integerPoints C.Variables _ _ _ dec (out.slice z)) he
  have hright := C.retainedLaw_complexMean_parameter (out.slice z).integerPoints
    (out.dense z).nonempty (out.slice z).integerPoints_subset_integerBox signal
  have hright' : (out.siteLaw z).complexMean (fun site => signal site.val) =
      𝔼 u ∈ (out.slice z).integerPoints, signal (C.parameter u) := by
    change (C.retainedLaw (out.slice z).integerPoints (out.dense z).nonempty
      (out.slice z).integerPoints_subset_integerBox).complexMean _ = _
    exact hright
  simpa only [heval] using hleft.trans hright'.symm

theorem retained_residual_mean_le_sampledSliceSeminorm
    {Ω : Type*} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ) :
    A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) ≤
    sampledSliceSeminorm A.law physical
      (fun z (_ : Unit) => (out.residualPacket hbudget hcost htest hshort z).slice.subtypeSites)
      (fun z (_ : Unit) t => (out.residualPacket hbudget hcost htest hshort z).weight t.val) err := by
  classical
  let : Nonempty A.Site := ⟨⟨fun _ => 0,
    (mem_integerBox A.sides _).mpr (fun i => ⟨le_rfl, by exact_mod_cast A.sides_pos i⟩)⟩⟩
  let packet := out.residualPacket hbudget hcost htest hshort
  have hnonempty (z : A.Path) : (packet z).slice.subtypeSites.Nonempty :=
    (packet z).slice.subtypeSites_nonempty_of_integerPoints (packet z).dense.nonempty
  have hsize (z : A.Path) : (Fintype.card A.Site : ℝ) / (packet z).slice.subtypeSites.card ≤
      Fintype.card A.Site := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hnonempty z).card_pos)).mpr
    have hcard : (1 : ℝ) ≤ (packet z).slice.subtypeSites.card := by
      exact_mod_cast (hnonempty z).card_pos
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card A.Site)]
  rw [sampledSliceSeminorm_apply A.law physical _ _ (fun z _ => hnonempty z)
    (fun z _ => hsize z) (fun z _ t => (packet z).weight_norm t.val)]
  simp only [packet, residualPacket_weight, mul_one, ciSup_unique]
  apply A.law.mean_mono
  intro z
  split_ifs with hz
  · rw [out.residualPacket_retained hbudget hcost htest hshort ⟨z, hz⟩,
      out.retainedResidualPacket_expect hbudget hcost htest hshort]
  · exact norm_nonneg _

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite
theorem allSiteLaw_restricted_residual_eq
    {Ω : Type} (physical : A.Path → A.Site → Ω) (err : Ω → ℂ) :
    A.law.mean (fun z => if z ∈ out.retained then
      ‖(out.allSiteLaw z).complexMean (fun t => err (physical z t))‖ else 0) =
    A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean (fun t => err (physical z t))‖ else 0) := by
  apply congrArg A.law.mean
  funext z
  by_cases hz : z ∈ out.retained
  · simp only [if_pos hz, dif_pos hz, out.allSiteLaw_of_mem z hz]
  · simp only [if_neg hz, dif_neg hz]

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (τ ξ : ℝ) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.instNonemptySite
theorem exists_fixedCenter_forecast_model
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata P C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ P)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy P)
    {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    {Ldetect : ∀ z, Tests z → Type} [∀ z j, LieRing (Ldetect z j)]
    [∀ z j, LieAlgebra ℚ (Ldetect z j)] {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] Ldetect z j)]
    [∀ z j, T2Space (ℝ ⊗[ℚ] Ldetect z j)]
    (Ddetect : ∀ z j, RationalFilteredNilmanifold (Ldetect z j) 0 (dims z j))
    (Vdetect : ∀ z j, (Ddetect z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset A.Site)
    (origin : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (length : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hshape : ∀ z j, (slices z j).image Subtype.val = commonStrideBox (origin z j) (step z j) (length z j))
    (hDense : ∀ z j, IsDenseCommonStrideBox A.sides pSlice ((slices z j).image Subtype.val))
    (hcomplex : ∀ z j, (Vdetect z j).ComplexityLE pTest)
    (hcap : ∀ z j, ((Vdetect z j).normBound : ℝ) ≤ 1)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let tests : ∀ z, Tests z → A.Site → ℂ := fun z j t =>
      star ((Vdetect z j).eval (commonStrideIndex (origin z j) (step z j) t.val))
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      sampledSliceSeminorm A.law (A.physicalBox hξone hmargin) slices tests model.residual ≤
        Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro tests commonBudget Qmodel native
  let : ∀ x, NeZero (N x) := fun x => ⟨(A.size_pos x).ne'⟩
  have hsize := preparedCenteredForecast_slice_family_bounds B U b S slices hDense
  have htests (z) (j) (t : A.Site) : ‖tests z j t‖ ≤ 1 :=
    preparedCenteredForecast_niltest_star_eval_bound (Vdetect z j) (hcap z j)
      (commonStrideIndex (origin z j) (step z j) t.val)
  have hdetect := hdirect Ddetect Vdetect slices origin step length
    hstep hshape hDense hcomplex hcap
  obtain ⟨nterms, hn, models, coefficient, residual, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    exists_fixedLaw_centered_forecast_twist_model 0 N poly localBudget Pnative hbudget hNative
      A.law (A.physicalBox hξone hmargin) A.physical (fun _ _ => rfl)
      slices tests (fun f => (data f).target) hu hp (le_max_left 0 massLog)
      (Real.exp_nonneg _) hC (Real.exp_nonneg _) (Real.exp_le_exp.mpr hSliceLog)
      hCp (Real.exp_le_exp.mpr hCap) hPrecision hsize.2 htests (fun f => (data f).cap)
      hdetect (fun f => (data f).Term) (fun f => (data f).coefficient)
      (fun f => (data f).centerConstant) (fun f => (data f).twists)
      (fun f => (data f).mass.trans (Real.exp_le_exp.mpr (le_max_right 0 massLog)))
      (fun f v => ((data f).approximation v).trans (Real.exp_le_exp.mpr (neg_le_neg hAccuracy)))
      hexcess le_rfl input hinput
  exact ⟨⟨nterms, hn, models, coefficient, residual⟩,
    hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalRetainedForecastModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_1
theorem exists_fixedCenter_retained_forecast_model
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (input : integerBox N → ℂ) (hinput : ∀ v, ‖input v‖ ≤ Real.exp p) :
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      input = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      A.law.mean (fun z => if hz : z ∈ out.retained then
        ‖(out.siteLaw ⟨z, hz⟩).complexMean
          (fun t => model.residual (A.physicalBox hξone hmargin z t))‖ else 0) ≤ Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) := by
  classical
  intro commonBudget Qmodel native
  let packet := out.residualPacket hSlice hcost htest hshort
  obtain ⟨model, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    A.exists_fixedCenter_forecast_model hξone hmargin hu hp hbudget hNative
      hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
      (Tests := fun _ => Unit)
      (fun _ _ => RationalTorus.trivialNilmanifold 0)
      (fun z _ => (packet z).test)
      (fun z _ => (packet z).slice.subtypeSites)
      (fun z _ i => ((packet z).slice.start i : ℤ))
      (fun z _ => (packet z).stride)
      (fun z _ => (packet z).slice.length)
      (fun z _ => (packet z).stride_pos)
      (fun z _ => (packet z).slice.subtypeSites_image_val.trans
        (packet z).slice.integerPoints_eq_commonStrideBox)
      (fun z _ => (packet z).slice.subtypeSites_dense (packet z).dense)
      (fun z _ => (packet z).complexity) (fun z _ => (packet z).norm)
      data input hinput
  refine ⟨model, hmodels, heq, hcoeff, ?_, hforecast, hterms⟩
  exact (out.retained_residual_mean_le_sampledSliceSeminorm hSlice hcost htest hshort
    (A.physicalBox hξone hmargin) model.residual).trans hlocal

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateShearBufferedModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_2
theorem exists_fixedCenter_shear_buffered_model
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative massLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 massLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative massLog capLog Edata)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    let score : integerBox N → ℝ := fun v =>
      bufferedScalarScore χ (fun x : integerBox N => coords x.val)
        (fun x lifts => returned.value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (lifts i : ℝ))))
        (fun x : integerBox N => f x.val) lam v
    let commonBudget := max localBudget (3 * Pnative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * p + max 0 massLog + 20)
    let native := twistedNativeSampleFunctions (1 : X → ℕ) 0 commonBudget
      (fun v : integerBox N => v.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp commonBudget) (Real.exp commonBudget)
        ⟨Real.exp commonBudget, Real.exp_nonneg _⟩)
        (v : integerBox N) => W.eval N poly v.val)
    ∃ model : CenteredForecastModel (integerBox N),
      (∀ i, model.models i ∈ native) ∧
      (fun v => (score v : ℂ)) = (∑ i, model.coefficient i • model.models i) + model.residual ∧
      (∑ i, |model.coefficient i|) ≤ Real.exp (Qmodel + 2) ∧
      A.law.mean (fun z => if hz : z ∈ out.retained then
        ‖(out.siteLaw ⟨z, hz⟩).complexMean
          (fun t => model.residual (A.physicalBox hξone hmargin z t))‖ else 0) ≤ Real.exp (-u) ∧
      (∀ f, ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data f).target‖ ≤ Real.exp (-u)) ∧
      (model.nterms : ℝ) ≤ Real.exp (2 * Qmodel + 2 * u + 4 * p + 34) ∧
      ∀ z : out.retained, outputScore ≤ (out.siteLaw z).mean
        (fun site => score (A.physicalBox hξone hmargin z.val site)) := by
  classical
  intro χ coords returned score commonBudget Qmodel native
  have hinput (v : integerBox N) : ‖(score v : ℂ)‖ ≤ Real.exp p :=
    norm_bufferedWeightedPatchScore_le_exp returned χ (fun x : integerBox N => coords x.val)
      (fun x : integerBox N => fun i => (x.val i : ℝ)) (fun x : integerBox N => f x.val)
      lam hp (fun x => hf x.val x.property) hlam v
  obtain ⟨model, hmodels, heq, hcoeff, hlocal, hforecast, hterms⟩ :=
    out.exists_fixedCenter_retained_forecast_model hξone hmargin hu hp hbudget hNative
      hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
      hSlice hcost htest hshort data (fun v => (score v : ℂ)) hinput
  refine ⟨model, hmodels, heq, hcoeff, hlocal, hforecast, hterms, ?_⟩
  intro z
  exact out.siteLaw_shear_buffered_score_s2 patch f lam hσ1 H hH hchart hsmall hpoly e z

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateActualShearForecastScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

local instance instNonemptySite_3_rfb1240_1 : Nonempty A.Site := A.site_nonempty
theorem exists_retained_degreeZero_forecast_score
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {Forecast : Type} {Pnative forecastMassLog capLog Edata : ℝ}
    (data : Forecast → ActualForecastData N poly Pnative forecastMassLog capLog Edata)
    (select : A.Path → Forecast)
    (hreal : ∀ z : out.retained, ∀ x,
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x)
    (v : integerBox N → ℝ) (model : CenteredForecastModel (integerBox N))
    {budget Q scoreLog massLogTransfer Ecompare u : ℝ}
    (hmodels : ∀ i, model.models i ∈ twistedNativeSampleFunctions (1 : X → ℕ) 0 budget
      (fun x : integerBox N => x.val)
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩) (x : integerBox N) => W.eval N poly x.val))
    (hmodel : (fun x => (v x : ℂ)) =
      (∑ i, model.coefficient i • model.models i) + model.residual)
    (hcoeff : (∑ i, |model.coefficient i|) ≤ Real.exp Q)
    (hT : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hu : scoreLog + massLogTransfer + 6 ≤ u)
    (hE : Q + (massLogTransfer + scoreLog) + 8 ≤ Ecompare)
    (hcompare : ∀ z : out.retained,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp budget) (Real.exp budget)
        ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ‖(out.siteLaw z).complexMean (fun a => W.eval N poly
          (A.physicalBox hξone hmargin z.val a).val) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤
        Real.exp (-Ecompare))
    (hforecast : ∀ g,
      ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).correlation
        model.residual (data g).target‖ ≤ Real.exp (-u))
    (hlocal : A.law.mean (fun z => if hz : z ∈ out.retained then
      ‖(out.siteLaw ⟨z, hz⟩).complexMean
        (fun t => model.residual (A.physicalBox hξone hmargin z t))‖ else 0) ≤ Real.exp (-u))
    (hscore : ∀ z : out.retained, outputScore ≤ (out.siteLaw z).mean
      (fun t => v (A.physicalBox hξone hmargin z.val t))) :
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N, ((data (select z.val)).target x).re * v x := by
  classical
  have hcoeff' : (∑ i, ‖(model.coefficient i : ℂ)‖) ≤ Real.exp Q := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hcoeff
  have hmodel' : (fun x => (v x : ℂ)) =
      (∑ i, (model.coefficient i : ℂ) • model.models i) + model.residual := hmodel
  obtain ⟨z, hz, htransfer⟩ := exists_finiteLaw_degreeZero_forecast_transfer
    N A.integerBox_nonempty poly budget A.law out.retained out.allSiteLaw
    (A.physicalBox hξone hmargin) (fun g => (data g).target) select
    (fun z hz => hreal ⟨z, hz⟩) v model.models (fun i => (model.coefficient i : ℂ))
    model.residual hmodels hmodel' hT hscoreLower hmassLower hu hE hcoeff' out.mass
    (fun z hz W => by simpa only [out.allSiteLaw_of_mem z hz] using hcompare ⟨z, hz⟩ W)
    hforecast
    (by simpa only [out.allSiteLaw_restricted_residual_eq] using hlocal)
    (fun z hz => by simpa only [out.allSiteLaw_of_mem z hz] using hscore ⟨z, hz⟩)
  exact ⟨⟨z, hz⟩, htransfer⟩

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_4
theorem exists_shear_buffered_forecast_score_s2_oai
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative forecastMassLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 forecastMassLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative forecastMassLog capLog Edata)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (select : A.Path → Forecast)
    (hreal : ∀ z : out.retained, ∀ x,
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x)
    {scoreLog massLogTransfer Ecompare : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * Pnative + 3))
        (2 * u + 4 * p + max 0 forecastMassLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcompare : ∀ z : out.retained,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (max localBudget (3 * Pnative + 3)))
        (Real.exp (max localBudget (3 * Pnative + 3)))
        ⟨Real.exp (max localBudget (3 * Pnative + 3)), Real.exp_nonneg _⟩,
      ‖(out.siteLaw z).complexMean
          (fun site => W.eval N poly (A.physical z.val site)) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤
        Real.exp (-Ecompare)) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    let score : integerBox N → ℝ := fun v =>
      bufferedScalarScore χ (fun x : integerBox N => coords x.val)
        (fun x lifts => returned.value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (lifts i : ℝ))))
        (fun x : integerBox N => f x.val) lam v
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N, ((data (select z.val)).target x).re * score x := by
  classical
  intro χ coords returned score
  obtain ⟨model, hmodels, hmodel, hcoeff, hlocal, hforecast, _hterms, hscore⟩ :=
    out.exists_fixedCenter_shear_buffered_model patch f lam hξone hmargin
      hu hp hbudget hNative hSliceLog hC hCp hCap hAccuracy hPrecision hdirect hexcess
      hSlice hcost htest hshort data hf hlam hσ1 H hH hchart hsmall hpoly e
  have hE :
      (max (max localBudget (3 * Pnative + 3))
        (2 * u + 4 * p + max 0 forecastMassLog + 20) + 2) +
        (massLogTransfer + scoreLog) + 8 ≤ Ecompare := by
    simpa only [add_assoc] using hEcompare
  exact out.exists_retained_degreeZero_forecast_score hξone hmargin data select hreal
    score model hmodels hmodel hcoeff hTransferMass hscoreLower hmassLower hU hE
    hcompare hforecast hlocal hscore

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score_s2_oai := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score_s2_oai
