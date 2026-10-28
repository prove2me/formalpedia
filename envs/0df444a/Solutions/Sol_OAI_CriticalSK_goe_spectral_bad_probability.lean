-- Prove2me | solution 1 for OAI.CriticalSK.goe_spectral_bad_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T02:31:52.381443+00:00
-- url     : https://prove2.me/submissions/04ea8421-1389-4b19-8e87-c35420eddcf2

import Mathlib
import Definitions.Def_OAIQWCSK000
import Theorems.Thm_OAI_CriticalSK_partial_sum_maximal_tail

section
-- module Solutions.OAIQW_CriticalSK.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
namespace OAI.CriticalSK
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434


end OAI.CriticalSK
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

lemma gaussian_square_density (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_integral (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ha : 0 < 1 / 2 - t := by linarith
  have hb : 0 < 1 - 2 * t := by linarith
  apply (mul_left_inj' (Real.sqrt_ne_zero'.mpr hb)).mp
  rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hb)]
  have he : Real.sqrt (Real.pi / (1 / 2 - t)) * Real.sqrt (1 - 2 * t) =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity), show Real.pi / (1 / 2 - t) * (1 - 2 * t) =
      2 * Real.pi by field_simp]
  calc
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (1 / 2 - t)) *
        Real.sqrt (1 - 2 * t) = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          rw [mul_assoc, he]
    _ = 1 := inv_mul_cancel₀ (by positivity)

open Set Filter MeasureTheory ProbabilityTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianConcentration
attribute [-instance] _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_1 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_10 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_11 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_12 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_13 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_14 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_15 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_16 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_17 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_18 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_19 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_2 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_20 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_21 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_3 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_4 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_5 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_6 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_7 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_8 _root_.OAI.CriticalSK.instIsProbabilityMeasureTriSampleTriLaw_9 _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

lemma chiSquare_mgf (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (chiSquare m) (standardGaussianProduct m) t =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ m := by
  unfold mgf chiSquare standardGaussianProduct
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin m) (x : ℝ) => Real.exp (t * x ^ 2))]
  simp_rw [gaussian_square_integral t ht]
  simp

lemma chiSquare_exp_integrable (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x => Real.exp (t * chiSquare m x)) (standardGaussianProduct m) := by
  apply mgf_pos_iff.mp
  rw [chiSquare_mgf m t ht]
  exact pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))) m

lemma chiSquare_mgf_exp (m : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (chiSquare m) (standardGaussianProduct m) t =
      Real.exp (-(m : ℝ) / 2 * Real.log (1 - 2 * t)) := by
  rw [chiSquare_mgf m t ht]
  have hb : 0 < 1 - 2 * t := by linarith
  rw [← Real.exp_log (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr hb)) m),
    Real.log_pow, Real.log_inv, Real.log_sqrt hb.le]
  congr 1
  ring

lemma chiSquare_chernoff_value (m : ℕ) (a : ℝ) (ha : 0 < a) :
    Real.exp (-((1 - a⁻¹) / 2) * (m * a)) *
      mgf (chiSquare m) (standardGaussianProduct m) ((1 - a⁻¹) / 2) =
    Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha; linarith
  rw [chiSquare_mgf_exp m _ ht, ← Real.exp_add]
  have he : 1 - 2 * ((1 - a⁻¹) / 2) = a⁻¹ := by ring
  rw [he, Real.log_inv]
  congr 1
  field_simp
  ring

lemma chiSquare_upper_tail (m : ℕ) (a : ℝ) (ha : 1 ≤ a) :
    (standardGaussianProduct m).real {x | (m : ℝ) * a ≤ chiSquare m x} ≤
      Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ha0 : 0 < a := by linarith
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha0; linarith
  have ht0 : 0 ≤ (1 - a⁻¹) / 2 := by
    have := inv_le_one₀ ha0 |>.mpr ha
    linarith
  have hh := measure_ge_le_exp_mul_mgf (μ := standardGaussianProduct m)
    (X := chiSquare m) ((m : ℝ) * a) ht0 (chiSquare_exp_integrable m _ ht)
  simpa only [chiSquare_chernoff_value m a ha0] using hh

lemma chiSquare_lower_tail (m : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (standardGaussianProduct m).real {x | chiSquare m x ≤ (m : ℝ) * a} ≤
      Real.exp (-(m : ℝ) / 2 * (a - 1 - Real.log a)) := by
  have ht : (1 - a⁻¹) / 2 < 1 / 2 := by have := inv_pos.mpr ha; linarith
  have ht0 : (1 - a⁻¹) / 2 ≤ 0 := by
    have := one_le_inv₀ ha |>.mpr ha1
    linarith
  have hh := measure_le_le_exp_mul_mgf (μ := standardGaussianProduct m)
    (X := chiSquare m) ((m : ℝ) * a) ht0 (chiSquare_exp_integrable m _ ht)
  simpa only [chiSquare_chernoff_value m a ha] using hh

lemma chi_entropy_lower (a : ℝ) (ha : 0 < a) :
    (Real.sqrt a - 1) ^ 2 ≤ a - 1 - Real.log a := by
  have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ha)
  rw [Real.log_sqrt ha.le] at hh
  nlinarith [Real.sq_sqrt ha.le]

lemma chiSquare_nonneg (m : ℕ) (x : Fin m → ℝ) : 0 ≤ chiSquare m x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma chiSquare_eq_zero_iff (m : ℕ) (x : Fin m → ℝ) : chiSquare m x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hle : x i ^ 2 ≤ chiSquare m x := Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
    rw [hx] at hle
    simpa using sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  · rintro rfl
    simp [chiSquare]

lemma chiSquare_zero_measure (m : ℕ) (hm : 0 < m) :
    standardGaussianProduct m {x | chiSquare m x = 0} = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  simp only [chiSquare_eq_zero_iff, Set.ofPred_eq_eq_singleton, standardGaussianProduct,
    measure_singleton]

lemma chi_radius_algebra (m : ℕ) (hm : 0 < m) (u : ℝ) :
    (m : ℝ) * (u / Real.sqrt m) ^ 2 = u ^ 2 ∧
    (m : ℝ) / 2 * (u / Real.sqrt m - 1) ^ 2 = (u - Real.sqrt m) ^ 2 / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb0 : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  have hb := Real.sq_sqrt hm0.le
  constructor
  · rw [div_pow, hb]
    field_simp
  · rw [div_sub_one hb0, div_pow, hb]
    field_simp

lemma chi_upper_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | Real.sqrt m + r ≤ Real.sqrt (chiSquare m x)} ≤
      Real.exp (-r ^ 2 / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  let u := Real.sqrt (m : ℝ) + r
  have hu : 0 < u := by dsimp [u]; linarith
  have hu1 : 1 ≤ u / Real.sqrt (m : ℝ) := (le_div_iff₀ hb).mpr (by dsimp [u]; linarith)
  have ha : 1 ≤ (u / Real.sqrt (m : ℝ)) ^ 2 := by nlinarith
  have halg := chi_radius_algebra m hm u
  calc
    _ ≤ (standardGaussianProduct m).real {x | (m : ℝ) * (u / Real.sqrt m) ^ 2 ≤ chiSquare m x} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro x hx
      rw [halg.1]
      have hsq := Real.sq_sqrt (chiSquare_nonneg m x)
      change u ≤ _ at hx
      change u ^ 2 ≤ chiSquare m x
      nlinarith [sq_le_sq₀ hu.le (Real.sqrt_nonneg (chiSquare m x)) |>.mpr hx]
    _ ≤ Real.exp (-(m : ℝ) / 2 * ((u / Real.sqrt m) ^ 2 - 1 - Real.log ((u / Real.sqrt m) ^ 2))) :=
      chiSquare_upper_tail m _ ha
    _ ≤ Real.exp (-r ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have he := chi_entropy_lower ((u / Real.sqrt m) ^ 2) (lt_of_lt_of_le zero_lt_one ha)
      rw [Real.sqrt_sq (by positivity)] at he
      have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ m / 2 by positivity)
      rw [halg.2] at hh
      dsimp [u] at hh
      nlinarith

lemma chi_lower_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} ≤
      Real.exp (-r ^ 2 / 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  by_cases hru : r < Real.sqrt (m : ℝ)
  · let u := Real.sqrt (m : ℝ) - r
    have hu : 0 < u := by dsimp [u]; linarith
    have hu1 : u / Real.sqrt (m : ℝ) ≤ 1 := (div_le_one hb).mpr (by dsimp [u]; linarith)
    have hur : 0 < u / Real.sqrt (m : ℝ) := div_pos hu hb
    have ha : (u / Real.sqrt (m : ℝ)) ^ 2 ≤ 1 := by nlinarith
    have ha0 : 0 < (u / Real.sqrt (m : ℝ)) ^ 2 := sq_pos_of_pos hur
    have halg := chi_radius_algebra m hm u
    calc
      _ ≤ (standardGaussianProduct m).real {x | chiSquare m x ≤ (m : ℝ) * (u / Real.sqrt m) ^ 2} := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        rw [halg.1]
        have hsq := Real.sq_sqrt (chiSquare_nonneg m x)
        change _ ≤ u at hx
        change chiSquare m x ≤ u ^ 2
        nlinarith [sq_le_sq₀ (Real.sqrt_nonneg (chiSquare m x)) hu.le |>.mpr hx]
      _ ≤ Real.exp (-(m : ℝ) / 2 * ((u / Real.sqrt m) ^ 2 - 1 - Real.log ((u / Real.sqrt m) ^ 2))) :=
        chiSquare_lower_tail m _ ha0 ha
      _ ≤ Real.exp (-r ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have he := chi_entropy_lower ((u / Real.sqrt m) ^ 2) ha0
        rw [Real.sqrt_sq hur.le] at he
        have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ m / 2 by positivity)
        rw [halg.2] at hh
        dsimp [u] at hh
        nlinarith
  · have hzero : (standardGaussianProduct m).real
        {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} = 0 := by
      apply measureReal_mono_null (s₂ := {x | chiSquare m x = 0})
      · intro x hx
        have hn : 0 ≤ Real.sqrt (chiSquare m x) := Real.sqrt_nonneg _
        have hz : Real.sqrt (chiSquare m x) = 0 := by dsimp at hx; linarith
        exact (Real.sqrt_eq_zero (chiSquare_nonneg m x)).mp hz
      · simp [Measure.real, chiSquare_zero_measure m hm]
    rw [hzero]
    positivity

lemma chi_tail (m : ℕ) (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (standardGaussianProduct m).real {x | r ≤ |Real.sqrt (chiSquare m x) - Real.sqrt m|} ≤
      2 * Real.exp (-r ^ 2 / 2) := by
  have hset : {x | r ≤ |Real.sqrt (chiSquare m x) - Real.sqrt m|} =
      {x | Real.sqrt m + r ≤ Real.sqrt (chiSquare m x)} ∪
      {x | Real.sqrt (chiSquare m x) ≤ Real.sqrt m - r} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor <;> intro h <;> rcases h with h | h <;> first | left; linarith | right; linarith
  rw [hset]
  exact (measureReal_union_le _ _).trans (by
    have := chi_upper_tail m hm r hr
    have := chi_lower_tail m hm r hr
    linarith)

lemma chi_measurable (m : ℕ) : Measurable (chi m) := by
  unfold chi chiSquare
  fun_prop

lemma chi_sq (m : ℕ) (x : Fin m → ℝ) : chi m x ^ 2 = chiSquare m x :=
  Real.sq_sqrt (chiSquare_nonneg m x)

lemma chiSquare_integrable (m : ℕ) : Integrable (chiSquare m) (standardGaussianProduct m) := by
  simpa using integrable_pow_of_integrable_exp_mul (X := chiSquare m)
    (by norm_num : (1 / 4 : ℝ) ≠ 0) (chiSquare_exp_integrable m _ (by norm_num))
    (chiSquare_exp_integrable m _ (by norm_num)) 1

lemma chi_integrable (m : ℕ) : Integrable (chi m) (standardGaussianProduct m) := by
  change Integrable (fun x => Real.sqrt (chiSquare m x)) _
  simpa only [Real.sqrt_eq_rpow] using integrable_rpow_of_integrable_exp_mul
    (X := chiSquare m) (by norm_num : (1 / 4 : ℝ) ≠ 0)
    (chiSquare_exp_integrable m _ (by norm_num))
    (chiSquare_exp_integrable m _ (by norm_num)) (p := 1 / 2) (by norm_num)

lemma chi_memLp_two (m : ℕ) : MemLp (chi m) 2 (standardGaussianProduct m) := by
  rw [memLp_two_iff_integrable_sq (chi_measurable m).aestronglyMeasurable]
  simpa only [chi_sq] using chiSquare_integrable m

lemma chi_center_integrable_sq (m : ℕ) (c : ℝ) :
    Integrable (fun x => (chi m x - c) ^ 2) (standardGaussianProduct m) := by
  have h := (chi_memLp_two m).sub (memLp_const c)
  exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h

lemma chi_mean_square_error (m : ℕ) (hm : 0 < m) :
    (∫ x, (chi m x - Real.sqrt m) ^ 2 ∂standardGaussianProduct m) ≤ 4 := by
  rw [(chi_center_integrable_sq m (Real.sqrt m)).integral_eq_integral_meas_le
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  have hbound : ∀ t : ℝ, 0 < t → (standardGaussianProduct m).real
      {x | t ≤ (chi m x - Real.sqrt m) ^ 2} ≤ 2 * Real.exp (-(1 / 2) * t) := by
    intro t ht
    have hset : {x | t ≤ (chi m x - Real.sqrt m) ^ 2} =
        {x | Real.sqrt t ≤ |chi m x - Real.sqrt m|} := by
      ext x
      simp only [Set.mem_ofPred_eq, Real.sqrt_le_iff, abs_nonneg, true_and, sq_abs]
    rw [hset]
    have h := chi_tail m hm (Real.sqrt t) (Real.sqrt_nonneg t)
    simpa [chi, Real.sq_sqrt ht.le, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using h
  calc
    _ ≤ ∫ t in Set.Ioi 0, 2 * Real.exp (-(1 / 2) * t) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => measureReal_nonneg)
      · exact (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0).const_mul 2
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hbound t ht
    _ = 4 := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0)]
      norm_num

lemma gaussian_integral_square : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (μ := gaussianReal 0 1) (X := id) (memLp_id_gaussianReal 2)
  simpa only [variance_id_gaussianReal, NNReal.coe_one, id_eq, Pi.pow_apply,
    integral_id_gaussianReal, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using h.symm

lemma chiSquare_mean (m : ℕ) :
    (∫ x, chiSquare m x ∂standardGaussianProduct m) = m := by
  have hg : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
    simpa using (memLp_two_iff_integrable_sq
      (measurable_id.aestronglyMeasurable : AEStronglyMeasurable id (gaussianReal 0 1))).mp
        (memLp_id_gaussianReal 2)
  unfold chiSquare standardGaussianProduct
  rw [integral_finsetSum Finset.univ (f := fun (i : Fin m) (x : Fin m → ℝ) => x i ^ 2)
    (fun i _ => integrable_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i) hg)]
  have hcomp (i : Fin m) :
      (∫ x : Fin m → ℝ, x i ^ 2 ∂Measure.pi (fun _ : Fin m => gaussianReal 0 1)) = 1 := by
    rw [integral_comp_eval (μ := fun _ : Fin m => gaussianReal 0 1) (i := i)
      hg.aestronglyMeasurable]
    exact gaussian_integral_square
  simp only [hcomp, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma chi_mean_nonneg (m : ℕ) : 0 ≤ ∫ x, chi m x ∂standardGaussianProduct m :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

lemma chi_mean_upper (m : ℕ) : (∫ x, chi m x ∂standardGaussianProduct m) ≤ Real.sqrt m := by
  have hv := variance_nonneg (X := chi m) (μ := standardGaussianProduct m)
  rw [variance_eq_sub (chi_memLp_two m)] at hv
  simp only [Pi.pow_apply, chi_sq, chiSquare_mean] at hv
  exact (Real.le_sqrt (chi_mean_nonneg m) (Nat.cast_nonneg m)).mpr (by linarith)

lemma chi_mean_bias (m : ℕ) (hm : 0 < m) :
    0 ≤ Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ∧
      Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ≤ 2 / Real.sqrt m := by
  refine ⟨sub_nonneg.mpr (chi_mean_upper m), ?_⟩
  have he := chi_mean_square_error m hm
  have hpoint : (fun x => (chi m x - Real.sqrt m) ^ 2) =
      (fun x => chiSquare m x - 2 * Real.sqrt m * chi m x + (m : ℝ)) := by
    funext x
    rw [sub_sq, chi_sq, Real.sq_sqrt (Nat.cast_nonneg m)]
    ring
  rw [hpoint, integral_add (f := fun x => chiSquare m x - 2 * Real.sqrt m * chi m x)
    (g := fun _ => (m : ℝ)) ((chiSquare_integrable m).sub
    ((chi_integrable m).const_mul _)) (integrable_const _),
    integral_sub (f := chiSquare m) (g := fun x => 2 * Real.sqrt m * chi m x)
      (chiSquare_integrable m) ((chi_integrable m).const_mul _),
    integral_const_mul, chiSquare_mean, integral_const] at he
  simp only [probReal_univ, smul_eq_mul, one_mul] at he
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm))).mpr
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg m)]

lemma chi_square_deviation_tail (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    (standardGaussianProduct m).real {x | t ≤ (chi m x - Real.sqrt m) ^ 2} ≤
      2 * Real.exp (-(1 / 2) * t) := by
  have hset : {x | t ≤ (chi m x - Real.sqrt m) ^ 2} =
      {x | Real.sqrt t ≤ |chi m x - Real.sqrt m|} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_le_iff, abs_nonneg, true_and, sq_abs]
  rw [hset]
  simpa [chi, Real.sq_sqrt ht, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using
    chi_tail m hm (Real.sqrt t) (Real.sqrt_nonneg t)

lemma chi_square_deviation_exp_integrable (m : ℕ) :
    Integrable (fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4))
      (standardGaussianProduct m) := by
  apply ((chiSquare_exp_integrable m (1 / 4) (by norm_num)).const_mul
    (Real.exp ((m : ℝ) / 4))).mono'
  · exact ((chi_measurable m).sub measurable_const).pow_const 2 |>.div_const 4 |>.exp
      |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := Real.sqrt_nonneg (chiSquare m x)
    have h2 := Real.sqrt_nonneg (m : ℝ)
    have h3 := chi_sq m x
    have h4 := Real.sq_sqrt (Nat.cast_nonneg m)
    change 0 ≤ chi m x at h1
    nlinarith [mul_nonneg h1 h2]

lemma chi_square_deviation_exp_bound (m : ℕ) (hm : 0 < m) :
    (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
      ∂standardGaussianProduct m) ≤ 3 := by
  have hi := chi_square_deviation_exp_integrable m
  have hnonneg : ∀ x, 0 ≤ Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1 := by
    intro x
    exact sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hformula (u : ℝ) : (∫ t in (0 : ℝ)..u, (1 / 4 : ℝ) * Real.exp (t / 4)) =
      Real.exp (u / 4) - 1 := by
    have hd (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t / 4))
        ((1 / 4 : ℝ) * Real.exp (x / 4)) x := by
      simpa only [id_eq, one_div, mul_comm] using ((hasDerivAt_id x).div_const 4).exp
    simpa only [zero_div, Real.exp_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
        ((by fun_prop : Continuous (fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4))).intervalIntegrable 0 u)
  have hl := lintegral_comp_eq_lintegral_meas_le_mul
    (f := fun x => (chi m x - Real.sqrt m) ^ 2)
    (g := fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4)) (standardGaussianProduct m)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (((chi_measurable m).sub measurable_const).pow_const 2).aemeasurable
    (fun t _ => (by fun_prop : Continuous (fun t : ℝ => (1 / 4 : ℝ) * Real.exp (t / 4))).intervalIntegrable 0 t)
    (Filter.Eventually.of_forall (fun _ => by positivity))
  simp_rw [hformula] at hl
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1) (hi.sub (integrable_const 1))
    (Filter.Eventually.of_forall hnonneg)] at hl
  have hb : ENNReal.ofReal (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) - 1
      ∂standardGaussianProduct m) ≤ ENNReal.ofReal 2 := by
    rw [hl]
    calc
      _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((1 / 2 : ℝ) * Real.exp (-(1 / 4) * t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ (2 * Real.exp (-(1 / 2) * t)) * ((1 / 4) * Real.exp (t / 4)) := by
            gcongr
            exact chi_square_deviation_tail m hm t ht.le
          _ = (1 / 2) * Real.exp (-(1 / 4) * t) := by
            rw [show -(1 / 4) * t = -(1 / 2) * t + t / 4 by ring, Real.exp_add]
            ring
      _ = ENNReal.ofReal 2 := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) 0).const_mul (1 / 2))
          (Filter.Eventually.of_forall (fun _ => by positivity))]
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0)]
        norm_num
  have hb' := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hb
  rw [integral_sub (f := fun x => Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4))
    (g := fun _ => (1 : ℝ)) hi (integrable_const 1)] at hb'
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb'
  linarith

lemma exp_quadratic_remainder (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h : |Real.exp x - (1 + x)| ≤ x ^ 2 * Real.exp |x| := by
    have hc := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
    norm_num [Finset.sum_range_succ] at hc
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hc
  have hh := (abs_le.mp h).2
  linarith

lemma exp_quadratic_domination (t z : ℝ) :
    Real.exp (t * z) ≤ 1 + t * z +
      (16 * t ^ 2 * Real.exp (4 * t ^ 2)) * Real.exp (z ^ 2 / 8) := by
  have hy : |t * z| ≤ 4 * t ^ 2 + z ^ 2 / 16 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (2 * t + z / 4), sq_nonneg (2 * t - z / 4)]
  have hz : z ^ 2 ≤ 16 * Real.exp (z ^ 2 / 16) := by
    have := Real.add_one_le_exp (z ^ 2 / 16)
    linarith
  calc
    _ ≤ 1 + t * z + (t * z) ^ 2 * Real.exp |t * z| := exp_quadratic_remainder _
    _ ≤ 1 + t * z + (t * z) ^ 2 * Real.exp (4 * t ^ 2 + z ^ 2 / 16) := by gcongr
    _ = 1 + t * z + (t ^ 2 * Real.exp (4 * t ^ 2)) * (z ^ 2 * Real.exp (z ^ 2 / 16)) := by
      rw [Real.exp_add]
      ring
    _ ≤ 1 + t * z + (t ^ 2 * Real.exp (4 * t ^ 2)) *
        (16 * Real.exp (z ^ 2 / 16) * Real.exp (z ^ 2 / 16)) := by gcongr
    _ = _ := by
      rw [show z ^ 2 / 8 = z ^ 2 / 16 + z ^ 2 / 16 by ring, Real.exp_add]
      ring

lemma one_add_linear_mul_exp_le (a b r : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    1 + a * r * Real.exp (b * r) ≤ Real.exp ((a + b) * r) := by
  calc
    _ ≤ Real.exp (b * r) + a * r * Real.exp (b * r) := by
      gcongr
      exact Real.one_le_exp (mul_nonneg hb hr)
    _ = (1 + a * r) * Real.exp (b * r) := by ring
    _ ≤ Real.exp (a * r) * Real.exp (b * r) := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp (a * r)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma centered_mgf_from_exp_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hX : Integrable X μ) (hzero : ∫ x, X x ∂μ = 0)
    (hexp : Integrable (fun x => Real.exp (X x ^ 2 / 8)) μ)
    (hB : (∫ x, Real.exp (X x ^ 2 / 8) ∂μ) ≤ B) (hB0 : 0 ≤ B) (t : ℝ) :
    (∫ x, Real.exp (t * X x) ∂μ) ≤ Real.exp ((16 * B + 4) * t ^ 2) := by
  have hbound := fun x => exp_quadratic_domination t (X x)
  calc
    _ ≤ ∫ x, (1 + t * X x) + (16 * t ^ 2 * Real.exp (4 * t ^ 2)) *
        Real.exp (X x ^ 2 / 8) ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
      · exact ((integrable_const 1).add (hX.const_mul t)).add (hexp.const_mul _)
      · exact Filter.Eventually.of_forall hbound
    _ = 1 + (16 * t ^ 2 * Real.exp (4 * t ^ 2)) *
        (∫ x, Real.exp (X x ^ 2 / 8) ∂μ) := by
      rw [integral_add (f := fun x => 1 + t * X x)
        (g := fun x => (16 * t ^ 2 * Real.exp (4 * t ^ 2)) * Real.exp (X x ^ 2 / 8))
        ((integrable_const 1).add (hX.const_mul t)) (hexp.const_mul _),
        integral_add (f := fun _ => (1 : ℝ)) (g := fun x => t * X x)
        (integrable_const 1) (hX.const_mul t), integral_const_mul, integral_const_mul, hzero]
      simp
    _ ≤ 1 + (16 * B) * (t ^ 2) * Real.exp (4 * t ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hB
        (show 0 ≤ 16 * t ^ 2 * Real.exp (4 * t ^ 2) by positivity)]
    _ ≤ _ := one_add_linear_mul_exp_le (16 * B) 4 (t ^ 2) (by positivity) (by norm_num) (sq_nonneg t)

lemma integrable_exp_of_exp_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ)
    (hexp : Integrable (fun x => Real.exp (X x ^ 2 / 8)) μ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * X x)) μ := by
  apply (hexp.const_mul (Real.exp (4 * t ^ 2))).mono'
  · exact Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul t)
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (2 * t - X x / 4), sq_nonneg (X x)]

lemma chi_bias_le_two (m : ℕ) (hm : 0 < m) :
    Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ≤ 2 := by
  have hs : (1 : ℝ) ≤ Real.sqrt m := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt this
  calc
    _ ≤ 2 / Real.sqrt m := (chi_mean_bias m hm).2
    _ ≤ 2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith

lemma chi_center_square_exp_pointwise (m : ℕ) (hm : 0 < m) (x : Fin m → ℝ) :
    Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8) ≤
      Real.exp 1 * Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb0 := (chi_mean_bias m hm).1
  have hb2 := chi_bias_le_two m hm
  have hb4 : (Real.sqrt m - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 ≤ 4 := by
    nlinarith
  nlinarith [sq_nonneg (chi m x - Real.sqrt m -
    (Real.sqrt m - (∫ y, chi m y ∂standardGaussianProduct m)))]

lemma chi_center_square_exp_integrable (m : ℕ) (hm : 0 < m) :
    Integrable (fun x => Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8))
      (standardGaussianProduct m) := by
  apply ((chi_square_deviation_exp_integrable m).const_mul (Real.exp 1)).mono'
  · exact ((chi_measurable m).sub measurable_const).pow_const 2 |>.div_const 8 |>.exp
      |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact chi_center_square_exp_pointwise m hm x

lemma chi_center_square_exp_bound (m : ℕ) (hm : 0 < m) :
    (∫ x, Real.exp ((chi m x - (∫ y, chi m y ∂standardGaussianProduct m)) ^ 2 / 8)
      ∂standardGaussianProduct m) ≤ 3 * Real.exp 1 := by
  calc
    _ ≤ ∫ x, Real.exp 1 * Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
        ∂standardGaussianProduct m := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
      · exact (chi_square_deviation_exp_integrable m).const_mul (Real.exp 1)
      · exact Filter.Eventually.of_forall (chi_center_square_exp_pointwise m hm)
    _ = Real.exp 1 * (∫ x, Real.exp ((chi m x - Real.sqrt m) ^ 2 / 4)
        ∂standardGaussianProduct m) := integral_const_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (chi_square_deviation_exp_bound m hm) (Real.exp_pos 1).le
      nlinarith

theorem chi_centered_subGaussian (m : ℕ) (hm : 0 < m) :
    HasSubgaussianMGF (fun x => chi m x - (∫ y, chi m y ∂standardGaussianProduct m))
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩ (standardGaussianProduct m) := by
  have hi : Integrable (fun x => chi m x - (∫ y, chi m y ∂standardGaussianProduct m))
      (standardGaussianProduct m) := (chi_integrable m).sub (integrable_const _)
  have hz : (∫ x, chi m x - (∫ y, chi m y ∂standardGaussianProduct m)
      ∂standardGaussianProduct m) = 0 := by
    rw [integral_sub (f := chi m) (g := fun _ => (∫ y, chi m y ∂standardGaussianProduct m))
      (chi_integrable m) (integrable_const _)]
    simp
  refine ⟨integrable_exp_of_exp_square hi.aestronglyMeasurable
    (chi_center_square_exp_integrable m hm), ?_⟩
  intro t
  have h := centered_mgf_from_exp_square hi hz (chi_center_square_exp_integrable m hm)
    (chi_center_square_exp_bound m hm) (by positivity) t
  change _ ≤ Real.exp ((2 * (48 * Real.exp 1 + 4)) * t ^ 2 / 2)
  convert h using 1
  congr 1
  ring_nf

lemma centeredChiRow_measurable (n i : ℕ) : Measurable (centeredChiRow n i) :=
  ((chi_measurable _).comp (measurable_pi_apply i)).sub measurable_const

lemma centeredChiRows_independent (n : ℕ) : iIndepFun (centeredChiRow n) (chiRowLaw n) := by
  exact iIndepFun_infinitePi (fun i => (chi_measurable _).sub measurable_const)

lemma centeredChiRow_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (centeredChiRow n i)
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩ (chiRowLaw n) := by
  have h := chi_centered_subGaussian (chiRowDim n i) (by unfold chiRowDim; omega)
  have h' : HasSubgaussianMGF
      (fun x => chi (chiRowDim n i) x -
        ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i))
      ⟨2 * (48 * Real.exp 1 + 4), by positivity⟩
      ((chiRowLaw n).map (fun ω => ω i)) := by
    simpa only [chiRowLaw, Measure.infinitePi_map_eval] using h
  exact HasSubgaussianMGF.of_map (μ := chiRowLaw n) (Y := fun ω : ChiRows n => ω i)
    (measurable_pi_apply i).aemeasurable h'

lemma centeredChiRow_mean (n i : ℕ) : (∫ ω, centeredChiRow n i ω ∂chiRowLaw n) = 0 := by
  let f (x : Fin (chiRowDim n i) → ℝ) := chi (chiRowDim n i) x -
    ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)
  have he := integral_map (μ := chiRowLaw n) (φ := fun ω : ChiRows n => ω i)
    (f := f) (measurable_pi_apply i).aemeasurable
    ((chi_measurable _).sub measurable_const).aestronglyMeasurable
  change (∫ ω, f (ω i) ∂chiRowLaw n) = 0
  rw [← he]
  simp only [chiRowLaw, Measure.infinitePi_map_eval]
  dsimp only [f]
  rw [integral_sub (chi_integrable _) (integrable_const _)]
  simp

lemma scaledChiRow_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (scaledChiRow n i)
      ⟨2 * (48 * Real.exp 1 + 4) / (n + 1), by positivity⟩ (chiRowLaw n) := by
  have h := (centeredChiRow_subGaussian n i).const_mul (Real.sqrt (n + 1))⁻¹
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  have ht := h.mgf_le t
  convert ht using 1
  congr 1
  apply congrArg Real.exp
  change (2 * (48 * Real.exp 1 + 4) / (n + 1)) * t ^ 2 / 2 =
    ((Real.sqrt (n + 1))⁻¹ ^ 2 * (2 * (48 * Real.exp 1 + 4))) * t ^ 2 / 2
  rw [inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)]
  ring

lemma scaledChiRows_independent (n : ℕ) : iIndepFun (scaledChiRow n) (chiRowLaw n) :=
  (centeredChiRows_independent n).comp (fun _ x => (Real.sqrt (n + 1))⁻¹ * x)
    (fun _ => measurable_const.mul measurable_id)

lemma scaledChiRow_measurable (n i : ℕ) : Measurable (scaledChiRow n i) :=
  (centeredChiRow_measurable n i).const_mul _

lemma scaledChiRow_mean (n i : ℕ) : (∫ ω, scaledChiRow n i ω ∂chiRowLaw n) = 0 := by
  change (∫ ω, (Real.sqrt (n + 1))⁻¹ * centeredChiRow n i ω ∂chiRowLaw n) = 0
  rw [integral_const_mul, centeredChiRow_mean, mul_zero]

lemma gaussian_id_subGaussian (v : ℝ≥0) : HasSubgaussianMGF id v (gaussianReal 0 v) := by
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_gaussianReal (μ := 0) (v := v) (by simp)]
  simp

lemma diagonalRows_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω i) ⟨2 / (n + 1), by positivity⟩ (diagonalLaw n) := by
  have h : HasSubgaussianMGF id ⟨2 / (n + 1), by positivity⟩
      ((diagonalLaw n).map (fun ω => ω i)) := by
    simpa only [diagonalLaw, Measure.infinitePi_map_eval, diagonalMarginal] using
      gaussian_id_subGaussian ⟨2 / (n + 1), by positivity⟩
  exact HasSubgaussianMGF.of_map (μ := diagonalLaw n) (Y := fun ω : ℕ → ℝ => ω i)
    (measurable_pi_apply i).aemeasurable h

lemma diagonalRows_independent (n : ℕ) :
    iIndepFun (fun i (ω : ℕ → ℝ) => ω i) (diagonalLaw n) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

lemma diagonalRows_mean (n i : ℕ) : (∫ ω, ω i ∂diagonalLaw n) = 0 := by
  have he := integral_map (μ := diagonalLaw n) (φ := fun ω : ℕ → ℝ => ω i)
    (f := id) (measurable_pi_apply i).aemeasurable (measurable_id.aestronglyMeasurable)
  change (∫ ω, id (ω i) ∂diagonalLaw n) = 0
  rw [← he]
  simp only [diagonalLaw, Measure.infinitePi_map_eval, diagonalMarginal]
  exact integral_id_gaussianReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma partial_sum_abs_maximal_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X i ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  have hp := partial_sum_maximal_tail hX hind hmgf hmean hc m ha
  have hn := partial_sum_maximal_tail (X := fun i ω => -X i ω)
    (fun i => (hX i).neg) (hind.comp (fun _ x => -x) (fun _ => measurable_neg))
    (fun i => (hmgf i).neg) (fun i => by rw [integral_neg, hmean, neg_zero]) hc m ha
  let A : Set Ω := {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω}
  let B : Set Ω := {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), -X i ω}
  have hs : {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X i ω|} ⊆ A ∪ B := by
    rintro ω ⟨k, hk, hka⟩
    rcases le_abs.mp hka with h | h
    · exact Or.inl ⟨k, hk, h⟩
    · exact Or.inr ⟨k, hk, by simpa only [Finset.sum_neg_distrib] using h⟩
  have h := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le A B)
  change μ.real _ ≤ μ.real A + μ.real B at h
  change μ.real A ≤ _ at hp
  change μ.real B ≤ _ at hn
  linarith

lemma block_prefix_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (start m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ |∑ i ∈ Finset.range (k + 1), X (start + i) ω|} ≤
      2 * Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  exact partial_sum_abs_maximal_tail (fun i => hX (start + i))
    (hind.precomp (fun i j h => Nat.add_left_cancel h))
    (fun i => hmgf (start + i)) (fun i => hmean (start + i)) hc m ha

lemma blockThreshold_sq (c : ℝ≥0) (m j r : ℕ) (h : ℝ) :
    blockThreshold c m j r h ^ 2 =
      2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16) := by
  apply Real.sq_sqrt
  positivity

lemma block_prefix_dyadic_tail {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (start m j r : ℕ) (h : ℝ) :
    μ.real {ω | ∃ k ≤ m, blockThreshold c m j r h ≤
      |∑ i ∈ Finset.range (k + 1), X (start + i) ω|} ≤
      2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r) := by
  have ht := block_prefix_tail hX hind hmgf hmean hc start m
    (a := blockThreshold c m j r h) (Real.sqrt_nonneg _)
  rw [blockThreshold_sq] at ht
  have hc' : (c : ℝ) ≠ 0 := ne_of_gt hc
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  have he : -(2 * (m + 1) * (c : ℝ) * (h ^ 2 + (j + r : ℕ) * Real.log 16)) /
      (2 * (m + 1) * (c : ℝ)) = -h ^ 2 + (j + r : ℕ) * (-Real.log 16) := by
    field_simp
    ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_neg (Real.log 16), Real.exp_log (by norm_num : (0 : ℝ) < 16)] at ht
  simpa only [one_div, mul_assoc] using ht

lemma geometric_half_sum_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).sum_le_tsum
    (Finset.range N) (fun _ _ => by positivity)
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)] at h
  norm_num at h ⊢
  exact h

omit [IsProbabilityMeasure μ] in
lemma finite_scale_shell_union_bound (A : ℕ → ℕ → ℕ → Set Ω)
    (B : ℕ → ℕ → Finset ℕ) (J R : ℕ) {C h : ℝ} (hC : 0 ≤ C)
    (hcard : ∀ j r, ((B j r).card : ℝ) ≤ C * (8 : ℝ) ^ (j + r))
    (hprob : ∀ j r b, b ∈ B j r → μ.real (A j r b) ≤
      2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) :
    μ.real (⋃ j ∈ Finset.range J, ⋃ r ∈ Finset.range R, ⋃ b ∈ B j r, A j r b) ≤
      8 * C * Real.exp (-h ^ 2) := by
  have hbr (j r : ℕ) : μ.real (⋃ b ∈ B j r, A j r b) ≤
      2 * C * Real.exp (-h ^ 2) * (1 / 2 : ℝ) ^ (j + r) := by
    calc
      _ ≤ ∑ b ∈ B j r, μ.real (A j r b) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ B j r, 2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r) :=
        Finset.sum_le_sum (fun b hb => hprob j r b hb)
      _ = (B j r).card * (2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) := by simp
      _ ≤ (C * (8 : ℝ) ^ (j + r)) *
          (2 * Real.exp (-h ^ 2) * (1 / 16 : ℝ) ^ (j + r)) :=
        mul_le_mul_of_nonneg_right (hcard j r) (by positivity)
      _ = _ := by
        have he : (8 : ℝ) ^ (j + r) * (1 / 16 : ℝ) ^ (j + r) = (1 / 2 : ℝ) ^ (j + r) := by
          rw [← mul_pow]
          norm_num
        calc
          _ = 2 * C * Real.exp (-h ^ 2) * ((8 : ℝ) ^ (j + r) * (1 / 16 : ℝ) ^ (j + r)) := by ring
          _ = _ := by rw [he]
  calc
    _ ≤ ∑ j ∈ Finset.range J, μ.real (⋃ r ∈ Finset.range R, ⋃ b ∈ B j r, A j r b) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range R, μ.real (⋃ b ∈ B j r, A j r b) := by
      exact Finset.sum_le_sum fun _ _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, ∑ r ∈ Finset.range R,
        2 * C * Real.exp (-h ^ 2) * (1 / 2 : ℝ) ^ (j + r) := by
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun r _ => hbr j r
    _ = 2 * C * Real.exp (-h ^ 2) *
        (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j) *
        (∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r) := by
      simp_rw [pow_add, ← mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [← Finset.mul_sum]
    _ ≤ 2 * C * Real.exp (-h ^ 2) * 2 * 2 := by
      gcongr
      · exact geometric_half_sum_le_two J
      · exact geometric_half_sum_le_two R
    _ = _ := by ring

lemma blockShell_card (j r : ℕ) :
    ((blockShell j r).card : ℝ) ≤ 2 * (8 : ℝ) ^ (j + r) := by
  cases r with
  | zero => simp [blockShell]
  | succ r =>
    have hpow : (2 : ℕ) ^ (r + 1) ≤ 8 ^ (r + 1) := Nat.pow_le_pow_left (by decide) _
    have he : 2 ^ (r + 2) * 8 ^ j - 2 ^ (r + 1) * 8 ^ j = 2 ^ (r + 1) * 8 ^ j := by
      rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      have hid : 2 ^ (r + 1) * 2 * 8 ^ j = 2 * (2 ^ (r + 1) * 8 ^ j) := by ring
      rw [hid]
      omega
    rw [blockShell, Nat.card_Ico, he]
    push_cast
    rw [pow_add (8 : ℝ) j (r + 1)]
    have hp : (2 : ℝ) ^ (r + 1) ≤ 8 ^ (r + 1) := by exact_mod_cast hpow
    calc
      _ ≤ 8 ^ (r + 1) * (8 : ℝ) ^ j := mul_le_mul_of_nonneg_right hp (by positivity)
      _ ≤ _ := by nlinarith [show 0 ≤ (8 : ℝ) ^ j * 8 ^ (r + 1) by positivity]

lemma blockShell_covers (j b : ℕ) :
    ∃ r ≤ b, b ∈ blockShell j r := by
  by_cases hb : b < 2 * 8 ^ j
  · exact ⟨0, Nat.zero_le _, by simpa [blockShell]⟩
  · have h8 : 0 < (8 : ℕ) ^ j := by positivity
    have hq : 2 ≤ b / 8 ^ j := (Nat.le_div_iff_mul_le h8).mpr (Nat.le_of_not_gt hb)
    let r := Nat.log 2 (b / 8 ^ j)
    have hr : 0 < r := Nat.log_pos (by decide) hq
    have hlo : 2 ^ r * 8 ^ j ≤ b :=
      (Nat.le_div_iff_mul_le h8).mp (Nat.pow_log_le_self 2 (by omega : b / 8 ^ j ≠ 0))
    have hhi : b < 2 ^ (r + 1) * 8 ^ j :=
      (Nat.div_lt_iff_lt_mul h8).mp (Nat.lt_pow_succ_log_self (by decide) _)
    refine ⟨r, (Nat.log_le_self _ _).trans (Nat.div_le_self _ _), ?_⟩
    obtain ⟨r', heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    rw [heq] at hlo hhi ⊢
    simpa [blockShell, Nat.succ_eq_add_one, Nat.add_assoc] using And.intro hlo hhi

lemma blockShell_lower (j r b : ℕ) (hr : 0 < r) (hb : b ∈ blockShell j r) :
    2 ^ r * 8 ^ j ≤ b := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  exact (Finset.mem_Ico.mp hb).1

lemma multiscaleBad_probability {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (d : ℕ → ℕ) (J N : ℕ) (h : ℝ) :
    μ.real (multiscaleBad X c d J N h) ≤ 16 * Real.exp (-h ^ 2) := by
  simpa only [multiscaleBad, show (8 : ℝ) * 2 = 16 by norm_num] using
    finite_scale_shell_union_bound
      (fun j r b => {ω | ∃ k ≤ d j, blockThreshold c (d j) j r h ≤
        |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω|})
      blockShell J (N + 1) (by norm_num : (0 : ℝ) ≤ 2)
      blockShell_card (fun j r b _ => block_prefix_dyadic_tail hX hind hmgf hmean hc _ _ _ _ _)

omit [MeasurableSpace Ω] in
lemma good_multiscale_prefix_all {X : ℕ → Ω → ℝ} {c : ℝ≥0} {d : ℕ → ℕ}
    {J N : ℕ} {h : ℝ} {ω : Ω} (hω : ω ∉ multiscaleBad X c d J N h)
    {j r b : ℕ} (hj : j < J) (hr : r ≤ N) (hb : b ∈ blockShell j r) {k : ℕ} (hk : k ≤ d j) :
    |∑ i ∈ Finset.range (k + 1), X (b * (d j + 1) + i) ω| ≤ blockThreshold c (d j) j r h := by
  apply le_of_lt
  by_contra! hbad
  apply hω
  simp only [multiscaleBad, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨j, Finset.mem_range.mpr hj, r, Finset.mem_range.mpr (by omega), b, hb, k, hk, hbad⟩

end

lemma block_summation_by_parts (ξ w : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, ξ i * w i =
      (∑ i ∈ Finset.range m, ξ i) * w m +
        ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range (i + 1), ξ j) * (w i - w (i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Finset.sum_range_succ]
    ring

lemma block_zero_sum_bound (ξ w : ℕ → ℝ) (m : ℕ) {B : ℝ}
    (htotal : ∑ i ∈ Finset.range (m + 1), ξ i = 0)
    (hpref : ∀ k ≤ m, |∑ i ∈ Finset.range (k + 1), ξ i| ≤ B) :
    |∑ i ∈ Finset.range (m + 1), ξ i * w i| ≤
      B * ∑ i ∈ Finset.range m, |w (i + 1) - w i| := by
  rw [block_summation_by_parts, htotal, zero_mul, zero_add,
    Finset.sum_range_succ, htotal, zero_mul, add_zero]
  calc
    _ ≤ ∑ i ∈ Finset.range m,
        |(∑ j ∈ Finset.range (i + 1), ξ j) * (w i - w (i + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range m, B * |w (i + 1) - w i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_sub_comm (w i)]
      exact mul_le_mul_of_nonneg_right (hpref i (Nat.le_of_lt (Finset.mem_range.mp hi)))
        (abs_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

lemma block_prefix_weight_bound (ξ w : ℕ → ℝ) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hpref : ∀ k ≤ m, |∑ i ∈ Finset.range (k + 1), ξ i| ≤ B) :
    |∑ i ∈ Finset.range (m + 1), ξ i * w i| ≤
      B / (m + 1) * (∑ i ∈ Finset.range (m + 1), |w i|) +
        2 * B * ∑ i ∈ Finset.range m, |w (i + 1) - w i| := by
  let avg : ℝ := (∑ i ∈ Finset.range (m + 1), ξ i) / (m + 1)
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have havg : |avg| ≤ B / (m + 1) := by
    dsimp [avg]
    rw [abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right (hpref m le_rfl) hm.le
  have hc (k : ℕ) : (∑ i ∈ Finset.range k, (ξ i - avg)) =
      (∑ i ∈ Finset.range k, ξ i) - k * avg := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hz : ∑ i ∈ Finset.range (m + 1), (ξ i - avg) = 0 := by
    rw [hc]
    dsimp [avg]
    push_cast
    field_simp
    ring
  have hp (k : ℕ) (hk : k ≤ m) : |∑ i ∈ Finset.range (k + 1), (ξ i - avg)| ≤ 2 * B := by
    rw [hc]
    have hk' : (k + 1 : ℝ) ≤ m + 1 := by exact_mod_cast Nat.succ_le_succ hk
    have hpart : |(k + 1 : ℝ) * avg| ≤ B := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
      calc
        _ ≤ (k + 1) * (B / (m + 1)) := mul_le_mul_of_nonneg_left havg (by positivity)
        _ ≤ (m + 1) * (B / (m + 1)) := mul_le_mul_of_nonneg_right hk' (by positivity)
        _ = B := by field_simp
    have ha := abs_sub (∑ i ∈ Finset.range (k + 1), ξ i) ((k + 1 : ℝ) * avg)
    push_cast
    exact ha.trans (by linarith [hpref k hk])
  have hs := block_zero_sum_bound (fun i => ξ i - avg) w m hz hp
  have hid : (∑ i ∈ Finset.range (m + 1), ξ i * w i) =
      avg * (∑ i ∈ Finset.range (m + 1), w i) +
        (∑ i ∈ Finset.range (m + 1), (ξ i - avg) * w i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add ?_ hs)
  rw [abs_mul]
  exact mul_le_mul havg (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by positivity)

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PathEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

lemma path_energy_identity (n : ℕ) (c u : ℕ → ℝ) (hc : c n = 0) :
    2 * (∑ i ∈ Finset.range (n + 1), u i ^ 2) -
      2 * (∑ i ∈ Finset.range n, c i * u i * u (i + 1)) =
    (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - c i - if i = 0 then 0 else c (i - 1)) * u i ^ 2 := by
  have hl : (∑ i ∈ Finset.range (n + 1),
      (if i = 0 then (0 : ℝ) else c (i - 1)) * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  have hr : (∑ i ∈ Finset.range (n + 1), c i * u i ^ 2) =
      ∑ i ∈ Finset.range n, c i * u i ^ 2 := by
    rw [Finset.sum_range_succ, hc, zero_mul, add_zero]
  have hg : (∑ i ∈ Finset.range n, c i * (u (i + 1) - u i) ^ 2) =
      (∑ i ∈ Finset.range n, c i * u i ^ 2) +
      (∑ i ∈ Finset.range n, c i * u (i + 1) ^ 2) -
      2 * ∑ i ∈ Finset.range n, c i * u i * u (i + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hl, hr, hg]
  ring

lemma edgeCoeff_nonneg (n i : ℕ) : 0 ≤ edgeCoeff n i := Real.sqrt_nonneg _

lemma edgeCoeff_last (n : ℕ) : edgeCoeff n n = 0 := by
  simp [edgeCoeff, show (n + 1 : ℝ) ≠ 0 by positivity]

lemma edgeCoeff_upper (n i : ℕ) (hi : i ≤ n) :
    edgeCoeff n i ≤ 1 - (i + 1 : ℝ) / (2 * (n + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hit : (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hi
  have ht : 0 ≤ (i + 1 : ℝ) / (n + 1) := by positivity
  have ht1 : (i + 1 : ℝ) / (n + 1) ≤ 1 := (div_le_one hn).mpr hit
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - (i + 1 : ℝ) / (n + 1))
  have hd : (i + 1 : ℝ) / (2 * (n + 1)) = ((i + 1 : ℝ) / (n + 1)) / 2 := by rw [div_div]; ring
  dsimp [edgeCoeff]
  rw [hd]
  nlinarith [Real.sqrt_nonneg (1 - (i + 1 : ℝ) / (n + 1)),
    sq_nonneg ((i + 1 : ℝ) / (n + 1))]

lemma edgeCoeff_le_one (n i : ℕ) (hi : i ≤ n) : edgeCoeff n i ≤ 1 :=
  (edgeCoeff_upper n i hi).trans (sub_le_self _ (by positivity))

lemma edge_deficit (n i : ℕ) (hi : i ≤ n) :
    (i + 1 : ℝ) / (2 * (n + 1)) ≤
      2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1) := by
  have h := edgeCoeff_upper n i hi
  split_ifs with hi0
  · linarith
  · have hprev := edgeCoeff_le_one n (i - 1) (by omega)
    linarith

lemma pathEnergy_expansion (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u =
      (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      ∑ i ∈ Finset.range (n + 1),
        (2 - edgeCoeff n i - if i = 0 then 0 else edgeCoeff n (i - 1)) * u i ^ 2 :=
  path_energy_identity n (edgeCoeff n) u (edgeCoeff_last n)

lemma pathEnergy_controls (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2) ≤
      pathEnergy n u := by
  rw [pathEnergy_expansion]
  gcongr with i hi
  exact edge_deficit n i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma pathEnergy_nonneg (n : ℕ) (u : ℕ → ℝ) : 0 ≤ pathEnergy n u :=
  (by
    unfold edgeCoeff
    positivity : 0 ≤
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
      (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2)).trans
        (pathEnergy_controls n u)

lemma pathEnergy_weighted_mass (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) ≤
      2 * pathEnergy n u := by
  have h := pathEnergy_controls n u
  have hg : 0 ≤ ∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2 := by
    unfold edgeCoeff
    positivity
  have hs : (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) =
      2 * ∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hs]
  linarith

lemma pathEnergy_weighted_gradient (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) ≤
      pathEnergy n u := by
  have h := pathEnergy_controls n u
  have hp : 0 ≤ ∑ i ∈ Finset.range (n + 1),
      (i + 1 : ℝ) / (2 * (n + 1)) * u i ^ 2 := by positivity
  linarith

lemma edgeCoeff_lower_half (n i : ℕ) (hi : 2 * (i + 1) ≤ n + 1) :
    1 / 2 ≤ edgeCoeff n i := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi' : 2 * (i + 1 : ℝ) ≤ n + 1 := by exact_mod_cast hi
  have ht : (i + 1 : ℝ) / (n + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hn).mpr
    linarith
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - (i + 1 : ℝ) / (n + 1))
  have hp := edgeCoeff_nonneg n i
  dsimp [edgeCoeff] at *
  nlinarith

lemma edge_gradient_control (n i : ℕ) (u : ℕ → ℝ) :
    (u (i + 1) - u i) ^ 2 ≤
      2 * edgeCoeff n i * (u (i + 1) - u i) ^ 2 +
      4 * ((i + 1 : ℝ) / (n + 1) * u i ^ 2 +
        (i + 2 : ℝ) / (n + 1) * u (i + 1) ^ 2) := by
  by_cases hi : 2 * (i + 1) ≤ n + 1
  · have hc := edgeCoeff_lower_half n i hi
    have hm : 0 ≤ (i + 1 : ℝ) / (n + 1) * u i ^ 2 +
        (i + 2 : ℝ) / (n + 1) * u (i + 1) ^ 2 := by positivity
    nlinarith [sq_nonneg (u (i + 1) - u i)]
  · have hi' : (n + 1 : ℝ) ≤ 2 * (i + 1) := by exact_mod_cast (by omega : n + 1 ≤ 2 * (i + 1))
    have hn : (0 : ℝ) < n + 1 := by positivity
    have h1 : 1 / 2 ≤ (i + 1 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hn).mpr
      linarith
    have h2 : 1 / 2 ≤ (i + 2 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hn).mpr
      linarith
    have hm1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (u i))
    have hm2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (u (i + 1)))
    have hg : 0 ≤ edgeCoeff n i * (u (i + 1) - u i) ^ 2 :=
      mul_nonneg (edgeCoeff_nonneg n i) (sq_nonneg _)
    nlinarith [sq_nonneg (u i + u (i + 1))]

lemma pathEnergy_gradient (n : ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (u (i + 1) - u i) ^ 2) ≤ 18 * pathEnergy n u := by
  let mass : ℕ → ℝ := fun i => (i + 1 : ℝ) / (n + 1) * u i ^ 2
  have hm0 : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  have hm1 : (∑ i ∈ Finset.range n, mass i) ≤ ∑ i ∈ Finset.range (n + 1), mass i := by
    rw [Finset.sum_range_succ]
    linarith [hm0 n]
  have hm2 : (∑ i ∈ Finset.range n, mass (i + 1)) ≤ ∑ i ∈ Finset.range (n + 1), mass i := by
    rw [Finset.sum_range_succ']
    linarith [hm0 0]
  have hm := pathEnergy_weighted_mass n u
  change (∑ i ∈ Finset.range (n + 1), mass i) ≤ _ at hm
  have hg := pathEnergy_weighted_gradient n u
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (2 * edgeCoeff n i * (u (i + 1) - u i) ^ 2 + 4 * (mass i + mass (i + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [mass, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using edge_gradient_control n i u
    _ = 2 * (∑ i ∈ Finset.range n, edgeCoeff n i * (u (i + 1) - u i) ^ 2) +
        4 * ((∑ i ∈ Finset.range n, mass i) + (∑ i ∈ Finset.range n, mass (i + 1))) := by
      simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by linarith

lemma square_weight_variation (s : Finset ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ^ 2 ≤
      (∑ i ∈ s, (u (i + 1) - u i) ^ 2) *
        (2 * ∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2)) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => |u (i + 1) ^ 2 - u i ^ 2|)
    (f := fun i => (u (i + 1) - u i) ^ 2)
    (g := fun i => 2 * (u i ^ 2 + u (i + 1) ^ 2))
    (fun _ _ => sq_nonneg _) (by intros; positivity) ?_
  · simpa only [← Finset.mul_sum] using h
  · intro i _
    rw [sq_abs]
    have h := sq_nonneg (u (i + 1) - u i)
    nlinarith [sq_nonneg ((u (i + 1) - u i) ^ 2)]

lemma product_weight_variation (s : Finset ℕ) (u : ℕ → ℝ) :
    (∑ i ∈ s, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ^ 2 ≤
      (2 * ∑ i ∈ s, ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2)) *
        (∑ i ∈ s, u (i + 1) ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => |u (i + 1) * u (i + 2) - u i * u (i + 1)|)
    (f := fun i => 2 * ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2))
    (g := fun i => u (i + 1) ^ 2)
    (by intros; positivity) (fun _ _ => sq_nonneg _) ?_
  · simpa only [← Finset.mul_sum] using h
  · intro i _
    rw [sq_abs]
    have he : (u (i + 1) * u (i + 2) - u i * u (i + 1)) ^ 2 =
        (u (i + 2) - u i) ^ 2 * u (i + 1) ^ 2 := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [sq_nonneg (u (i + 2) - 2 * u (i + 1) + u i)]

lemma pathEnergy_le_four_mass (n : ℕ) (u : ℕ → ℝ) :
    pathEnergy n u ≤ 4 * ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
  have hm1 : (∑ i ∈ Finset.range n, u i ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ]
    linarith [sq_nonneg (u n)]
  have hm2 : (∑ i ∈ Finset.range n, u (i + 1) ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
    rw [Finset.sum_range_succ']
    linarith [sq_nonneg (u 0)]
  have he : -2 * (∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)) ≤
      (∑ i ∈ Finset.range n, u i ^ 2) + (∑ i ∈ Finset.range n, u (i + 1) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have hci := edgeCoeff_le_one n i (Nat.le_of_lt (Finset.mem_range.mp hi))
    have hcn := edgeCoeff_nonneg n i
    have hprod : -2 * u i * u (i + 1) ≤ u i ^ 2 + u (i + 1) ^ 2 := by
      nlinarith [sq_nonneg (u i + u (i + 1))]
    have hmul := mul_le_mul_of_nonneg_left hprod hcn
    have hmass := mul_le_mul_of_nonneg_right hci
      (add_nonneg (sq_nonneg (u i)) (sq_nonneg (u (i + 1))))
    nlinarith
  unfold pathEnergy
  linarith

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.BlockEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

namespace CriticalSK

lemma sum_consecutive_blocks (K d : ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.range K, ∑ i ∈ Finset.range d, f (b * d + i)) =
      ∑ i ∈ Finset.range (K * d), f i := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

lemma block_index_injective (d l : ℕ) (B : Finset ℕ) (hd : 0 < d) (hl : l ≤ d) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * d + p.2) (B ×ˢ Finset.range l : Finset _ ) := by
  rintro ⟨b, i⟩ hbi ⟨c, k⟩ hck he
  have hi : i < d := (Finset.mem_range.mp (Finset.mem_product.mp hbi).2).trans_le hl
  have hk : k < d := (Finset.mem_range.mp (Finset.mem_product.mp hck).2).trans_le hl
  have hi' : i = k := by
    have hm := congrArg (fun n => n % d) he
    simpa only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk] using hm
  have hb : b = c := by
    simp only [hi', Nat.add_right_cancel_iff] at he
    exact Nat.eq_of_mul_eq_mul_right hd he
  exact Prod.ext hb hi'

lemma blockIndices_sum (d l : ℕ) (B : Finset ℕ) (hd : 0 < d) (hl : l ≤ d) (f : ℕ → ℝ) :
    (∑ b ∈ B, ∑ i ∈ Finset.range l, f (b * d + i)) =
      ∑ i ∈ blockIndices d l B, f i := by
  rw [blockIndices, Finset.sum_image (block_index_injective d l B hd hl), Finset.sum_product]

lemma blockIndices_lower (d l a : ℕ) (B : Finset ℕ) (hB : ∀ b ∈ B, a ≤ b * d) :
    ∀ i ∈ blockIndices d l B, a ≤ i := by
  intro i hi
  obtain ⟨⟨b, k⟩, hbk, rfl⟩ := Finset.mem_image.mp hi
  exact (hB b (Finset.mem_product.mp hbk).1).trans (Nat.le_add_right _ _)

lemma sum_supported_le (N : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hzero : ∀ i, N ≤ i → f i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, f i) ≤ ∑ i ∈ Finset.range N, f i := by
  have he : (∑ i ∈ s, f i) = ∑ i ∈ s.filter (fun i => i < N), f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · exact hzero i (Nat.le_of_not_gt hi)
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · exact fun i _ _ => hf i

lemma supported_mass (n : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) :
    (∑ i ∈ s, u i ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 :=
  sum_supported_le _ _ (fun i => sq_nonneg _) (fun i hi => by rw [hu i hi]; norm_num) s

lemma supported_shift_mass (n k : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) :
    (∑ i ∈ s, u (i + k) ^ 2) ≤ ∑ i ∈ Finset.range (n + 1), u i ^ 2 := by
  have he : (∑ i ∈ s, u (i + k) ^ 2) = ∑ i ∈ s.image (fun i => i + k), u i ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  exact supported_mass n u hu _

lemma supported_energy_tail (n : ℕ) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (s : Finset ℕ) (r : ℝ) (hr : ∀ i ∈ s, r ≤ (i + 1 : ℝ) / (n + 1)) :
    r * (∑ i ∈ s, u i ^ 2) ≤ 2 * pathEnergy n u := by
  calc
    _ = ∑ i ∈ s, r * u i ^ 2 := Finset.mul_sum ..
    _ ≤ ∑ i ∈ s, (i + 1 : ℝ) / (n + 1) * u i ^ 2 := by
      gcongr with i hi
      exact hr i hi
    _ ≤ ∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2 :=
      sum_supported_le _ _ (by intro i; positivity)
        (fun i hi => by rw [hu i hi]; ring) s
    _ ≤ _ := pathEnergy_weighted_mass n u

lemma supported_energy_gradient (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + 1) - u i) ^ 2) ≤ 20 * pathEnergy n u := by
  have hs := sum_supported_le (n + 1) (fun i => (u (i + 1) - u i) ^ 2)
    (fun _ => sq_nonneg _) (fun i hi => by rw [hu i hi, hu (i + 1) (by omega)]; ring) s
  rw [Finset.sum_range_succ, hu (n + 1) le_rfl, zero_sub, neg_sq] at hs
  have hn := supported_energy_tail n u hu {n} 1 (by
    intro i hi
    have : i = n := Finset.mem_singleton.mp hi
    subst i
    rw [div_self (by positivity : (n + 1 : ℝ) ≠ 0)])
  simp only [Finset.sum_singleton, one_mul] at hn
  have hg := pathEnergy_gradient n u
  linarith

lemma supported_shift_energy_gradient (n k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + k + 1) - u (i + k)) ^ 2) ≤ 20 * pathEnergy n u := by
  have he : (∑ i ∈ s, (u (i + k + 1) - u (i + k)) ^ 2) =
      ∑ i ∈ s.image (fun i => i + k), (u (i + 1) - u i) ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  exact supported_energy_gradient n u hu _

lemma many_block_prefix_abs_bound (ξ w : ℕ → ℝ) (d : ℕ) (B : Finset ℕ)
    (hd : 0 < d) {bnd : ℝ} (hbnd : 0 ≤ bnd)
    (hpref : ∀ b ∈ B, ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ bnd) :
    (∑ b ∈ B, |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)|) ≤
      bnd / d * (∑ i ∈ blockIndices d d B, |w i|) +
        2 * bnd * ∑ i ∈ blockIndices d (d - 1) B, |w (i + 1) - w i| := by
  have hd' : d - 1 + 1 = d := by omega
  have hblock (b : ℕ) (hb : b ∈ B) := block_prefix_weight_bound
    (fun i => ξ (b * d + i)) (fun i => w (b * d + i)) (d - 1) hbnd
    (fun k hk => hpref b hb k (by omega))
  simp only [hd', Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)), Nat.cast_one,
    sub_add_cancel] at hblock
  calc
    _ ≤ ∑ b ∈ B, (bnd / d * (∑ i ∈ Finset.range d, |w (b * d + i)|) +
        2 * bnd * ∑ i ∈ Finset.range (d - 1), |w (b * d + i + 1) - w (b * d + i)|) := by
      exact Finset.sum_le_sum (fun b hb => by simpa only [Nat.add_assoc] using hblock b hb)
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [blockIndices_sum d d B hd le_rfl (fun i => |w i|),
        blockIndices_sum d (d - 1) B hd (Nat.sub_le _ _) (fun i => |w (i + 1) - w i|)]

lemma supported_shift_energy_tail (n k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) (r : ℝ)
    (hr : ∀ i ∈ s, r ≤ (i + k + 1 : ℕ) / (n + 1 : ℝ)) :
    r * (∑ i ∈ s, u (i + k) ^ 2) ≤ 2 * pathEnergy n u := by
  have he : (∑ i ∈ s, u (i + k) ^ 2) = ∑ i ∈ s.image (fun i => i + k), u i ^ 2 := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => Nat.add_right_cancel h
  rw [he]
  apply supported_energy_tail n u hu _ r
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
  subst i
  simpa only [Nat.cast_add, Nat.cast_one] using hr j hj

lemma localized_product_mass (s : Finset ℕ) (u : ℕ → ℝ) {M : ℝ}
    (h0 : (∑ i ∈ s, u i ^ 2) ≤ M) (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u i * u (i + 1)|) ≤ M := by
  have h : (∑ i ∈ s, |u i * u (i + 1)|) ≤
      (∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2) / 2) := by
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    nlinarith [sq_abs (u i), sq_abs (u (i + 1)), sq_nonneg (|u i| - |u (i + 1)|)]
  rw [← Finset.sum_div, Finset.sum_add_distrib] at h
  linarith

lemma localized_square_variation (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h0 : (∑ i ∈ s, u i ^ 2) ≤ M) (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ≤
      Real.sqrt (80 * pathEnergy n u * M) := by
  have hs := square_weight_variation s u
  have hg := supported_energy_gradient n u hu s
  have he := pathEnergy_nonneg n u
  have hm : (2 * ∑ i ∈ s, (u i ^ 2 + u (i + 1) ^ 2)) ≤ 4 * M := by
    rw [Finset.sum_add_distrib]
    linarith
  have hn : 0 ≤ ∑ i ∈ s, (u (i + 1) - u i) ^ 2 := by positivity
  have hb := mul_le_mul hg hm (by positivity) (by positivity : 0 ≤ 20 * pathEnergy n u)
  have hsq : (∑ i ∈ s, |u (i + 1) ^ 2 - u i ^ 2|) ^ 2 ≤ 80 * pathEnergy n u * M := by
    nlinarith
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hsq

lemma localized_product_variation (n : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0) (s : Finset ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h1 : (∑ i ∈ s, u (i + 1) ^ 2) ≤ M) :
    (∑ i ∈ s, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ≤
      Real.sqrt (80 * pathEnergy n u * M) := by
  have hs := product_weight_variation s u
  have hg0 := supported_energy_gradient n u hu s
  have hg1 := supported_shift_energy_gradient n 1 u hu s
  have he := pathEnergy_nonneg n u
  have hg : (2 * ∑ i ∈ s, ((u (i + 1) - u i) ^ 2 + (u (i + 2) - u (i + 1)) ^ 2)) ≤
      80 * pathEnergy n u := by
    rw [Finset.sum_add_distrib]
    simp only [Nat.add_assoc] at hg1
    linarith
  have hn : 0 ≤ ∑ i ∈ s, u (i + 1) ^ 2 := by positivity
  have hb := mul_le_mul hg h1 hn (by positivity : 0 ≤ 80 * pathEnergy n u)
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (hs.trans hb)

lemma sum_covered_by_shells (B R : Finset ℕ) (S : ℕ → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ b, 0 ≤ f b) (hcover : ∀ b ∈ B, ∃ r ∈ R, b ∈ S r) :
    (∑ b ∈ B, f b) ≤ ∑ r ∈ R, ∑ b ∈ B.filter (fun b => b ∈ S r), f b := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨r, hr, hbr⟩ := hcover b hb
  calc
    f b = if b ∈ S r then f b else 0 := by rw [ite_eq_left hbr]
    _ ≤ ∑ x ∈ R, if b ∈ S x then f b else 0 := by
      exact Finset.single_le_sum (f := fun x => if b ∈ S x then f b else 0)
        (fun x _ => by split_ifs <;> first | exact hf b | exact le_rfl) hr

lemma sum_range_eq_of_supported (f : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M)
    (hf : ∀ i, N ≤ i → f i = 0) :
    (∑ i ∈ Finset.range M, f i) = ∑ i ∈ Finset.range N, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono hNM)
  intro i _ hi
  exact hf i (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi))

lemma shell_indices_mass (n j r d l k : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d l B, u (i + k) ^ 2) ≤ 2 * (1 / 2 : ℝ) ^ r := by
  by_cases hr : r = 0
  · subst r
    have hm := supported_shift_mass n k u hu (blockIndices d l B)
    rw [hnorm] at hm
    simpa only [pow_zero, mul_one] using hm.trans (by norm_num : (1 : ℝ) ≤ 2)
  · have hr' : 0 < r := Nat.pos_of_ne_zero hr
    have hlo (i : ℕ) (hi : i ∈ blockIndices d l B) :
        (2 : ℝ) ^ r * σ ≤ (i + k + 1 : ℕ) / (n + 1 : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      have hi' := blockIndices_lower d l (2 ^ r * 8 ^ j * d) B
        (fun b hb => Nat.mul_le_mul_right d (blockShell_lower j r b hr' (hB b hb))) i hi
      have hc : (2 : ℝ)^r * 8^j * d ≤ (i : ℝ) + k + 1 := by
        exact_mod_cast hi'.trans (by omega : i ≤ i + k + 1)
      have hm := mul_le_mul_of_nonneg_left hsize (by positivity : (0 : ℝ) ≤ 2^r)
      push_cast
      nlinarith
    have ht := supported_shift_energy_tail n k u hu (blockIndices d l B)
      ((2 : ℝ)^r * σ) hlo
    have hm : (2 : ℝ)^r * (∑ i ∈ blockIndices d l B, u (i + k)^2) ≤ 2 := by
      apply (mul_le_mul_iff_right₀ hσ).mp
      nlinarith
    have hp : (2 : ℝ)^r * (1 / 2 : ℝ)^r = 1 := by
      rw [← mul_pow]
      norm_num
    nlinarith [show (0 : ℝ) < 2^r by positivity]

lemma half_pow_le_three_quarters_sq (r : ℕ) :
    (1 / 2 : ℝ)^r ≤ ((3 / 4 : ℝ)^r)^2 := by
  rw [← pow_mul, mul_comm r 2, pow_mul]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) r

lemma sqrt_shell_energy_bound {e : ℝ} (he : 0 ≤ e) (r : ℕ) :
    Real.sqrt (80 * e * (2 * (1 / 2 : ℝ)^r)) ≤
      13 * Real.sqrt e * (3 / 4 : ℝ)^r := by
  apply (Real.sqrt_le_iff).mpr ⟨by positivity, ?_⟩
  have hp := half_pow_le_three_quarters_sq r
  have hs := Real.sq_sqrt he
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 160 * e)
  nlinarith [sq_nonneg ((3 / 4 : ℝ)^r)]

lemma shell_square_mass_variation (n j r d : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d d B, |u i ^ 2|) ≤ 2 * (3 / 4 : ℝ)^r ∧
    (∑ i ∈ blockIndices d (d - 1) B, |u (i + 1)^2 - u i^2|) ≤
      13 * Real.sqrt (pathEnergy n u) * (3 / 4 : ℝ)^r := by
  have hm (l k : ℕ) := shell_indices_mass n j r d l k u hu hnorm B hB hσ he hsize
  constructor
  · simp only [abs_sq]
    have h0 := hm d 0
    simp only [Nat.add_zero] at h0
    exact h0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) _) (by norm_num))
  · apply (localized_square_variation n u hu _ (by positivity)
      (by simpa only [Nat.add_zero] using hm (d - 1) 0) (hm (d - 1) 1)).trans
    exact sqrt_shell_energy_bound (pathEnergy_nonneg n u) r

lemma shell_product_mass_variation (n j r d : ℕ) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ∈ blockShell j r)
    {σ : ℝ} (hσ : 0 < σ) (he : pathEnergy n u ≤ σ)
    (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d) :
    (∑ i ∈ blockIndices d d B, |u i * u (i + 1)|) ≤ 2 * (3 / 4 : ℝ)^r ∧
    (∑ i ∈ blockIndices d (d - 1) B, |u (i + 1) * u (i + 2) - u i * u (i + 1)|) ≤
      13 * Real.sqrt (pathEnergy n u) * (3 / 4 : ℝ)^r := by
  have hm (l k : ℕ) := shell_indices_mass n j r d l k u hu hnorm B hB hσ he hsize
  constructor
  · apply (localized_product_mass _ u
      (by simpa only [Nat.add_zero] using hm d 0) (hm d 1)).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) _) (by norm_num)
  · exact (localized_product_variation n u hu _ (by positivity) (hm (d - 1) 1)).trans
      (sqrt_shell_energy_bound (pathEnergy_nonneg n u) r)

lemma weighted_geometric_three_quarters (N : ℕ) :
    (∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r) ≤ 16 := by
  have hident : (∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r) =
      16 - (4 * N + 16) * (3 / 4 : ℝ)^N := by
    induction N with
    | zero => norm_num
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; push_cast; ring
  rw [hident]
  have : 0 ≤ (4 * N + 16) * (3 / 4 : ℝ)^N := by positivity
  linarith

lemma shifted_weighted_geometric {a : ℝ} (ha : 1 ≤ a) (N : ℕ) :
    (∑ r ∈ Finset.range N, (a + r) * (3 / 4 : ℝ)^r) ≤ 16 * a := by
  calc
    _ ≤ ∑ r ∈ Finset.range N, a * ((r + 1) * (3 / 4 : ℝ)^r) := by
      apply Finset.sum_le_sum
      intro r _
      have h : a + r ≤ a * (r + 1) := by nlinarith [show (0 : ℝ) ≤ r by positivity]
      nlinarith [mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ (3 / 4 : ℝ)^r)]
    _ = a * ∑ r ∈ Finset.range N, (r + 1 : ℝ) * (3 / 4 : ℝ)^r := by rw [Finset.mul_sum]
    _ ≤ 16 * a := by nlinarith [weighted_geometric_three_quarters N]

lemma weighted_multiscale_prefix (ξ w : ℕ → ℝ) (N j d : ℕ) (hd : 0 < d)
    (hw : ∀ i, N ≤ i → w i = 0) {h K e : ℝ} (hh : 0 ≤ h) (hK : 0 ≤ K) (_he : 0 ≤ e)
    (hpref : ∀ r < N, ∀ b < N, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1))
    (hmass : ∀ r < N, (∑ i ∈ blockIndices d d
      ((Finset.range N).filter (fun b => b ∈ blockShell j r)), |w i|) ≤ 2 * (3 / 4 : ℝ)^r)
    (hvar : ∀ r < N, (∑ i ∈ blockIndices d (d - 1)
      ((Finset.range N).filter (fun b => b ∈ blockShell j r)), |w (i + 1) - w i|) ≤
        13 * Real.sqrt e * (3 / 4 : ℝ)^r) :
    |∑ i ∈ Finset.range N, ξ i * w i| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt e) := by
  have hblock (r : ℕ) (hr : r < N) := many_block_prefix_abs_bound ξ w d
    ((Finset.range N).filter (fun b => b ∈ blockShell j r)) hd
    (by positivity : 0 ≤ K * (h + j + r + 1))
    (fun b hb k hk => hpref r hr b (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
      (Finset.mem_filter.mp hb).2 k hk)
  have hblock' (r : ℕ) (hr : r < N) :
      (∑ b ∈ (Finset.range N).filter (fun b => b ∈ blockShell j r),
        |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)|) ≤
      K * (2 / d + 26 * Real.sqrt e) * ((h + j + 1 + r) * (3 / 4 : ℝ)^r) := by
    calc
      _ ≤ K * (h + j + r + 1) / d * (2 * (3 / 4 : ℝ)^r) +
          2 * (K * (h + j + r + 1)) * (13 * Real.sqrt e * (3 / 4 : ℝ)^r) := by
        apply (hblock r hr).trans
        exact add_le_add (mul_le_mul_of_nonneg_left (hmass r hr) (by positivity))
          (mul_le_mul_of_nonneg_left (hvar r hr) (by positivity))
      _ = _ := by ring
  have hsum : (∑ i ∈ Finset.range N, ξ i * w i) =
      ∑ b ∈ Finset.range N, ∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i) := by
    rw [sum_consecutive_blocks N d (fun i => ξ i * w i)]
    symm
    exact sum_range_eq_of_supported (fun i => ξ i * w i) N (N * d)
      (by nlinarith) (fun i hi => by rw [hw i hi, mul_zero])
  rw [hsum]
  calc
    _ ≤ ∑ b ∈ Finset.range N, |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Finset.range N, ∑ b ∈ (Finset.range N).filter (fun b => b ∈ blockShell j r),
        |∑ i ∈ Finset.range d, ξ (b * d + i) * w (b * d + i)| := by
      apply sum_covered_by_shells _ _ (blockShell j) _ (fun _ => abs_nonneg _)
      intro b hb
      obtain ⟨r, hr, hbr⟩ := blockShell_covers j b
      exact ⟨r, Finset.mem_range.mpr (hr.trans_lt (Finset.mem_range.mp hb)), hbr⟩
    _ ≤ ∑ r ∈ Finset.range N,
        K * (2 / d + 26 * Real.sqrt e) * ((h + j + 1 + r) * (3 / 4 : ℝ)^r) := by
      exact Finset.sum_le_sum (fun r hr => hblock' r (Finset.mem_range.mp hr))
    _ = K * (2 / d + 26 * Real.sqrt e) *
        (∑ r ∈ Finset.range N, ((h + j + 1 + r) * (3 / 4 : ℝ)^r)) := by rw [Finset.mul_sum]
    _ ≤ K * (2 / d + 26 * Real.sqrt e) * (16 * (h + j + 1)) := by
      exact mul_le_mul_of_nonneg_left (shifted_weighted_geometric (by linarith [show (0 : ℝ) ≤ j by positivity]) N) (by positivity)
    _ = _ := by ring

lemma square_multiscale_prefix (ξ : ℕ → ℝ) (n j d : ℕ) (hd : 0 < d) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    {σ h K : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (he : pathEnergy n u ≤ σ) (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d)
    (hpref : ∀ r < n + 1, ∀ b < n + 1, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1)) :
    |∑ i ∈ Finset.range (n + 1), ξ i * u i^2| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt (pathEnergy n u)) := by
  have hmv (r : ℕ) := shell_square_mass_variation n j r d u hu hnorm
    ((Finset.range (n + 1)).filter (fun b => b ∈ blockShell j r))
    (fun _ hb => (Finset.mem_filter.mp hb).2) hσ he hsize
  exact weighted_multiscale_prefix ξ (fun i => u i^2) (n + 1) j d hd
    (fun i hi => by rw [hu i hi]; norm_num) hh hK (pathEnergy_nonneg n u) hpref
    (fun r _ => (hmv r).1) (fun r _ => (hmv r).2)

lemma product_multiscale_prefix (ξ : ℕ → ℝ) (n j d : ℕ) (hd : 0 < d) (u : ℕ → ℝ)
    (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1)
    {σ h K : ℝ} (hσ : 0 < σ) (hh : 0 ≤ h) (hK : 0 ≤ K)
    (he : pathEnergy n u ≤ σ) (hsize : (n + 1 : ℝ) * σ ≤ (8 : ℝ)^j * d)
    (hpref : ∀ r < n + 1, ∀ b < n + 1, b ∈ blockShell j r → ∀ k < d,
      |∑ i ∈ Finset.range (k + 1), ξ (b * d + i)| ≤ K * (h + j + r + 1)) :
    |∑ i ∈ Finset.range (n + 1), ξ i * (u i * u (i + 1))| ≤
      32 * K * (h + j + 1) * (1 / d + 13 * Real.sqrt (pathEnergy n u)) := by
  have hmv (r : ℕ) := shell_product_mass_variation n j r d u hu hnorm
    ((Finset.range (n + 1)).filter (fun b => b ∈ blockShell j r))
    (fun _ hb => (Finset.mem_filter.mp hb).2) hσ he hsize
  exact weighted_multiscale_prefix ξ (fun i => u i * u (i + 1)) (n + 1) j d hd
    (fun i hi => by rw [hu i hi, zero_mul]) hh hK (pathEnergy_nonneg n u) hpref
    (fun r _ => (hmv r).1) (fun r _ => by simpa only [Nat.add_assoc] using (hmv r).2)

lemma blockThreshold_linear_bound (c : ℝ≥0) (m j r : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    blockThreshold c m j r h ≤
      Real.sqrt (32 * (c : ℝ)) * Real.sqrt (m + 1) * (h + j + r + 1) := by
  have hlog : Real.log 16 ≤ 15 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16) using 1
    norm_num
  have hjr : (0 : ℝ) ≤ j + r := by positivity
  have hq : h^2 + (j + r : ℕ) * Real.log 16 ≤ 16 * (h + j + r + 1)^2 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlog hjr, mul_nonneg hh hjr,
      sq_nonneg h, sq_nonneg ((j : ℝ) + r)]
  unfold blockThreshold
  apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc
    _ ≤ 2 * (m + 1) * (c : ℝ) * (16 * (h + j + r + 1)^2) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      ring

lemma blockThreshold_length_bound (c : ℝ≥0) (d j r : ℕ) (hd : 0 < d) {h : ℝ} (hh : 0 ≤ h) :
    blockThreshold c (d - 1) j r h ≤
      Real.sqrt (32 * (c : ℝ)) * Real.sqrt d * (h + j + r + 1) := by
  have hd' : (d - 1 : ℝ) + 1 = d := by ring
  have hnat : 1 ≤ d := hd
  simpa only [Nat.cast_sub hnat, Nat.cast_one, hd'] using blockThreshold_linear_bound c (d - 1) j r hh

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GaussianMatrices
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace
open Module
namespace CriticalSK


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_apply (e v x : E) :
    alignIsometry e v x = x -
      (2 * (inner ℝ (v - ‖v‖ • e) x / ‖v - ‖v‖ • e‖ ^ 2)) • (v - ‖v‖ • e) := by
  rw [alignIsometry, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub, two_smul]
  rw [two_mul, add_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma alignIsometry_align (e v : E) (he : ‖e‖ = 1) :
    alignIsometry e v v = ‖v‖ • e := by
  apply Submodule.reflection_sub
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), he, mul_one]

lemma covariance_inner_stdGaussian (v w : E) :
    cov[fun x => inner ℝ v x, fun x => inner ℝ w x; stdGaussian E] = inner ℝ v w := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian]
  rfl

lemma inner_stdGaussian_law (v : E) :
    (stdGaussian E).map (fun x => inner ℝ v x) =
      gaussianReal 0 (‖v‖ ^ 2).toNNReal := by
  have hG : HasGaussianLaw (fun x : E => inner ℝ v x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ v)
  rw [hG.map_eq_gaussianReal]
  congr 1
  · exact integral_strongDual_stdGaussian (innerSL ℝ v)
  · rw [← covariance_self (by fun_prop), covariance_inner_stdGaussian, real_inner_self_eq_norm_sq]

lemma gaussian_orthogonal_independent {κ : Type*} [Fintype κ] (v : κ → E)
    (hv : Pairwise (fun i j => inner ℝ (v i) (v j) = 0)) :
    iIndepFun (fun i x => inner ℝ (v i) x) (stdGaussian E) := by
  have hG : HasGaussianLaw (fun x : E => fun i => inner ℝ (v i) x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi (fun i => innerSL ℝ (v i)))
  apply hG.iIndepFun_of_covariance_eq_zero
  intro i j hij
  rw [covariance_inner_stdGaussian]
  exact hv hij

variable {ι : Type*} [Fintype ι]

lemma conjugateGaussianMatrix_preserves (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U) =
      stdGaussian (GaussianMatrix ι) :=
  stdGaussian_map _

lemma euclidean_isometry_apply_eq_sum
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι) (i : ι) :
    U v i = ∑ j, v j * U (EuclideanSpace.basisFun ι ℝ j) i := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v, map_sum]
  simp

lemma conjugateGaussianMatrix_apply
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (i j : ι) :
    conjugateGaussianMatrix U A i j =
      ∑ k, ∑ l, U (EuclideanSpace.basisFun ι ℝ k) i * A k l *
        U (EuclideanSpace.basisFun ι ℝ l) j := by
  simp only [conjugateGaussianMatrix, LinearIsometryEquiv.trans_apply,
    transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [transposeGaussianMatrix_apply, rowIsometry_apply]
  rw [euclidean_isometry_apply_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma conjugateGaussianMatrix_transpose
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (transposeGaussianMatrix A) =
      transposeGaussianMatrix (conjugateGaussianMatrix U A) := by
  ext i j
  simp only [conjugateGaussianMatrix_apply, transposeGaussianMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma symmetrizeGaussianMatrix_continuous (s : ℝ) :
    Continuous (symmetrizeGaussianMatrix (ι := ι) s) := by
  unfold symmetrizeGaussianMatrix
  fun_prop

lemma conjugate_symmetrize (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (A : GaussianMatrix ι) :
    conjugateGaussianMatrix U (symmetrizeGaussianMatrix s A) =
      symmetrizeGaussianMatrix s (conjugateGaussianMatrix U A) := by
  simp only [symmetrizeGaussianMatrix, map_smul, map_add,
    conjugateGaussianMatrix_transpose]

lemma goeLaw_conjugate (s : ℝ)
    (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (goeLaw ι s).map (conjugateGaussianMatrix U) = goeLaw ι s := by
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, conjugate_symmetrize]
  calc
    _ = ((stdGaussian (GaussianMatrix ι)).map (conjugateGaussianMatrix U)).map
        (symmetrizeGaussianMatrix s) :=
      (Measure.map_map (symmetrizeGaussianMatrix_continuous s).measurable
        (conjugateGaussianMatrix U).continuous.measurable).symm
    _ = _ := by rw [conjugateGaussianMatrix_preserves]

lemma conjugateGaussianMatrix_measurable {Ω : Type*} [MeasurableSpace Ω]
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    Measurable (fun p : Ω × GaussianMatrix ι => conjugateGaussianMatrix (U p.1) p.2) := by
  have hc (k i : ι) : Measurable (fun ω => U ω (EuclideanSpace.basisFun ι ℝ k) i) :=
    (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι => x i)).comp
      (hU.comp (measurable_id.prodMk measurable_const))
  change Measurable (fun p : Ω × GaussianMatrix ι => WithLp.toLp 2
    (fun i => WithLp.toLp 2 (fun j => conjugateGaussianMatrix (U p.1) p.2 i j)))
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  simp only [conjugateGaussianMatrix_apply]
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact ((hc k i).comp measurable_fst |>.mul
    ((by fun_prop : Measurable (fun A : GaussianMatrix ι => A k l)).comp measurable_snd)).mul
      ((hc l j).comp measurable_fst)

lemma random_goe_conjugation_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (s : ℝ)
    (U : Ω → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : Ω × EuclideanSpace ℝ ι => U p.1 p.2)) :
    MeasurePreserving (fun p : Ω × GaussianMatrix ι =>
      (p.1, conjugateGaussianMatrix (U p.1) p.2))
      (μ.prod (goeLaw ι s)) (μ.prod (goeLaw ι s)) := by
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  exact (MeasurePreserving.id μ).skew_product
    (g := fun ω A => conjugateGaussianMatrix (U ω) A)
    (conjugateGaussianMatrix_measurable U hU)
    (Filter.Eventually.of_forall (fun ω => goeLaw_conjugate s (U ω)))

lemma goeEntryVector_inner (s : ℝ) (i j : ι) (A : GaussianMatrix ι) :
    inner ℝ (goeEntryVector s i j) A = symmetrizeGaussianMatrix s A i j := by
  simp [goeEntryVector, symmetrizeGaussianMatrix, inner_smul_left, inner_add_left]

lemma goe_entry_variance [DecidableEq ι] (s : ℝ) (i j : ι) :
    ‖goeEntryVector s i j‖ ^ 2 = if i = j then 4 * s ^ 2 else 2 * s ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  by_cases hij : i = j
  · subst j
    simp only [and_self, ite_true]
    ring
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, and_self, ite_true, ite_false]
    ring

lemma goe_entry_law [DecidableEq ι] (s : ℝ) (i j : ι) :
    (goeLaw ι s).map (fun A => A i j) =
      gaussianReal 0 (if i = j then (4 * s ^ 2).toNNReal else (2 * s ^ 2).toNNReal) := by
  classical
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  simp only [Function.comp_def, ← goeEntryVector_inner]
  rw [inner_stdGaussian_law, goe_entry_variance]
  split_ifs <;> rfl

variable [LinearOrder ι]

lemma goeEntryVector_orthogonal (s : ℝ) :
    Pairwise (fun p q : UpperEntry ι =>
      inner ℝ (goeEntryVector s p.1.1 p.1.2) (goeEntryVector s q.1.1 q.1.2) = 0) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩ hpq
  have h1 : ¬(i = k ∧ j = l) := by
    rintro ⟨rfl, rfl⟩
    exact hpq rfl
  have h2 : ¬(i = l ∧ j = k) := by
    intro hs
    have he : i = j := le_antisymm hij (by simpa only [hs.1, hs.2] using hkl)
    apply hpq
    apply Subtype.ext
    exact Prod.ext (he.trans hs.2) (he.symm.trans hs.1)
  simp only [goeEntryVector, real_inner_smul_left, real_inner_smul_right,
    inner_add_left, inner_add_right, matrixUnit_inner, matrixUnit_apply]
  simp only [h1, h2, ite_false, add_zero, mul_zero,
    show ¬(j = k ∧ i = l) from fun h => h2 ⟨h.2, h.1⟩,
    show ¬(j = l ∧ i = k) from fun h => h1 ⟨h.2, h.1⟩]

lemma goe_entries_independent (s : ℝ) :
    iIndepFun (fun p : UpperEntry ι => fun A : GaussianMatrix ι => A p.1.1 p.1.2)
      (goeLaw ι s) := by
  have h := gaussian_orthogonal_independent
    (fun p : UpperEntry ι => goeEntryVector s p.1.1 p.1.2) (goeEntryVector_orthogonal s)
  simp only [goeEntryVector_inner] at h
  let : IsProbabilityMeasure (goeLaw ι s) :=
    (Measure.isProbabilityMeasure_map_iff
      (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun _ => by fun_prop)).2
  unfold goeLaw
  rw [Measure.map_map (by fun_prop) (symmetrizeGaussianMatrix_continuous s).measurable]
  have hh := h.map_fun_eq_pi_map (fun _ => by fun_prop)
  simp only [Function.comp_def] at *
  rw [hh]
  congr 1
  ext p : 1
  exact (Measure.map_map (g := fun A : GaussianMatrix ι => A p.1.1 p.1.2) (by fun_prop)
    (symmetrizeGaussianMatrix_continuous s).measurable).symm

end

section

open scoped NNReal

section Upper

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

lemma upperRead_measurable : Measurable (upperRead (ι := ι)) := by
  apply Measurable.of_eval
  intro p
  fun_prop [upperRead]

lemma upperWrite_measurable : Measurable (upperWrite (ι := ι)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  dsimp [upperWrite]
  split_ifs <;> fun_prop

lemma upperWrite_upperRead (A : GaussianMatrix ι) (hA : ∀ i j, A i j = A j i) :
    upperWrite (upperRead A) = A := by
  ext i j
  dsimp [upperWrite, upperRead]
  split_ifs
  · rfl
  · exact hA j i

@[simp] lemma upperRead_upperWrite (a : UpperEntry ι → ℝ) :
    upperRead (upperWrite a) = a := by
  funext p
  exact dite_eq_left p.2

lemma goe_symmetric_ae (s : ℝ) : ∀ᵐ A ∂goeLaw ι s, ∀ i j, A i j = A j i := by
  rw [goeLaw]
  apply (ae_map_iff (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable (by measurability)).2
  filter_upwards [] with A i j
  simp only [symmetrizeGaussianMatrix, PiLp.smul_apply, PiLp.add_apply,
    transposeGaussianMatrix_apply, smul_eq_mul]
  ring

lemma goe_upper_law (s : ℝ) :
    (goeLaw ι s).map upperRead = Measure.pi (fun p : UpperEntry ι =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal)) := by
  unfold upperRead
  rw [(goe_entries_independent (ι := ι) s).map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext p
  exact goe_entry_law s p.1.1 p.1.2

lemma goeLaw_eq_upper_product (s : ℝ) :
    goeLaw ι s = (Measure.pi (fun p : UpperEntry ι =>
      gaussianReal 0 (if p.1.1 = p.1.2 then (4 * s^2).toNNReal else (2 * s^2).toNNReal))).map
        upperWrite := by
  rw [← goe_upper_law, Measure.map_map upperWrite_measurable upperRead_measurable]
  have heq : (upperWrite ∘ upperRead : GaussianMatrix ι → GaussianMatrix ι) =ᵐ[goeLaw ι s] id := by
    filter_upwards [goe_symmetric_ae (ι := ι) s] with A hA
    exact upperWrite_upperRead A hA
  rw [Measure.map_congr heq, Measure.map_id]

end Upper

lemma splitUpper_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (splitUpper n) (Measure.pi (goeUpperMarginal (ι := Fin (n + 1)) s))
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (Measure.pi (goeUpperMarginal (ι := Fin n) s)))) := by
  let μ := goeUpperMarginal (ι := Fin (n + 1)) s
  have h1 := (measurePreserving_piCongrLeft μ (upperSplit n)).symm
  have h2 := measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n i))
  have h3 := (measurePreserving_piUnique (fun u : Unit => μ (upperSplit n (Sum.inl u)))).prod
    (measurePreserving_sumPiEquivProdPi (fun i => μ (upperSplit n (Sum.inr i))))
  have h := h3.comp (h2.comp h1)
  convert h using 1
  · rfl
  · dsimp [μ, goeUpperMarginal]
    simp only [Fin.succ_inj, (Ne.symm (Fin.succ_ne_zero _)), ite_false]
    rfl

open scoped BigOperators

lemma extendTailIsometry_basis_succ {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    extendTailIsometry U (EuclideanSpace.basisFun (Fin (n + 1)) ℝ k.succ) =
      WithLp.toLp 2 (Fin.cases 0 (U (EuclideanSpace.basisFun (Fin n) ℝ k))) := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [extendTailIsometry_succ, Fin.cases_succ]
    apply congrArg (fun w : EuclideanSpace ℝ (Fin n) => U w i)
    ext j
    simp

lemma extendTailIsometry_border {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (a : ℝ) (v : EuclideanSpace ℝ (Fin n)) (B : GaussianMatrix (Fin n)) :
    conjugateGaussianMatrix (extendTailIsometry U) (borderMatrix a v B) =
      borderMatrix a (U v) (conjugateGaussianMatrix U B) := by
  classical
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [conjugateGaussianMatrix_apply, Fin.sum_univ_succ]
  all_goals simp only [extendTailIsometry_basis_zero, extendTailIsometry_basis_succ]
  all_goals simp only [Fin.cases_zero, Fin.cases_succ,
    EuclideanSpace.basisFun_apply]
  all_goals simp only [PiLp.single_apply, Fin.succ_ne_zero,
    ite_true, ite_false, borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ, zero_mul, mul_zero,
    one_mul, mul_one, Finset.sum_const_zero, add_zero, zero_add]
  · simpa only [EuclideanSpace.basisFun_apply] using (euclidean_isometry_apply_eq_sum U v _).symm
  · rw [euclidean_isometry_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [EuclideanSpace.basisFun_apply, mul_comm]
  · simpa only [EuclideanSpace.basisFun_apply] using (conjugateGaussianMatrix_apply U B _ _).symm

instance goeLaw_probability {ι : Type*} [Fintype ι] (s : ℝ) :
    IsProbabilityMeasure (goeLaw ι s) :=
  (Measure.isProbabilityMeasure_map_iff
    (symmetrizeGaussianMatrix_continuous s).measurable.aemeasurable).2 inferInstance

lemma matrixTail_measurable (n : ℕ) : Measurable (matrixTail (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  fun_prop [matrixTail]

lemma goeBlocks_measurable (n : ℕ) : Measurable (goeBlocks (n := n)) := by
  exact (by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
    ((Measurable.of_eval (fun _ => by fun_prop)).prodMk (matrixTail_measurable n))

lemma borderMatrix_blocks {n : ℕ} (A : GaussianMatrix (Fin (n + 1)))
    (hA : ∀ i j, A i j = A j i) :
    borderMatrix (goeBlocks A).1 (WithLp.toLp 2 (goeBlocks A).2.1) (goeBlocks A).2.2 = A := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · rfl
  · exact hA _ _
  · rfl

lemma goeBlocks_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (goeBlocks (n := n)) (goeLaw (Fin (n + 1)) s)
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (goeLaw (Fin n) s))) := by
  let μ := Measure.pi (goeUpperMarginal (ι := Fin (n+1)) s)
  have hw : MeasurePreserving (upperWrite (ι := Fin n))
      (Measure.pi (goeUpperMarginal s)) (goeLaw (Fin n) s) :=
    ⟨upperWrite_measurable, (goeLaw_eq_upper_product s).symm⟩
  have hr : MeasurePreserving (upperRead (ι := Fin (n+1))) (goeLaw (Fin (n+1)) s) μ :=
    ⟨upperRead_measurable, goe_upper_law s⟩
  have hp := (MeasurePreserving.id (gaussianReal 0 (4 * s^2).toNNReal)).prod
    ((MeasurePreserving.id (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal)).prod hw)
  have h := hp.comp ((splitUpper_preserving n s).comp hr)
  refine ⟨goeBlocks_measurable n, ?_⟩
  rw [← h.map_eq]
  apply Measure.map_congr
  filter_upwards [goe_symmetric_ae (ι := Fin (n+1)) s] with A hA
  dsimp only [Function.comp_apply, Prod.map_apply, id_eq, splitUpper, upperRead, goeBlocks]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change matrixTail A = upperWrite (upperRead (matrixTail A))
  exact (upperWrite_upperRead _ (fun i j => hA i.succ j.succ)).symm

lemma aligned_goeBlock_preserving (n : ℕ) (s : ℝ)
    (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun p : (Fin n → ℝ) × GaussianMatrix (Fin n) =>
      (p.1, conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 p.1)) p.2))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (goeLaw (Fin n) s))
      ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod (goeLaw (Fin n) s)) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × EuclideanSpace ℝ (Fin n) =>
      alignIsometry e (WithLp.toLp 2 p.1) p.2) := by
    simp_rw [alignIsometry_apply]
    fun_prop
  exact random_goe_conjugation_preserving
    (Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal) s
    (fun v : Fin n → ℝ => alignIsometry e (WithLp.toLp 2 v)) hm

lemma exposed_column_tail_law (n : ℕ) (s : ℝ) (e : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (fun A : GaussianMatrix (Fin (n+1)) =>
      (A 0 0, (fun i => A 0 i.succ,
        conjugateGaussianMatrix (alignIsometry e (WithLp.toLp 2 (fun i => A 0 i.succ)))
          (matrixTail A))))
      (goeLaw (Fin (n+1)) s)
      ((gaussianReal 0 (4 * s^2).toNNReal).prod
        ((Measure.pi fun _ : Fin n => gaussianReal 0 (2 * s^2).toNNReal).prod
          (goeLaw (Fin n) s))) :=
  ((MeasurePreserving.id _).prod (aligned_goeBlock_preserving n s e)).comp (goeBlocks_preserving n s)

end

section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

lemma matrixOfGaussian_injective : Function.Injective (matrixOfGaussian (ι := ι)) := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i) j

lemma orthoMatrix_trans (U V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    orthoMatrix (U.trans V) = orthoMatrix V * orthoMatrix U := by
  ext i j
  change V (U (EuclideanSpace.basisFun ι ℝ j)) i = _
  rw [euclidean_isometry_apply_eq_sum]
  simp only [Matrix.mul_apply, orthoMatrix]
  apply Finset.sum_congr rfl
  intros
  ring

lemma matrixOfGaussian_conjugate (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) :
    matrixOfGaussian (conjugateGaussianMatrix U A) =
      orthoMatrix U * matrixOfGaussian A * (orthoMatrix U).transpose := by
  ext i j
  simp only [matrixOfGaussian, conjugateGaussianMatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, orthoMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma conjugateGaussianMatrix_trans (U V : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) :
    conjugateGaussianMatrix (U.trans V) A =
      conjugateGaussianMatrix V (conjugateGaussianMatrix U A) := by
  apply matrixOfGaussian_injective
  simp only [matrixOfGaussian_conjugate, orthoMatrix_trans, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma conjugate_symmetric (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (A : GaussianMatrix ι) (hA : ∀ i j, A i j = A j i) :
    ∀ i j, conjugateGaussianMatrix U A i j = conjugateGaussianMatrix U A j i := by
  have hT : transposeGaussianMatrix A = A := by ext i j; exact hA j i
  have h := conjugateGaussianMatrix_transpose U A
  rw [hT] at h
  intro i j
  exact congrArg (fun B : GaussianMatrix ι => B i j) h

end

open scoped BigOperators

lemma firstAxis_succ (n : ℕ) : firstAxis (n+1) = EuclideanSpace.basisFun (Fin (n+1)) ℝ 0 := by
  ext i
  cases i using Fin.cases <;> simp [firstAxis, EuclideanSpace.basisFun_apply]

lemma firstAxis_norm_succ (n : ℕ) : ‖firstAxis (n+1)‖ = 1 := by
  rw [firstAxis_succ]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.norm_eq_one 0

lemma align_firstAxis (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    alignIsometry (firstAxis n) v v = ‖v‖ • firstAxis n := by
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n => exact alignIsometry_align _ _ (firstAxis_norm_succ n)

lemma extendTailIsometry_firstAxis {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    extendTailIsometry U (firstAxis (n+1)) = firstAxis (n+1) := by
  rw [firstAxis_succ]
  exact extendTailIsometry_basis_zero U

lemma reducedTail_symmetric {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) : ∀ i j, reducedTail A i j = reducedTail A j i :=
  conjugate_symmetric _ _ (fun i j => hA i.succ j.succ)

@[fun_prop] lemma firstColumn_measurable (n : ℕ) : Measurable (firstColumn (n := n)) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  fun_prop [firstColumn]

lemma reducedTail_measurable (n : ℕ) : Measurable (reducedTail (n := n)) := by
  have hm := (exposed_column_tail_law n 1 (firstAxis n)).measurable
  have ht : Measurable (fun p : ℝ × ((Fin n → ℝ) × GaussianMatrix (Fin n)) => p.2.2) :=
    measurable_snd.comp measurable_snd
  exact ht.comp hm

lemma first_step_conjugate {n : ℕ} (A : GaussianMatrix (Fin (n+1)))
    (hA : ∀ i j, A i j = A j i) :
    conjugateGaussianMatrix (extendTailIsometry (alignIsometry (firstAxis n) (firstColumn A))) A =
      borderMatrix (A 0 0) (‖firstColumn A‖ • firstAxis n) (reducedTail A) := by
  conv_lhs => arg 2; rw [← borderMatrix_blocks A hA]
  rw [extendTailIsometry_border]
  dsimp only [goeBlocks]
  change borderMatrix (A 0 0) (alignIsometry (firstAxis n) (firstColumn A) (firstColumn A))
    (reducedTail A) = _
  rw [align_firstAxis]

lemma triIsometry_firstAxis (n : ℕ) (A : GaussianMatrix (Fin n)) :
    triIsometry n A (firstAxis n) = firstAxis n := by
  cases n with
  | zero => rfl
  | succ n => simp only [triIsometry, LinearIsometryEquiv.trans_apply, extendTailIsometry_firstAxis]

lemma triReduce_conjugate (n : ℕ) (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    triReduce n A = conjugateGaussianMatrix (triIsometry n A) A := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [triIsometry, conjugateGaussianMatrix_trans, first_step_conjugate A hA,
      extendTailIsometry_border]
    simp only [map_smul, triIsometry_firstAxis]
    rw [← ih _ (reducedTail_symmetric A hA)]
    rfl

lemma borderMatrix_measurable (n : ℕ) :
    Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
      borderMatrix p.1 p.2.1 p.2.2) := by
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro i
  apply (WithLp.measurable_toLp _ _).comp
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : ℝ × (EuclideanSpace ℝ (Fin n) × GaussianMatrix (Fin n)) =>
    borderMatrix p.1 p.2.1 p.2.2 i j)
  cases i using Fin.cases <;> cases j using Fin.cases
  all_goals simp only [borderMatrix_zero_zero, borderMatrix_zero_succ,
    borderMatrix_succ_zero, borderMatrix_succ_succ]
  all_goals fun_prop

lemma triReduce_measurable (n : ℕ) : Measurable (triReduce n) := by
  induction n with
  | zero => exact measurable_id
  | succ n ih =>
    exact (borderMatrix_measurable n).comp
      ((by fun_prop : Measurable fun A : GaussianMatrix (Fin (n+1)) => A 0 0).prodMk
        (((firstColumn_measurable n).norm.smul measurable_const).prodMk
          (ih.comp (reducedTail_measurable n))))

lemma assembleTri_measurable (n : ℕ) : Measurable (assembleTri n) :=
  (borderMatrix_measurable n).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd |>.smul measurable_const).prodMk
      (measurable_snd.comp measurable_snd)))

lemma columnNorm_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun v : Fin n → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖)
      (Measure.pi fun _ : Fin n => gaussianReal 0 (2*s^2).toNNReal) (columnNormLaw n s) :=
  ⟨(WithLp.measurable_toLp _ _).norm, rfl⟩

instance columnNormLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (columnNormLaw n s) :=
  (Measure.isProbabilityMeasure_map_iff
    (columnNorm_preserving n s).measurable.aemeasurable).2 inferInstance

instance triMatrixLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triMatrixLaw n s) := by
  induction n with
  | zero => exact goeLaw_probability s
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (assembleTri_measurable n).aemeasurable).2 inferInstance

lemma triReduce_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (triReduce n) (goeLaw (Fin n) s) (triMatrixLaw n s) := by
  induction n with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hp := (MeasurePreserving.id (gaussianReal 0 (4*s^2).toNNReal)).prod
      ((columnNorm_preserving n s).prod ih)
    have ha : MeasurePreserving (assembleTri n)
        ((gaussianReal 0 (4*s^2).toNNReal).prod ((columnNormLaw n s).prod (triMatrixLaw n s)))
        (triMatrixLaw (n+1) s) := ⟨assembleTri_measurable n, rfl⟩
    exact ha.comp (hp.comp (exposed_column_tail_law n s (firstAxis n)))

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.MinMax
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

namespace CriticalSK

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_finrank {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (s : Finset (Fin n)) :
    finrank ℝ (basisSpan b s) = s.card := by
  have hli : LinearIndependent ℝ (fun i : s => b i) :=
    b.orthonormal.linearIndependent.comp (fun i : s => (i : Fin n)) Subtype.val_injective
  rw [basisSpan, finrank_span_eq_card hli, Fintype.card_coe]

omit [FiniteDimensional ℝ E] in
lemma basisSpan_repr_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s)
    (i : Fin n) (hi : i ∉ s) : b.repr x i = 0 := by
  have hmem : x ∈ Submodule.span ℝ (b.toBasis '' (s : Set (Fin n))) := by
    convert hx using 1
    congr 1
    ext y
    simp [Set.mem_range, Set.mem_image]
  have hs := b.toBasis.repr_support_subset_of_mem_span _ hmem
  have hz : b.toBasis.repr x i = 0 := by
    by_contra hz
    exact hi (hs (Finsupp.mem_support_iff.mpr hz))
  simpa only [b.coe_toBasis_repr_apply] using hz

lemma basisSpan_intersection_unit {n : ℕ}
    (b c : OrthonormalBasis (Fin n) ℝ E) (s t : Finset (Fin n))
    (hcard : n < s.card + t.card) :
    ∃ x : E, ‖x‖ = 1 ∧ x ∈ basisSpan b s ∧ x ∈ basisSpan c t := by
  have hn : finrank ℝ E = n := by
    rw [finrank_eq_card_basis b.toBasis, Fintype.card_fin]
  have hnot : ¬ Disjoint (basisSpan b s) (basisSpan c t) := by
    intro hd
    have h := Submodule.finrank_add_finrank_le_of_disjoint hd
    rw [basisSpan_finrank, basisSpan_finrank, hn] at h
    omega
  rw [Submodule.disjoint_def] at hnot
  push Not at hnot
  obtain ⟨x, hxs, hxt, hx⟩ := hnot
  refine ⟨‖x‖⁻¹ • x, ?_, (basisSpan b s).smul_mem _ hxs, (basisSpan c t).smul_mem _ hxt⟩
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

omit [FiniteDimensional ℝ E] in
lemma basis_sum_squares {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (x : E) :
    ∑ i, (b.repr x i) ^ 2 = ‖x‖ ^ 2 := by
  simp only [b.repr_apply_apply]
  exact b.sum_sq_inner_right x

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_le {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, a i ≤ r) : basisQuadratic b a x ≤ r := by
  calc
    _ ≤ ∑ i, r * (b.repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]
    _ = r := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring

omit [FiniteDimensional ℝ E] in
lemma basisQuadratic_ge {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (s : Finset (Fin n)) {x : E} (hx : x ∈ basisSpan b s) (hunit : ‖x‖ = 1)
    {r : ℝ} (hr : ∀ i ∈ s, r ≤ a i) : r ≤ basisQuadratic b a x := by
  calc
    _ = ∑ i, r * (b.repr x i) ^ 2 := by rw [← Finset.mul_sum, basis_sum_squares, hunit]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ s
      · exact mul_le_mul_of_nonneg_right (hr i hi) (sq_nonneg _)
      · simp [basisSpan_repr_zero b s hx i hi]

lemma basis_minmax_upper {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → basisQuadratic a α x ≤ f (basisQuadratic b β x))
    (i : Fin n) : α i ≤ f (β i) := by
  have hcard : n < (Finset.Iic i).card + (Finset.Ici i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Iic i) (Finset.Ici i) hcard
  have hlow : α i ≤ basisQuadratic a α x :=
    basisQuadratic_ge a α (Finset.Iic i) hxa hx
      (fun j hj => hα (Finset.mem_Iic.mp hj))
  have hupp : basisQuadratic b β x ≤ β i :=
    basisQuadratic_le b β (Finset.Ici i) hxb hx
      (fun j hj => hβ (Finset.mem_Ici.mp hj))
  exact hlow.trans ((hform x hx).trans (hf (hqS x hx) (hβS i) hupp))

lemma basis_minmax_lower {n : ℕ} (a b : OrthonormalBasis (Fin n) ℝ E)
    (α β : Fin n → ℝ) (hα : Antitone α) (hβ : Antitone β)
    {S : Set ℝ} {f : ℝ → ℝ} (hf : MonotoneOn f S)
    (hβS : ∀ i, β i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → basisQuadratic b β x ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 → f (basisQuadratic b β x) ≤ basisQuadratic a α x)
    (i : Fin n) : f (β i) ≤ α i := by
  have hcard : n < (Finset.Ici i).card + (Finset.Iic i).card := by
    simp only [Fin.card_Iic, Fin.card_Ici]
    omega
  obtain ⟨x, hx, hxa, hxb⟩ := basisSpan_intersection_unit a b
    (Finset.Ici i) (Finset.Iic i) hcard
  have hupp : basisQuadratic a α x ≤ α i :=
    basisQuadratic_le a α (Finset.Ici i) hxa hx
      (fun j hj => hα (Finset.mem_Ici.mp hj))
  have hlow : β i ≤ basisQuadratic b β x :=
    basisQuadratic_ge b β (Finset.Iic i) hxb hx
      (fun j hj => hβ (Finset.mem_Iic.mp hj))
  exact (hf (hβS i) (hqS x hx) hlow).trans ((hform x hx).trans hupp)

lemma eigenbasisQuadratic_eq {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (x : E) :
    basisQuadratic (hT.eigenvectorBasis hn) (hT.eigenvalues hn) x = inner ℝ x (T x) := by
  rw [basisQuadratic, ← (hT.eigenvectorBasis hn).sum_inner_mul_inner x (T x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) x, ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply, hT.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

lemma eigenvalue_form_comparison {A B : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) {S : Set ℝ} {Φ : ℝ → ℝ}
    (hplus : MonotoneOn (fun e => e + Φ e) S)
    (hminus : MonotoneOn (fun e => e - Φ e) S)
    (hBS : ∀ i, hB.eigenvalues hn i ∈ S)
    (hqS : ∀ x : E, ‖x‖ = 1 → inner ℝ x (B x) ∈ S)
    (hform : ∀ x : E, ‖x‖ = 1 →
      |inner ℝ x (A x) - inner ℝ x (B x)| ≤ Φ (inner ℝ x (B x)))
    (i : Fin n) : |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ Φ (hB.eigenvalues hn i) := by
  have hu := basis_minmax_upper (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hplus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).2
      linarith) i
  have hl := basis_minmax_lower (hA.eigenvectorBasis hn) (hB.eigenvectorBasis hn)
    (hA.eigenvalues hn) (hB.eigenvalues hn) (hA.eigenvalues_antitone hn)
    (hB.eigenvalues_antitone hn) hminus hBS
    (fun x hx => by simpa only [eigenbasisQuadratic_eq] using hqS x hx)
    (fun x hx => by
      simp only [eigenbasisQuadratic_eq]
      have h := (abs_le.mp (hform x hx)).1
      linarith) i
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.PathSpectra
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

open Matrix Polynomial Filter

lemma jacobi_edgeCoeff (n : ℕ) (i j : Fin (n+1)) :
    jacobi (n+1 : ℝ)⁻¹ (n+1) i j =
      (if i.val+1=j.val then edgeCoeff n i.val else 0) +
      (if j.val+1=i.val then edgeCoeff n j.val else 0) := by
  have hs (k : Fin (n+1)) :
      Real.sqrt ((n+1 : ℝ)⁻¹ * ((n+1 : ℝ)-1-k.val)) = edgeCoeff n k.val := by
    unfold edgeCoeff
    congr 1
    field_simp
    ring
  simp only [jacobi, Nat.cast_add, Nat.cast_one, hs]
  split_ifs with h h' h' <;> try rfl
  · omega
  · simp
  · simp
  · simp

lemma directed_neighbor_sum (n : ℕ) (u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u i.val * u j.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n+1),
      (if (Fin.last n).val+1=j.val then edgeCoeff n (Fin.last n).val else 0) *
        u (Fin.last n).val * u j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega), zero_mul, zero_mul]
  rw [hl, add_zero, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h.symm))), zero_mul, zero_mul]
  · simp

lemma pathOperator_inner (n : ℕ) (u : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))
      (pathOperator n (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))) =
      2 * ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
  simp only [pathOperator, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply, star_trivial, dotProduct, Matrix.mulVec,
    jacobi_edgeCoeff, add_mul, Finset.sum_add_distrib]
  have hlo : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if i.val+1=j.val then edgeCoeff n i.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    convert directed_neighbor_sum n u using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intros
    ring
  have hhi : (∑ i : Fin (n+1), (∑ j : Fin (n+1),
      (if j.val+1=i.val then edgeCoeff n j.val else 0) * u j.val) * u i.val) =
      ∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i+1) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact directed_neighbor_sum n u
  rw [hlo, hhi]
  ring

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

lemma rpow_three_eighth_sub_le {s x y : ℝ} (hs : 0 < s) (hsx : s ≤ x) (hxy : x ≤ y) :
    y ^ (3 / 8 : ℝ) - x ^ (3 / 8 : ℝ) ≤
      (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) * (y - x) := by
  have hx : 0 < x := hs.trans_le hsx
  have hd (z : ℝ) (hz : z ∈ Set.Icc x y) :
      HasDerivWithinAt (fun z : ℝ => z ^ (3 / 8 : ℝ))
        ((3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ)) (Set.Icc x y) z := by
    have h := (Real.hasDerivAt_rpow_const (p := (3 / 8 : ℝ))
      (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Set.Icc x y)
    norm_num at h ⊢
    exact h
  have hb (z : ℝ) (hz : z ∈ Set.Ico x y) :
      ‖(3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ)‖ ≤ (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) := by
    have hz0 : 0 ≤ z := (hx.trans_le hz.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (3 / 8 : ℝ) * z ^ (-5 / 8 : ℝ))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hs (hsx.trans hz.1) (by norm_num)) (by norm_num)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb y ⟨hxy, le_rfl⟩
  exact (le_abs_self _).trans h

lemma edgeError_mono {A B C s : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s) :
    MonotoneOn (edgeError A B C s) (Set.Ici 0) := by
  intro x hx y _hy hxy
  change 0 ≤ x at hx
  dsimp [edgeError]
  gcongr

lemma edgeError_increment {A B C s x y : ℝ} (hA : 0 ≤ A) (hs : 0 < s)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    edgeError A B C s y - edgeError A B C s x ≤
      (A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C) * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (rpow_three_eighth_sub_le hs
    (show s ≤ x + s by linarith) (show x + s ≤ y + s by linarith)) hA
  dsimp [edgeError]
  nlinarith

lemma edgeError_gap_comparison_mono {A B C s : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s)
    (hsmall : A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C ≤ 1) :
    MonotoneOn (fun e => e + edgeError A B C s e) (Set.Ici 0) ∧
    MonotoneOn (fun e => e - edgeError A B C s e) (Set.Ici 0) := by
  constructor
  · intro x hx y hy hxy
    have := edgeError_mono (B := B) hA hC hs hx hy hxy
    linarith
  · intro x hx y _hy hxy
    have h := edgeError_increment (B := B) (C := C) hA hs hx hxy
    have h' := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hxy)
    linarith

lemma edgeError_eigenvalue_comparison_mono {A B C s : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hs : 0 < s)
    (hsmall : A * (3 / 8 : ℝ) * s ^ (-5 / 8 : ℝ) + C ≤ 1) :
    MonotoneOn (fun v => v + edgeError A B C s (2 - v)) (Set.Iic 2) ∧
    MonotoneOn (fun v => v - edgeError A B C s (2 - v)) (Set.Iic 2) := by
  obtain ⟨hp, hm⟩ := edgeError_gap_comparison_mono (B := B) hA hC hs hsmall
  constructor
  · intro x hx y hy hxy
    have h := hm (show 0 ≤ 2 - y by exact sub_nonneg.mpr hy)
      (show 0 ≤ 2 - x by exact sub_nonneg.mpr hx) (by linarith : 2 - y ≤ 2 - x)
    linarith
  · intro x hx y hy hxy
    have h := hp (show 0 ≤ 2 - y by exact sub_nonneg.mpr hy)
      (show 0 ≤ 2 - x by exact sub_nonneg.mpr hx) (by linarith : 2 - y ≤ 2 - x)
    linarith

open Set MeasureTheory Filter

open Set Filter MeasureTheory

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.TriNoise
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

lemma scaleLength_pos (J j : ℕ) : 0 < scaleLength J j := by
  unfold scaleLength
  positivity

lemma scaleRoot_pos (J j : ℕ) : 0 < scaleRoot J j := by
  unfold scaleRoot
  positivity

lemma scaleEnergy_pos (J j : ℕ) : 0 < scaleEnergy J j := sq_pos_of_pos (scaleRoot_pos J j)

lemma scale_length_root_eq_one {J j : ℕ} (hj : j ≤ J) :
    (scaleLength J j : ℝ) * scaleRoot J j = 1 := by
  unfold scaleLength scaleRoot
  push_cast
  rw [← mul_div_assoc, ← pow_add, Nat.sub_add_cancel hj, div_self (by positivity)]

lemma scale_last (J : ℕ) : scaleRoot J (J + 1) = 2 := by
  unfold scaleRoot
  rw [pow_succ]
  field_simp

lemma scale_length_root {J j : ℕ} (hj : j ≤ J + 1) :
    1 ≤ (scaleLength J j : ℝ) * scaleRoot J j ∧
    (scaleLength J j : ℝ) * scaleRoot J j ≤ 2 := by
  by_cases h : j ≤ J
  · rw [scale_length_root_eq_one h]
    norm_num
  · have : j = J + 1 := by omega
    subst j
    simp [scaleLength, scale_last]

lemma scaleEnergy_step (J j : ℕ) : scaleEnergy J (j + 1) = 4 * scaleEnergy J j := by
  unfold scaleEnergy scaleRoot
  rw [pow_succ]
  ring

lemma energy_first_scale (J : ℕ) {e : ℝ} (hen : 0 ≤ e) (he : e ≤ 4) :
    ∃ j ≤ J + 1, e ≤ scaleEnergy J j ∧
      scaleEnergy J j ≤ 4 * (e + scaleEnergy J 0) := by
  by_cases he0 : e ≤ scaleEnergy J 0
  · exact ⟨0, by omega, he0, by nlinarith [scaleEnergy_pos J 0]⟩
  · have hex : ∃ j, e ≤ scaleEnergy J j := ⟨J + 1, by norm_num [scaleEnergy, scale_last]; exact he⟩
    let j := Nat.find hex
    have hj : j ≤ J + 1 := Nat.find_min' hex (by norm_num [scaleEnergy, scale_last]; exact he)
    have hj0 : 0 < j := by
      by_contra! h
      have : j = 0 := Nat.eq_zero_of_le_zero h
      exact he0 (this ▸ Nat.find_spec hex)
    have hprev : scaleEnergy J (j - 1) < e := lt_of_not_ge (Nat.find_min hex (by omega))
    refine ⟨j, hj, Nat.find_spec hex, ?_⟩
    have heq : j - 1 + 1 = j := by omega
    rw [← heq, scaleEnergy_step]
    nlinarith [scaleEnergy_pos J 0]

lemma scale_shell_geometry {N J j : ℕ} (hN : (N : ℝ) ≤ ((2 : ℝ)^J) ^ 3)
    (hj : j ≤ J + 1) :
    (N : ℝ) * scaleEnergy J j ≤ (8 : ℝ)^j * scaleLength J j := by
  have hscale := (scale_length_root hj).1
  have hp : (8 : ℝ)^j = ((2 : ℝ)^j)^3 := by
    rw [← pow_mul, mul_comm j 3, pow_mul]
    norm_num
  have hm : 0 < (2 : ℝ)^J := by positivity
  have ht : 0 < (2 : ℝ)^j := by positivity
  unfold scaleRoot at hscale
  rw [← mul_div_assoc, le_div_iff₀ hm] at hscale
  unfold scaleEnergy scaleRoot
  rw [div_pow, ← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hm), hp]
  have hmul := mul_le_mul_of_nonneg_right hN (sq_nonneg ((2 : ℝ)^j))
  have hmul2 := mul_le_mul_of_nonneg_right hscale
    (by positivity : 0 ≤ ((2 : ℝ)^j)^2 * ((2 : ℝ)^J)^2)
  nlinarith

lemma dyadic_cube_scale (N : ℕ) (hN : 0 < N) :
    (N : ℝ) ≤ ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ∧
    ((2 : ℝ)^(Nat.clog 8 N)) ^ 3 ≤ 8 * N := by
  have he : ((2 : ℝ)^Nat.clog 8 N) ^ 3 = (8 : ℝ)^Nat.clog 8 N := by
    rw [← pow_mul, mul_comm (Nat.clog 8 N) 3, pow_mul]
    norm_num
  rw [he]
  constructor
  · exact_mod_cast Nat.le_pow_clog (by decide : 1 < 8) N
  · by_cases hn : N = 1
    · subst N
      norm_num [Nat.clog_one_right]
    · have hn' : 1 < N := by omega
      have hi := Nat.pow_pred_clog_lt_self (by decide : 1 < 8) hn'
      have hj := Nat.clog_pos (by decide : 1 < 8) hn'
      have hid : Nat.clog 8 N = (Nat.clog 8 N).pred + 1 := by
        simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj).symm
      rw [hid, pow_succ]
      have hi' : (8 : ℝ)^(Nat.clog 8 N).pred < N := by exact_mod_cast hi
      linarith

lemma natural_le_exponential_quarter (j : ℕ) :
    (j + 1 : ℝ) ≤ 8 * ((2 : ℝ)^j) ^ (1 / 4 : ℝ) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow]
  have he := Real.add_one_le_exp ((j : ℝ) * Real.log 2 * (1 / 4 : ℝ))
  have hj : (0 : ℝ) ≤ j := by positivity
  nlinarith

lemma block_scale_factor {d t e : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hdt : 1 ≤ d * t) (hdt2 : d * t ≤ 2) (he : 0 ≤ e) (het : e ≤ t^2) :
    Real.sqrt d * (1 / d + 13 * Real.sqrt e) ≤ 27 * Real.sqrt t := by
  have hsd := Real.sq_sqrt hd.le
  have hst := Real.sq_sqrt ht.le
  have hse := Real.sq_sqrt he
  have hsd0 := Real.sqrt_pos.mpr hd
  have hst0 := Real.sqrt_pos.mpr ht
  have hsmall : Real.sqrt d / d ≤ Real.sqrt t := by
    apply (div_le_iff₀ hd).mpr
    have hmul := mul_le_mul_of_nonneg_right hdt hd.le
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [hsd, mul_pow, hst]
    nlinarith
  have hlarge : Real.sqrt d * Real.sqrt e ≤ 2 * Real.sqrt t := by
    have hm := mul_le_mul_of_nonneg_left het hd.le
    have hm2 := mul_le_mul_of_nonneg_right hdt2 ht.le
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, hsd, hse, hst]
    nlinarith
  calc
    _ = Real.sqrt d / d + 13 * (Real.sqrt d * Real.sqrt e) := by ring
    _ ≤ Real.sqrt t + 13 * (2 * Real.sqrt t) := by linarith
    _ = _ := by ring

lemma scale_block_factor {J j : ℕ} (hj : j ≤ J + 1) {e : ℝ}
    (he : 0 ≤ e) (het : e ≤ scaleEnergy J j) :
    Real.sqrt (scaleLength J j) * (1 / scaleLength J j + 13 * Real.sqrt e) ≤
      27 * Real.sqrt (scaleRoot J j) :=
  block_scale_factor (by exact_mod_cast scaleLength_pos J j) (scaleRoot_pos J j)
    (scale_length_root hj).1 (scale_length_root hj).2 he het

lemma scale_weight_absorption (J j : ℕ) {e s h : ℝ} (hh : 0 ≤ h) (hes : 0 ≤ e + s)
    (hscale : scaleEnergy J j ≤ 4 * (e + s)) :
    (h + j + 1) * Real.sqrt (scaleRoot J j) ≤
      16 * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ) := by
  have hj : (0 : ℝ) ≤ j := by positivity
  have ht := scaleRoot_pos J j
  have hm : (0 : ℝ) < (2 : ℝ)^J := by positivity
  have hlin : h + j + 1 ≤ (h + 1) * (j + 1) := by nlinarith
  have hcoef := natural_le_exponential_quarter j
  have hfactor : ((2 : ℝ)^j) ^ (1 / 4 : ℝ) * Real.sqrt (scaleRoot J j) =
      ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (scaleEnergy J j) ^ (3 / 8 : ℝ) := by
    have htdef : (2 : ℝ)^j = (2 : ℝ)^J * scaleRoot J j := by
      unfold scaleRoot
      field_simp
    rw [htdef, Real.mul_rpow hm.le ht.le, Real.sqrt_eq_rpow]
    unfold scaleEnergy
    rw [← Real.rpow_natCast (scaleRoot J j) 2, ← Real.rpow_mul ht.le,
      mul_assoc, ← Real.rpow_add ht]
    norm_num
  have hfour : (4 : ℝ) ^ (3 / 8 : ℝ) ≤ 2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (by norm_num : (3 / 8 : ℝ) ≤ 1 / 2)
    simpa only [← Real.sqrt_eq_rpow, show Real.sqrt 4 = 2 by norm_num] using hp
  have henergy : (scaleEnergy J j) ^ (3 / 8 : ℝ) ≤ 2 * (e + s) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ (4 * (e + s)) ^ (3 / 8 : ℝ) := Real.rpow_le_rpow (scaleEnergy_pos J j).le hscale (by norm_num)
      _ = (4 : ℝ) ^ (3 / 8 : ℝ) * (e + s) ^ (3 / 8 : ℝ) := Real.mul_rpow (by norm_num) hes
      _ ≤ _ := mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hes _)
  calc
    _ ≤ ((h + 1) * (j + 1)) * Real.sqrt (scaleRoot J j) :=
      mul_le_mul_of_nonneg_right hlin (Real.sqrt_nonneg _)
    _ ≤ ((h + 1) * (8 * ((2 : ℝ)^j) ^ (1 / 4 : ℝ))) * Real.sqrt (scaleRoot J j) := by
      gcongr
    _ = 8 * (h + 1) * (((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (scaleEnergy J j) ^ (3 / 8 : ℝ)) := by
      rw [← hfactor]
      ring
    _ ≤ 8 * (h + 1) * (((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (2 * (e + s) ^ (3 / 8 : ℝ))) := by
      gcongr
    _ = _ := by ring

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma good_scale_prefix {X : ℕ → Ω → ℝ} {c : ℝ≥0} {J N : ℕ} {h : ℝ} {ω : Ω}
    (hh : 0 ≤ h)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength J j - 1) (J + 2) N h)
    {j r b k : ℕ} (hj : j ≤ J + 1) (hr : r < N) (hb : b ∈ blockShell j r)
    (hk : k < scaleLength J j) :
    |∑ i ∈ Finset.range (k + 1), X (b * scaleLength J j + i) ω| ≤
      (Real.sqrt (32 * (c : ℝ)) * Real.sqrt (scaleLength J j)) * (h + j + r + 1) := by
  have hd := scaleLength_pos J j
  have he : scaleLength J j - 1 + 1 = scaleLength J j := by omega
  have hp := good_multiscale_prefix_all hω (j := j) (r := r) (b := b)
    (by omega) (by omega) hb (k := k) (by omega)
  simpa only [he] using hp.trans (blockThreshold_length_bound c (scaleLength J j) j r hd hh)

lemma selected_scale_form_bound {J j : ℕ} {e s h c a : ℝ}
    (hj : j ≤ J + 1) (he : 0 ≤ e) (hs : 0 ≤ s) (hh : 0 ≤ h) (_hc : 0 ≤ c)
    (heσ : e ≤ scaleEnergy J j) (hσ : scaleEnergy J j ≤ 4 * (e + s))
    (ha : a ≤ 32 * (Real.sqrt (32 * c) * Real.sqrt (scaleLength J j)) *
      (h + j + 1) * (1 / scaleLength J j + 13 * Real.sqrt e)) :
    a ≤ 13824 * Real.sqrt (32 * c) * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) *
      (e + s) ^ (3 / 8 : ℝ) := by
  calc
    a ≤ 32 * Real.sqrt (32 * c) * (h + j + 1) *
        (Real.sqrt (scaleLength J j) * (1 / scaleLength J j + 13 * Real.sqrt e)) := by
      convert ha using 1
      ring
    _ ≤ 32 * Real.sqrt (32 * c) * (h + j + 1) * (27 * Real.sqrt (scaleRoot J j)) :=
      mul_le_mul_of_nonneg_left (scale_block_factor hj he heσ) (by positivity)
    _ = 864 * Real.sqrt (32 * c) * ((h + j + 1) * Real.sqrt (scaleRoot J j)) := by ring
    _ ≤ 864 * Real.sqrt (32 * c) *
        (16 * (h + 1) * ((2 : ℝ)^J) ^ (1 / 4 : ℝ) * (e + s) ^ (3 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left (scale_weight_absorption J j hh (add_nonneg he hs) hσ) (by positivity)
    _ = _ := by ring

omit [MeasurableSpace Ω] in
lemma centered_square_form_good {X : ℕ → Ω → ℝ} {c : ℝ≥0} (n : ℕ) {h s : ℝ} {ω : Ω}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
      (Nat.clog 8 (n + 1) + 2) (n + 1) h)
    (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i^2) = 1) :
    |∑ i ∈ Finset.range (n + 1), X i ω * u i^2| ≤
      13824 * Real.sqrt (32 * (c : ℝ)) * (h + 1) *
        ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) *
        (pathEnergy n u + s) ^ (3 / 8 : ℝ) := by
  have he0 := pathEnergy_nonneg n u
  have he4 : pathEnergy n u ≤ 4 := by simpa only [hnorm, mul_one] using pathEnergy_le_four_mass n u
  obtain ⟨j, hj, heσ, hσ⟩ := energy_first_scale (Nat.clog 8 (n + 1)) he0 he4
  have hsize := scale_shell_geometry (dyadic_cube_scale (n + 1) (by omega)).1 hj
  have hscale := square_multiscale_prefix (fun i => X i ω) n j
    (scaleLength (Nat.clog 8 (n + 1)) j) (scaleLength_pos _ _) u hu hnorm
    (scaleEnergy_pos _ _) hh (by positivity) heσ (by exact_mod_cast hsize)
    (fun r hr b _ hb k hk => good_scale_prefix hh hω hj hr hb hk)
  exact selected_scale_form_bound hj he0 ((scaleEnergy_pos _ _).le.trans hs) hh c.prop
    heσ (hσ.trans (by linarith)) hscale

omit [MeasurableSpace Ω] in
lemma centered_product_form_good {X : ℕ → Ω → ℝ} {c : ℝ≥0} (n : ℕ) {h s : ℝ} {ω : Ω}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ multiscaleBad X c (fun j => scaleLength (Nat.clog 8 (n + 1)) j - 1)
      (Nat.clog 8 (n + 1) + 2) (n + 1) h)
    (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i^2) = 1) :
    |∑ i ∈ Finset.range (n + 1), X i ω * (u i * u (i + 1))| ≤
      13824 * Real.sqrt (32 * (c : ℝ)) * (h + 1) *
        ((2 : ℝ)^(Nat.clog 8 (n + 1))) ^ (1 / 4 : ℝ) *
        (pathEnergy n u + s) ^ (3 / 8 : ℝ) := by
  have he0 := pathEnergy_nonneg n u
  have he4 : pathEnergy n u ≤ 4 := by simpa only [hnorm, mul_one] using pathEnergy_le_four_mass n u
  obtain ⟨j, hj, heσ, hσ⟩ := energy_first_scale (Nat.clog 8 (n + 1)) he0 he4
  have hsize := scale_shell_geometry (dyadic_cube_scale (n + 1) (by omega)).1 hj
  have hscale := product_multiscale_prefix (fun i => X i ω) n j
    (scaleLength (Nat.clog 8 (n + 1)) j) (scaleLength_pos _ _) u hu hnorm
    (scaleEnergy_pos _ _) hh (by positivity) heσ (by exact_mod_cast hsize)
    (fun r hr b _ hb k hk => good_scale_prefix hh hω hj hr hb hk)
  exact selected_scale_form_bound hj he0 ((scaleEnergy_pos _ _).le.trans hs) hh c.prop
    heσ (hσ.trans (by linarith)) hscale

end

lemma edgeCoeff_sqrt_div (n i : ℕ) (hi : i ≤ n) :
    edgeCoeff n i = Real.sqrt (n - i : ℕ) / Real.sqrt (n + 1 : ℝ) := by
  rw [edgeCoeff, ← Real.sqrt_div (by positivity)]
  congr 1
  rw [Nat.cast_sub hi]
  field_simp
  ring

lemma chi_scaled_bias_bound (n i : ℕ) (hi : i < n) :
    (Real.sqrt (n - i : ℕ) - ∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) /
      Real.sqrt (n + 1 : ℝ) ≤
      4 / (n + 1) + (4 / Real.sqrt (n + 1 : ℝ)) * ((i + 1 : ℝ) / (n + 1)) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hsN : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hN
  have hm : 0 < n - i := by omega
  have hsm : 0 < Real.sqrt (n - i : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have hb := (chi_mean_bias (n - i) hm).2
  have hb2 := chi_bias_le_two (n - i) hm
  by_cases hearly : 2 * (i + 1 : ℝ) ≤ n + 1
  · have hdiff : (n + 1 : ℝ) / 2 ≤ (n - i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      linarith
    have hroot : Real.sqrt (n + 1 : ℝ) ≤ 2 * Real.sqrt (n - i : ℕ) := by
      have hsqN := Real.sq_sqrt hN.le
      have hd0 : (0 : ℝ) ≤ (n - i : ℕ) := Nat.cast_nonneg _
      have hsqD := Real.sq_sqrt hd0
      nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n - i : ℕ)]
    have hbound : (Real.sqrt (n - i : ℕ) - ∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) /
        Real.sqrt (n + 1 : ℝ) ≤ 4 / (n + 1) := by
      apply (div_le_iff₀ hsN).mpr
      have hprod : 2 / Real.sqrt (n - i : ℕ) ≤ 4 / Real.sqrt (n + 1 : ℝ) := by
        apply (div_le_div_iff₀ hsm hsN).mpr
        linarith
      have hid : 4 / (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) = 4 / Real.sqrt (n + 1 : ℝ) := by
        have hsq := Real.sq_sqrt hN.le
        field_simp
        nlinarith
      rw [hid]
      exact hb.trans hprod
    exact hbound.trans (le_add_of_nonneg_right (by positivity))
  · have hlate : (1 / 2 : ℝ) ≤ (i + 1 : ℝ) / (n + 1) := by
      apply (le_div_iff₀ hN).mpr
      push Not at hearly
      linarith
    calc
      _ ≤ 2 / Real.sqrt (n + 1 : ℝ) := div_le_div_of_nonneg_right hb2 hsN.le
      _ ≤ (4 / Real.sqrt (n + 1 : ℝ)) * ((i + 1 : ℝ) / (n + 1)) := by
        have := mul_le_mul_of_nonneg_left hlate (show 0 ≤ 4 / Real.sqrt (n + 1 : ℝ) by positivity)
        calc
          2 / Real.sqrt (n + 1 : ℝ) = (4 / Real.sqrt (n + 1 : ℝ)) * (1 / 2) := by ring
          _ ≤ _ := this
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma weighted_neighbor_sum (n : ℕ) (u w : ℕ → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ w (i + 1)) :
    (∑ i ∈ Finset.range n, w i * (u i ^ 2 + u (i + 1) ^ 2)) ≤
      2 * ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
  have ha : (∑ i ∈ Finset.range n, w i * u i ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (mul_nonneg (hw0 _) (sq_nonneg _))
  have hb : (∑ i ∈ Finset.range n, w i * u (i + 1) ^ 2) ≤
      ∑ i ∈ Finset.range (n + 1), w i * u i ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, w (i + 1) * u (i + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _)
      _ ≤ _ := by
        rw [Finset.sum_range_succ']
        exact le_add_of_nonneg_right (mul_nonneg (hw0 _) (sq_nonneg _))
  simp_rw [mul_add, Finset.sum_add_distrib]
  linarith

lemma weighted_edge_form (n : ℕ) (u a : ℕ → ℝ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ∀ i < n, |a i| ≤ B + C * ((i + 1 : ℝ) / (n + 1))) :
    2 * |∑ i ∈ Finset.range n, a i * u i * u (i + 1)| ≤
      2 * B * (∑ i ∈ Finset.range (n + 1), u i ^ 2) + 4 * C * pathEnergy n u := by
  let w (i : ℕ) : ℝ := B + C * ((i + 1 : ℝ) / (n + 1))
  have hw0 : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hw : ∀ i, w i ≤ w (i + 1) := by
    intro i
    dsimp [w]
    gcongr
    norm_num
  have habs : 2 * |∑ i ∈ Finset.range n, a i * u i * u (i + 1)| ≤
      ∑ i ∈ Finset.range n, w i * (u i ^ 2 + u (i + 1) ^ 2) := by
    calc
      _ ≤ 2 * ∑ i ∈ Finset.range n, |a i * u i * u (i + 1)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ = ∑ i ∈ Finset.range n, |a i| * (2 * |u i * u (i + 1)|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [abs_mul]
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul (ha i (Finset.mem_range.mp hi)) ?_ (by positivity) (hw0 i)
        nlinarith [sq_nonneg (|u i| - |u (i + 1)|), sq_abs (u i), sq_abs (u (i + 1)),
          show |u i * u (i + 1)| = |u i| * |u (i + 1)| from abs_mul _ _]
  have hid : (∑ i ∈ Finset.range (n + 1), w i * u i ^ 2) =
      B * (∑ i ∈ Finset.range (n + 1), u i ^ 2) +
        C * (∑ i ∈ Finset.range (n + 1), (i + 1 : ℝ) / (n + 1) * u i ^ 2) := by
    simp only [w, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  have hvari := pathEnergy_weighted_mass n u
  have hn := habs.trans (weighted_neighbor_sum n u w hw0 hw)
  rw [hid] at hn
  nlinarith [mul_le_mul_of_nonneg_left hvari hC]

lemma chi_mean_form_bias (n : ℕ) (u : ℕ → ℝ) :
    2 * |∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)| ≤
      8 / (n + 1) * (∑ i ∈ Finset.range (n + 1), u i ^ 2) +
        16 / Real.sqrt (n + 1 : ℝ) * pathEnergy n u := by
  have hb := weighted_edge_form n u
    (fun i => (∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ) -
      edgeCoeff n i)
    (B := 4 / (n + 1)) (C := 4 / Real.sqrt (n + 1 : ℝ)) (by positivity) (by positivity) ?_
  · convert hb using 1
    ring
  intro i hi
  rw [edgeCoeff_sqrt_div n i (by omega), ← sub_div]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm,
    abs_of_nonneg (chi_mean_bias (n - i) (by omega)).1]
  exact chi_scaled_bias_bound n i hi

lemma entryVariance_pos (n : ℕ) : 0 < entryVariance n := by
  change 0 < 2 * (48 * Real.exp 1 + 4) / (n + 1 : ℝ)
  positivity

lemma subGaussian_enlarge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  gcongr

lemma diagonalRows_common_subGaussian (n i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω i) (entryVariance n) (diagonalLaw n) := by
  apply subGaussian_enlarge (diagonalRows_subGaussian n i)
  change 2 / (n + 1 : ℝ) ≤ 2 * (48 * Real.exp 1 + 4) / (n + 1)
  gcongr
  have := Real.exp_pos (1 : ℝ)
  linarith

lemma triBad_probability (n : ℕ) (h : ℝ) :
    (triLaw n).real (triBad n h) ≤ 32 * Real.exp (-h ^ 2) := by
  have ha : (diagonalLaw n).real (entryBad n (fun i (ω : ℕ → ℝ) => ω i) h) ≤
      16 * Real.exp (-h ^ 2) :=
    multiscaleBad_probability (fun i => (measurable_pi_apply i).stronglyMeasurable)
      (diagonalRows_independent n) (diagonalRows_common_subGaussian n) (diagonalRows_mean n)
      (entryVariance_pos n) _ _ _ _
  have hb : (chiRowLaw n).real (entryBad n (scaledChiRow n) h) ≤
      16 * Real.exp (-h ^ 2) :=
    multiscaleBad_probability (fun i => (scaledChiRow_measurable n i).stronglyMeasurable)
      (scaledChiRows_independent n) (scaledChiRow_subGaussian n) (scaledChiRow_mean n)
      (entryVariance_pos n) _ _ _ _
  have hU := measureReal_union_le (μ := triLaw n)
    (Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h)
    (Prod.snd ⁻¹' entryBad n (scaledChiRow n) h)
  have heA : Prod.fst ⁻¹' entryBad n (fun i (ω : ℕ → ℝ) => ω i) h =
      (entryBad n (fun i (ω : ℕ → ℝ) => ω i) h) ×ˢ (Set.univ : Set (ChiRows n)) := by ext; simp
  have heB : Prod.snd ⁻¹' entryBad n (scaledChiRow n) h =
      (Set.univ : Set (ℕ → ℝ)) ×ˢ (entryBad n (scaledChiRow n) h) := by ext; simp
  simpa only [triBad, heA, heB, triLaw, measureReal_prod_prod, probReal_univ, mul_one, one_mul]
    using hU.trans (by simpa only [heA, heB, triLaw, measureReal_prod_prod, probReal_univ,
      mul_one, one_mul] using (show _ + _ ≤ 32 * Real.exp (-h ^ 2) by linarith [ha, hb]))

lemma triForm_decomposition (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) :
    triForm n ω u - (2 * (∑ i ∈ Finset.range (n + 1), u i ^ 2) - pathEnergy n u) =
    (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))) +
    2 * (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)) := by
  unfold triForm pathEnergy
  have he : (∑ i ∈ Finset.range n,
      (chi (chiRowDim n i) (ω.2 i) / Real.sqrt (n + 1 : ℝ)) * u i * u (i + 1)) =
      (∑ i ∈ Finset.range n, edgeCoeff n i * u i * u (i + 1)) +
      (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))) +
      (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hd : chiRowDim n i = n - i := by unfold chiRowDim; have := Finset.mem_range.mp hi; omega
    have hmean : (∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)) =
        (∫ y, chi (n - i) y ∂standardGaussianProduct (n - i)) := by rw [hd]
    simp only [scaledChiRow, centeredChiRow]
    rw [hmean]
    ring
  rw [he]
  ring

lemma triForm_good (n : ℕ) {h s : ℝ} {ω : TriSample n}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n + 1)) 0 ≤ s)
    (hω : ω ∉ triBad n h) (u : ℕ → ℝ) (hu : ∀ i, n + 1 ≤ i → u i = 0)
    (hnorm : (∑ i ∈ Finset.range (n + 1), u i ^ 2) = 1) :
    |triForm n ω u - (2 - pathEnergy n u)| ≤ formError n h s (pathEnergy n u) := by
  have hA : ω.1 ∉ entryBad n (fun i (a : ℕ → ℝ) => a i) h := by
    intro ha
    exact hω (Or.inl ha)
  have hB : ω.2 ∉ entryBad n (scaledChiRow n) h := by
    intro hb
    exact hω (Or.inr hb)
  have ha := centered_square_form_good n hh hs hA u hu hnorm
  have hb := centered_product_form_good n hh hs hB u hu hnorm
  have hbias := chi_mean_form_bias n u
  rw [hnorm, mul_one] at hbias
  have heB : (∑ i ∈ Finset.range (n + 1), scaledChiRow n i ω.2 * (u i * u (i + 1))) =
      ∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1)) := by
    rw [Finset.sum_range_succ, hu (n + 1) (by omega)]
    ring
  rw [heB] at hb
  have he := triForm_decomposition n ω u
  rw [hnorm, mul_one] at he
  rw [he]
  have habs := abs_add_le
    ((∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2) +
    2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))))
    (2 * (∑ i ∈ Finset.range n,
      (((∫ x, chi (n - i) x ∂standardGaussianProduct (n - i)) / Real.sqrt (n + 1 : ℝ)) -
        edgeCoeff n i) * u i * u (i + 1)))
  have habs2 := abs_add_le
    (∑ i ∈ Finset.range (n + 1), ω.1 i * u i ^ 2)
    (2 * (∑ i ∈ Finset.range n, scaledChiRow n i ω.2 * (u i * u (i + 1))))
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at habs habs2
  dsimp only [formError]
  linarith

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.Resolvent
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK


lemma directed_neighbor_sum_general (n : ℕ) (b u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then b i.val else 0)*u i.val*u j.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
  rw [Fin.sum_univ_castSucc]
  have hl : (∑ j : Fin (n+1),
      (if (Fin.last n).val+1=j.val then b (Fin.last n).val else 0)*u (Fin.last n).val*u j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right (by have := j.isLt; simp only [Fin.val_last]; omega),zero_mul,zero_mul]
  rw [hl,add_zero,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i.succ]
  · simp
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (Fin.ext (by simpa using h.symm))),zero_mul,zero_mul]
  · simp

lemma generic_tridiagonal_quadratic (n : ℕ) (d b u : ℕ → ℝ) :
    (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      ((if i=j then d i.val else 0)+(if i.val+1=j.val then b i.val else 0)+
        (if j.val+1=i.val then b j.val else 0))*u j.val*u i.val) =
      (∑ i ∈ Finset.range (n+1), d i*u i^2)+2*(∑ i ∈ Finset.range n, b i*u i*u (i+1)) := by
  simp only [add_mul,Finset.sum_add_distrib]
  have hd : (∑ i : Fin (n+1), ∑ j : Fin (n+1), (if i=j then d i.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range (n+1), d i*u i^2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  have hlo : (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if i.val+1=j.val then b i.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
    convert directed_neighbor_sum_general n b u using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intros
    ring
  have hhi : (∑ i : Fin (n+1), ∑ j : Fin (n+1),
      (if j.val+1=i.val then b j.val else 0)*u j.val*u i.val) =
      ∑ i ∈ Finset.range n, b i*u i*u (i+1) := by
    rw [Finset.sum_comm]
    exact directed_neighbor_sum_general n b u
  rw [hd,hlo,hhi]
  ring

lemma triSampleOperator_inner (n : ℕ) (ω : TriSample n) (u : ℕ → ℝ) :
    inner ℝ (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))
      (triSampleOperator n ω (WithLp.toLp 2 (fun i : Fin (n+1) => u i.val))) = triForm n ω u := by
  simp only [triSampleOperator,Matrix.toLpLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Pi.star_apply,star_trivial,dotProduct,Matrix.mulVec,triSampleMatrix,Finset.sum_mul]
  exact generic_tridiagonal_quadratic n ω.1 (fun i => chi (chiRowDim n i) (ω.2 i)/Real.sqrt (n+1:ℝ)) u

lemma extendPath_restrict (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (WithLp.toLp 2 (fun i : Fin (n+1) => extendPath n x i.val)) = x := by
  ext i
  simp only [extendPath,dite_eq_left i.isLt]

lemma extendPath_mass (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    (∑ i ∈ Finset.range (n+1), extendPath n x i^2) = ‖x‖^2 := by
  rw [← Fin.sum_univ_eq_sum_range,EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [extendPath,dite_eq_left i.isLt]

lemma pathOperator_energy (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    inner ℝ x (pathOperator n x) = 2*‖x‖^2-pathEnergy n (extendPath n x) := by
  have h := pathOperator_inner n (extendPath n x)
  rw [extendPath_restrict] at h
  rw [h,pathEnergy,extendPath_mass]
  ring

lemma pathOperator_inner_le_two (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖=1) :
    inner ℝ x (pathOperator n x) ≤ 2 := by
  rw [pathOperator_energy,hx]
  have := pathEnergy_nonneg n (extendPath n x)
  linarith

lemma pathOperator_eigenvalue_le_two (n : ℕ) (i : Fin (n+1)) :
    (pathOperator_symmetric n).eigenvalues (by simp) i ≤ 2 := by
  let h := pathOperator_symmetric n
  have hh := pathOperator_inner_le_two n (h.eigenvectorBasis (by simp) i) ((h.eigenvectorBasis (by simp)).norm_eq_one i)
  rw [h.apply_eigenvectorBasis] at hh
  simpa only [inner_smul_right,real_inner_self_eq_norm_sq,
    (h.eigenvectorBasis (by simp)).norm_eq_one i,one_pow,mul_one,
    RCLike.ofReal_real_eq_id,id_eq] using hh

lemma triSampleOperator_form_good (n : ℕ) {ω : TriSample n} {h s : ℝ}
    (hh : 0 ≤ h) (hs : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s) (hω : ω ∉ triBad n h)
    (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖=1) :
    |inner ℝ x (triSampleOperator n ω x)-inner ℝ x (pathOperator n x)| ≤
      formError n h s (2-inner ℝ x (pathOperator n x)) := by
  have hmass : (∑ i ∈ Finset.range (n+1), extendPath n x i^2) = 1 := by rw [extendPath_mass,hx]; norm_num
  have hc := triForm_good n hh hs hω (extendPath n x)
    (fun i hi => dite_eq_right (by omega)) hmass
  have ht := triSampleOperator_inner n ω (extendPath n x)
  rw [extendPath_restrict] at ht
  rw [ht,pathOperator_energy,hx]
  simp only [one_pow,mul_one]
  convert hc using 1
  congr 1
  ring

open MeasureTheory Set



open MeasureTheory Set

lemma formError_eq (n : ℕ) (h s e : ℝ) :
    formError n h s e = edgeError (formA n h) (formB n) (formC n) s e := rfl

lemma formA_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ formA n h := by unfold formA; positivity

lemma formC_nonneg (n : ℕ) : 0 ≤ formC n := by unfold formC; positivity

lemma triSample_eigenvalue_good (n : ℕ) {ω : TriSample n} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1)
    (hω : ω ∉ triBad n h) (i : Fin (n+1)) :
    |sampleEigenvalues n ω i-(2-orderedJacobiGaps n i)| ≤
      edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i) := by
  have hm := edgeError_eigenvalue_comparison_mono (B := formB n)
    (formA_nonneg n hh) (formC_nonneg n) hs hsmall
  have he := eigenvalue_form_comparison (triSampleOperator_symmetric n ω) (pathOperator_symmetric n)
    (by simp) hm.1 hm.2 (pathOperator_eigenvalue_le_two n)
    (pathOperator_inner_le_two n)
    (fun x hx => by simpa only [← formError_eq] using triSampleOperator_form_good n hh hscale hω x hx) i
  simpa only [sampleEigenvalues,orderedJacobiGaps,sub_sub_cancel] using he

end CriticalSK

end

end OAI
end

section
-- module Solutions.OAIQW_CriticalSK.GOESpectrum
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open scoped BigOperators
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
namespace CriticalSK

open scoped InnerProductSpace

lemma symmetric_eigenvalue_norm_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (A B : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    |hA.eigenvalues hn i - hB.eigenvalues hn i| ≤ ‖A-B‖ := by
  refine eigenvalue_form_comparison hA hB hn (S := Set.univ) (Φ := fun _ => ‖A-B‖)
    (by intro a ha b hb hab; dsimp; linarith) (by intro a ha b hb hab; dsimp; linarith)
    (fun _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) ?_ i
  intro x hx
  calc
    _ = |inner ℝ x ((A-B) x)| := by rw [_root_.sub_apply,inner_sub_right]; rfl
    _ ≤ ‖x‖*‖(A-B) x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖A-B‖*‖x‖) := mul_le_mul_of_nonneg_left ((A-B).le_opNorm x) (norm_nonneg _)
    _ = _ := by rw [hx]; ring

lemma finite_real_linear_continuous {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] (T : D →ₗ[ℝ] F) : Continuous T :=
  T.continuous_of_finiteDimensional

lemma gaussianMatrixCLM_continuous (n : ℕ) : Continuous (gaussianMatrixCLM (n := n)) := by
  change Continuous (gaussianMatrixToCLM n)
  exact finite_real_linear_continuous (gaussianMatrixToCLM n)

lemma symmetrize_half_eq {n : ℕ} (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    symmetrizeGaussianMatrix (1/2:ℝ) A = A := by
  ext i j
  rw [symmetrize_half_entry,hA j i]
  ring

lemma matrixOrderedEigenvalues_eq {n : ℕ} (A : GaussianMatrix (Fin n))
    (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues A = (gaussianMatrixCLM_symmetric A hA).eigenvalues (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := by
  unfold matrixOrderedEigenvalues
  congr 2
  exact congrArg gaussianMatrixCLM (symmetrize_half_eq A hA)

lemma matrixOrderedEigenvalues_continuous {n : ℕ} (i : Fin n) :
    Continuous (fun A : GaussianMatrix (Fin n) => matrixOrderedEigenvalues A i) := by
  let F := fun A : GaussianMatrix (Fin n) => gaussianMatrixCLM (symmetrizeGaussianMatrix (1/2:ℝ) A)
  have hc : Continuous F := (gaussianMatrixCLM_continuous n).comp (symmetrizeGaussianMatrix_continuous _)
  rw [continuous_iff_continuousAt]
  intro A
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp hc.continuousAt ε hε
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have hh := symmetric_eigenvalue_norm_bound (F B) (F A)
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric B))
    (gaussianMatrixCLM_symmetric _ (symmetrize_half_symmetric A)) (by simp : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) i
  exact (show dist (matrixOrderedEigenvalues B i) (matrixOrderedEigenvalues A i) ≤ dist (F B) (F A) by
    simpa only [dist_eq_norm,Real.norm_eq_abs,matrixOrderedEigenvalues] using hh).trans_lt (h hB)

lemma orthoMatrix_transpose {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (orthoMatrix U).transpose = orthoMatrix U.symm := by
  ext i j
  have hh := U.inner_map_eq_flip (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)
  simpa only [EuclideanSpace.inner_basisFun_real,EuclideanSpace.basisFun_inner,
    orthoMatrix,Matrix.transpose_apply] using hh

lemma orthoMatrix_toLpLin {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.toLpLin 2 2 (orthoMatrix U) = U.toLinearEquiv.toLinearMap := by
  ext x i
  change (∑ j, U (EuclideanSpace.basisFun (Fin n) ℝ j) i * x j) = U x i
  rw [euclidean_isometry_apply_eq_sum]
  apply Finset.sum_congr rfl
  intros
  ring

lemma gaussianMatrixCLM_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) :
    (gaussianMatrixCLM (conjugateGaussianMatrix U A)).toLinearMap =
      U.toLinearEquiv.conj (gaussianMatrixCLM A).toLinearMap := by
  change Matrix.toLpLin 2 2 (matrixOfGaussian (conjugateGaussianMatrix U A)) = _
  rw [matrixOfGaussian_conjugate,Matrix.toLpLin_mul_same,Matrix.toLpLin_mul_same,
    orthoMatrix_transpose,orthoMatrix_toLpLin,orthoMatrix_toLpLin]
  rfl

lemma matrixOrderedEigenvalues_conjugate {n : ℕ}
    (U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (conjugateGaussianMatrix U A) = matrixOrderedEigenvalues A := by
  rw [matrixOrderedEigenvalues_eq _ (conjugate_symmetric U A hA),matrixOrderedEigenvalues_eq _ hA]
  apply (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff _ _ _ _).mpr
  rw [gaussianMatrixCLM_conjugate,LinearEquiv.charpoly_conj]

lemma matrixOrderedEigenvalues_triReduce {n : ℕ}
    (A : GaussianMatrix (Fin n)) (hA : ∀ i j, A i j = A j i) :
    matrixOrderedEigenvalues (triReduce n A) = matrixOrderedEigenvalues A := by
  rw [triReduce_conjugate n A hA]
  exact matrixOrderedEigenvalues_conjugate _ _ hA

lemma matrixOrderedEigenvalues_sample (n : ℕ) (ω : TriSample n) :
    matrixOrderedEigenvalues (WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => triSampleMatrix n ω i j))) =
      sampleEigenvalues n ω := by
  have hA : ∀ i j, triSampleMatrix n ω i j = triSampleMatrix n ω j i := by
    intro i j
    have hh := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M i j) (triSampleMatrix_hermitian n ω)
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh.symm
  rw [matrixOrderedEigenvalues_eq _ hA]
  rfl

instance triEntriesLaw_probability (n : ℕ) (s : ℝ) : IsProbabilityMeasure (triEntriesLaw n s) := by
  unfold triEntriesLaw; infer_instance

lemma triEntriesMatrix_measurable (n : ℕ) : Measurable (triEntriesMatrix n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (assembleTri_measurable n).comp
      (((measurable_pi_apply (0 : Fin (n+1))).fst).prodMk
        (((measurable_pi_apply (0 : Fin (n+1))).snd).prodMk
          (ih.comp (Measurable.of_eval (fun i => measurable_pi_apply i.succ)))))

lemma triEntriesLaw_split (n : ℕ) (s : ℝ) :
    MeasurePreserving (fun p : Fin (n+1) → ℝ × ℝ => (p 0, fun i : Fin n => p i.succ))
      (triEntriesLaw (n+1) s)
      (((gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw n s)).prod (triEntriesLaw n s)) := by
  convert measurePreserving_piFinSuccAbove
    (fun i : Fin (n+1) => (gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw (n+1-i.val-1) s)) 0 using 1
  · rfl
  · rfl
  · simp only [Fin.val_zero,Nat.sub_zero,Nat.add_sub_cancel_right,triEntriesLaw,
      Fin.succAbove_zero,Fin.val_succ,Nat.add_sub_add_right]

lemma probability_eq_on_subsingleton {Ω : Type*} [MeasurableSpace Ω] [Subsingleton Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ=ν := by
  apply Measure.ext
  intro t _
  by_cases ht : t.Nonempty
  · obtain ⟨x,hx⟩ := ht
    have he : t=Set.univ := Set.eq_univ_of_forall (fun y => by simpa only [Subsingleton.elim y x] using hx)
    simp only [he,measure_univ]
  · simp only [Set.not_nonempty_iff_eq_empty.mp ht,measure_empty]

lemma triEntriesMatrix_preserving (n : ℕ) (s : ℝ) :
    MeasurePreserving (triEntriesMatrix n) (triEntriesLaw n s) (triMatrixLaw n s) := by
  induction n with
  | zero =>
    refine ⟨triEntriesMatrix_measurable 0,?_⟩
    have := Measure.isProbabilityMeasure_map (μ := triEntriesLaw 0 s) (triEntriesMatrix_measurable 0).aemeasurable
    exact probability_eq_on_subsingleton _ _
  | succ n ih =>
    have hp := (MeasurePreserving.id ((gaussianReal 0 (4*s^2).toNNReal).prod (columnNormLaw n s))).prod ih
    have ha := measurePreserving_prodAssoc (gaussianReal 0 (4*s^2).toNNReal)
      (columnNormLaw n s) (triMatrixLaw n s)
    have hb : MeasurePreserving (assembleTri n)
        ((gaussianReal 0 (4*s^2).toNNReal).prod ((columnNormLaw n s).prod (triMatrixLaw n s)))
        (triMatrixLaw (n+1) s) := ⟨assembleTri_measurable n,rfl⟩
    exact hb.comp (ha.comp (hp.comp (triEntriesLaw_split n s)))

lemma triEntriesMatrix_apply (n : ℕ) (p : Fin n → ℝ × ℝ) (i j : Fin n) :
    triEntriesMatrix n p i j =
      (if i=j then (p i).1 else 0)+(if i.val+1=j.val then (p i).2 else 0)+
        (if j.val+1=i.val then (p j).2 else 0) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp [triEntriesMatrix,assembleTri,borderMatrix_zero_zero]
      | succ j =>
        rw [triEntriesMatrix,assembleTri,borderMatrix_zero_succ]
        have he : (1=j.val+1) ↔ (j.val=0) := by omega
        have hn : ¬(j.val+1+1=0) := by omega
        simp only [Ne.symm (Fin.succ_ne_zero j),Fin.val_zero,Fin.val_succ,hn,ite_false,
          zero_add,add_zero,he]
        change (p 0).2*(if j.val=0 then 1 else 0) = _
        split_ifs <;> simp only [mul_one,mul_zero]
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        rw [triEntriesMatrix,assembleTri,borderMatrix_succ_zero]
        have he : (1=i.val+1) ↔ (i.val=0) := by omega
        have hn : ¬(i.val+1+1=0) := by omega
        simp only [Fin.succ_ne_zero i,Fin.val_zero,Fin.val_succ,hn,ite_false,
          zero_add,add_zero,he]
        change (p 0).2*(if i.val=0 then 1 else 0) = _
        split_ifs <;> simp only [mul_one,mul_zero]
      | succ j =>
        simpa only [triEntriesMatrix,assembleTri,borderMatrix_succ_succ,Fin.succ_inj,
          Fin.val_succ,Nat.add_right_cancel_iff] using ih (fun k => p k.succ) i j

lemma goeScale_square (n : ℕ) : 2*(goeScale n)^2 = (n+1:ℝ)⁻¹ := by
  have hn : (0:ℝ) < n+1 := by positivity
  unfold goeScale
  rw [inv_pow,Real.sq_sqrt (by positivity)]
  field_simp

lemma goeScale_diagonal (n : ℕ) : 4*(goeScale n)^2 = 2/(n+1:ℝ) := by
  have := goeScale_square n
  rw [div_eq_mul_inv]
  nlinarith

lemma gaussian_div_sqrt_preserving (n : ℕ) :
    MeasurePreserving (fun x : ℝ => x/Real.sqrt (n+1:ℝ)) (gaussianReal 0 1)
      (gaussianReal 0 (2*(goeScale n)^2).toNNReal) := by
  refine ⟨by fun_prop,?_⟩
  rw [gaussianReal_map_div_const,zero_div,goeScale_square]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_mk,Real.coe_toNNReal _ (by positivity : 0 ≤ (n+1:ℝ)⁻¹)]
  rw [Real.sq_sqrt (by positivity),one_div]

lemma chi_eq_norm (m : ℕ) (x : Fin m → ℝ) :
    chi m x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [chi,chiSquare,Real.norm_eq_abs,sq_abs]

lemma columnNormLaw_scale (n m : ℕ) :
    columnNormLaw m (goeScale n) =
      (standardGaussianProduct m).map (fun x => chi m x/Real.sqrt (n+1:ℝ)) := by
  have hp := measurePreserving_pi (fun _ : Fin m => gaussianReal 0 1)
    (fun _ : Fin m => gaussianReal 0 (2*(goeScale n)^2).toNNReal)
    (fun _ => gaussian_div_sqrt_preserving n)
  have hh := (columnNorm_preserving m (goeScale n)).comp hp
  have he : (fun x : Fin m → ℝ => ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m))‖) =
      (fun x => chi m x/Real.sqrt (n+1:ℝ)) := by
    funext x
    have hv : (WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m)) =
        (Real.sqrt (n+1:ℝ))⁻¹ • WithLp.toLp 2 x := by ext i; simp [div_eq_mul_inv,mul_comm]
    rw [hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),← chi_eq_norm]
    ring
  have hmap := hh.map_eq
  change (standardGaussianProduct m).map (fun x : Fin m → ℝ =>
    ‖(WithLp.toLp 2 (fun i => x i/Real.sqrt (n+1:ℝ)) : EuclideanSpace ℝ (Fin m))‖) = _ at hmap
  rw [he] at hmap
  exact hmap.symm

lemma columnNormLaw_zero (s : ℝ) : columnNormLaw 0 s = Measure.dirac 0 := by
  unfold columnNormLaw
  have he : (fun v : Fin 0 → ℝ => ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 0))‖) = fun _ => (0:ℝ) := by
    funext v
    rw [show (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 0)) = 0 from Subsingleton.elim _ _,norm_zero]
  rw [he,Measure.map_const,measure_univ,one_smul]

lemma measurePreserving_independent {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] (μ : Measure Ω) (ν : ∀ i, Measure (β i))
    (f : ∀ i, Ω → β i) (hf : ∀ i, MeasurePreserving (f i) μ (ν i)) (hi : iIndepFun f μ) :
    MeasurePreserving (fun ω i => f i ω) μ (Measure.pi ν) := by
  refine ⟨Measurable.of_eval (fun i => (hf i).measurable),?_⟩
  rw [hi.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  exact (hf i).map_eq

lemma diagonalMarginal_scale (n i : ℕ) :
    diagonalMarginal n i = gaussianReal 0 (4*(goeScale n)^2).toNNReal := by
  rw [goeScale_diagonal]
  unfold diagonalMarginal
  congr 1
  apply NNReal.coe_injective
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2/(n+1:ℝ))]
  rfl

lemma diagonalFinite_preserving (n : ℕ) :
    MeasurePreserving (fun a : ℕ → ℝ => fun i : Fin (n+1) => a i.val)
      (diagonalLaw n) (Measure.pi fun _ => gaussianReal 0 (4*(goeScale n)^2).toNNReal) := by
  have hi : iIndepFun (fun i : ℕ => fun a : ℕ → ℝ => a i) (diagonalLaw n) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  exact measurePreserving_independent _ _ _
    (fun i => by simpa only [diagonalLaw,diagonalMarginal_scale] using measurePreserving_eval_infinitePi (diagonalMarginal n) i.val)
    (hi.precomp Fin.val_injective)

lemma finiteChiEntry_measurable (n i : ℕ) : Measurable (finiteChiEntry n i) := by
  unfold finiteChiEntry
  split_ifs
  · exact (chi_measurable _).div_const _
  · exact measurable_const

lemma finiteChiEntry_preserving (n i : ℕ) :
    MeasurePreserving (finiteChiEntry n i) (standardGaussianProduct (chiRowDim n i))
      (columnNormLaw (n-i) (goeScale n)) := by
  refine ⟨finiteChiEntry_measurable n i,?_⟩
  change Measure.map (fun x => if i<n then chi (chiRowDim n i) x / Real.sqrt (n+1:ℝ) else 0) _ = _
  by_cases hi : i<n
  · have hd : chiRowDim n i = n-i := by unfold chiRowDim; omega
    simp only [ite_eq_left hi]
    rw [hd, columnNormLaw_scale]
  · have hd : n-i=0 := by omega
    simp only [ite_eq_right hi,hd,columnNormLaw_zero,Measure.map_const,
      measure_univ,one_smul]

lemma chiFinite_preserving (n : ℕ) :
    MeasurePreserving (fun a : ChiRows n => fun i : Fin (n+1) => finiteChiEntry n i.val (a i.val))
      (chiRowLaw n) (Measure.pi fun i => columnNormLaw (n-i.val) (goeScale n)) := by
  have hi : iIndepFun (fun i : ℕ => fun a : ChiRows n => finiteChiEntry n i (a i)) (chiRowLaw n) :=
    iIndepFun_infinitePi (fun i => finiteChiEntry_measurable n i)
  exact measurePreserving_independent _ _ _
    (fun i => (finiteChiEntry_preserving n i.val).comp
      (measurePreserving_eval_infinitePi (fun i => standardGaussianProduct (chiRowDim n i)) i.val))
    (hi.precomp Fin.val_injective)

lemma sampleEntries_preserving (n : ℕ) :
    MeasurePreserving (sampleEntries n) (triLaw n) (triEntriesLaw (n+1) (goeScale n)) := by
  have hp := (diagonalFinite_preserving n).prod (chiFinite_preserving n)
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (n+1))
    (fun _ => gaussianReal 0 (4*(goeScale n)^2).toNNReal)
    (fun i => columnNormLaw (n-i.val) (goeScale n))).symm
  convert he.comp hp using 1
  · rfl
  · rfl
  · unfold triEntriesLaw
    congr 1
    funext i
    congr 2
    omega

lemma sampleEntriesMatrix_apply (n : ℕ) (ω : TriSample n) (i j : Fin (n+1)) :
    triEntriesMatrix (n+1) (sampleEntries n ω) i j = triSampleMatrix n ω i j := by
  rw [triEntriesMatrix_apply]
  simp only [sampleEntries,triSampleMatrix,finiteChiEntry]
  congr 1
  · congr 1
    split_ifs with he hi
    · rfl
    · omega
    · rfl
  · split_ifs with he hi
    · rfl
    · omega
    · rfl

lemma sampleMatrix_preserving (n : ℕ) :
    MeasurePreserving (fun ω : TriSample n => WithLp.toLp 2
      (fun i => WithLp.toLp 2 (fun j => triSampleMatrix n ω i j)))
      (triLaw n) (triMatrixLaw (n+1) (goeScale n)) := by
  have hh := (triEntriesMatrix_preserving (n+1) (goeScale n)).comp (sampleEntries_preserving n)
  convert hh using 1
  funext ω
  ext i j
  exact (sampleEntriesMatrix_apply n ω i j).symm

lemma matrixOrderedEigenvalues_measurable (n : ℕ) :
    Measurable (matrixOrderedEigenvalues (n := n)) :=
  Measurable.of_eval (fun i => (matrixOrderedEigenvalues_continuous i).measurable)

lemma goe_sample_eigenvalues_law (n : ℕ) :
    (goeLaw (Fin (n+1)) (goeScale n)).map matrixOrderedEigenvalues =
      (triLaw n).map (sampleEigenvalues n) := by
  have hT : (triMatrixLaw (n+1) (goeScale n)).map matrixOrderedEigenvalues =
      (goeLaw (Fin (n+1)) (goeScale n)).map matrixOrderedEigenvalues := by
    rw [← (triReduce_preserving (n+1) (goeScale n)).map_eq,
      Measure.map_map (matrixOrderedEigenvalues_measurable _) (triReduce_measurable _)]
    apply Measure.map_congr
    filter_upwards [goe_symmetric_ae (ι := Fin (n+1)) (goeScale n)] with A hA
    exact matrixOrderedEigenvalues_triReduce A hA
  rw [← hT,← (sampleMatrix_preserving n).map_eq,
    Measure.map_map (matrixOrderedEigenvalues_measurable _) (sampleMatrix_preserving n).measurable]
  congr 1
  funext ω
  exact matrixOrderedEigenvalues_sample n ω

lemma spectralGood_measurable (n : ℕ) (h s : ℝ) : MeasurableSet (spectralGood n h s) := by
  simp only [spectralGood,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le ((measurable_pi_apply i).sub_const _).abs measurable_const

lemma sampleEigenvalues_measurable (n : ℕ) : Measurable (sampleEigenvalues n) := by
  have hc := (matrixOrderedEigenvalues_measurable (n+1)).comp (sampleMatrix_preserving n).measurable
  simpa only [Function.comp_def,matrixOrderedEigenvalues_sample] using hc

lemma goe_spectral_bad_probability_oai (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
    (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
    (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2) := by
  have he := congrArg (fun μ : Measure (Fin (n+1) → ℝ) => μ.real (spectralGood n h s)ᶜ)
    (goe_sample_eigenvalues_law n)
  simp only [Measure.real,Measure.map_apply (matrixOrderedEigenvalues_measurable _)
    (spectralGood_measurable n h s).compl,Measure.map_apply (sampleEigenvalues_measurable n)
    (spectralGood_measurable n h s).compl] at he
  rw [show (goeLaw (Fin (n+1)) (goeScale n)).real
    (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) =
      (triLaw n).real (sampleEigenvalues n ⁻¹' (spectralGood n h s)ᶜ) from he]
  apply (measureReal_mono ?_).trans (triBad_probability n h)
  intro ω hω
  by_contra hn
  exact hω (triSample_eigenvalue_good n hh hs hscale hsmall hn)

end CriticalSK

end

end OAI
end

theorem solution : type_of% @OAI.CriticalSK.goe_spectral_bad_probability_oai := @OAI.CriticalSK.goe_spectral_bad_probability_oai
