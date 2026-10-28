-- Prove2me | solution 1 for OAI.CriticalSK.triSample_eigenvalue_good_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:13:02.27486+00:00
-- url     : https://prove2.me/submissions/d2b7d4e2-2419-4094-8056-950155c3477e

import Mathlib
import Definitions.Def_OAIQ074C000

section
-- module Solutions.OAIQ074_CM.Compat
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianMoments
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
-- module Solutions.OAIQ074_CM.CriticalSK_GaussianConcentration
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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

lemma chi_bias_le_two (m : ℕ) (hm : 0 < m) :
    Real.sqrt m - (∫ x, chi m x ∂standardGaussianProduct m) ≤ 2 := by
  have hs : (1 : ℝ) ≤ Real.sqrt m := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt this
  calc
    _ ≤ 2 / Real.sqrt m := (chi_mean_bias m hm).2
    _ ≤ 2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

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
-- module Solutions.OAIQ074_CM.CriticalSK_PathEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
-- module Solutions.OAIQ074_CM.CriticalSK_BlockEnergy
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
    all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ074_CM.CriticalSK_MinMax
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
    all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ074_CM.CriticalSK_PathSpectra
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
    all_goals try with_reducible_and_instances rfl
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
-- module Solutions.OAIQ074_CM.CriticalSK_Powers
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
-- module Solutions.OAIQ074_CM.CriticalSK_TriNoise
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
      all_goals try with_reducible_and_instances rfl
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
    all_goals try with_reducible_and_instances rfl
    ring
  intro i hi
  rw [edgeCoeff_sqrt_div n i (by omega), ← sub_div]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm,
    abs_of_nonneg (chi_mean_bias (n - i) (by omega)).1]
  exact chi_scaled_bias_bound n i hi

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
-- module Solutions.OAIQ074_CM.CriticalSK_Resolvent
attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
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
    all_goals try with_reducible_and_instances rfl
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
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

open MeasureTheory Set



open MeasureTheory Set

lemma formError_eq (n : ℕ) (h s e : ℝ) :
    formError n h s e = edgeError (formA n h) (formB n) (formC n) s e := rfl

lemma formA_nonneg (n : ℕ) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ formA n h := by unfold formA; positivity

lemma formC_nonneg (n : ℕ) : 0 ≤ formC n := by unfold formC; positivity

lemma triSample_eigenvalue_good_s2_oai (n : ℕ) {ω : TriSample n} {h s : ℝ}
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

theorem solution : type_of% @OAI.CriticalSK.triSample_eigenvalue_good_s2_oai := @OAI.CriticalSK.triSample_eigenvalue_good_s2_oai
