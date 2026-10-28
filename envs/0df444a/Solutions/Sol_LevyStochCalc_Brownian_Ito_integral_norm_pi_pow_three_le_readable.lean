-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:30.022231+00:00
-- url     : https://prove2.me/submissions/92ad3e47-7ca4-4cea-979d-ecc49aeab58c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section PiNorm
variable {n : ℕ}
/-- The supremum norm on `Fin n → ℝ` is at most the sum of the absolute coordinates. -/
theorem LevyStochCalc.Brownian.Ito.norm_pi_le_sum_abs (x : Fin n → ℝ) : ‖x‖ ≤ ∑ m, |x m| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (x j))).2 fun m => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ m)
/-- The cube of the supremum norm on `Fin n → ℝ` is at most `n²` times the sum of the cubed
absolute coordinates. -/
theorem LevyStochCalc.Brownian.Ito.cube_norm_pi_le_sum_abs_cube (x : Fin n → ℝ) :
    ‖x‖ ^ 3 ≤ (n : ℝ) ^ 2 * ∑ m, |x m| ^ 3 := by
  have h1 : ‖x‖ ^ 3 ≤ (∑ m, |x m|) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg x) (norm_pi_le_sum_abs x) 3
  have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
    (f := fun m => |x m|) (fun j _ => abs_nonneg (x j)) 2
  simpa using h1.trans h2
end PiNorm
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section GenericThird
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The third moment of the supremum norm on `Fin n → ℝ` from the coordinates. -/
theorem solution {n : ℕ} {x : Ω → Fin n → ℝ} (hxm : Measurable x)
    (h3 : ∀ p : Fin n, Integrable (fun ω => |x ω p| ^ 3) P) {c : Fin n → ℝ}
    (hc : ∀ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P ≤ c p) :
    ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ (n : ℝ) ^ 2 * ∑ p, c p := by
  have hdom : Integrable (fun ω => (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun p _ => h3 p).const_mul _
  have hpt : ∀ ω, ‖x ω‖ ^ 3 ≤ (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3 := fun ω =>
    LevyStochCalc.Brownian.Ito.cube_norm_pi_le_sum_abs_cube (x ω)
  have hint : Integrable (fun ω => ‖x ω‖ ^ 3) P := by
    refine hdom.mono' (hxm.norm.pow_const 3).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact hpt ω
  calc ∫ ω, ‖x ω‖ ^ 3 ∂P ≤ ∫ ω, (n : ℝ) ^ 2 * ∑ p : Fin n, |x ω p| ^ 3 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (n : ℝ) ^ 2 * ∑ p : Fin n, ∫ ω, |x ω p| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun p _ => h3 p]
    _ ≤ (n : ℝ) ^ 2 * ∑ p : Fin n, c p :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hc p) (by positivity)
