-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValue_natTendstoZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:58:06.020605+00:00
-- url     : https://prove2.me/submissions/eac631b7-59d7-4216-b459-92f199f4e047

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative
import Theorems.Thm_e7_exp_neg_scale_tendsto_zero

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Discount eliminates a uniformly bounded value at infinite horizons. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (ω : Ω) :
    Filter.Tendsto (fun n : ℕ =>
      Real.exp (-q * (n : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X (n : ℝ≥0) ω))
      Filter.atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ =>
      Real.exp (-q * (n : ℝ))) atTop (nhds 0) :=
    (e7_exp_neg_scale_tendsto_zero q hq).comp hn
  have hbound : Tendsto (fun n : ℕ =>
      K * Real.exp (-q * (n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul he :
        Tendsto (fun n : ℕ => K * Real.exp (-q * (n : ℝ)))
          atTop (nhds (K * 0)))
  have hV (n : ℕ) :=
    Kyprianou.Ch01.mckeanValueBoundedNonnegative
      K phi (x + X (n : ℝ≥0) ω) hK hphi
  apply squeeze_zero
  · intro n
    exact mul_nonneg (Real.exp_nonneg _) (hV n).1
  · intro n
    calc
      Real.exp (-q * (n : ℝ)) *
          mckeanValue K (Real.log (K * phi / (1 + phi))) phi
            (x + X (n : ℝ≥0) ω) =
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
            (x + X (n : ℝ≥0) ω) * Real.exp (-q * (n : ℝ)) :=
          mul_comm _ _
      _ ≤ K * Real.exp (-q * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (hV n).2 (Real.exp_nonneg _)
  · exact hbound
