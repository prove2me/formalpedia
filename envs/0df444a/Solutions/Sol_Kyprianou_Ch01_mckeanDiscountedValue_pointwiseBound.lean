-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValue_pointwiseBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:22:39.877745+00:00
-- url     : https://prove2.me/submissions/0429c424-7fcc-409b-a235-4c69f3fdf313

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValueBoundedNonnegative

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (t : ℝ≥0) (ω : Ω) :
    let barrier := Real.log (K * phi / (1 + phi))
    0 ≤ Real.exp (-q * (t : ℝ)) *
      mckeanValue K barrier phi (x + X t ω) ∧
    Real.exp (-q * (t : ℝ)) *
      mckeanValue K barrier phi (x + X t ω) ≤ K := by
  dsimp only
  have hV := Kyprianou.Ch01.mckeanValueBoundedNonnegative
    K phi (x + X t ω) hK hphi
  dsimp only at hV
  have hqtime : 0 ≤ q * (t : ℝ) :=
    mul_nonneg hq.le (NNReal.coe_nonneg t)
  have he : 0 ≤ Real.exp (-q * (t : ℝ)) := Real.exp_nonneg _
  have he1 : Real.exp (-q * (t : ℝ)) ≤ 1 := by
    have hc : -q * (t : ℝ) ≤ 0 := by linarith
    simpa using Real.exp_le_exp.mpr hc
  constructor
  · exact mul_nonneg he hV.1
  · calc
      Real.exp (-q * (t : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X t ω) ≤
          1 * mckeanValue K (Real.log (K * phi / (1 + phi))) phi
            (x + X t ω) :=
            mul_le_mul_of_nonneg_right he1 hV.1
      _ ≤ K := by simpa using hV.2
