-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValue_continuousPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:33:55.219005+00:00
-- url     : https://prove2.me/submissions/98d14db2-56f7-468f-86f7-4e9603438d6a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_continuous

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Continuous Brownian paths give continuous discounted value paths. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hphi : 0 < phi)
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∀ ω, Continuous (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        mckeanValue K (Real.log (K * phi / (1 + phi))) phi
          (x + X t ω)) := by
  intro ω
  let b : ℝ := Real.log (K * phi / (1 + phi))
  have hV : Continuous (mckeanValue K b phi) :=
    Kyprianou.Ch01.mckeanValue_continuous K phi hK hphi
  have hX : Continuous (fun t : ℝ≥0 => x + X t ω) :=
    continuous_const.add (hAllContinuous ω)
  have hComp : Continuous (fun t : ℝ≥0 =>
      mckeanValue K b phi (x + X t ω)) :=
    hV.comp hX
  have hDiscount : Continuous (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ))) := by
    fun_prop
  exact hDiscount.mul hComp
