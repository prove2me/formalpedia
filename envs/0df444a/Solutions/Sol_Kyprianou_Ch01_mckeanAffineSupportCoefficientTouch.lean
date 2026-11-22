-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanAffineSupportCoefficientTouch
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:56:15.236332+00:00
-- url     : https://prove2.me/submissions/e9ece266-a256-4155-9e2f-24d8e5b5c167

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanAffineCoefficientsNonnegative
import Theorems.Thm_Kyprianou_Ch01_mckeanAffineSupportTouchesValue
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

/-- The two elementary certificates imply the touching positive affine support. -/
theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let u : ℝ := min y b
    let A : ℝ := K - (1 + 1 / phi) * Real.exp u
    let B : ℝ := Real.exp u / phi
    0 ≤ A ∧ 0 ≤ B ∧
      mckeanValue K b phi y =
        A + B * Real.exp (-phi * (y - u)) := by
  have hPos :=
    Kyprianou.Ch01.mckeanAffineCoefficientsNonnegative K phi y hK hphi
  have hTouch :=
    Kyprianou.Ch01.mckeanAffineSupportTouchesValue K phi y hK hphi
  exact ⟨hPos.1, hPos.2, hTouch⟩
