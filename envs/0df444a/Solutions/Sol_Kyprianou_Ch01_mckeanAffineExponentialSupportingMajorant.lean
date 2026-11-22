-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanAffineExponentialSupportingMajorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:58:38.055385+00:00
-- url     : https://prove2.me/submissions/f8f11a05-d136-4885-b0da-a4078fa0ba0b

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanAffineSupportCoefficientTouch
import Theorems.Thm_Kyprianou_Ch01_mckeanPayoffAffineExponentialUpper
import Theorems.Thm_Kyprianou_Ch01_mckeanAffineUpperContinuationFromBarrier

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The exercise and continuation affine majorants meet at the value. -/
theorem solution
    (K phi y : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let b : ℝ := Real.log (K * phi / (1 + phi))
    let u : ℝ := min y b
    let A : ℝ := K - (1 + 1 / phi) * Real.exp u
    let B : ℝ := Real.exp u / phi
    0 ≤ A ∧ 0 ≤ B ∧
      mckeanValue K b phi y =
        A + B * Real.exp (-phi * (y - u)) ∧
      ∀ z : ℝ, mckeanValue K b phi z ≤
        A + B * Real.exp (-phi * (z - u)) := by
  dsimp only
  let b : ℝ := Real.log (K * phi / (1 + phi))
  let u : ℝ := min y b
  let A : ℝ := K - (1 + 1 / phi) * Real.exp u
  let B : ℝ := Real.exp u / phi
  change 0 ≤ A ∧ 0 ≤ B ∧
    mckeanValue K b phi y =
      A + B * Real.exp (-phi * (y - u)) ∧
    ∀ z, mckeanValue K b phi z ≤
      A + B * Real.exp (-phi * (z - u))
  have hTouch :
      0 ≤ A ∧ 0 ≤ B ∧
        mckeanValue K b phi y =
          A + B * Real.exp (-phi * (y - u)) :=
    Kyprianou.Ch01.mckeanAffineSupportCoefficientTouch K phi y hK hphi
  rcases hTouch with ⟨hA, hB, hEq⟩
  refine ⟨hA, hB, hEq, ?_⟩
  intro z
  have hPayoff (w : ℝ) :
      K - Real.exp w ≤ A + B * Real.exp (-phi * (w - u)) :=
    Kyprianou.Ch01.mckeanPayoffAffineExponentialUpper K phi u w hphi
  by_cases hz : z < b
  · change (if z < b then K - Real.exp z else
      (K - Real.exp b) * Real.exp (-phi * (z - b))) ≤
        A + B * Real.exp (-phi * (z - u))
    rw [if_pos hz]
    exact hPayoff z
  · change (if z < b then K - Real.exp z else
      (K - Real.exp b) * Real.exp (-phi * (z - b))) ≤
        A + B * Real.exp (-phi * (z - u))
    rw [if_neg hz]
    exact Kyprianou.Ch01.mckeanAffineUpperContinuationFromBarrier
      K phi b u A B hphi hA (hPayoff b) z (le_of_not_gt hz)
