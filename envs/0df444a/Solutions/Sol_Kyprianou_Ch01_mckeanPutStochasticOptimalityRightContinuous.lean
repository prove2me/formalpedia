-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanPutStochasticOptimalityRightContinuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:29:58.60601+00:00
-- url     : https://prove2.me/submissions/fff8c7d1-c8a9-4384-a937-9a0d57dcec38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanRightFirstLowerPassageStopping
import Theorems.Thm_Kyprianou_Ch01_mckeanRightBarrierRewardIdentity
import Theorems.Thm_Kyprianou_Ch01_mckeanRightAllStoppingPayoffUpperBound

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma K q x : ℝ)
    (hsigma : 0 < sigma) (hK : 0 < K) (hq : 0 < q)
    (hB : IsLinearBrownian P X sigma gamma)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    let phi : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
        sigma ^ 2
    let barrier : ℝ := Real.log (K * phi / (1 + phi))
    let tauStar : Ω → WithTop ℝ≥0 :=
      firstLowerPassage X x barrier
    IsNaturalRightStoppingTime (fun t ω => x + X t ω) tauStar ∧
      Integrable (discountedPut X x K q tauStar) P ∧
      (∫ ω, discountedPut X x K q tauStar ω ∂P) =
        mckeanValue K barrier phi x ∧
      (∀ tau : Ω → WithTop ℝ≥0,
        IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau →
        (∫ ω, discountedPut X x K q tau ω ∂P) ≤
          mckeanValue K barrier phi x) := by
  dsimp only
  have hstopping :=
    Kyprianou.Ch01.mckeanRightFirstLowerPassageStopping
      X hXmeas hAllContinuous x
        (Real.log (K *
          ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
            sigma ^ 2) /
          (1 + ((Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) + gamma) /
            sigma ^ 2))))
  have hreward :=
    Kyprianou.Ch01.mckeanRightBarrierRewardIdentity
      P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous
  have hbound :=
    Kyprianou.Ch01.mckeanRightAllStoppingPayoffUpperBound
      P X sigma gamma K q x hsigma hK hq hB hXmeas hAllContinuous
  dsimp only at hreward hbound
  exact ⟨hstopping, hreward.1, hreward.2, hbound⟩
