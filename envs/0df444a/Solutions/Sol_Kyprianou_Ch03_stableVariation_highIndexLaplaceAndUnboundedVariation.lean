-- Prove2me | solution 1 for Kyprianou.Ch03.stableVariation_highIndexLaplaceAndUnboundedVariation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:01:54.394663+00:00
-- url     : https://prove2.me/submissions/551dd1b2-df76-4f43-a13c-c9bb574ad003
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_stableHighIndexLaplaceV1
import Theorems.Thm_Kyprianou_Ch03_stableHighIndexNoIntegerMomentsV1
import Theorems.Thm_Kyprianou_Ch03_stableHighIndexUnitIntervalVariationV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03
theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (alpha c : ℝ) (hAlpha : 0 < alpha ∧ alpha < 2)
    (hC : 0 < c) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStablePositiveMeasure c alpha 0)
    (hStable : ∀ (t : NNReal) (scale : ℝ), 0 < scale →
      P.map (X (t * Real.toNNReal scale)) =
        P.map (fun omega => scale ^ (1 / alpha) * X t omega)) :
    (1 < alpha →
      (∃ C : ℝ, 0 < C ∧
        ∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              C * theta ^ alpha) ∧
      (∀ n : ℕ, 2 ≤ n →
        ¬ Integrable (fun omega => |X 1 omega| ^ n) P) ∧
      (∀ᵐ omega ∂P, ∀ M : ℝ,
        ∃ n : ℕ, ∃ times : Fin (n + 1) → NNReal,
          times 0 = 0 ∧ times (Fin.last n) ≤ 1 ∧
          (∀ i : Fin n, times i.castSucc < times i.succ) ∧
          M < ∑ i : Fin n,
            |X (times i.succ) omega -
              X (times i.castSucc) omega|)) := by
  intro ha
  exact ⟨Kyprianou.Ch03.stableHighIndexLaplaceV1 P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable ha,
    Kyprianou.Ch03.stableHighIndexNoIntegerMomentsV1 P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable ha,
    Kyprianou.Ch03.stableHighIndexUnitIntervalVariationV1 P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable ha⟩
