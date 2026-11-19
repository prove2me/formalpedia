-- Prove2me | solution 1 for Kyprianou.Ch03.exercise37PositiveStableLaplaceAndVariation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:12:55.242192+00:00
-- url     : https://prove2.me/submissions/0a4e0770-984f-4b50-98bd-745eed48ff3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_stableVariation_lowIndexLaplaceAndMonotone
import Theorems.Thm_Kyprianou_Ch03_stableVariation_highIndexLaplaceAndUnboundedVariation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (alpha < 1 →
      (∃ C : ℝ, 0 < C ∧
        (∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega,
            Real.exp (-theta * X 1 omega) ∂P) =
              -C * theta ^ alpha)) ∧
      (∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega))) ∧
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
  exact ⟨
    Kyprianou.Ch03.stableVariation_lowIndexLaplaceAndMonotone P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable,
    Kyprianou.Ch03.stableVariation_highIndexLaplaceAndUnboundedVariation P X hX T hLK alpha c hAlpha hC hGaussian hMeasure hStable
  ⟩

