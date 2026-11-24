-- Prove2me | solution 1 for Kyprianou.Ch03.stableHighIndexLaplaceV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:02:12.192941+00:00
-- url     : https://prove2.me/submissions/6f2870a1-2de0-4028-ac98-516e13969eba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_stablePositiveNegativeExpIntegrableV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveLogLaplaceHomogeneityV1
import Theorems.Thm_Kyprianou_Ch03_stablePositiveUnitNonzeroV1
import Theorems.Thm_Kyprianou_Ch03_stableLogLaplaceCoefficientStrictSignV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03
open scoped Topology
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
    1 < alpha →
      ∃ C : ℝ, 0 < C ∧
        ∀ theta : ℝ, 0 ≤ theta →
          Real.log (∫ omega, Real.exp (-theta * X 1 omega) ∂P) =
            C * theta ^ alpha := by
  intro ha
  have hi := Kyprianou.Ch03.stablePositiveNegativeExpIntegrableV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hh := Kyprianou.Ch03.stablePositiveLogLaplaceHomogeneityV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hn := Kyprianou.Ch03.stablePositiveUnitNonzeroV1 P X hX T hLK
    alpha c hAlpha hC hGaussian hMeasure hStable
  have hs := Kyprianou.Ch03.stableLogLaplaceCoefficientStrictSignV1 P (X 1)
    alpha hAlpha.1 hn (fun theta htheta => hi theta htheta 1) hh
  exact ⟨_, hs.2 ha, hh⟩
