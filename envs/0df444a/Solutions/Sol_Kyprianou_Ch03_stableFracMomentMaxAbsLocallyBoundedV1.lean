-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentMaxAbsLocallyBoundedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:47:02.534429+00:00
-- url     : https://prove2.me/submissions/05b2ec61-2231-4105-a77b-04e20053a4ed

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (eta : Real) (heta : 0 < eta) :
    ∀ R : Real, 0 ≤ R → ∃ M : Real, ∀ x : Real, |x| ≤ R →
      (max |x| 1) ^ eta ≤ M := by
  intro R hR
  refine ⟨(max R 1) ^ eta, fun x hx => ?_⟩
  exact Real.rpow_le_rpow (le_trans (abs_nonneg _) (le_max_left _ _))
    (max_le_max hx le_rfl) heta.le
