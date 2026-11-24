-- Prove2me | solution 1 for GlobalTheory.SplitWeil.continuous_density_volGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:19.908536+00:00
-- url     : https://prove2.me/submissions/11a81826-d6fd-4b73-8c12-2f02d49006a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_isLocallyConstant_nabs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) :=
  (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => ENNReal.ofReal (t ^ (-(Fintype.card n : ℝ))))).continuous
end GlobalTheory.SplitWeil
