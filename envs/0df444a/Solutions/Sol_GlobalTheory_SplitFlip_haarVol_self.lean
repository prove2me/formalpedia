-- Prove2me | solution 1 for GlobalTheory.SplitFlip.haarVol_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:55:55.049402+00:00
-- url     : https://prove2.me/submissions/4408b4f8-70a8-4102-9ec9-84031a2f0d78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {J : Subgroup (GL n k)} (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    haarVol J J = 1 := by
  have h := haar_ne_zero_ne_top Measure.haar ho hK
  simp [haarVol, ENNReal.inv_mul_cancel h.1 h.2]
end GlobalTheory.SplitFlip
