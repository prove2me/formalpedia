-- Prove2me | solution 1 for GlobalTheory.BruhatRep.en_wS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:59.873817+00:00
-- url     : https://prove2.me/submissions/6a1375ed-f390-4a9f-9c2a-b11ab0ff82d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
namespace GlobalTheory.BruhatRep
theorem _root_.solution : en (wS K) 0 0 = 0 ∧ en (wS K) 0 1 = 1 ∧ en (wS K) 1 0 = -1 ∧ en (wS K) 1 1 = 0 := by
  simp [en, wS]
end GlobalTheory.BruhatRep
