-- Prove2me | solution 1 for GlobalTheory.BruhatRep.en_nS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:58.921064+00:00
-- url     : https://prove2.me/submissions/af23219d-1a80-4236-95ec-90227ab4c047

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
theorem _root_.solution (z : K) : en (nS z) 0 0 = 1 ∧ en (nS z) 0 1 = z ∧ en (nS z) 1 0 = 0 ∧ en (nS z) 1 1 = 1 := by
  simp [en, nS]
end GlobalTheory.BruhatRep
