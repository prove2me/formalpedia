-- Prove2me | solution 1 for GlobalTheory.BruhatRep.a_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:45.894123+00:00
-- url     : https://prove2.me/submissions/4be1a9e9-88a2-47d1-b4a1-64ce26883c92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_det_en

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
variable {M : Type} [Monoid M]
namespace GlobalTheory.BruhatRep
theorem _root_.solution (g : SpecialLinearGroup (Fin 2) K) (hc : en g 1 0 = 0) : en g 0 0 ≠ 0 := by
  intro h; have := det_en g; rw [h, hc] at this; simp at this
end GlobalTheory.BruhatRep
