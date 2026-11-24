-- Prove2me | solution 1 for GlobalTheory.BruhatRep.d_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:57.282544+00:00
-- url     : https://prove2.me/submissions/bfc21786-b89d-4384-b6cc-d18d2e65aac5

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
theorem _root_.solution (g : SpecialLinearGroup (Fin 2) K) (hc : en g 1 0 = 0) : en g 1 1 ≠ 0 := by
  intro h; have := det_en g; rw [h, hc] at this; simp at this
end GlobalTheory.BruhatRep
