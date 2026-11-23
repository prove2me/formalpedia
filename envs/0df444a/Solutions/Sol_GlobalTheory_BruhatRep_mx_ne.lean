-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:01.718027+00:00
-- url     : https://prove2.me/submissions/4d76f929-be4c-42fd-a34b-9e528a2da782

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
variable {M : Type} [Monoid M]
namespace GlobalTheory.BruhatRep
theorem _root_.solution (m : Kˣ → M) {x : K} (hx : x ≠ 0) : mx m x = m (Units.mk0 x hx) := by
  unfold mx; rw [dif_neg hx]
end GlobalTheory.BruhatRep
