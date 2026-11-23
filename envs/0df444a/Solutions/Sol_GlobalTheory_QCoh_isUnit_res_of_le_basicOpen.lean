-- Prove2me | solution 1 for GlobalTheory.QCoh.isUnit_res_of_le_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:46.323621+00:00
-- url     : https://prove2.me/submissions/a390a8e6-fa8b-4b83-ae26-31d6bd67b512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Theorems.Thm_GlobalTheory_QCoh_res_res_ring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (f : Γ(X, U)) (h : V ≤ U) (hV : V ≤ X.basicOpen f) :
    IsUnit (X.presheaf.map (homOfLE h).op f) := by
  rw [← res_res_ring (X.basicOpen_le f) hV]
  exact (X.toRingedSpace.isUnit_res_basicOpen f).map _
end GlobalTheory.QCoh
