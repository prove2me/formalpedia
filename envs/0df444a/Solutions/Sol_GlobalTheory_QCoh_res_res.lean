-- Prove2me | solution 1 for GlobalTheory.QCoh.res_res
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:28.541674+00:00
-- url     : https://prove2.me/submissions/ccce7f99-d1d5-41ea-8213-458e1aca691f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine

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
theorem _root_.solution (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h').op (F.presheaf.map (homOfLE h).op s) =
      F.presheaf.map (homOfLE (h'.trans h)).op s := by
  rw [← F.presheaf.map_comp_apply]; rfl
end GlobalTheory.QCoh
