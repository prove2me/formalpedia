-- Prove2me | solution 1 for GlobalTheory.QCoh.res_res_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:29.399356+00:00
-- url     : https://prove2.me/submissions/40164701-88af-47c3-a90b-3e4369b835ec

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
theorem _root_.solution (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (h'.trans h)).op s := by
  rw [← X.presheaf.map_comp_apply]; rfl
end GlobalTheory.QCoh
