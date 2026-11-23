-- Prove2me | solution 1 for GlobalTheory.QCoh.res_self_ring
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:29.655131+00:00
-- url     : https://prove2.me/submissions/f459e44b-2701-4702-97f4-08b2dff3c45d

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
theorem _root_.solution (h : U ≤ U) (s : Γ(X, U)) : X.presheaf.map (homOfLE h).op s = s := by
  have : (homOfLE h).op = 𝟙 (op U) := rfl
  rw [this, X.presheaf.map_id]; rfl
end GlobalTheory.QCoh
