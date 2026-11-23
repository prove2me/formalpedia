-- Prove2me | solution 1 for GlobalTheory.QCoh.resBasicOpen_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:27.224648+00:00
-- url     : https://prove2.me/submissions/639cb597-ce86-47f4-8d03-4f0ed61649e1

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
theorem _root_.solution (f : Γ(X, U)) (s : Γ(F, U)) :
    resBasicOpen F f s = F.presheaf.map (homOfLE (X.basicOpen_le f)).op s := rfl
end GlobalTheory.QCoh
