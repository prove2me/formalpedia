-- Prove2me | solution 1 for GlobalTheory.QCoh.stalkModuleSections_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:53.262417+00:00
-- url     : https://prove2.me/submissions/c57f8d45-e685-4069-bec3-b3a2c8ee83fe

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
theorem _root_.solution (x : U) (r : Γ(X, U)) (t : (F.presheaf.stalk (x : X) :)) :
    r • t = X.presheaf.germ U x x.2 r • t := rfl
end GlobalTheory.QCoh
