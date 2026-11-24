-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:54:13.737678+00:00
-- url     : https://prove2.me/submissions/dfa592ff-ced4-4f55-b347-a92fd4fdf337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_isBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution (p : X ⟶ S)
    (h : ∀ U : S.affineOpens, IsIso (p ∣_ U.1).appTop) (U : S.Opens) : IsIso (p.app U) :=
  isIso_app_of_isBasis p (fun U : S.affineOpens ↦ U.1) (by simpa using S.isBasis_affineOpens) h U
end GlobalTheory.ProperFunctions
