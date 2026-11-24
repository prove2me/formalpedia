-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:27:35.403386+00:00
-- url     : https://prove2.me/submissions/9cc3cf21-7cc8-4872-8f76-dda6f8d02b98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_forall_affineOpens
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine

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
theorem _root_.solution (p : X ⟶ S) [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] (U : S.Opens) :
    IsIso (p.app U) :=
  isIso_app_of_forall_affineOpens p (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_of_isAffine (p ∣_ V.1)) U
end GlobalTheory.ProperFunctions
