-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:48.129799+00:00
-- url     : https://prove2.me/submissions/8790d110-d3b2-4bef-bbaf-fc47c188fc38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_forall_affineOpens
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_baseChange_of_field

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
theorem _root_.solution {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}
    {f : T ⟶ Spec (.of k)} {g : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback g q p f)
    [GeometricallyIntegral p] [UniversallyClosed p] [QuasiSeparated p] (U : T.Opens) :
    IsIso (q.app U) :=
  isIso_app_of_forall_affineOpens q (fun V ↦
    have : IsAffine V.1 := V.2
    isIso_appTop_baseChange_of_field ((isPullback_morphismRestrict q V.1).flip.paste_horiz H)) U
end GlobalTheory.ProperFunctions
