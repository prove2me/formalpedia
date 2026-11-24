-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.isIso_appTop_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:12:59.960406+00:00
-- url     : https://prove2.me/submissions/4db52c02-7385-4243-b216-cfdd56f721a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback_of_surjective
import Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAlgClosed

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
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [GeometricallyIntegral p] [UniversallyClosed p] : IsIso p.appTop := by
  let f : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsIntegral (pullback p f) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback p f)
  have := isIso_appTop_of_isAlgClosed (pullback.snd p f)
  have : Surjective f := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  exact isIso_appTop_of_isPullback_of_surjective (.of_hasPullback p f)
end GlobalTheory.ProperFunctions
