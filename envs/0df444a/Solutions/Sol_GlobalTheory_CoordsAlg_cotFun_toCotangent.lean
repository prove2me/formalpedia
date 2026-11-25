-- Prove2me | solution 1 for GlobalTheory.CoordsAlg.cotFun_toCotangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:15.37797+00:00
-- url     : https://prove2.me/submissions/b03a360c-399d-4b35-9b66-a7d4dbd1e195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationFamilyCotangentBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoordsAlg
namespace GlobalTheory.CoordsAlg
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) (x : I) :
    cotFun I f hf (I.toCotangent x) = f x := rfl
end GlobalTheory.CoordsAlg
