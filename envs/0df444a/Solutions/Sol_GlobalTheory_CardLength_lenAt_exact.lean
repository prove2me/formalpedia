-- Prove2me | solution 1 for GlobalTheory.CardLength.lenAt_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:32.993807+00:00
-- url     : https://prove2.me/submissions/ad2fb8ae-84bd-4e82-9147-20c190d06679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]
namespace GlobalTheory.CardLength
theorem _root_.solution (w : Ideal R) [w.IsPrime] {N M P : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] (f : N →ₗ[R] M) (g : M →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    lenAt w M = lenAt w N + lenAt w P :=
  Module.length_eq_add_of_exact (LocalizedModule.map w.primeCompl f)
    (LocalizedModule.map w.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)
end GlobalTheory.CardLength
