-- Prove2me | solution 1 for GlobalTheory.HerbrandLength.loc_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:47.332951+00:00
-- url     : https://prove2.me/submissions/c2a3a0a2-6de2-47db-892c-2d3a88869d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]
namespace GlobalTheory.HerbrandLength
theorem _root_.solution (p : Ideal A) [p.IsPrime] {N M Q : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup M] [Module A M] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] M) (g : M →ₗ[A] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl N) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
  Module.length_eq_add_of_exact (LocalizedModule.map p.primeCompl f)
    (LocalizedModule.map p.primeCompl g) (LocalizedModule.map_injective _ f hf)
    (LocalizedModule.map_surjective _ g hg) (LocalizedModule.map_exact _ f g H)
end GlobalTheory.HerbrandLength
