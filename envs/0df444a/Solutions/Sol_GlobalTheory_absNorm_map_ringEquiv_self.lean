-- Prove2me | solution 1 for GlobalTheory.absNorm_map_ringEquiv_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:13.307067+00:00
-- url     : https://prove2.me/submissions/b685e241-c7a7-404b-a37a-aa13a131ea3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_AbsNormSqOfMulConjEqDifferentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (e : R ≃+* R) (J : Ideal R) :
    Ideal.absNorm (J.map e.toRingHom) = Ideal.absNorm J := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv J (J.map e.toRingHom) e rfl).toEquiv).symm
end GlobalTheory
