-- Prove2me | solution 1 for GlobalTheory.CardLength.lenAt_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:26.642243+00:00
-- url     : https://prove2.me/submissions/5998edfe-e068-4adb-94be-d28c18b2bc30

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
theorem _root_.solution (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : lenAt w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))
end GlobalTheory.CardLength
