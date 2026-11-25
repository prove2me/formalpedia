-- Prove2me | solution 1 for GlobalTheory.T.log_card_eq_finsum_length_localized_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:26:44.311336+00:00
-- url     : https://prove2.me/submissions/a0678a91-2706-40e3-989b-799e10dcc9ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximalStatement
import Theorems.Thm_GlobalTheory_CardLength_log_card_eq_finsum_length


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] (N : Type) [AddCommGroup N] [Module B N] [Finite N], Real.log (Nat.card N) = ∑ᶠ m : MaximalSpectrum B, ((Module.length (Localization.AtPrime m.asIdeal) (LocalizedModule m.asIdeal.primeCompl N)).toNat : ℝ) * Real.log (Nat.card (B ⧸ m.asIdeal)) := by
  first | exact @GlobalTheory.CardLength.log_card_eq_finsum_length | exact GlobalTheory.CardLength.log_card_eq_finsum_length | (intros; apply GlobalTheory.CardLength.log_card_eq_finsum_length <;> assumption)
end _root_.GlobalTheory.T
