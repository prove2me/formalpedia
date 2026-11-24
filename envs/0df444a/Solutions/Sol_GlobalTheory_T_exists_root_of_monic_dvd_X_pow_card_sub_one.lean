-- Prove2me | solution 1 for GlobalTheory.T.exists_root_of_monic_dvd_X_pow_card_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:09.390625+00:00
-- url     : https://prove2.me/submissions/ca755b6e-9839-4850-90e4-19f77f80fdc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
import Theorems.Thm_GlobalTheory_monic_dvd_X_pow_card_sub_one_exists_root


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] [HenselianLocalRing S] [Finite (ResidueField S)] (f : S[X]), f.Monic → f.natDegree ≠ 0 → f ∣ X ^ (Nat.card (ResidueField S) - 1) - 1 → ∃ y : S, f.eval y = 0 := by
  first | exact @GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | exact GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root | (intros; apply GlobalTheory.monic_dvd_X_pow_card_sub_one_exists_root <;> assumption)
end _root_.GlobalTheory.T
