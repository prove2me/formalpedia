-- Prove2me | solution 1 for GlobalTheory.T.teichmuller_distinguished_regular_sequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:49.251443+00:00
-- url     : https://prove2.me/submissions/8dbad7b9-7f9f-4175-a301-47d894c4b427

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TeichmullerDistinguishedRegularSequence
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TeichmullerDistinguishedRegularSequenceStatement
import Theorems.Thm_GlobalTheory_teichmuller_distinguished_regular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  first | exact @GlobalTheory.teichmuller_distinguished_regular | exact GlobalTheory.teichmuller_distinguished_regular | (intros; apply GlobalTheory.teichmuller_distinguished_regular <;> assumption)
end _root_.GlobalTheory.T
