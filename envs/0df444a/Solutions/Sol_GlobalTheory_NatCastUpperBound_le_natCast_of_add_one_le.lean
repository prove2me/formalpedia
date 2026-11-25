-- Prove2me | solution 1 for GlobalTheory.NatCastUpperBound.le_natCast_of_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:07.482961+00:00
-- url     : https://prove2.me/submissions/12a227f3-07f9-4329-b71a-4ec177fe765c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeNatCastOfAddOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastUpperBound
namespace GlobalTheory.NatCastUpperBound
theorem _root_.solution {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (1 : WithBot ℕ∞) ≤ (↑(n + (1 : ℕ)) : WithBot ℕ∞)) :
    a ≤ (↑n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, top_le_iff] at h
      exact ENat.coe_ne_top _ h
    | coe m =>
      have h1 : ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      have h3 : ((n : ℕ) : WithBot ℕ∞) = (((n : ℕ) : ℕ∞) : WithBot ℕ∞) := rfl
      rw [h1, h2, WithBot.coe_le_coe, ENat.coe_le_coe] at h
      rw [h3, WithBot.coe_le_coe, ENat.coe_le_coe]
      omega
end GlobalTheory.NatCastUpperBound
