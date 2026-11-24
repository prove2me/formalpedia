-- Prove2me | solution 1 for GlobalTheory.FinWeil.exists_injective_addChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:34.396259+00:00
-- url     : https://prove2.me/submissions/eb59553b-781e-49d5-9920-eb5354e67186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PerfectPairingQuotients
import Theorems.Thm_GlobalTheory_FinWeil_exists_addChar_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution {G K : Type} [AddCommGroup G] [AddCommGroup K] (H : AddSubgroup G)
    (L : AddSubgroup K) (p : G → K → ℂ)
    (hl : ∀ x y z, p (x + y) z = p x z * p y z) (hr : ∀ x y z, p x (y + z) = p x y * p x z)
    (h0 : ∀ x, p x 0 = 1) (h0' : ∀ y, p 0 y = 1)
    (hH : ∀ g, g ∈ H ↔ ∀ k, p g k = 1) (hL : ∀ k ∈ L, ∀ g, p g k = 1) :
    ∃ Φ : G ⧸ H → AddChar (K ⧸ L) ℂ, Function.Injective Φ ∧
      ∀ (g : G) (k : K), Φ (g : G ⧸ H) (k : K ⧸ L) = p g k := by
  choose χ hχ using fun g : G =>
    exists_addChar_quotient L (p g) (h0 g) (hr g) (fun k hk => hL k hk g)
  have hout : ∀ (g : G) (k : K), p (Quotient.out (g : G ⧸ H)) k = p g k := by
    intro g k
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hl, (hH _).1 h.2, mul_one]
  have hΦ : ∀ (g : G) (k : K), χ (Quotient.out (g : G ⧸ H)) (k : K ⧸ L) = p g k := by
    intro g k
    rw [hχ, hout]
  refine ⟨fun q => χ (Quotient.out q), ?_, hΦ⟩
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | _ a
  induction b using QuotientAddGroup.induction_on with | _ b
  rw [QuotientAddGroup.eq, hH]
  intro k
  have h1 : p a k = p b k := by
    rw [← hΦ, ← hΦ]
    exact congrArg (fun ψ : AddChar (K ⧸ L) ℂ => ψ (k : K ⧸ L)) hab
  rw [hl, ← h1, ← hl, neg_add_cancel, h0']
end GlobalTheory.FinWeil
