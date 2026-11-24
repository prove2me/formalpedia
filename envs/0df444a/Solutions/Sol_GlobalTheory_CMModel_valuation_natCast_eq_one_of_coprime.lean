-- Prove2me | solution 1 for GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:04:04.385121+00:00
-- url     : https://prove2.me/submissions/740c4867-1c7d-4655-a76a-f8f509b7a626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuationNatCastEqOneOfCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMModel
namespace GlobalTheory.CMModel
theorem _root_.solution (V : ValuationSubring ℂ) (a b : ℕ)
    (h : Nat.Coprime a b) :
    V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  have hint : ∀ z : ℤ, V.valuation (z : ℂ) ≤ 1 := fun z =>
    (V.valuation_le_one_iff _).2 (intCast_mem V z)
  have hnat : ∀ n : ℕ, V.valuation (n : ℂ) ≤ 1 := fun n =>
    (V.valuation_le_one_iff _).2 (natCast_mem V n)
  by_contra hcon
  rw [not_or] at hcon
  have ha : V.valuation (a : ℂ) < 1 := lt_of_le_of_ne (hnat a) hcon.1
  have hb : V.valuation (b : ℂ) < 1 := lt_of_le_of_ne (hnat b) hcon.2
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.2 h
  have hC : (x : ℂ) * (a : ℂ) + (y : ℂ) * (b : ℂ) = 1 := by exact_mod_cast hxy
  have h1 : V.valuation ((x : ℂ) * (a : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint x)) ha
  have h2 : V.valuation ((y : ℂ) * (b : ℂ)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint y)) hb
  have h3 := V.valuation.map_add_lt h1 h2
  rw [hC, map_one] at h3
  exact lt_irrefl _ h3
end GlobalTheory.CMModel
