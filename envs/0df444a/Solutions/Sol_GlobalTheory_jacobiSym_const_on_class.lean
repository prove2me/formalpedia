-- Prove2me | solution 1 for GlobalTheory.jacobiSym_const_on_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:48.742965+00:00
-- url     : https://prove2.me/submissions/2cd4e31d-ad77-4230-bb70-24de71f3255a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JacobiSymEqOfModEqFourMul
import Theorems.Thm_GlobalTheory_jacobiSym_eq_of_modEq_four_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : Formalism.HermitianLattices.GL2a2.ClassConst := by
  intro m₀ d q q' h8 hd hsq hq hq' hqq
  have h4 : 4 ∣ m₀ := Dvd.dvd.trans (by norm_num) h8
  have key : ∀ e : ℕ, Odd e → e ∣ m₀ → jacobiSym (e : ℤ) q = jacobiSym (e : ℤ) q' := by
    intro e he hem
    have hc : Nat.Coprime 4 e := by
      have h2 : Nat.Coprime 2 e := Nat.coprime_two_left.mpr he
      simpa using Nat.Coprime.pow_left 2 h2
    exact jacobiSym_eq_of_modEq_four_mul e q q' hq hq'
      (hqq.of_dvd (hc.mul_dvd_of_dvd_of_dvd h4 hem))
  rcases Nat.even_or_odd d with hev | hodd
  · obtain ⟨e, rfl⟩ := hev.two_dvd
    have he : Odd e := by
      rcases Nat.even_or_odd e with h | h
      · obtain ⟨f, rfl⟩ := h.two_dvd
        have : IsUnit (2 : ℕ) := hsq 2 ⟨f, by ring⟩
        simp at this
      · exact h
    have h2 := jacobiSym_eq_of_modEq_four_mul 2 q q' hq hq' (hqq.of_dvd h8)
    have he' := key e he (Dvd.dvd.trans (Dvd.intro_left 2 rfl) hd)
    rw [Nat.cast_mul, jacobiSym.mul_left, jacobiSym.mul_left, h2, he']
  · exact key d hodd hd
end GlobalTheory
