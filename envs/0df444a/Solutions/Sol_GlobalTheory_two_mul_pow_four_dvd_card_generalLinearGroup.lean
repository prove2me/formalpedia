-- Prove2me | solution 1 for GlobalTheory.two_mul_pow_four_dvd_card_generalLinearGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:52:33.318924+00:00
-- url     : https://prove2.me/submissions/771b61e3-1ddf-46a9-a6ea-878cd0c793b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Theorems.Thm_GlobalTheory_orderOf_transvectionUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [Finite R] (p : ℕ), Odd p → CharP R (p ^ 4) → 1 < p →
      ∀ r : ℕ, 2 ≤ r → 2 * p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
  intro R _ _ p hp hchar h1 r hr
  have hij : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp
  have hq : p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
    rw [← orderOf_transvectionUnit (R := R) (p ^ 4) hij]
    exact orderOf_dvd_natCard _
  have h2 : (2 : R) ≠ 0 := by
    intro h
    have hd : p ^ 4 ∣ 2 := (CharP.cast_eq_zero_iff R (p ^ 4) 2).1 (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by norm_num) hd
    have : 2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h1 4
    omega
  have hneg : orderOf (-1 : GL (Fin r) R) = 2 := by
    apply orderOf_eq_prime
    · simp
    · intro h
      have h' := congrArg (fun u : GL (Fin r) R =>
        (u : Matrix (Fin r) (Fin r) R) ⟨0, by omega⟩ ⟨0, by omega⟩) h
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
      apply h2
      linear_combination -h'
  have h2d : 2 ∣ Nat.card (GL (Fin r) R) := by
    rw [← hneg]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow_right 4 ((Nat.coprime_two_left).2 hp)) h2d hq
end GlobalTheory
