-- Prove2me | solution 1 for GlobalTheory.card_pow_eq_one_two_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:36:08.983692+00:00
-- url     : https://prove2.me/submissions/bd9c196b-f2fb-4eea-889e-0b9559409e0e

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPowEqOneLeOfIsCyclicUnits
import Theorems.Thm_GlobalTheory_card_pow_eq_one_le_index_mul
import Theorems.Thm_GlobalTheory_card_pow_eq_one_le_units
import Theorems.Thm_GlobalTheory_card_pow_eq_one_le_of_isCyclic_units

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
theorem _root_.solution (w : ℕ) (hw : 1 ≤ w) {d : ℕ} (hd : 0 < d) :
    Nat.card {x : ZMod (2 ^ w) // x ^ d = 1} ≤ 2 * d := by
  have : NeZero (2 ^ w) := ⟨by positivity⟩
  obtain _ | _ | n := w
  · omega
  ·
    have : IsCyclic (ZMod (2 ^ 1))ˣ := (ZMod.isCyclic_units_two_pow_iff 1).mpr (by norm_num)
    exact (card_pow_eq_one_le_of_isCyclic_units _ hd).trans (by omega)
  ·
    let u : (ZMod (2 ^ (n + 2)))ˣ :=
      ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by norm_num))
    have hu : orderOf u = 2 ^ n := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, ZMod.orderOf_five]
    have hG : Nat.card (ZMod (2 ^ (n + 2)))ˣ = 2 ^ n * 2 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (by omega)]
      simp [pow_succ]
    have hidx : (Subgroup.zpowers u).index = 2 := by
      have h := (Subgroup.zpowers u).card_mul_index
      rw [Nat.card_zpowers, hu, hG] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    calc Nat.card {x : ZMod (2 ^ (n + 2)) // x ^ d = 1}
        ≤ Nat.card {x : (ZMod (2 ^ (n + 2)))ˣ // x ^ d = 1} := card_pow_eq_one_le_units hd
      _ ≤ (Subgroup.zpowers u).index * d := card_pow_eq_one_le_index_mul _ hd
      _ = 2 * d := by rw [hidx]
end GlobalTheory
