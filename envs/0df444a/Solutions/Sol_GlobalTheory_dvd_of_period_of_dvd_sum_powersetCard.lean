-- Prove2me | solution 1 for GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:35:58.258853+00:00
-- url     : https://prove2.me/submissions/34c6b00f-ea00-45bc-a249-bd963a22342b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_card_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_sum_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_iff_mem_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_pow_mod_modEq
import Theorems.Thm_GlobalTheory_PeriodDvd_sum_vadd_modEq
import Theorems.Thm_GlobalTheory_PeriodDvd_vadd_killed_subset
import Theorems.Thm_GlobalTheory_PeriodDvd_card_stabilizer_dvd
import Theorems.Thm_GlobalTheory_PeriodDvd_le_card_stabilizer_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_sum_finset_zmod
import Theorems.Thm_GlobalTheory_PeriodDvd_exists_eq_mul_geom
import Theorems.Thm_GlobalTheory_card_dvd_sum_of_invariant_of_card_stabilizer_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open PeriodDvd
namespace GlobalTheory
theorem _root_.solution (q d : ℕ) (a : ℕ → ℤ) (hq : 2 ≤ q) (hd : 0 < d)
    (hinv : ∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l)
    (hsum : ∀ k s : ℕ, (d : ℤ) ∣ ∑ I ∈ (Finset.range d).powersetCard s, a (k * ∑ i ∈ I, q ^ i))
    (s e l : ℕ) (hse : s * e = d) (hl : l * q ^ e ≡ l [MOD q ^ d - 1]) : (s : ℤ) ∣ a l := by
  classical
  haveI : NeZero d := ⟨hd.ne'⟩
  have hq1 : 1 ≤ q := by omega
  induction s using Nat.strong_induction_on generalizing e l with
  | _ s ih =>
  have hs : 0 < s := Nat.pos_of_mul_pos_right (hse ▸ hd)
  obtain ⟨k, hk⟩ := exists_eq_mul_geom hq hd hse hl
  rw [← sum_killed hse] at hk
  set h : Finset (ZMod d) → ℤ :=
    fun I => if I.card = s then a (k * ∑ x ∈ I, q ^ x.val) else 0 with hh
  have hmod : ∀ (g : ZMod d) (I : Finset (ZMod d)),
      (k * ∑ x ∈ I, q ^ x.val) * q ^ g.val ≡ k * ∑ x ∈ g +ᵥ I, q ^ x.val [MOD q ^ d - 1] := by
    intro g I
    rw [mul_assoc]
    exact (sum_vadd_modEq q hq1 g I).mul_left k
  have hhinv : ∀ (g : ZMod d) (I : Finset (ZMod d)), h (g +ᵥ I) = h I := by
    intro g I
    simp only [hh, Finset.card_vadd_finset]
    rw [hinv _ _ _ (hmod g I)]
  have htot : (d : ℤ) ∣ ∑ I, h I := by
    have := sum_finset_zmod (d := d) s (fun n => a (k * n)) q
    rw [hh, this]
    exact hsum k s
  set O := AddAction.orbit (ZMod d) (killed d s) with hO
  have hoff : (d : ℤ) ∣ ∑ I, (if I ∈ O then 0 else h I) := by
    have := card_dvd_sum_of_invariant_of_card_stabilizer_dvd (ZMod d) (Finset (ZMod d))
      (fun I => if I ∈ O then 0 else h I) ?_ ?_
    · rwa [Nat.card_zmod] at this
    · intro g I
      have : g +ᵥ I ∈ O ↔ I ∈ O := by
        constructor
        · intro hg
          have := AddAction.mem_orbit_of_mem_orbit (-g) hg
          simpa using this
        · exact fun hI => AddAction.mem_orbit_of_mem_orbit g hI
      simp only [this, hhinv]
    · intro I
      by_cases hI : I ∈ O
      · simp [hI]
      simp only [hI, if_false]
      by_cases hc : I.card = s
      swap
      · simp [hh, hc]
      obtain ⟨x, hx⟩ : I.Nonempty := Finset.card_pos.mp (hc ▸ hs)
      obtain ⟨e', he'⟩ := card_stabilizer_dvd I
      have hsub := vadd_killed_subset I hx
      have hle := Finset.card_le_card hsub
      rw [Finset.card_vadd_finset, card_killed he'.symm, hc] at hle
      rcases hle.lt_or_eq with hlt | heq
      · simp only [hh, hc, if_true]
        refine ih _ hlt e' _ he'.symm ?_
        have hmem : (e' : ZMod d) +ᵥ I = I := by
          refine (mem_iff_mem_killed (AddAction.stabilizer (ZMod d) I) _).mpr ?_
          rw [mem_killed, nsmul_eq_mul, ← Nat.cast_mul, ← he', ZMod.natCast_self]
        have h1 := hmod (e' : ZMod d) I
        rw [hmem, ZMod.val_natCast] at h1
        exact ((pow_mod_modEq q d e' hq1).mul_left _).symm.trans h1
      · exfalso
        apply hI
        rw [heq] at hsub
        have := Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_vadd_finset, card_killed hse, hc])
        exact ⟨x, this⟩
  have hon : ∑ I, (if I ∈ O then h I else 0) = (Nat.card O : ℤ) * a l := by
    rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ => a l), Finset.sum_const,
      nsmul_eq_mul]
    · congr 2
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
    · intro I hI
      obtain ⟨g, rfl⟩ : I ∈ O := (Finset.mem_filter.mp hI).2
      change h (g +ᵥ killed d s) = _
      rw [hhinv]
      simp only [hh, card_killed hse, if_true, hk]
  have hsplit : ∑ I, h I = ∑ I, (if I ∈ O then h I else 0) + ∑ I, (if I ∈ O then 0 else h I) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp
  rw [hsplit, hon] at htot
  have h1 : (d : ℤ) ∣ (Nat.card O : ℤ) * a l := (dvd_add_left hoff).mp htot
  have hG : d = Nat.card O * Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) := by
    rw [hO, Nat.card_congr (AddAction.orbitEquivQuotientStabilizer (ZMod d) (killed d s)),
      ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup, Nat.card_zmod]
  have hO0 : (Nat.card O : ℤ) ≠ 0 := by
    intro h0
    have : Nat.card O = 0 := by exact_mod_cast h0
    rw [this, zero_mul] at hG
    omega
  have h2 : (Nat.card O : ℤ) * (Nat.card (AddAction.stabilizer (ZMod d) (killed d s)) : ℤ)
      ∣ (Nat.card O : ℤ) * a l := by
    rw [← Nat.cast_mul, ← hG]; exact h1
  exact (Int.natCast_dvd_natCast.mpr (le_card_stabilizer_killed hse)).trans
    ((mul_dvd_mul_iff_left hO0).mp h2)
end GlobalTheory
