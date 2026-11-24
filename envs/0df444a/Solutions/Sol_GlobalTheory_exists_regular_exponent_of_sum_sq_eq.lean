-- Prove2me | solution 1 for GlobalTheory.exists_regular_exponent_of_sum_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:59.640848+00:00
-- url     : https://prove2.me/submissions/d74b9a40-56db-4e5f-a5c7-3bf58b02700b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularExponentOfSumSqEq

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
theorem _root_.solution :
    ∀ (q d : ℕ) (a : ℕ → ℤ), 2 ≤ q → 0 < d →
      (∀ k l i : ℕ, k * q ^ i ≡ l [MOD q ^ d - 1] → a k = a l) →
      ∑ k ∈ Finset.range (q ^ d - 1), a k ^ 2 = d →
      (∀ s e l : ℕ, s * e = d → l * q ^ e ≡ l [MOD q ^ d - 1] → (s : ℤ) ∣ a l) →
      ∃ k : ℕ, a k ≠ 0 ∧ ∀ i : ℕ, 0 < i → i < d → ¬ k * q ^ i ≡ k [MOD q ^ d - 1] := by
  classical
  intro q d a hq hd hinv hsum hdiv
  have h1 : 1 < q ^ d := Nat.one_lt_pow hd.ne' (by omega)
  have hN : 0 < q ^ d - 1 := by omega
  have hqd : q ^ d ≡ 1 [MOD q ^ d - 1] :=
    ((Nat.modEq_iff_dvd' h1.le).2 dvd_rfl).symm
  generalize q ^ d - 1 = N at *
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hsum
    omega
  refine ⟨k, hk, fun i hi hid hki => ?_⟩
  have hex : ∃ e, 0 < e ∧ k * q ^ e ≡ k [MOD N] := ⟨i, hi, hki⟩
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ i := Nat.find_min' hex ⟨hi, hki⟩
  have hmin : ∀ m, 0 < m → m < Nat.find hex → ¬ k * q ^ m ≡ k [MOD N] :=
    fun m hm hlt h => Nat.find_min hex hlt ⟨hm, h⟩
  generalize Nat.find hex = e at hspec hle hmin
  obtain ⟨he, hke⟩ := hspec
  have hmul : ∀ m, k * q ^ (e * m) ≡ k [MOD N] := by
    intro m
    induction m with
    | zero => simp [Nat.ModEq]
    | succ m ih =>
      have : k * q ^ (e * (m + 1)) = k * q ^ (e * m) * q ^ e := by ring
      rw [this]
      exact (ih.mul_right _).trans hke
  have hmod : d % e = 0 := by
    by_contra h
    apply hmin (d % e) (Nat.pos_of_ne_zero h) (Nat.mod_lt _ he)
    have h2 : k * q ^ d = k * q ^ (e * (d / e)) * q ^ (d % e) := by
      rw [mul_assoc, ← pow_add, Nat.div_add_mod]
    have h3 : k * q ^ d ≡ k [MOD N] := by simpa using hqd.mul_left k
    rw [h2] at h3
    exact ((hmul (d / e)).mul_right _).symm.trans h3
  obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s ≤ 1 := by omega
    have : e * s ≤ e * 1 := Nat.mul_le_mul_left _ this
    omega
  have hdv : (s : ℤ) ∣ a k := hdiv s e k (by rw [hs, mul_comm]) hke
  have hsq : (s : ℤ) ^ 2 ≤ a k ^ 2 :=
    Int.le_of_dvd (by positivity) (pow_dvd_pow_of_dvd hdv 2)
  have key : ∀ i j, i < j → j < e → ¬ k * q ^ i ≡ k * q ^ j [MOD N] := by
    intro i j hij hj h
    apply hmin (i + (e - j)) (by omega) (by omega)
    have h2 := h.mul_right (q ^ (e - j))
    rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, Nat.add_sub_cancel' hj.le] at h2
    exact h2.trans hke
  have hinj : Set.InjOn (fun i => k * q ^ i % N) (Finset.range e : Set ℕ) := by
    intro i hi j hj h
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (key i j h' hj)
    · exact h'
    · exact absurd (Eq.symm h) (key j i h' hi)
  have hsub : (Finset.range e).image (fun i => k * q ^ i % N) ⊆ Finset.range N := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hN)
  have hle2 := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => a k ^ 2) hsub
    (fun _ _ _ => by positivity)
  rw [Finset.sum_image hinj, hsum] at hle2
  have heq : ∑ i ∈ Finset.range e, a (k * q ^ i % N) ^ 2 = (e : ℤ) * a k ^ 2 := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [← hinv k _ i (Nat.mod_modEq _ _).symm])]
    simp
  rw [heq, hs] at hle2
  push_cast at hle2
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hs' : (2 : ℤ) ≤ s := by exact_mod_cast hs2
  have := le_of_mul_le_mul_left hle2 he'
  nlinarith
end GlobalTheory
