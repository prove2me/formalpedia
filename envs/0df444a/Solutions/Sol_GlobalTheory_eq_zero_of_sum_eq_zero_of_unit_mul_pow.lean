-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_sum_eq_zero_of_unit_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:37:56.763948+00:00
-- url     : https://prove2.me/submissions/1ba55120-e8ea-47a1-b368-4e16020a88ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpan

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
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))
end GlobalTheory
