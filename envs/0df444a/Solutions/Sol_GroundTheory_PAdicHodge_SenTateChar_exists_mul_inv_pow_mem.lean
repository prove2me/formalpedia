-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.exists_mul_inv_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:57.471203+00:00
-- url     : https://prove2.me/submissions/b3c552a5-1388-4ea9-9ef2-9bb66d7fde54

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_unitsOneAdd_antitone
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_levelHom_eq_one_iff
import Theorems.Thm_GroundTheory_PAdicHodge_SenTateChar_pow_prime_pow_mem_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.SenTateChar
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution {s : ℕ} (hs : 2 ≤ s) {a : ℤ_[p]ˣ} (ha : a ∈ unitsOneAdd p s)
    (ha' : a ∉ unitsOneAdd p (s + 1)) {b : ℤ_[p]ˣ} (hb : b ∈ unitsOneAdd p s) (k : ℕ) :
    ∃ j : ℕ, b * (a ^ j)⁻¹ ∈ unitsOneAdd p k := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    by_cases hks : k + 1 ≤ s
    · exact ⟨0, by simpa using unitsOneAdd_antitone hks hb⟩
    push Not at hks

    obtain ⟨hc, hc'⟩ := pow_prime_pow_mem_not_mem hs ha ha' (k - s)
    rw [Nat.add_sub_cancel' (by omega)] at hc hc'
    have hk1 : 1 ≤ k := by omega
    set c := a ^ p ^ (k - s)
    set d := b * (a ^ j)⁻¹
    set φ := levelHom p k hk1
    have hcφ : Multiplicative.toAdd (φ ⟨c, hc⟩) ≠ 0 := by
      intro h
      exact hc' ((levelHom_eq_one_iff hk1 ⟨c, hc⟩).1
        (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
    set r : ℕ := (Multiplicative.toAdd (φ ⟨d, hj⟩) / Multiplicative.toAdd (φ ⟨c, hc⟩)).val
    refine ⟨j + p ^ (k - s) * r, ?_⟩
    have hmem : d * (c ^ r)⁻¹ ∈ unitsOneAdd p k := mul_mem hj (inv_mem (pow_mem hc r))
    have hφ : φ ⟨d * (c ^ r)⁻¹, hmem⟩ = 1 := by
      have e : (⟨d * (c ^ r)⁻¹, hmem⟩ : unitsOneAdd p k) = ⟨d, hj⟩ * (⟨c, hc⟩ ^ r)⁻¹ := rfl
      rw [e, map_mul, map_inv, map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_one, nsmul_eq_mul]
      simp only [r, ZMod.natCast_val, ZMod.cast_id', id]
      rw [div_mul_cancel₀ _ hcφ, add_neg_cancel]
    have h := (levelHom_eq_one_iff hk1 _).1 hφ
    have e2 : b * (a ^ (j + p ^ (k - s) * r))⁻¹ = d * (c ^ r)⁻¹ := by
      simp only [d, c, pow_add, pow_mul, mul_inv_rev]
      group
    rw [e2]
    exact h
end GroundTheory.PAdicHodge.SenTateChar
