-- Prove2me | solution 1 for JuschenkoMonod.invariantMean_subset_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:38:50.977642+00:00
-- url     : https://prove2.me/submissions/eb03c2d6-6c17-4e84-9533-3733c0935f86

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod

open scoped ENNReal Pointwise

namespace JuschenkoMonod

theorem invariantMean_subset_eq_one_dev (m : Set (Finset ℤ) → ℝ≥0∞)
    (hm : IsInvariantMean (IntervalExchange.wobbling ℤ) m) (h0 : m {E | 0 ∈ E} = 1)
    (E₀ : Finset ℤ) : m {E | E₀ ⊆ E} = 1 := by
  obtain ⟨⟨hm0, hadd⟩, hu, hinv⟩ := hm
  have mono : ∀ S T : Set (Finset ℤ), S ⊆ T → m S ≤ m T := by
    intro S T h
    have := hadd S (T \ S) Set.disjoint_sdiff_right
    rw [Set.union_sdiff_cancel h] at this
    rw [this]; exact le_self_add
  have compl0 : ∀ S : Set (Finset ℤ), m S = 1 → m Sᶜ = 0 := by
    intro S hS
    have := hadd S Sᶜ disjoint_compl_right
    rw [Set.union_compl_self, hu, hS] at this
    have h1 : (1 : ℝ≥0∞) + m Sᶜ = 1 + 0 := by rw [← this]; simp
    exact (ENNReal.add_right_inj (by simp)).1 h1
  have union0 : ∀ S T : Set (Finset ℤ), m S = 0 → m T = 0 → m (S ∪ T) = 0 := by
    intro S T hS hT
    have := hadd S (T \ S) Set.disjoint_sdiff_right
    have hle : m (T \ S) ≤ m T := mono _ _ Set.sdiff_subset
    have : m (S ∪ T) = m S + m (T \ S) := by
      rw [← hadd S (T \ S) Set.disjoint_sdiff_right, Set.union_sdiff_self]
    rw [this, hS]
    have : m (T \ S) = 0 := le_antisymm (hT ▸ hle) zero_le
    simp [this]
  have inter1 : ∀ S T : Set (Finset ℤ), m S = 1 → m T = 1 → m (S ∩ T) = 1 := by
    intro S T hS hT
    have h := union0 _ _ (compl0 S hS) (compl0 T hT)
    rw [← Set.compl_inter] at h
    have := hadd (S ∩ T) (S ∩ T)ᶜ disjoint_compl_right
    rw [Set.union_compl_self, hu, h, add_zero] at this
    exact this.symm
  -- translates
  have hshift : ∀ e : ℤ, m {E | e ∈ E} = 1 := by
    intro e
    let g : IntervalExchange.wobbling ℤ := ⟨Equiv.addRight e, ⟨|(e : ℝ)|, fun x => by
      simp [Int.norm_eq_abs]⟩⟩
    have := hinv g {E | 0 ∈ E}
    rw [h0] at this
    rw [← this]
    congr 1
    ext E
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      Finset.mem_inv_smul_finset_iff]
    show e ∈ E ↔ (0 + e) ∈ E
    simp
  induction E₀ using Finset.induction_on with
  | empty => simpa using hu
  | insert a s ha ih =>
    have : {E : Finset ℤ | insert a s ⊆ E} = {E | a ∈ E} ∩ {E | s ⊆ E} := by
      ext E; simp [Finset.insert_subset_iff]
    rw [this]
    exact inter1 _ _ (hshift a) ih

end JuschenkoMonod

theorem solution : type_of% @JuschenkoMonod.invariantMean_subset_eq_one_dev := @JuschenkoMonod.invariantMean_subset_eq_one_dev
