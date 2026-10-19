-- Prove2me | solution 1 for LandauFunction.landau_initial_values
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:30:53.901867+00:00
-- url     : https://prove2.me/submissions/c6658ffd-b054-44be-9227-fedc5b1ba9c0

import Mathlib
import Definitions.Def_LandauFunction_landau
open LandauFunction

namespace LandauPartition

lemma lcm_eq_one_of_le_one (s : Multiset ℕ) (h : ∀ a ∈ s, a ≤ 1) (hpos : ∀ a ∈ s, 0 < a) :
    s.lcm = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [Multiset.lcm_dvd]
  intro b hb
  have : b = 1 := le_antisymm (h b hb) (hpos b hb)
  rw [this]

/-- The partition of `n` attached to a permutation of `Fin n`. -/
def permPartition (n : ℕ) (σ : Equiv.Perm (Fin n)) : Nat.Partition n where
  parts := σ.cycleType + Multiset.replicate (n - σ.support.card) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · exact lt_of_lt_of_le (by norm_num) (Equiv.Perm.two_le_of_mem_cycleType h)
    · rw [Multiset.eq_of_mem_replicate h]; norm_num
  parts_sum := by
    have h1 := Equiv.Perm.sum_cycleType σ
    have h2 : σ.support.card ≤ n := by
      have := Finset.card_le_univ σ.support
      simpa using this
    rw [Multiset.sum_add, h1, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

lemma permPartition_lcm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permPartition n σ).parts.lcm = orderOf σ := by
  simp only [permPartition]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (Multiset.replicate _ 1)
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha])
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; norm_num),
    lcm_one_right, Equiv.Perm.lcm_cycleType]
  exact normalize_eq _

lemma exists_perm (n : ℕ) (p : Nat.Partition n) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = p.parts.lcm := by
  set m := p.parts.filter (fun a => 2 ≤ a) with hm
  have hsum : m.sum ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← p.parts_sum]
    calc m.sum ≤ m.sum + (p.parts.filter (fun a => ¬ 2 ≤ a)).sum := Nat.le_add_right _ _
      _ = p.parts.sum := by rw [← Multiset.sum_add, hm, Multiset.filter_add_not]
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)).mpr
    ⟨hsum, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  refine ⟨σ, ?_⟩
  rw [← Equiv.Perm.lcm_cycleType, hσ]
  conv_rhs => rw [← Multiset.filter_add_not (fun a => 2 ≤ a) p.parts]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (p.parts.filter (fun a => ¬ 2 ≤ a))
    (fun a ha => by have := (Multiset.mem_filter.mp ha).2; omega)
    (fun a ha => p.parts_pos (Multiset.mem_filter.mp ha).1), lcm_one_right]
  exact (normalize_eq _).symm

end LandauPartition

open LandauPartition in
theorem landau_eq_sup (n : ℕ) :
    landau n = (Finset.univ : Finset (Nat.Partition n)).sup fun p => p.parts.lcm := by
  unfold landau
  apply le_antisymm
  · refine Finset.sup_le fun σ _ => ?_
    rw [← permPartition_lcm]
    exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.lcm) (Finset.mem_univ _)
  · refine Finset.sup_le fun p _ => ?_
    obtain ⟨σ, hσ⟩ := exists_perm n p
    rw [← hσ]
    exact Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => orderOf σ) (Finset.mem_univ _)

namespace LandauPartition

/-- Upper bound: the largest lcm of a set of distinct positive integers with sum `≤ n`. -/
def B (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).powerset.filter (fun D => D.sum id ≤ n)).sup (fun D => D.lcm id)

lemma parts_lcm_le_B (n : ℕ) (p : Nat.Partition n) : p.parts.lcm ≤ B n := by
  have hle : p.parts.dedup ≤ p.parts := Multiset.dedup_le _
  obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hle
  have hsum : p.parts.toFinset.sum id ≤ n := by
    refine le_trans ?_ p.parts_sum.le
    rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, Multiset.map_id]
    conv_rhs => rw [ht]
    rw [Multiset.sum_add]; exact Nat.le_add_right _ _
  have hsub : p.parts.toFinset ⊆ Finset.range (n + 1) := by
    intro a ha
    rw [Multiset.mem_toFinset] at ha
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Multiset.le_sum_of_mem ha).trans p.parts_sum.le
  have hl : p.parts.lcm = p.parts.toFinset.lcm id := by
    rw [Finset.lcm_def, Multiset.toFinset_val, Multiset.map_id, Multiset.lcm_dedup]
  rw [hl]
  exact Finset.le_sup (f := fun D : Finset ℕ => D.lcm id)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsum⟩)

lemma landau_le_B (n : ℕ) : landau n ≤ B n := by
  rw [landau_eq_sup]
  exact Finset.sup_le fun p _ => parts_lcm_le_B n p

lemma le_landau (n : ℕ) (l : Multiset ℕ) (h1 : ∀ i ∈ l, 0 < i) (h2 : l.sum = n) :
    l.lcm ≤ landau n := by
  rw [landau_eq_sup]
  exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.lcm)
    (b := ⟨l, fun hi => h1 _ hi, h2⟩) (Finset.mem_univ _)

lemma landau_eq (n v : ℕ) (l : Multiset ℕ) (h1 : ∀ i ∈ l, 0 < i) (h2 : l.sum = n)
    (hl : l.lcm = v) (hB : B n = v) : landau n = v :=
  le_antisymm (hB ▸ landau_le_B n) (hl ▸ le_landau n l h1 h2)

end LandauPartition

open LandauPartition in
set_option maxRecDepth 100000 in
theorem solution :
    landau 0 = 1 ∧ landau 1 = 1 ∧ landau 2 = 2 ∧ landau 3 = 3 ∧ landau 4 = 4 ∧
      landau 5 = 6 ∧ landau 6 = 6 ∧ landau 7 = 12 ∧ landau 8 = 15 := by
  refine ⟨landau_eq 0 1 {} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 1 1 {1} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 2 2 {2} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 3 3 {3} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 4 4 {4} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 5 6 {2, 3} (by simp) (by simp) (by decide) (by decide +kernel),
    landau_eq 6 6 {6} (by simp) (by simp) (by simp) (by decide +kernel),
    landau_eq 7 12 {3, 4} (by simp) (by simp) (by decide) (by decide +kernel),
    landau_eq 8 15 {3, 5} (by simp) (by simp) (by decide) (by decide +kernel)⟩
