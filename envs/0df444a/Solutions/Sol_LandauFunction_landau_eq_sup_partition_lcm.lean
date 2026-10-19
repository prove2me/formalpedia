-- Prove2me | solution 1 for LandauFunction.landau_eq_sup_partition_lcm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:28:38.198835+00:00
-- url     : https://prove2.me/submissions/ce9b2379-a1c8-4288-a123-6969a3f929b3

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
theorem solution (n : ℕ) :
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
