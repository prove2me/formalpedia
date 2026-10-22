-- Prove2me | solution 1 for LNTopology.StarBound.eq_14_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:31:02.312404+00:00
-- url     : https://prove2.me/submissions/768e05d6-d105-43bc-b3c9-7beb12315917

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model

set_option autoImplicit false

open LNTopology.StarBound

section LNSHelpers
variable {c : ℝ → ℝ}

lemma c_abs_eq (hc : IsChannelCost c) (x : ℝ) : c |x| = c x := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, hc.symm]

lemma c_mono_weak (hc : IsChannelCost c) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) : c y ≤ c x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (hc.mono x y hy h).le

lemma c_add_nonneg (hc : IsChannelCost c) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    c (x + y) ≤ c x + c y := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, hc.zero]; simp
  rcases eq_or_lt_of_le hy with h' | h'
  · rw [← h', hc.zero]; simp
  exact (hc.subadd x y h h').le

lemma c_add_le (hc : IsChannelCost c) (x y : ℝ) : c (x + y) ≤ c x + c y := by
  calc c (x + y) = c |x + y| := (c_abs_eq hc _).symm
    _ ≤ c (|x| + |y|) := c_mono_weak hc (abs_nonneg _) (abs_add_le x y)
    _ ≤ c |x| + c |y| := c_add_nonneg hc (abs_nonneg _) (abs_nonneg _)
    _ = c x + c y := by rw [c_abs_eq hc, c_abs_eq hc]

lemma c_sum_le {ι : Type*} (hc : IsChannelCost c) (s : Finset ι) (g : ι → ℝ) :
    c (∑ i ∈ s, g i) ≤ ∑ i ∈ s, c (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hc.zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (c_add_le hc _ _).trans (by linarith)

lemma cost_eq_pos {V : Type*} [Fintype V] (hc : IsChannelCost c) (Λ : V → V → ℝ) (hLN : IsLN Λ) :
    cost c Λ = ∑ i, ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) := by
  have h1 : ∑ i, ∑ j, c (Λ i j) =
      ∑ i, ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) +
      ∑ i, ∑ j, (if Λ i j < 0 then c (Λ i j) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rcases lt_trichotomy (Λ i j) 0 with h | h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, hc.zero]
    · simp [h, not_lt.mpr h.le]
  have h2 : ∑ i, ∑ j, (if Λ i j < 0 then c (Λ i j) else 0) =
      ∑ i, ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have e : Λ j i = - Λ i j := hLN j i
    simp only [e, neg_lt_zero, hc.symm]
  unfold cost
  rw [h1, h2]; ring

end LNSHelpers

section LNSHelpers2
variable {c : ℝ → ℝ}

lemma pos_bound {V : Type*} [Fintype V] (hc : IsChannelCost c) (f : V → ℝ) (Λ : V → V → ℝ)
    (hLN : IsLN Λ) (hΛ : Supports Λ f) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i) ≤ cost c Λ := by
  classical
  rw [cost_eq_pos hc Λ hLN]
  have hrow : ∀ i, 0 < f i → c (f i) ≤ ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) := by
    intro i hi
    set T := ∑ j, (if 0 < Λ i j then Λ i j else 0) with hT
    have h1 : f i ≤ T := by
      rw [← hΛ i, hT]
      exact Finset.sum_le_sum (fun j _ => by
        by_cases h : 0 < Λ i j
        · simp [h]
        · simp [h]; exact not_lt.mp h)
    have h2 : c (f i) ≤ c T := c_mono_weak hc hi.le h1
    have h3 := c_sum_le hc Finset.univ (fun j => if 0 < Λ i j then Λ i j else 0)
    refine h2.trans (h3.trans (le_of_eq (Finset.sum_congr rfl (fun j _ => ?_))))
    by_cases h : 0 < Λ i j
    · simp [h]
    · simp [h, hc.zero]
  calc ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) :=
        Finset.sum_le_sum (fun i hi => hrow i (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, ∑ j, (if 0 < Λ i j then c (Λ i j) else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact Finset.sum_nonneg (fun j _ => by
          by_cases h : 0 < Λ i j
          · simp [h, hc.nonneg]
          · simp [h])

lemma neg_bound {V : Type*} [Fintype V] (hc : IsChannelCost c) (f : V → ℝ) (Λ : V → V → ℝ)
    (hLN : IsLN Λ) (hΛ : Supports Λ f) :
    ∑ i ∈ Finset.univ.filter (fun i => f i < 0), c (f i) ≤ cost c Λ := by
  classical
  have hLN' : IsLN (fun i j => - Λ i j) := fun u v => by simp [hLN u v]
  have hΛ' : Supports (fun i j => - Λ i j) (fun i => - f i) := fun i => by
    simp [Finset.sum_neg_distrib, hΛ i]
  have := pos_bound hc (fun i => - f i) (fun i j => - Λ i j) hLN' hΛ'
  have hcost : cost c (fun i j => - Λ i j) = cost c Λ := by
    unfold cost; simp [hc.symm]
  rw [hcost] at this
  refine le_trans (le_of_eq ?_) this
  apply Finset.sum_congr
  · ext i; simp
  · intro i _; rw [hc.symm]

end LNSHelpers2

theorem solution {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c) (f : V → ℝ)
    (Λ : V → V → ℝ) (hLN : IsLN Λ) (hΛ : Supports Λ f) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i) ≤ cost c Λ ∧
      ∑ i ∈ Finset.univ.filter (fun i => f i < 0), c (f i) ≤ cost c Λ :=
  ⟨pos_bound hc f Λ hLN hΛ, neg_bound hc f Λ hLN hΛ⟩
