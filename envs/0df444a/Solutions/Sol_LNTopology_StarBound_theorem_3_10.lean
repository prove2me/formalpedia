-- Prove2me | solution 1 for LNTopology.StarBound.theorem_3_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:41:11.556668+00:00
-- url     : https://prove2.me/submissions/4b8dd6b3-1f71-4bbf-9c25-0b7d6332909e

import Mathlib
import Definitions.Def_LNTopology_StarBound_Model
import Definitions.Def_LNTopology_StarBound_MinCost
import Definitions.Def_LNTopology_Local_Star

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

section LNSStar
variable {c : ℝ → ℝ}

lemma star_props {V : Type*} [Fintype V] [DecidableEq V] (hc : IsChannelCost c) (f : V → ℝ)
    (hf : ∑ i, f i = 0) (h : V) :
    IsLN (LNTopology.Local.star f h) ∧ Supports (LNTopology.Local.star f h) f ∧
      cost c (LNTopology.Local.star f h) = ∑ i, c (f i) - c (f h) := by
  have hLN : IsLN (LNTopology.Local.star f h) := by
    intro u v
    unfold LNTopology.Local.star
    by_cases hu : u = h <;> by_cases hv : v = h <;> simp [hu, hv]
  have hsup : Supports (LNTopology.Local.star f h) f := by
    intro i
    by_cases hi : i = h
    · subst hi
      have key : ∀ j, LNTopology.Local.star f i i j = -f j + (if j = i then f i else 0) := by
        intro j
        unfold LNTopology.Local.star
        by_cases hj : j = i <;> simp [hj]
      simp [key, Finset.sum_add_distrib, Finset.sum_neg_distrib, hf]
    · have key : ∀ j, LNTopology.Local.star f h i j = if j = h then f i else 0 := by
        intro j
        unfold LNTopology.Local.star
        by_cases hj : j = h <;> simp [hj, hi]
      simp [key]
  refine ⟨hLN, hsup, ?_⟩
  set T := ∑ j, (if j = h then 0 else c (f j)) with hT
  have hrow : ∀ i, ∑ j, c (LNTopology.Local.star f h i j) =
      (if i = h then 0 else c (f i)) + (if i = h then T else 0) := by
    intro i
    by_cases hi : i = h
    · subst hi
      simp only [if_true, zero_add]
      rw [hT]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold LNTopology.Local.star
      by_cases hj : j = i <;> simp [hj, hc.zero, hc.symm]
    · have : ∀ j, c (LNTopology.Local.star f h i j) = if j = h then c (f i) else 0 := by
        intro j
        unfold LNTopology.Local.star
        by_cases hj : j = h <;> simp [hj, hi, hc.zero]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, hi, if_false, add_zero]
  have hT2 : T = ∑ i, c (f i) - c (f h) := by
    have : ∀ j, (if j = h then 0 else c (f j)) = c (f j) - (if j = h then c (f h) else 0) := by
      intro j
      by_cases hj : j = h <;> simp [hj]
    rw [hT]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold cost
  simp only [hrow, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h0 : ∑ i, (if i = h then (0:ℝ) else c (f i)) = T := by rw [hT]
  rw [h0, hT2]
  ring

lemma cost_nonneg {V : Type*} [Fintype V] (hc : IsChannelCost c) (Λ : V → V → ℝ) :
    0 ≤ cost c Λ := by
  unfold cost
  have : 0 ≤ ∑ i, ∑ j, c (Λ i j) :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hc.nonneg _))
  linarith

end LNSStar

section LNSCmin
variable {c : ℝ → ℝ}

lemma cmin_le_star {V : Type*} [Fintype V] [DecidableEq V] (hc : IsChannelCost c) (f : V → ℝ)
    (hf : ∑ i, f i = 0) (h : V) :
    cmin c f ≤ ∑ i, c (f i) - c (f h) := by
  obtain ⟨h1, h2, h3⟩ := star_props hc f hf h
  rw [← h3]
  apply csInf_le
  · exact ⟨0, by rintro x ⟨Λ, _, _, rfl⟩; exact cost_nonneg hc Λ⟩
  · exact ⟨_, h1, h2, rfl⟩

lemma le_cmin {V : Type*} [Fintype V] [DecidableEq V] (hc : IsChannelCost c) (f : V → ℝ)
    (hf : ∑ i, f i = 0) (B : ℝ)
    (hB : ∀ Λ : V → V → ℝ, IsLN Λ → Supports Λ f → B ≤ cost c Λ) :
    B ≤ cmin c f := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨h⟩ := hV
    obtain ⟨h1, h2, _⟩ := star_props hc f hf h
    apply le_csInf
    · exact ⟨_, _, h1, h2, rfl⟩
    · rintro x ⟨Λ, hΛ1, hΛ2, rfl⟩
      exact hB Λ hΛ1 hΛ2
  · have hE : IsEmpty V := not_nonempty_iff.mp hV
    have : B ≤ cost c (fun _ _ : V => (0:ℝ)) := hB _ (fun u => isEmptyElim u) (fun i => isEmptyElim i)
    have h0 : {x : ℝ | ∃ Λ : V → V → ℝ, IsLN Λ ∧ Supports Λ f ∧ cost c Λ = x} = {0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨Λ, _, _, rfl⟩
        unfold cost; simp
      · rintro rfl
        exact ⟨fun _ _ => 0, fun u => isEmptyElim u, fun i => isEmptyElim i, by unfold cost; simp⟩
    unfold cmin
    rw [h0, csInf_singleton]
    have : cost c (fun _ _ : V => (0:ℝ)) = 0 := by unfold cost; simp
    linarith

end LNSCmin

theorem solution {V : Type*} [Fintype V] [Nonempty V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (hf : ∑ i, f i = 0) :
    cmin c f ≤ ∑ i, c (f i) - Finset.univ.sup' Finset.univ_nonempty (fun i => c (f i)) ∧
      max (∑ i ∈ Finset.univ.filter (fun i => 0 < f i), c (f i))
          (∑ i ∈ Finset.univ.filter (fun i => f i < 0), c (f i)) ≤ cmin c f := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨h, _, hh⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => c (f i))
    rw [hh]
    exact cmin_le_star hc f hf h
  · exact max_le
      (le_cmin hc f hf _ (fun Λ h1 h2 => pos_bound hc f Λ h1 h2))
      (le_cmin hc f hf _ (fun Λ h1 h2 => neg_bound hc f Λ h1 h2))
