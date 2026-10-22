-- Prove2me | solution 1 for LNTopology.Local.corollary_3_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:54:06.276992+00:00
-- url     : https://prove2.me/submissions/c09a26c5-75c1-46dc-83a0-a9235fa5bcfe

import Mathlib
import Definitions.Def_LNTopology_Local_Model
import Definitions.Def_LNTopology_Local_Star

set_option autoImplicit false

open LNTopology.Local

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

section LNLCore
variable {c : ℝ → ℝ}

def eFlow {V : Type*} [DecidableEq V] (a b : V) (i j : V) : ℝ :=
  (if i = a ∧ j = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0)

lemma eFlow_anti {V : Type*} [DecidableEq V] (a b i j : V) : eFlow a b i j = - eFlow a b j i := by
  unfold eFlow
  simp only [and_comm (a := j = a) (b := i = b), and_comm (a := j = b) (b := i = a)]
  ring

lemma sum_eFlow {V : Type*} [Fintype V] [DecidableEq V] (a b i : V) :
    ∑ j, eFlow a b i j = (if i = a then 1 else 0) - (if i = b then 1 else 0) := by
  unfold eFlow
  rw [Finset.sum_sub_distrib]
  simp [ite_and]

lemma sum_sparse {V : Type*} [Fintype V] (G : V → V → ℝ) (S : Finset (V × V))
    (hG : ∀ i j, (i, j) ∉ S → G i j = 0) :
    ∑ i, ∑ j, G i j = ∑ q ∈ S, G q.1 q.2 := by
  rw [← Fintype.sum_prod_type' (f := G)]
  exact (Finset.sum_subset (Finset.subset_univ S) (fun q _ hq => hG q.1 q.2 hq)).symm

lemma in_out_core {V : Type*} [Fintype V] [DecidableEq V] (hc : IsChannelCost c) (f : V → ℝ)
    (Λ : V → V → ℝ) (hΛ : IsLN Λ) (hs : Supports Λ f) (u v w : V)
    (huv : 0 < Λ u v) (hvw : 0 < Λ v w) :
    ∃ Λ' : V → V → ℝ, IsLN Λ' ∧ Supports Λ' f ∧ cost c Λ' < cost c Λ := by
  have hne1 : u ≠ v := by
    rintro rfl; have := hΛ u u; linarith
  have hne2 : v ≠ w := by
    rintro rfl; have := hΛ v v; linarith
  have hne3 : u ≠ w := by
    rintro rfl; have := hΛ u v; have := hΛ v u; linarith
  set a := Λ u v with ha
  set b := Λ v w with hb
  set t := Λ u w with ht
  set ε := min a b with hε
  have hε0 : 0 < ε := lt_min huv hvw
  set Λ' : V → V → ℝ := fun i j => Λ i j + ε * (eFlow u w i j - eFlow u v i j - eFlow v w i j)
    with hΛ'
  have hLN' : IsLN Λ' := by
    intro i j
    simp only [hΛ']
    rw [hΛ i j, eFlow_anti u w i j, eFlow_anti u v i j, eFlow_anti v w i j]
    ring
  have hS' : Supports Λ' f := by
    intro i
    simp only [hΛ']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      sum_eFlow, sum_eFlow, sum_eFlow, hs i]
    ring
  refine ⟨Λ', hLN', hS', ?_⟩
  -- values at the six positions
  have p1 : Λ' u v = a - ε := by
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm] <;> first | rfl | ring
  have p2 : Λ' v u = -a + ε := by
    have : Λ v u = -a := hΛ v u ▸ rfl
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm, this] <;> first | rfl | ring
  have p3 : Λ' v w = b - ε := by
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm] <;> first | rfl | ring
  have p4 : Λ' w v = -b + ε := by
    have : Λ w v = -b := hΛ w v ▸ rfl
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm, this] <;> first | rfl | ring
  have p5 : Λ' u w = t + ε := by
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm] <;> first | rfl | ring
  have p6 : Λ' w u = -t - ε := by
    have : Λ w u = -t := hΛ w u ▸ rfl
    simp [hΛ', eFlow, hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm, this] <;> first | rfl | ring
  have q2 : Λ v u = -a := hΛ v u ▸ rfl
  have q4 : Λ w v = -b := hΛ w v ▸ rfl
  have q6 : Λ w u = -t := hΛ w u ▸ rfl
  set S : Finset (V × V) := {(u, v), (v, u), (v, w), (w, v), (u, w), (w, u)} with hSdef
  have hG : ∀ i j, (i, j) ∉ S → c (Λ' i j) - c (Λ i j) = 0 := by
    intro i j hij
    simp only [hSdef, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or] at hij
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hij
    have e1 : eFlow u w i j = 0 := by unfold eFlow; rw [if_neg h5, if_neg h6]; simp
    have e2 : eFlow u v i j = 0 := by unfold eFlow; rw [if_neg h1, if_neg h2]; simp
    have e3 : eFlow v w i j = 0 := by unfold eFlow; rw [if_neg h3, if_neg h4]; simp
    simp [hΛ', e1, e2, e3]
  have hsum : ∑ i, ∑ j, (c (Λ' i j) - c (Λ i j)) =
      (c (a - ε) - c a) + (c (-a + ε) - c (-a)) + (c (b - ε) - c b) + (c (-b + ε) - c (-b))
        + (c (t + ε) - c t) + (c (-t - ε) - c (-t)) := by
    rw [sum_sparse _ S hG, hSdef]
    rw [Finset.sum_insert (by simp [hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm]),
      Finset.sum_insert (by simp [hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm]),
      Finset.sum_insert (by simp [hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm]),
      Finset.sum_insert (by simp [hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm]),
      Finset.sum_pair (by simp [hne1, hne2, hne3, hne1.symm, hne2.symm, hne3.symm])]
    simp only [p1, p2, p3, p4, p5, p6, q2, q4, q6, ha, hb, ht]
    ring
  have hsym : ∀ x, c (-x) = c x := hc.symm
  have e1 : c (-a + ε) = c (a - ε) := by rw [← hsym (a - ε)]; congr 1; ring
  have e2 : c (-b + ε) = c (b - ε) := by rw [← hsym (b - ε)]; congr 1; ring
  have e3 : c (-t - ε) = c (t + ε) := by rw [← hsym (t + ε)]; congr 1; ring
  have e4 : c (-a) = c a := hsym a
  have e5 : c (-b) = c b := hsym b
  have e6 : c (-t) = c t := hsym t
  have hcost : cost c Λ' - cost c Λ = (1 / 2) * ∑ i, ∑ j, (c (Λ' i j) - c (Λ i j)) := by
    unfold cost
    simp only [Finset.sum_sub_distrib]
    ring
  rw [hsum, e1, e2, e3, e4, e5, e6] at hcost
  have hadd := c_add_le hc t ε
  have hε_le_a : ε ≤ a := min_le_left _ _
  have hε_le_b : ε ≤ b := min_le_right _ _
  have hz : c 0 = 0 := hc.zero
  rcases le_total a b with hab | hab
  · have hεa : ε = a := min_eq_left hab
    have h1 : c (b - ε) < c b := hc.mono b (b - ε) (by linarith) (by linarith)
    have h2 : c (a - ε) = 0 := by rw [hεa, sub_self, hz]
    have h3 : c (t + ε) ≤ c t + c a := by
      have := hadd; rw [hεa] at this ⊢; exact this
    have : cost c Λ' - cost c Λ < 0 := by rw [hcost]; linarith [h1, h2, h3]
    linarith
  · have hεb : ε = b := min_eq_right hab
    have h1 : c (a - ε) < c a := hc.mono a (a - ε) (by linarith) (by linarith)
    have h2 : c (b - ε) = 0 := by rw [hεb, sub_self, hz]
    have h3 : c (t + ε) ≤ c t + c b := by
      have := hadd; rw [hεb] at this ⊢; exact this
    have : cost c Λ' - cost c Λ < 0 := by rw [hcost]; linarith [h1, h2, h3]
    linarith

end LNLCore

lemma in_and_out_lem {V : Type*} [Fintype V] (c : ℝ → ℝ) (hc : IsChannelCost c)
    (f : V → ℝ) (Λ : V → V → ℝ) (hΛ : IsLN Λ) (hsupp : Supports Λ f) (u v w : V)
    (huv : 0 < Λ u v) (hvw : 0 < Λ v w) :
    ¬ IsCostMinimizing c f Λ := by
  classical
  intro ⟨_, _, hmin⟩
  obtain ⟨Λ', h1, h2, h3⟩ := in_out_core hc f Λ hΛ hsupp u v w huv hvw
  exact absurd (hmin Λ' h1 h2) (not_le.mpr h3)

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (hc : IsChannelCost c) (f : V → ℝ) (hsum : ∑ i, f i = 0)
    (i₁ i₂ j₁ j₂ : V) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hi₁ : 0 < f i₁) (hi₂ : 0 < f i₂) (hj₁ : f j₁ < 0) (hj₂ : f j₂ < 0) :
    ∀ h : V, ¬ IsCostMinimizing c f (LNTopology.Local.star f h) := by
  intro h hmin
  obtain ⟨hLN, hsup, _⟩ := star_props hc f hsum h
  obtain ⟨p, hp, hpos⟩ : ∃ p, p ≠ h ∧ 0 < f p := by
    by_cases h1 : i₁ = h
    · exact ⟨i₂, fun e => hi (h1.trans e.symm), hi₂⟩
    · exact ⟨i₁, h1, hi₁⟩
  obtain ⟨q, hq, hneg⟩ : ∃ q, q ≠ h ∧ f q < 0 := by
    by_cases h1 : j₁ = h
    · exact ⟨j₂, fun e => hj (h1.trans e.symm), hj₂⟩
    · exact ⟨j₁, h1, hj₁⟩
  have e1 : LNTopology.Local.star f h p h = f p := by simp [LNTopology.Local.star, hp]
  have e2 : LNTopology.Local.star f h h q = - f q := by simp [LNTopology.Local.star, hq]
  exact in_and_out_lem c hc f _ hLN hsup p h q (by rw [e1]; exact hpos) (by rw [e2]; linarith) hmin
