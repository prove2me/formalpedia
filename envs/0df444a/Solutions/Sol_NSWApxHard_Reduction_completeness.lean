-- Prove2me | solution 1 for NSWApxHard.Reduction.completeness
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:41:43.679029+00:00
-- url     : https://prove2.me/submissions/ee69df7f-d5e3-4ca5-9a7d-17da145ecf05

import Mathlib
import Definitions.Def_NSWApxHard_Reduction_Instance

open NSWApxHard.Reduction Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace P2MH

lemma utility_eq' {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] (u : A → B → ℝ)
    (x : B → A) (a : A) : utility u x a = ∑ i, if x i = a then u a i else 0 := by
  unfold utility; rw [sum_filter]


lemma deg3 {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) (v : Fin N) :
    G.degree v = 3 := by
  rw [← hG v, ← SimpleGraph.card_neighborFinset_eq_degree, Set.ncard_eq_toFinset_card']
  rfl

lemma card_edges {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) :
    2 * #G.edgeFinset = 3 * N := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  simp [deg3 hG]
  ring

lemma card_inc {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) :
    Fintype.card (Inc G) = 3 * N := by
  rw [Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
  have : ∀ v : Fin N, (∑ e : Sym2 (Fin N), if e ∈ G.edgeFinset ∧ v ∈ e then 1 else 0) = 3 := by
    intro v
    rw [← card_filter, ← deg3 hG v, ← SimpleGraph.card_incidenceFinset_eq_degree]
    congr 1
    ext e
    simp [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet]
  simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  ring


lemma fiber_v {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (hG : IsCubic G) (v : Fin N) :
    #{s : Inc G | s.1.1 = v} = 3 := by
  rw [← deg3 hG v, ← SimpleGraph.card_incidenceFinset_eq_degree]
  refine card_nbij (fun s => s.1.2) ?_ ?_ ?_
  · rintro ⟨⟨w, e⟩, h1, h2⟩ hs
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs
    subst hs
    rw [mem_coe, SimpleGraph.mem_incidenceFinset]
    exact ⟨by simpa using h1, h2⟩
  · rintro ⟨⟨w, e⟩, h1, h2⟩ hs ⟨⟨w', e'⟩, h1', h2'⟩ hs' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs hs'
    simp only at h
    subst hs hs' h
    rfl
  · intro e he
    rw [mem_coe, SimpleGraph.mem_incidenceFinset] at he
    have h : e ∈ G.edgeFinset ∧ v ∈ e := ⟨by simpa using he.1, he.2⟩
    exact ⟨⟨(v, e), h⟩, by simp, rfl⟩

lemma fiber_e {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (e : Edge G) :
    #{s : Inc G | s.1.2 = e.1} = 2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := G.ne_of_adj (by simpa using he)
  have : (univ.filter fun s : Inc G => s.1.2 = s(a, b)) =
      {⟨(a, s(a, b)), he, by simp⟩, ⟨(b, s(a, b)), he, by simp⟩} := by
    ext ⟨⟨v, e'⟩, h1, h2⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Subtype.mk.injEq,
      Prod.mk.injEq]
    constructor
    · rintro rfl
      simpa [and_true] using h2
    · rintro (⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rfl
  rw [this, card_pair]
  intro h
  simp [Subtype.ext_iff] at h
  exact hab h

lemma sum_fiber_e {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (P : Inc G → Prop)
    [DecidablePred P] : ∑ e : Edge G, #{s : Inc G | P s ∧ s.1.2 = e.1} = #{s : Inc G | P s} := by
  rw [card_eq_sum_card_fiberwise (f := fun s : Inc G => (⟨s.1.2, s.2.1⟩ : Edge G)) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun e _ => ?_
  congr 1; ext s; simp [filter_filter, Subtype.ext_iff]

lemma sum_fiber_v {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] (P : Inc G → Prop)
    [DecidablePred P] : ∑ v : Fin N, #{s : Inc G | P s ∧ s.1.1 = v} = #{s : Inc G | P s} := by
  rw [card_eq_sum_card_fiberwise (f := fun s : Inc G => s.1.1) (t := univ)
    (fun _ _ => mem_coe.2 (mem_univ _))]
  refine sum_congr rfl fun e _ => ?_
  congr 1; ext s; simp [filter_filter]

section Gen
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma utility_nonneg (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (x : B → A) (a : A) :
    0 ≤ utility u x a := sum_nonneg fun i _ => hu a i

lemma prod_le_of_nsw_le (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (hA : 0 < Fintype.card A)
    {x y : B → A} (h : nsw u y ≤ nsw u x) : ∏ a, utility u y a ≤ ∏ a, utility u x a := by
  unfold nsw at h
  have h1 : (0:ℝ) < 1 / Fintype.card A := by positivity
  exact (Real.rpow_le_rpow_iff (prod_nonneg fun a _ => utility_nonneg u hu y a)
    (prod_nonneg fun a _ => utility_nonneg u hu x a) h1).1 h

lemma utility_update (u : A → B → ℝ) (x : B → A) (i : B) (b : A) (a : A) :
    utility u (Function.update x i b) a =
      utility u x a - (if x i = a then u a i else 0) + (if b = a then u a i else 0) := by
  rw [utility_eq', utility_eq', ← add_sum_erase _ _ (mem_univ i), ← add_sum_erase _ _ (mem_univ i)]
  have : ∑ j ∈ univ.erase i, (if Function.update x i b j = a then u a j else 0) =
      ∑ j ∈ univ.erase i, (if x j = a then u a j else 0) :=
    sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this]; simp only [Function.update_self]; ring

lemma move (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (x : B → A) (hx : IsOptimal u x)
    (hpos : 0 < ∏ a, utility u x a) (i : B) (b : A) (hb : b ≠ x i) :
    (utility u x (x i) - u (x i) i) * (utility u x b + u b i) ≤
      utility u x (x i) * utility u x b := by
  set y := Function.update x i b with hy
  have hA : 0 < Fintype.card A := Fintype.card_pos_iff.2 ⟨b⟩
  have h := prod_le_of_nsw_le u hu hA (hx y)
  have hm : b ∈ univ.erase (x i) := mem_erase.2 ⟨hb, mem_univ b⟩
  rw [← mul_prod_erase _ _ (mem_univ (x i)), ← mul_prod_erase _ _ hm] at h hpos
  rw [← mul_prod_erase _ _ (mem_univ (x i)), ← mul_prod_erase _ _ hm] at h
  have hrest : ∏ a ∈ (univ.erase (x i)).erase b, utility u y a =
      ∏ a ∈ (univ.erase (x i)).erase b, utility u x a := prod_congr rfl fun a ha => by
    have h1 := ne_of_mem_erase ha
    have h2 := ne_of_mem_erase (mem_of_mem_erase ha)
    rw [hy, utility_update]; simp [Ne.symm h1, Ne.symm h2]
  have hyi : utility u y (x i) = utility u x (x i) - u (x i) i := by
    rw [hy, utility_update]; simp [hb]
  have hyb : utility u y b = utility u x b + u b i := by
    rw [hy, utility_update]; simp [Ne.symm hb]
  rw [hrest, hyi, hyb] at h
  set Q := ∏ a ∈ (univ.erase (x i)).erase b, utility u x a
  have hQ0 : 0 ≤ Q := prod_nonneg fun a _ => utility_nonneg u hu x a
  have hQ : 0 < Q := by
    rcases hQ0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hpos; simp at hpos
  have := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.2 hQ))
  calc _ = (utility u x (x i) - u (x i) i) * ((utility u x b + u b i) * Q) * Q⁻¹ := by
          field_simp
    _ ≤ utility u x (x i) * (utility u x b * Q) * Q⁻¹ := this
    _ = _ := by field_simp

end Gen

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {k : ℕ}

def vsh (x : Item G k → Agent G) (v : Fin N) : ℕ :=
  #{s : Inc G | x s.item = Sum.inl v ∧ s.1.1 = v}

def esh (x : Item G k → Agent G) (e : Edge G) : ℕ :=
  #{s : Inc G | x s.item = Sum.inr e ∧ e.1 = s.1.2}

lemma util_v (α : ℝ) (x : Item G k → Agent G) (v : Fin N) :
    utility (redUtil G k α) x (Sum.inl v) = (vItems x v : ℝ) + (vsh x v : ℝ) / 3 := by
  rw [utility_eq', Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [redUtil, ite_self, sum_const_zero, zero_add]
  rw [vItems, vsh, natCast_card_filter, natCast_card_filter, sum_div]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  simp only [Inc.item]
  split_ifs <;> simp_all

lemma util_e (α : ℝ) (x : Item G k → Agent G) (e : Edge G) :
    utility (redUtil G k α) x (Sum.inr e) =
      (if x (Sum.inr (Sum.inl e)) = Sum.inr e then 1 - α else 0) + α * (esh x e : ℝ) := by
  rw [utility_eq', Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [redUtil, ite_self, sum_const_zero, zero_add]
  rw [esh, natCast_card_filter, mul_sum]
  congr 1
  · rw [Fintype.sum_eq_single e]
    · simp
    · intro e' he'; simp [Ne.symm he']
  · refine sum_congr rfl fun s _ => ?_
    simp only [Inc.item]
    split_ifs <;> simp_all

end P2MH

open P2MH in
theorem instance_size {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (hG : IsCubic G) :
    2 * Fintype.card (Agent G) = 5 * N ∧ 2 * Fintype.card (Item G k) = 2 * k + 9 * N := by
  have h1 := card_edges hG
  have h2 := card_inc hG
  simp only [Agent, Item, Edge, Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]
  omega

open P2MH in
theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (C : Finset (Fin N)) (hC : G.IsVertexCover ↑C) (hCk : C.card = k) :
    ∃ x : Item G k → Agent G,
      nsw (redUtil G k α) x = (1 + α) ^ ((3 * (k : ℝ) - 3 * N / 2) / (5 * N / 2)) := by
  subst hCk
  let f : Fin C.card → Fin N := fun j => (C.equivFin.symm j).1
  have hf : ∀ j, f j ∈ C := fun j => (C.equivFin.symm j).2
  let x : Item G C.card → Agent G := fun i => match i with
    | Sum.inl j => Sum.inl (f j)
    | Sum.inr (Sum.inl e) => Sum.inr e
    | Sum.inr (Sum.inr s) => if s.1.1 ∈ C then s.eAgent else s.vAgent
  refine ⟨x, ?_⟩
  have hv : ∀ v, utility (redUtil G C.card α) x (Sum.inl v) = 1 := by
    intro v
    rw [util_v]
    by_cases hvC : v ∈ C
    · have h1 : vItems x v = 1 := by
        rw [vItems, card_eq_one]
        refine ⟨C.equivFin ⟨v, hvC⟩, ?_⟩
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_singleton, x, Sum.inl.injEq]
        constructor
        · intro h; subst h; simp [f]
        · rintro rfl; simp [f]
      have h2 : vsh x v = 0 := by
        rw [vsh, card_eq_zero, filter_eq_empty_iff]
        rintro s - ⟨h, rfl⟩
        simp [x, Inc.item, hvC, Inc.eAgent] at h
      rw [h1, h2]; norm_num
    · have h1 : vItems x v = 0 := by
        rw [vItems, card_eq_zero, filter_eq_empty_iff]
        intro j _ h
        simp only [x, Sum.inl.injEq] at h
        exact hvC (h ▸ hf j)
      have h2 : vsh x v = 3 := by
        rw [← fiber_v hG v, vsh]
        congr 1; ext s
        simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
        rintro rfl
        simp [x, Inc.item, hvC, Inc.vAgent]
      rw [h1, h2]; norm_num
  let m : Edge G → ℕ := fun e => #{s : Inc G | s.1.1 ∈ C ∧ s.1.2 = e.1}
  have he : ∀ e, utility (redUtil G C.card α) x (Sum.inr e) = 1 - α + α * m e := by
    intro e
    have : esh x e = m e := by
      unfold esh
      congr 1
      apply Finset.filter_congr
      intro s _
      simp only [Inc.item, x]
      by_cases hs : s.1.1 ∈ C
      · simp [hs, Inc.eAgent, Subtype.ext_iff, eq_comm]
      · simp [hs, Inc.vAgent]
    rw [util_e, this]
    simp [x]
  have hm1 : ∀ e, 1 ≤ m e := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
    have hab : G.Adj a b := by simpa using he
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [card_eq_zero, filter_eq_empty_iff] at h0
    rcases hC hab with ha | hb
    · exact h0 (x := ⟨(a, s(a, b)), he, by simp⟩) (mem_univ _) ⟨ha, rfl⟩
    · exact h0 (x := ⟨(b, s(a, b)), he, by simp⟩) (mem_univ _) ⟨hb, rfl⟩
  have hm2 : ∀ e, m e ≤ 2 := by
    intro e
    rw [← fiber_e e]
    exact card_le_card fun s => by simp
  have hsum : ∑ e : Edge G, (m e : ℝ) = 3 * C.card := by
    rw [← Nat.cast_sum, sum_fiber_e (fun s : Inc G => s.1.1 ∈ C)]
    rw [← sum_fiber_v (fun s : Inc G => s.1.1 ∈ C)]
    rw [← sum_filter_add_sum_filter_not univ (fun v => v ∈ C)]
    have h1 : ∀ v ∈ univ.filter (fun v => v ∈ C), #{s : Inc G | s.1.1 ∈ C ∧ s.1.1 = v} = 3 := by
      intro v hv
      rw [← fiber_v hG v]; congr 1; ext s
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hv, rfl⟩
    have h2 : ∀ v ∈ univ.filter (fun v => v ∉ C), #{s : Inc G | s.1.1 ∈ C ∧ s.1.1 = v} = 0 := by
      intro v hv
      rw [card_eq_zero, filter_eq_empty_iff]
      simp only [mem_filter, mem_univ, true_and] at hv
      rintro s - ⟨h, rfl⟩; exact hv h
    rw [sum_congr rfl h1, sum_congr rfl h2]
    simp [filter_mem_eq_inter]
    ring
  have hE : (2 : ℝ) * #G.edgeFinset = 3 * N := by exact_mod_cast card_edges hG
  have hA : (2 : ℝ) * Fintype.card (Agent G) = 5 * N := by exact_mod_cast (instance_size G 0 hG).1
  have hprod : ∏ a, utility (redUtil G C.card α) x a =
      (1 + α) ^ (3 * (C.card : ℝ) - 3 * N / 2) := by
    rw [Fintype.prod_sum_type]
    simp only [hv, he, prod_const_one, one_mul]
    have : ∀ e : Edge G, 1 - α + α * (m e : ℝ) = (1 + α) ^ ((m e : ℝ) - 1) := by
      intro e
      rcases (show m e = 1 ∨ m e = 2 by have := hm1 e; have := hm2 e; omega) with h | h <;>
        rw [h] <;> norm_num <;> ring
    simp only [this]
    rw [← Real.rpow_sum_of_pos (by linarith), sum_sub_distrib, hsum]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
    congr 1
    have : (Fintype.card (Edge G) : ℝ) = #G.edgeFinset := by simp
    rw [this]; linarith
  unfold nsw
  rw [hprod, ← Real.rpow_mul (by linarith)]
  congr 1
  have : (Fintype.card (Agent G) : ℝ) = 5 * N / 2 := by linarith
  rw [this]; ring
