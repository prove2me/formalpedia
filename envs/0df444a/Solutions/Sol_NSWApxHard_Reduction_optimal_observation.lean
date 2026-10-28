-- Prove2me | solution 1 for NSWApxHard.Reduction.optimal_observation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:46:30.872103+00:00
-- url     : https://prove2.me/submissions/c1b9ca21-24b8-4212-a93b-e9579e3e8829

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

lemma util_pos_of_prod_pos (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (x : B → A)
    (hpos : 0 < ∏ a, utility u x a) (a : A) : 0 < utility u x a := by
  rcases (utility_nonneg u hu x a).lt_or_eq with h | h
  · exact h
  · rw [prod_eq_zero (mem_univ a) h.symm] at hpos; exact absurd hpos (lt_irrefl _)

lemma prod_pos_of_opt (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (hA : 0 < Fintype.card A)
    (x : B → A) (hx : IsOptimal u x) (y : B → A) (hy : 0 < ∏ a, utility u y a) :
    0 < ∏ a, utility u x a := by
  have h1 : 0 < nsw u y := Real.rpow_pos_of_pos hy _
  have h2 := lt_of_lt_of_le h1 (hx y)
  rcases (prod_nonneg fun a _ => utility_nonneg u hu x a).lt_or_eq with h | h
  · exact h
  · unfold nsw at h2
    rw [← h, Real.zero_rpow (by positivity)] at h2
    exact absurd h2 (lt_irrefl _)

lemma move_zero (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) (x : B → A) (hx : IsOptimal u x)
    (hpos : 0 < ∏ a, utility u x a) (i : B) (b : A) (hb : b ≠ x i) (h0 : u (x i) i = 0)
    (h1 : 0 < u b i) : False := by
  have h := move u hu x hx hpos i b hb
  have h2 := util_pos_of_prod_pos u hu x hpos (x i)
  rw [h0, sub_zero] at h
  nlinarith

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

lemma redUtil_nonneg {α : ℝ} (h1 : 1 / 3 < α) (h2 : α < 1 / 2) :
    ∀ a i, 0 ≤ redUtil G k α a i := by
  intro a i
  rcases a with v | e <;> rcases i with j | e' | s <;> simp only [redUtil] <;>
    (try split_ifs) <;> linarith

lemma exists_pos (hG : IsCubic G) (hN : 0 < N) (α : ℝ) (h1 : 1 / 3 < α) (h2 : α < 1 / 2) :
    ∃ y : Item G k → Agent G, 0 < ∏ a, utility (redUtil G k α) y a := by
  let y : Item G k → Agent G := fun i => match i with
    | Sum.inl _ => Sum.inl ⟨0, hN⟩
    | Sum.inr (Sum.inl e) => Sum.inr e
    | Sum.inr (Sum.inr s) => s.vAgent
  refine ⟨y, prod_pos fun a _ => ?_⟩
  rcases a with v | e
  · rw [util_v]
    have : vsh y v = 3 := by
      rw [← fiber_v hG v, vsh]
      congr 1
      apply Finset.filter_congr
      intro s _
      simp only [Inc.item, y, Inc.vAgent]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by rw [h], h⟩
    rw [this]; positivity
  · rw [util_e]
    simp only [y, if_true]
    have : (0:ℝ) ≤ α * (esh y e : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith

lemma card_agent_pos (hN : 0 < N) : 0 < Fintype.card (Agent G) :=
  Fintype.card_pos_iff.2 ⟨Sum.inl ⟨0, hN⟩⟩

lemma agent_pos (a : Agent G) : 0 < N := by
  rcases a with v | ⟨e, he⟩
  · exact v.pos
  · induction e using Sym2.ind with
    | _ a b => exact a.pos

lemma opt_pos (hG : IsCubic G) {α : ℝ} (h1 : 1 / 3 < α) (h2 : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) (a : Agent G) :
    0 < ∏ a, utility (redUtil G k α) x a := by
  have hN := agent_pos a
  obtain ⟨y, hy⟩ := exists_pos (k := k) hG hN α h1 h2
  exact prod_pos_of_opt _ (redUtil_nonneg h1 h2) (card_agent_pos hN) x hx y hy

end P2MH

open P2MH in
theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
    (α : ℝ) (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) :
    (∀ j : Fin k, ∃ v : Fin N, x (Sum.inl j) = Sum.inl v) ∧
      ∀ e : Edge G, x (Sum.inr (Sum.inl e)) = Sum.inr e := by
  have hu := redUtil_nonneg (G := G) (k := k) hα₁ hα₂
  constructor
  · intro j
    have hpos := opt_pos hG hα₁ hα₂ x hx (x (Sum.inl j))
    rcases hxj : x (Sum.inl j) with v | e
    · exact ⟨v, rfl⟩
    · exfalso
      have hN := agent_pos (x (Sum.inl j))
      refine move_zero _ hu x hx hpos (Sum.inl j) (Sum.inl ⟨0, hN⟩) (by rw [hxj]; simp) ?_ ?_
      · rw [hxj]; simp [redUtil]
      · simp [redUtil]
  · intro e
    have hpos := opt_pos hG hα₁ hα₂ x hx (Sum.inr e)
    by_contra hne
    refine move_zero _ hu x hx hpos (Sum.inr (Sum.inl e)) (Sum.inr e) (Ne.symm hne) ?_ ?_
    · rcases hb : x (Sum.inr (Sum.inl e)) with v | e'
      · simp [redUtil]
      · rw [hb] at hne
        have : e' ≠ e := fun h => hne (by rw [h])
        simp [redUtil, this]
    · simp [redUtil]; linarith
