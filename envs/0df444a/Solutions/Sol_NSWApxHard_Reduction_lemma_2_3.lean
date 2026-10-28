-- Prove2me | solution 1 for NSWApxHard.Reduction.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:58:42.399637+00:00
-- url     : https://prove2.me/submissions/d4b2e620-7bef-462f-a8b7-ee42fa24a1c8

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

lemma prod_update_split (u : A → B → ℝ) (x : B → A) (i : B) (b : A) (hb : b ≠ x i) :
    ∏ a, utility u (Function.update x i b) a =
      (utility u x (x i) - u (x i) i) * ((utility u x b + u b i) *
        ∏ a ∈ (univ.erase (x i)).erase b, utility u x a) ∧
    ∏ a, utility u x a = utility u x (x i) * (utility u x b *
        ∏ a ∈ (univ.erase (x i)).erase b, utility u x a) := by
  set y := Function.update x i b with hy
  have hm : b ∈ univ.erase (x i) := mem_erase.2 ⟨hb, mem_univ b⟩
  rw [← mul_prod_erase _ _ (mem_univ (x i)), ← mul_prod_erase _ _ hm]
  rw [← mul_prod_erase _ _ (mem_univ (x i)), ← mul_prod_erase _ _ hm]
  refine ⟨?_, rfl⟩
  have hrest : ∏ a ∈ (univ.erase (x i)).erase b, utility u y a =
      ∏ a ∈ (univ.erase (x i)).erase b, utility u x a := prod_congr rfl fun a ha => by
    have h1 := ne_of_mem_erase ha
    have h2 := ne_of_mem_erase (mem_of_mem_erase ha)
    rw [hy, utility_update]; simp [Ne.symm h1, Ne.symm h2]
  have hyi : utility u y (x i) = utility u x (x i) - u (x i) i := by
    rw [hy, utility_update]; simp [hb]
  have hyb : utility u y b = utility u x b + u b i := by
    rw [hy, utility_update]; simp [Ne.symm hb]
  rw [hrest, hyi, hyb]

lemma nsw_le_of_prod_le (u : A → B → ℝ) (hu : ∀ a i, 0 ≤ u a i) {x y : B → A}
    (h : ∏ a, utility u x a ≤ ∏ a, utility u y a) : nsw u x ≤ nsw u y :=
  Real.rpow_le_rpow (prod_nonneg fun a _ => utility_nonneg u hu x a) h (by positivity)

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

namespace P2MH
variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {k : ℕ}

lemma vItems_update (x : Item G k → Agent G) (j : Fin k) (w u : Fin N) :
    (vItems (Function.update x (Sum.inl j) (Sum.inl w)) u : ℤ) =
      vItems x u - (if x (Sum.inl j) = Sum.inl u then 1 else 0) + (if w = u then 1 else 0) := by
  unfold vItems
  rw [natCast_card_filter, natCast_card_filter, ← add_sum_erase _ _ (mem_univ j),
    ← add_sum_erase _ _ (mem_univ j)]
  have : ∑ j' ∈ univ.erase j,
      (if Function.update x (Sum.inl j) (Sum.inl w) (Sum.inl j') = Sum.inl u then (1:ℤ) else 0) =
      ∑ j' ∈ univ.erase j, (if x (Sum.inl j') = Sum.inl u then (1:ℤ) else 0) :=
    sum_congr rfl fun j' hj' => by
      rw [Function.update_of_ne (by simpa using ne_of_mem_erase hj')]
  rw [this]; simp only [Function.update_self, Sum.inl.injEq]; ring

lemma vsh_le (hG : IsCubic G) (x : Item G k → Agent G) (v : Fin N) : vsh x v ≤ 3 := by
  rw [← fiber_v hG v]
  exact card_le_card fun s => by simp only [mem_filter, mem_univ, true_and]; exact fun h => h.2

lemma lemma22_core (hG : IsCubic G) {α : ℝ} (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N)
    (P : (Item G k → Agent G) → Prop) (hP : ∃ x, IsOptimal (redUtil G k α) x ∧ P x)
    (hPup : ∀ x, P x → IsOptimal (redUtil G k α) x → ∀ j w,
      P (Function.update x (Sum.inl j) (Sum.inl w))) :
    ∃ x : Item G k → Agent G,
      IsOptimal (redUtil G k α) x ∧ P x ∧ ∀ v : Fin N, vItems x v ≤ 1 := by
  classical
  have hu := redUtil_nonneg (G := G) (k := k) hα₁ hα₂
  let Φ : (Item G k → Agent G) → ℤ := fun x => ∑ v, (vItems x v : ℤ) ^ 2
  have hne : (univ.filter fun x => IsOptimal (redUtil G k α) x ∧ P x).Nonempty := by
    obtain ⟨x, hx⟩ := hP; exact ⟨x, by simpa using hx⟩
  obtain ⟨x, hxm, hmin⟩ := exists_min_image _ Φ hne
  simp only [mem_filter, mem_univ, true_and] at hxm hmin
  refine ⟨x, hxm.1, hxm.2, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv⟩ := hcon
  have hw : ∃ w, vItems x w = 0 := by
    by_contra hall
    push Not at hall
    have : ∀ u, ∃ j, x (Sum.inl j) = Sum.inl u := by
      intro u
      have := Nat.pos_of_ne_zero (hall u)
      rw [vItems, card_pos] at this
      obtain ⟨j, hj⟩ := this
      exact ⟨j, by simpa using hj⟩
    choose g hg using this
    have hinj : Function.Injective g := by
      intro a b h
      have := (hg a).symm.trans (h ▸ hg b)
      exact Sum.inl_injective this
    have := Fintype.card_le_of_injective g hinj
    simp at this; omega
  obtain ⟨w, hw⟩ := hw
  have hvw : w ≠ v := by rintro rfl; omega
  obtain ⟨j, hj⟩ : ∃ j, x (Sum.inl j) = Sum.inl v := by
    have : 0 < vItems x v := by omega
    rw [vItems, card_pos] at this
    obtain ⟨j, hj⟩ := this
    exact ⟨j, by simpa using hj⟩
  set y := Function.update x (Sum.inl j) (Sum.inl w) with hy
  have hb : (Sum.inl w : Agent G) ≠ x (Sum.inl j) := by rw [hj]; simpa using hvw
  obtain ⟨h1, h2⟩ := prod_update_split (redUtil G k α) x (Sum.inl j) (Sum.inl w) hb
  have hyopt : IsOptimal (redUtil G k α) y := by
    intro z
    refine le_trans (hxm.1 z) (nsw_le_of_prod_le _ hu ?_)
    rw [h1, h2]
    set Q := ∏ a ∈ (univ.erase (x (Sum.inl j))).erase (Sum.inl w), utility (redUtil G k α) x a
    have hQ : 0 ≤ Q := prod_nonneg fun a _ => utility_nonneg _ hu x a
    rw [hj]
    simp only [redUtil]
    rw [util_v, util_v, hw]
    simp only [Nat.cast_zero, zero_add]
    have e1 : (2:ℝ) ≤ vItems x v := by exact_mod_cast hv
    have e2 : (vsh x w : ℝ) ≤ 3 := by exact_mod_cast vsh_le hG x w
    have e3 : (0:ℝ) ≤ vsh x v := Nat.cast_nonneg _
    set A : ℝ := ↑(vItems x v) + ↑(vsh x v) / 3
    set B : ℝ := ↑(vsh x w) / 3
    have hA : 2 ≤ A := by simp only [A]; linarith
    have hB : B ≤ 1 := by simp only [B]; linarith
    have : A * B ≤ (A - 1) * (B + 1) := by nlinarith
    rw [← mul_assoc, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right this hQ
  have hlt : Φ y < Φ x := by
    simp only [Φ]
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_erase.2 ⟨hvw, mem_univ w⟩)]
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_erase.2 ⟨hvw, mem_univ w⟩)]
    have hrest : ∑ u ∈ (univ.erase v).erase w, (vItems y u : ℤ) ^ 2 =
        ∑ u ∈ (univ.erase v).erase w, (vItems x u : ℤ) ^ 2 := sum_congr rfl fun u hu' => by
      have a1 := ne_of_mem_erase hu'
      have a2 := ne_of_mem_erase (mem_of_mem_erase hu')
      rw [hy, vItems_update, hj]
      simp [Ne.symm a1, a2.symm, Ne.symm a2]
    rw [hrest, hy, vItems_update, vItems_update, hj]
    simp only [if_true, hvw, if_false, hvw.symm, Sum.inl.injEq, hw, Nat.cast_zero]
    have : (2:ℤ) ≤ vItems x v := by exact_mod_cast hv
    nlinarith
  exact absurd (hmin y ⟨hyopt, hPup x hxm.2 hxm.1 j w⟩) (not_le.2 hlt)

lemma exists_opt (hN : 0 < N) (α : ℝ) :
    ∃ x : Item G k → Agent G, IsOptimal (redUtil G k α) x := by
  have : Nonempty (Item G k → Agent G) := ⟨fun _ => Sum.inl ⟨0, hN⟩⟩
  obtain ⟨x, hx⟩ := Finite.exists_max (nsw (redUtil G k α))
  exact ⟨x, hx⟩

end P2MH

open P2MH in
theorem lemma_2_2 {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G,
      IsOptimal (redUtil G k α) x ∧ ∀ v : Fin N, vItems x v ≤ 1 := by
  obtain ⟨x, hx⟩ := exists_opt (G := G) (k := k) (by omega) α
  obtain ⟨y, hy1, -, hy2⟩ := lemma22_core hG hα₁ hα₂ hk (fun _ => True) ⟨x, hx, trivial⟩
    (fun _ _ _ _ _ => trivial)
  exact ⟨y, hy1, hy2⟩

open P2MH in
theorem optimal_observation' {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ)
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

lemma card_split {α : Type} [Fintype α] [DecidableEq α] (P : α → Prop) [DecidablePred P] (a : α) :
    #{b | P b} = #{b | b ≠ a ∧ P b} + if P a then 1 else 0 := by
  by_cases h : P a
  · rw [if_pos h]
    have : (univ.filter P) = insert a (univ.filter fun b => b ≠ a ∧ P b) := by
      ext b; by_cases hb : b = a <;> simp [hb, h]
    rw [this, card_insert_of_notMem (by simp)]
  · rw [if_neg h, add_zero]
    congr 1; ext b; by_cases hb : b = a <;> simp [hb, h]

namespace P2MH
variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {k : ℕ}

lemma shared_placed (hG : IsCubic G) {α : ℝ} (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) (s : Inc G) :
    x s.item = s.vAgent ∨ x s.item = s.eAgent := by
  have hu := redUtil_nonneg (G := G) (k := k) hα₁ hα₂
  have hpos := opt_pos hG hα₁ hα₂ x hx (x s.item)
  by_contra hc
  push Not at hc
  refine move_zero _ hu x hx hpos s.item s.vAgent (Ne.symm hc.1) ?_ ?_
  · rcases hxs : x s.item with w | e'
    · have : s.1.1 ≠ w := fun h => hc.1 (by rw [hxs, Inc.vAgent, h])
      simp [redUtil, Inc.item, this]
    · have : e'.1 ≠ s.1.2 := fun h => hc.2 (by rw [hxs, Inc.eAgent]; congr 1; exact Subtype.ext h)
      simp [redUtil, Inc.item, this]
  · simp [redUtil, Inc.item, Inc.vAgent]

lemma rule_of_opt (hG : IsCubic G) {α : ℝ} (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2)
    (x : Item G k → Agent G) (hx : IsOptimal (redUtil G k α) x) (hv1 : ∀ v, vItems x v ≤ 1)
    (s : Inc G) : Rule x s := by
  classical
  have hu := redUtil_nonneg (G := G) (k := k) hα₁ hα₂
  have hpos := opt_pos hG hα₁ hα₂ x hx (Sum.inl s.1.1)
  have hF1 := (optimal_observation' G k α hG hα₁ hα₂ x hx).2
  have hF2 := shared_placed hG hα₁ hα₂ x hx
  let eE : Edge G := ⟨s.1.2, s.2.1⟩
  have hva : s.vAgent = Sum.inl s.1.1 := rfl
  have hea : s.eAgent = Sum.inr eE := rfl
  have hUv := util_v (G := G) (k := k) α x s.1.1
  have hUe : utility (redUtil G k α) x (Sum.inr eE) = 1 - α + α * esh x eE := by
    rw [util_e, hF1, if_pos rfl]
  have hvsh : vsh x s.1.1 = sharedOther x (Sum.inl s.1.1) s +
      if x s.item = Sum.inl s.1.1 then 1 else 0 := by
    rw [sharedOther, vsh]
    rw [card_split (fun s' : Inc G => x s'.item = Sum.inl s.1.1 ∧ s'.1.1 = s.1.1) s]
    simp only [and_true]
    congr 1
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro s' _
    simp only [Inc.item]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      rcases hF2 s' with h' | h'
      · simp only [Inc.item] at h'; rw [h.2, Inc.vAgent] at h'; exact (Sum.inl_injective h').symm
      · simp only [Inc.item] at h'; rw [h.2, Inc.eAgent] at h'; simp at h'
  have hesh : esh x eE = sharedOther x (Sum.inr eE) s +
      if x s.item = Sum.inr eE then 1 else 0 := by
    rw [sharedOther, esh]
    rw [card_split (fun s' : Inc G => x s'.item = Sum.inr eE ∧ eE.1 = s'.1.2) s]
    simp only [eE, and_true]
    congr 1
    refine congrArg Finset.card (Finset.filter_congr ?_)
    intro s' _
    simp only [Inc.item]
    constructor
    · exact fun h => ⟨h.1, h.2.1⟩
    · intro h
      refine ⟨h.1, h.2, ?_⟩
      rcases hF2 s' with h' | h'
      · simp only [Inc.item] at h'; rw [h.2, Inc.vAgent] at h'; simp at h'
      · simp only [Inc.item] at h'; rw [h.2, Inc.eAgent] at h'
        have := congrArg Subtype.val (Sum.inr_injective h')
        exact this
  have ha2 : sharedOther x (Sum.inl s.1.1) s ≤ 2 := by
    have h3 := fiber_v hG s.1.1
    rw [card_split (fun s' : Inc G => s'.1.1 = s.1.1) s, if_pos rfl] at h3
    have : sharedOther x (Sum.inl s.1.1) s ≤ #{b : Inc G | b ≠ s ∧ b.1.1 = s.1.1} := by
      apply card_le_card
      intro s' hs'
      simp only [mem_filter, mem_univ, true_and] at hs' ⊢
      refine ⟨hs'.1, ?_⟩
      rcases hF2 s' with h' | h'
      · have := hs'.2; simp only [Inc.item] at h'; rw [this, Inc.vAgent] at h'
        exact (Sum.inl_injective h').symm
      · have := hs'.2; simp only [Inc.item] at h'; rw [this, Inc.eAgent] at h'; simp at h'
    omega
  have hr1 : sharedOther x (Sum.inr eE) s ≤ 1 := by
    have h3 := fiber_e (G := G) eE
    rw [card_split (fun s' : Inc G => s'.1.2 = eE.1) s, if_pos rfl] at h3
    have : sharedOther x (Sum.inr eE) s ≤ #{b : Inc G | b ≠ s ∧ b.1.2 = eE.1} := by
      apply card_le_card
      intro s' hs'
      simp only [mem_filter, mem_univ, true_and] at hs' ⊢
      refine ⟨hs'.1, ?_⟩
      rcases hF2 s' with h' | h'
      · have := hs'.2; simp only [Inc.item] at h'; rw [this, Inc.vAgent] at h'; simp at h'
      · have := hs'.2; simp only [Inc.item] at h'; rw [this, Inc.eAgent] at h'
        exact (congrArg Subtype.val (Sum.inr_injective h')).symm
    omega
  have hn1 := hv1 s.1.1
  have hne : (Sum.inl s.1.1 : Agent G) ≠ Sum.inr eE := by simp
  -- the two move inequalities
  have hAtV : x s.item = Sum.inl s.1.1 →
      ((vItems x s.1.1 : ℝ) + (sharedOther x (Sum.inl s.1.1) s : ℝ) / 3) *
        (1 - α + α * ((sharedOther x (Sum.inr eE) s : ℝ) + 1)) ≤
      ((vItems x s.1.1 : ℝ) + ((sharedOther x (Sum.inl s.1.1) s : ℝ) + 1) / 3) *
        (1 - α + α * (sharedOther x (Sum.inr eE) s : ℝ)) := by
    intro hs
    have hm := move _ hu x hx hpos s.item (Sum.inr eE) (by rw [hs]; exact hne.symm)
    rw [hs, hUv, hUe, hvsh, hesh, if_pos hs, if_neg (by rw [hs]; exact hne)] at hm
    simp only [redUtil, Inc.item, eE, if_true] at hm
    push_cast at hm
    linarith
  have hAtE : x s.item = Sum.inr eE →
      (1 - α + α * (sharedOther x (Sum.inr eE) s : ℝ)) *
        ((vItems x s.1.1 : ℝ) + ((sharedOther x (Sum.inl s.1.1) s : ℝ) + 1) / 3) ≤
      (1 - α + α * ((sharedOther x (Sum.inr eE) s : ℝ) + 1)) *
        ((vItems x s.1.1 : ℝ) + (sharedOther x (Sum.inl s.1.1) s : ℝ) / 3) := by
    intro hs
    have hm := move _ hu x hx hpos s.item (Sum.inl s.1.1) (by rw [hs]; exact hne)
    rw [hs, hUv, hUe, hvsh, hesh, if_pos hs, if_neg (by rw [hs]; exact hne.symm)] at hm
    simp only [redUtil, Inc.item, eE, if_true] at hm
    push_cast at hm
    linarith
  unfold Rule
  rw [hva, hea]
  generalize hn : vItems x s.1.1 = n at hAtV hAtE hn1
  generalize ha : sharedOther x (Sum.inl s.1.1) s = a at hAtV hAtE ha2
  generalize hr : sharedOther x (Sum.inr eE) s = r at hAtV hAtE hr1
  rcases hF2 s with hs | hs
  · rw [hva] at hs
    have h := hAtV hs
    clear hAtE hUv hUe hvsh hesh hF1 hF2 hpos hu hx hn ha hr
    split_ifs with c1 c2 c3
    · exfalso; subst c1
      interval_cases a <;> interval_cases r <;> norm_num at h <;> linarith
    · exact hs
    · exfalso
      have : n = 0 := by omega
      have : r = 0 := by omega
      subst_vars; norm_num at h; linarith
    · exact hs
  · rw [hea] at hs
    have h := hAtE hs
    clear hAtV hUv hUe hvsh hesh hF1 hF2 hpos hu hx hn ha hr
    split_ifs with c1 c2 c3
    · exact hs
    · exfalso
      have : n = 0 := by omega
      subst_vars
      interval_cases a <;> norm_num at h <;> linarith
    · exact hs
    · exfalso
      have : n = 0 := by omega
      have : r = 0 := by omega
      subst_vars
      interval_cases a <;> norm_num at h <;> first | linarith | omega

end P2MH

open P2MH in
theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k : ℕ) (α : ℝ)
    (hG : IsCubic G) (hα₁ : 1 / 3 < α) (hα₂ : α < 1 / 2) (hk : k < N) :
    ∃ x : Item G k → Agent G, IsOptimal (redUtil G k α) x ∧ (∀ v : Fin N, vItems x v ≤ 1) ∧
      ∀ s : Inc G, Rule x s := by
  obtain ⟨x, hx, hv⟩ := lemma_2_2 G k α hG hα₁ hα₂ hk
  exact ⟨x, hx, hv, rule_of_opt hG hα₁ hα₂ x hx hv⟩
