-- Prove2me | solution 1 for HeldKarp.Gap.w_lp_form
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T12:12:25.079072+00:00
-- url     : https://prove2.me/submissions/e656b6e9-4bdc-4bd2-aa64-195cd8f08dad

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Gap_SubtourLP
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction
import Theorems.Thm_HeldKarp_Gap_gap_eq


open Finset

namespace X6HK

/-- Layer-cake (Abel summation) inequality. -/
theorem layer {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℝ) (hw : ∑ e ∈ s, w e = 0) :
    ∀ (k : ℕ) (d : α → ℝ), (s.image d).card ≤ k →
    (∀ t ∈ s.image d, ∑ e ∈ s.filter (fun e => d e ≤ t), w e ≤ 0) →
    0 ≤ ∑ e ∈ s, d e * w e := by
  intro k
  induction k with
  | zero =>
    intro d hk _
    have h0 : s.image d = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
    rw [Finset.image_eq_empty] at h0
    simp [h0]
  | succ k ih =>
    intro d hk hpre
    rcases s.eq_empty_or_nonempty with hs | hs
    · simp [hs]
    have hI : (s.image d).Nonempty := hs.image d
    set m := (s.image d).min' hI with hmdef
    by_cases hone : (s.image d).card ≤ 1
    · have hc : ∀ e ∈ s, d e = m := fun e he =>
        Finset.card_le_one.mp hone (d e) (mem_image_of_mem d he) m (min'_mem _ _)
      rw [Finset.sum_congr rfl (fun e he => by rw [hc e he]), ← Finset.mul_sum, hw, mul_zero]
    · push Not at hone
      have hE : ((s.image d).erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem (min'_mem _ _)]; omega
      set m2 := ((s.image d).erase m).min' hE with hm2def
      have hm2mem := min'_mem _ hE
      rw [← hm2def] at hm2mem
      have hm2img : m2 ∈ s.image d := (Finset.mem_erase.mp hm2mem).2
      have hm2 : m < m2 := by
        have h1 := Finset.mem_erase.mp hm2mem
        exact lt_of_le_of_ne (min'_le _ _ h1.2) (Ne.symm h1.1)
      have hval : ∀ e ∈ s, d e = m ∨ m2 ≤ d e := by
        intro e he
        by_cases h : d e = m
        · exact Or.inl h
        · exact Or.inr (min'_le _ _ (mem_erase.mpr ⟨h, mem_image_of_mem d he⟩))
      have hmle : ∀ e ∈ s, m ≤ d e := fun e he => min'_le _ _ (mem_image_of_mem d he)
      set d' : α → ℝ := fun e => max (d e) m2 with hd'
      have hsub : s.image d' ⊆ (s.image d).erase m := by
        intro t ht
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
        rcases hval e he with h | h
        · have : d' e = m2 := by simp only [hd']; rw [h]; exact max_eq_right hm2.le
          rw [this]; exact hm2mem
        · have : d' e = d e := by simp only [hd']; exact max_eq_left h
          rw [this]
          exact mem_erase.mpr ⟨by linarith, mem_image_of_mem d he⟩
      have hcard : (s.image d').card ≤ k := by
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (min'_mem _ _)] at this
        omega
      have hpre' : ∀ t ∈ s.image d', ∑ e ∈ s.filter (fun e => d' e ≤ t), w e ≤ 0 := by
        intro t ht
        have ht2 := hsub ht
        have htm2 : m2 ≤ t := by
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
          exact le_max_right _ _
        have hfeq : s.filter (fun e => d' e ≤ t) = s.filter (fun e => d e ≤ t) := by
          apply Finset.filter_congr
          intro e _
          simp only [hd', max_le_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, htm2⟩⟩
        rw [hfeq]
        exact hpre t (Finset.mem_erase.mp ht2).2
      have hrec := ih d' hcard hpre'
      have hdiff : ∑ e ∈ s, d e * w e = ∑ e ∈ s, d' e * w e +
          (m - m2) * ∑ e ∈ s.filter (fun e => d e ≤ m), w e := by
        rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e he
        rcases hval e he with h | h
        · have h1 : d' e = m2 := by simp only [hd']; rw [h]; exact max_eq_right hm2.le
          rw [h1, if_pos h.le, h]; ring
        · have h1 : d' e = d e := by simp only [hd']; exact max_eq_left h
          rw [h1, if_neg (by linarith)]; ring
      rw [hdiff]
      have := hpre m (min'_mem _ _)
      have : 0 ≤ (m - m2) * ∑ e ∈ s.filter (fun e => d e ≤ m), w e :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) this
      linarith

/-- Transfer of sums over the off-diagonal pairs inside a predicate to the subtype. -/
theorem sum_inside {V : Type*} [Fintype V] [DecidableEq V] (p : V → Prop) [DecidablePred p]
    (f : Sym2 V → ℝ) :
    ∑ e ∈ univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∀ v ∈ e, p v), f e =
      ∑ e ∈ univ.filter (fun e : Sym2 (Subtype p) => ¬ e.IsDiag), f (e.map Subtype.val) := by
  symm
  apply Finset.sum_nbij (fun e => e.map Subtype.val)
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    refine ⟨?_, ?_⟩
    · rwa [Sym2.isDiag_map Subtype.val_injective]
    · intro v hv
      obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp hv
      exact a.2
  · intro a _ b _ h
    exact Sym2.map.injective Subtype.val_injective h
  · intro e he
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at he
    induction e using Sym2.ind with
    | h a b =>
      have ha : p a := he.2 a (Sym2.mem_mk_left a b)
      have hb : p b := he.2 b (Sym2.mem_mk_right a b)
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
        rw [Sym2.mk_isDiag_iff] at he ⊢
        exact fun h => he.1 (congrArg Subtype.val h)
      · simp [Sym2.map_mk]
  · intro e _; rfl

/-- off-diagonal pairs -/
def E (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  univ.filter (fun e : Sym2 V => ¬ e.IsDiag)

/-- off-diagonal pairs inside `S` -/
def inside {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) : Finset (Sym2 V) :=
  univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ S)

/-- Partition bound: if `y ≥ 0` satisfies the subtour bounds on all nonempty sets, then the
`y`-mass of the pairs inside the blocks of any partition is at most `|V| - #blocks`. -/
theorem partition_upper {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : V → ι) (y : Sym2 V → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hsub : ∀ S : Finset V, S.Nonempty → ∑ e ∈ inside S, y e ≤ (S.card : ℝ) - 1) :
    ∑ e ∈ (E V).filter (fun e => ∀ u ∈ e, ∀ v ∈ e, p u = p v), y e ≤
      (Fintype.card V : ℝ) - ((univ : Finset V).image p).card := by
  set F := (E V).filter (fun e => ∀ u ∈ e, ∀ v ∈ e, p u = p v)
  have h1 : ∑ e ∈ F, y e = ∑ i ∈ (univ : Finset V).image p,
      ∑ e ∈ F.filter (fun e => p (Quot.out e).1 = i), y e := by
    rw [Finset.sum_fiberwise_of_maps_to]
    intro e _
    exact Finset.mem_image_of_mem p (Finset.mem_univ _)
  have h2 : ∀ i, F.filter (fun e => p (Quot.out e).1 = i) =
      inside (univ.filter (fun v => p v = i)) := by
    intro i
    ext e
    simp only [F, E, inside, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hd, hc⟩, hi⟩
      exact ⟨hd, fun v hv => by rw [← hi]; exact hc v hv _ (Sym2.out_fst_mem e)⟩
    · rintro ⟨hd, hc⟩
      refine ⟨⟨hd, fun u hu v hv => by rw [hc u hu, hc v hv]⟩, hc _ (Sym2.out_fst_mem e)⟩
  rw [h1]
  have h3 : ∀ i ∈ (univ : Finset V).image p,
      ∑ e ∈ F.filter (fun e => p (Quot.out e).1 = i), y e ≤
        ((univ.filter (fun v => p v = i)).card : ℝ) - 1 := by
    intro i hi
    rw [h2]
    apply hsub
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hi
    exact ⟨v, by simp [hv]⟩
  calc _ ≤ ∑ i ∈ (univ : Finset V).image p,
        (((univ.filter (fun v => p v = i)).card : ℝ) - 1) := Finset.sum_le_sum h3
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Finset.card_univ]

end X6HK


open Finset

namespace X6HK

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem card_edges_eq (H : SimpleGraph V) [DecidableRel H.Adj] :
    (H.edgeFinset.card : ℝ) = ∑ e ∈ E V, if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext e
  simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_edgeFinset]
  exact ⟨fun h => ⟨H.not_isDiag_of_mem_edgeSet h, h⟩, fun h => h.2⟩

omit [Fintype V] [DecidableEq V] in
theorem mem_edgeSet_induce (H : SimpleGraph V) (p : V → Prop) (e : Sym2 (Subtype p)) :
    e ∈ (H.induce {v | p v}).edgeSet ↔ e.map Subtype.val ∈ H.edgeSet := by
  induction e using Sym2.ind with
  | h a b => simp [Sym2.map_mk]

/-- edges of an induced subgraph = edges inside the vertex set -/
theorem card_induce (H : SimpleGraph V) [DecidableRel H.Adj] (p : V → Prop) [DecidablePred p]
    [DecidableRel (H.induce {v | p v}).Adj] :
    ((H.induce {v | p v}).edgeFinset.card : ℝ) =
      ∑ e ∈ univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∀ v ∈ e, p v),
        if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
  rw [sum_inside p, card_edges_eq]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mem_edgeSet_induce]

/-- A graph has at least `|V| - #components` edges. -/
theorem lower (H : SimpleGraph V) [DecidableRel H.Adj] [DecidableEq H.ConnectedComponent] :
    (Fintype.card V : ℝ) - ((univ : Finset V).image H.connectedComponentMk).card ≤
      ∑ e ∈ E V, if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
  classical
  set p := H.connectedComponentMk
  -- per block bound
  have hblock : ∀ i ∈ (univ : Finset V).image p,
      ((univ.filter (fun v => p v = i)).card : ℝ) - 1 ≤
        ∑ e ∈ univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∀ v ∈ e, p v = i),
          if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
    intro i hi
    rw [← card_induce H (fun v => p v = i)]
    have hconn : (H.induce {v | p v = i}).Connected := i.connected_toSimpleGraph
    have h := hconn.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Fintype.card_ofFinset] at h
    have : ((univ.filter (fun v => p v = i)).card : ℝ) ≤
        ((H.induce {v | p v = i}).edgeFinset.card : ℝ) + 1 := by exact_mod_cast h
    linarith
  calc (Fintype.card V : ℝ) - ((univ : Finset V).image p).card
      = ∑ i ∈ (univ : Finset V).image p, (((univ.filter (fun v => p v = i)).card : ℝ) - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        congr 1
        rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_image, Finset.card_univ]
    _ ≤ ∑ i ∈ (univ : Finset V).image p,
        ∑ e ∈ univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∀ v ∈ e, p v = i),
          if e ∈ H.edgeSet then (1 : ℝ) else 0 := Finset.sum_le_sum hblock
    _ = ∑ i ∈ (univ : Finset V).image p,
        ∑ e ∈ (E V).filter (fun e => p (Quot.out e).1 = i),
          if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_filter, Finset.sum_filter, E, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hd : e.IsDiag
        · simp [hd]
        by_cases he : e ∈ H.edgeSet
        · have hc : ∀ v ∈ e, p v = p (Quot.out e).1 := by
            have ho := Sym2.out_fst_mem e
            induction e using Sym2.ind with
            | h a b =>
              have hab : p a = p b := SimpleGraph.ConnectedComponent.sound (H.adj_iff_exists_edge.mpr
                ⟨by simpa using hd, s(a, b), he, by simp⟩ |>.reachable)
              intro v hv
              rcases Sym2.mem_iff.mp hv with rfl | rfl <;> rcases Sym2.mem_iff.mp ho with h | h <;>
                rw [h] <;> simp [hab]
          simp only [hd, not_false_eq_true, true_and, he, if_true]
          by_cases hi : p (Quot.out e).1 = i
          · simp only [hi, if_true]; rw [if_pos (fun v hv => (hc v hv).trans hi)]
          · rw [if_neg hi, if_neg (fun h => hi (h _ (Sym2.out_fst_mem e)))]
        · simp [he]
    _ = ∑ e ∈ E V, if e ∈ H.edgeSet then (1 : ℝ) else 0 := by
        rw [Finset.sum_fiberwise_of_maps_to]
        intro e _
        exact Finset.mem_image_of_mem p (Finset.mem_univ _)

/-- nested spanning forests along a monotone family of graphs -/
theorem nested (G : ℝ → SimpleGraph V) (hmono : Monotone G) (τ : Finset ℝ) :
    ∃ T : SimpleGraph V, T.IsAcyclic ∧ (∀ b, (∀ x ∈ τ, x ≤ b) → T ≤ G b) ∧
      ∀ t ∈ τ, ∀ u v, (T ⊓ G t).Reachable u v ↔ (G t).Reachable u v := by
  induction τ using Finset.induction_on_max with
  | empty => exact ⟨⊥, SimpleGraph.isAcyclic_bot, fun _ _ => bot_le, fun t ht => by simp at ht⟩
  | insert a s hlt ih =>
    obtain ⟨T, hT, hle, hreach⟩ := ih
    have hTa : T ≤ G a := hle a (fun x hx => (hlt x hx).le)
    obtain ⟨F, hTF, hFG, hF, hFr⟩ :=
      SimpleGraph.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hTa hT
    refine ⟨F, hF, ?_, ?_⟩
    · intro b hb
      exact hFG.trans (hmono (hb a (Finset.mem_insert_self a s)))
    · intro t ht u v
      rcases Finset.mem_insert.mp ht with rfl | ht
      · rw [inf_eq_left.mpr hFG, hFr]
      · constructor
        · intro h; exact h.mono inf_le_right
        · intro h
          exact ((hreach t ht u v).mpr h).mono (inf_le_inf_right _ hTF)

end X6HK


open Finset

namespace X6HK

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- Spanning-tree LP bound: every point of the spanning-tree polytope has cost at least
that of some spanning tree. -/
theorem ST [Nonempty V] (y d : Sym2 V → ℝ) (hy : ∀ e, 0 ≤ y e)
    (hsub : ∀ S : Finset V, S.Nonempty → ∑ e ∈ inside S, y e ≤ (S.card : ℝ) - 1)
    (htot : ∑ e ∈ E V, y e = (Fintype.card V : ℝ) - 1) :
    ∃ T : SimpleGraph V, T.IsTree ∧
      ∑ e ∈ E V, d e * (if e ∈ T.edgeSet then (1 : ℝ) else 0) ≤ ∑ e ∈ E V, d e * y e := by
  classical
  let G : ℝ → SimpleGraph V := fun t => SimpleGraph.fromRel (fun u v => d s(u, v) ≤ t)
  have hmono : Monotone G := by
    intro a b hab u v h
    simp only [G, SimpleGraph.fromRel_adj] at h ⊢
    rcases h with ⟨hne, h | h⟩
    · exact ⟨hne, Or.inl (h.trans hab)⟩
    · exact ⟨hne, Or.inr (h.trans hab)⟩
  set τ := (E V).image d
  obtain ⟨T, hT, -, hreach⟩ := nested G hmono τ
  have key : ∀ e ∈ E V, ∀ t, d e ≤ t → ∀ u ∈ e, ∀ v ∈ e, (G t).Reachable u v := by
    intro e he t hdt
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.mk_isDiag_iff] at he
      have hadj : (G t).Adj a b := by
        simp only [G, SimpleGraph.fromRel_adj]; exact ⟨he, Or.inl hdt⟩
      intro u hu v hv
      rcases Sym2.mem_iff.mp hu with rfl | rfl <;> rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable
      · exact hadj.reachable.symm
      · exact SimpleGraph.Reachable.refl _
  have hconn : ∀ u v, T.Reachable u v := by
    intro u v
    by_cases huv : u = v
    · subst huv; exact SimpleGraph.Reachable.refl _
    have he : s(u, v) ∈ E V := by
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff]; exact huv
    have ht : d s(u, v) ∈ τ := Finset.mem_image_of_mem d he
    have := (hreach _ ht u v).mpr (key _ he _ le_rfl u (Sym2.mem_mk_left _ _) v
      (Sym2.mem_mk_right _ _))
    exact this.mono inf_le_left
  have hTree : T.IsTree := ⟨⟨hconn⟩, hT⟩
  refine ⟨T, hTree, ?_⟩
  set z : Sym2 V → ℝ := fun e => if e ∈ T.edgeSet then (1 : ℝ) else 0 with hz
  have hzsum : ∑ e ∈ E V, z e = (Fintype.card V : ℝ) - 1 := by
    rw [← card_edges_eq T]
    have := hTree.card_edgeFinset
    have h2 : ((T.edgeFinset.card : ℕ) : ℝ) + 1 = (Fintype.card V : ℝ) := by
      exact_mod_cast this
    linarith
  have hw : ∑ e ∈ E V, (y e - z e) = 0 := by
    rw [Finset.sum_sub_distrib, htot, hzsum]; ring
  have hpre : ∀ t ∈ τ, ∑ e ∈ (E V).filter (fun e => d e ≤ t), (y e - z e) ≤ 0 := by
    intro t ht
    set H := T ⊓ G t
    set p := H.connectedComponentMk
    have hA : ∑ e ∈ (E V).filter (fun e => d e ≤ t), y e ≤
        ∑ e ∈ (E V).filter (fun e => ∀ u ∈ e, ∀ v ∈ e, p u = p v), y e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [Finset.mem_filter] at he ⊢
        refine ⟨he.1, fun u hu v hv => ?_⟩
        exact SimpleGraph.ConnectedComponent.sound ((hreach t ht u v).mpr
          (key e he.1 t he.2 u hu v hv))
      · intro e _ _; exact hy e
    have hB := partition_upper p y hy hsub
    have hC := lower H
    have hD : (∑ e ∈ E V, if e ∈ H.edgeSet then (1 : ℝ) else 0) ≤
        ∑ e ∈ (E V).filter (fun e => d e ≤ t), z e := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro e he
      by_cases hH : e ∈ H.edgeSet
      · rw [if_pos hH]
        have hTe : e ∈ T.edgeSet := SimpleGraph.edgeSet_mono inf_le_left hH
        have hGe : e ∈ (G t).edgeSet := SimpleGraph.edgeSet_mono inf_le_right hH
        have hdt : d e ≤ t := by
          induction e using Sym2.ind with
          | h a b =>
            simp only [SimpleGraph.mem_edgeSet, G, SimpleGraph.fromRel_adj] at hGe
            rcases hGe with ⟨-, h | h⟩
            · exact h
            · rwa [Sym2.eq_swap]
        rw [if_pos hdt, hz]; simp only; rw [if_pos hTe]
      · rw [if_neg hH]
        split_ifs <;> simp [hz] <;> split_ifs <;> norm_num
    rw [Finset.sum_sub_distrib]
    have : ((univ : Finset V).image p).card = ((univ : Finset V).image p).card := rfl
    linarith
  have := layer (E V) (fun e => y e - z e) hw _ d le_rfl hpre
  have h2 : ∑ e ∈ E V, d e * (y e - z e) =
      ∑ e ∈ E V, d e * y e - ∑ e ∈ E V, d e * z e := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro e _; ring
  rw [h2] at this
  linarith

end X6HK


open Finset Classical
open HeldKarp.Ascent HeldKarp.Gap

namespace X6HK

/-- extension of an edge function to all of `Sym2 (Fin n)` -/
noncomputable def ext {n : ℕ} (x : Edge n → ℝ) (e : Sym2 (Fin n)) : ℝ :=
  if h : e.IsDiag then 0 else x ⟨e, h⟩

theorem ext_val {n : ℕ} (x : Edge n → ℝ) (e : Edge n) : ext x e.1 = x e := by
  simp [ext, e.2]

theorem sum_edge {n : ℕ} (h : Edge n → ℝ) (H : Sym2 (Fin n) → ℝ)
    (hH : ∀ e : Edge n, h e = H e.1) :
    ∑ e : Edge n, h e = ∑ e ∈ E (Fin n), H e := by
  rw [Finset.sum_subtype (E (Fin n)) (p := fun e : Sym2 (Fin n) => ¬ e.IsDiag)]
  · exact Finset.sum_congr rfl (fun e _ => hH e)
  · intro e; simp [E]

theorem L_deg {n : ℕ} (x : Edge n → ℝ) (i : Fin n) :
    deg x i = ∑ e ∈ E (Fin n), if i ∈ e then ext x e else 0 := by
  unfold deg
  rw [Finset.sum_filter]
  apply sum_edge
  intro e
  simp only [ext_val]

theorem L_total {n : ℕ} (x : Edge n → ℝ) : total x = ∑ e ∈ E (Fin n), ext x e := by
  unfold total
  apply sum_edge
  intro e; rw [ext_val]

theorem L_inside {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) :
    insideSum x S = ∑ e ∈ E (Fin n), if (∀ v ∈ e, v ∈ S) then ext x e else 0 := by
  unfold insideSum
  rw [Finset.sum_filter]
  apply sum_edge
  intro e
  simp only [ext_val]

theorem L_lin {n : ℕ} (D x : Edge n → ℝ) :
    ∑ e : Edge n, D e * x e = ∑ e ∈ E (Fin n), ext D e * ext x e := by
  apply sum_edge
  intro e; rw [ext_val, ext_val]

/-- the non-root vertices -/
abbrev Wn (n : ℕ) [NeZero n] := ↥({v : Fin n | v ≠ 0} : Set (Fin n))

theorem split {n : ℕ} [NeZero n] (F : Sym2 (Fin n) → ℝ) :
    ∑ e ∈ E (Fin n), F e = ∑ a : Wn n, F s(0, a.1) +
      ∑ e ∈ E (Wn n), F (e.map Subtype.val) := by
  rw [← Finset.sum_filter_add_sum_filter_not (E (Fin n)) (fun e => (0 : Fin n) ∈ e)]
  congr 1
  · symm
    apply Finset.sum_nbij (fun a : Wn n => s(0, a.1))
    · intro a _
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff,
        Sym2.mem_mk_left, and_true]
      exact fun h => a.2 h.symm
    · intro a _ b _ h
      exact Subtype.ext (Sym2.congr_right.mp h)
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      obtain ⟨he1, he2⟩ := he
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he1
      obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp he2
      have hb : b ≠ 0 := by
        intro hb; subst hb; exact he1 (Sym2.mk_isDiag_iff.mpr rfl)
      exact ⟨⟨b, hb⟩, by simp, rfl⟩
    · intro a _; rfl
  · have hf : (E (Fin n)).filter (fun e => ¬ (0 : Fin n) ∈ e) =
        univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧
          ∀ v ∈ e, v ∈ ({v : Fin n | v ≠ 0} : Set (Fin n))) := by
      ext e
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun v hv h => h2 (h ▸ hv)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 0 h rfl⟩
    rw [hf]
    convert sum_inside (fun v => v ∈ ({v : Fin n | v ≠ 0} : Set (Fin n))) F using 1 <;>
      first | rfl | (congr 1; ext e; simp [E]) | (congr 1)

/-- choose the two cheapest coordinates -/
theorem two_min {ι : Type*} [Fintype ι] [DecidableEq ι] (u D : ι → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    (hu1 : ∀ i, u i ≤ 1) (hsum : ∑ i, u i = 2) (hcard : 2 ≤ Fintype.card ι) :
    ∃ a b, a ≠ b ∧ D a + D b ≤ ∑ i, D i * u i := by
  have hne : (univ : Finset ι).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]; omega
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image univ D hne
  have hne2 : ((univ : Finset ι).erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]; omega
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image _ D hne2
  have hab : b ≠ a := (Finset.mem_erase.mp hb).1
  refine ⟨a, b, hab.symm, ?_⟩
  have h1 : ∑ i, D i * u i = ∑ i, (D i - D b) * u i + D b * 2 := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have h2 : ∑ i, (D i - D b) * u i = (D a - D b) * u a +
      ∑ i ∈ (univ : Finset ι).erase a, (D i - D b) * u i := by
    exact (Finset.add_sum_erase _ (fun i => (D i - D b) * u i) (Finset.mem_univ a)).symm
  have h3 : 0 ≤ ∑ i ∈ (univ : Finset ι).erase a, (D i - D b) * u i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (by linarith [hbmin i hi]) (hu0 i)
  have h4 : D a - D b ≤ (D a - D b) * u a := by
    have : D a - D b ≤ 0 := by linarith [ha b (Finset.mem_univ b)]
    nlinarith [hu1 a]
  linarith

/-- the 1-tree built from a tree on the non-root vertices and two root edges -/
def mk1 {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (a b : Wn n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v : Fin n =>
    (∃ (hu : u ≠ 0) (hv : v ≠ 0), T.Adj ⟨u, hu⟩ ⟨v, hv⟩) ∨ (u = 0 ∧ (v = a.1 ∨ v = b.1)))

theorem mk1_induce {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (a b : Wn n) :
    (mk1 T a b).induce {v : Fin n | v ≠ 0} = T := by
  ext x y
  simp only [SimpleGraph.comap_adj, SimpleGraph.induce, mk1, SimpleGraph.fromRel_adj]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  have hx' : x ≠ 0 := hx
  have hy' : y ≠ 0 := hy
  simp only [Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨-, (⟨_, _, h⟩ | ⟨h, -⟩) | (⟨_, _, h⟩ | ⟨h, -⟩)⟩
    · exact h
    · exact absurd h hx'
    · exact h.symm
    · exact absurd h hy'
  · intro h
    refine ⟨fun e => T.ne_of_adj h (Subtype.ext e), Or.inl (Or.inl ⟨hx', hy', h⟩)⟩

theorem mk1_adj0 {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (a b : Wn n) (v : Fin n) :
    (mk1 T a b).Adj 0 v ↔ v = a.1 ∨ v = b.1 := by
  simp only [mk1, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (⟨h, _, _⟩ | ⟨-, h⟩) | (⟨_, h, _⟩ | ⟨h, -⟩)⟩
    · exact absurd rfl h
    · exact h
    · exact absurd rfl h
    · exact absurd h.symm hne
  · intro h
    refine ⟨?_, Or.inl (Or.inr ⟨by trivial, h⟩)⟩
    rcases h with h | h <;> (subst h; first | exact fun e => a.2 e.symm | exact fun e => b.2 e.symm)

theorem mk1_oneTree {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (hT : T.IsTree) (a b : Wn n)
    (hab : a ≠ b) : IsOneTree (mk1 T a b) := by
  refine ⟨?_, ?_⟩
  · rw [mk1_induce]; exact hT
  · rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (mk1 T a b).neighborFinset 0 = {a.1, b.1} := by
      ext v
      rw [SimpleGraph.mem_neighborFinset, mk1_adj0]
      simp
    rw [this, Finset.card_pair (fun h => hab (Subtype.ext h))]

theorem mk1_edge0 {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (a b : Wn n) (w : Wn n) :
    s(0, w.1) ∈ (mk1 T a b).edgeSet ↔ w = a ∨ w = b := by
  rw [SimpleGraph.mem_edgeSet, mk1_adj0]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem mk1_edgeW {n : ℕ} [NeZero n] (T : SimpleGraph (Wn n)) (a b : Wn n) (e : Sym2 (Wn n)) :
    e.map Subtype.val ∈ (mk1 T a b).edgeSet ↔ e ∈ T.edgeSet := by
  have := mk1_induce T a b
  conv_rhs => rw [← this]
  exact (mem_edgeSet_induce (mk1 T a b) (fun v => v ≠ 0) e).symm

end X6HK


open Finset Classical
open HeldKarp.Ascent HeldKarp.Gap

namespace X6HK

theorem ext_inc {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    ext (incidence G) e = if e ∈ G.edgeSet then 1 else 0 := by
  unfold ext incidence
  simp [he]

theorem not_mem_map_zero {n : ℕ} [NeZero n] (e : Sym2 (Wn n)) :
    (0 : Fin n) ∉ e.map Subtype.val := by
  intro h
  obtain ⟨w, -, hw⟩ := Sym2.mem_map.mp h
  exact w.2 hw

theorem cardW {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (Fintype.card (Wn n) : ℝ) = n - 1 := by
  have h := Set.card_ne_eq (0 : Fin n)
  rw [Fintype.card_fin] at h
  rw [h, Nat.cast_sub (by omega)]
  simp

theorem inside_eq {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    inside S = (E V).filter (fun e => ∀ v ∈ e, v ∈ S) := by
  ext e; simp [inside, E]

theorem core {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : Edge n → ℝ) (hx : x ∈ OneTreePolyhedron n)
    (D : Sym2 (Fin n) → ℝ) :
    ∃ G : SimpleGraph (Fin n), IsOneTree G ∧
      ∑ e ∈ E (Fin n), D e * ext (incidence G) e ≤ ∑ e ∈ E (Fin n), D e * ext x e := by
  obtain ⟨h0, htot, hsubt, hle1, hge0⟩ := hx
  set X := ext x with hXdef
  have hX0 : ∀ e, 0 ≤ X e := by
    intro e; simp only [hXdef, ext]; split_ifs
    · exact le_rfl
    · exact hge0 _
  have hX1 : ∀ e, X e ≤ 1 := by
    intro e; simp only [hXdef, ext]; split_ifs
    · exact zero_le_one
    · exact hle1 _
  set y : Sym2 (Wn n) → ℝ := fun e => X (e.map Subtype.val) with hydef
  have hdeg0 : deg x 0 = ∑ a : Wn n, X s(0, a.1) := by
    rw [L_deg, split]
    have h2 : ∑ e ∈ E (Wn n), (if (0 : Fin n) ∈ e.map Subtype.val then
        X (e.map Subtype.val) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg (not_mem_map_zero e)]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    intro a _
    rw [if_pos (Sym2.mem_mk_left _ _)]
  have htot' : total x = ∑ a : Wn n, X s(0, a.1) + ∑ e ∈ E (Wn n), y e := by
    rw [L_total, split]
  have hyW : ∑ e ∈ E (Wn n), y e = (n : ℝ) - 2 := by
    rw [htot', ← hdeg0, h0] at htot; linarith
  have hcW := cardW hn
  have hsub : ∀ S' : Finset (Wn n), S'.Nonempty →
      ∑ e ∈ inside S', y e ≤ (S'.card : ℝ) - 1 := by
    intro S' hS'
    by_cases hfull : S' = univ
    · subst hfull
      have : inside (univ : Finset (Wn n)) = E (Wn n) := by
        rw [inside_eq]; ext e; simp
      rw [this, hyW, Finset.card_univ, hcW]; linarith
    · set S := S'.map (Function.Embedding.subtype _) with hSdef
      have hSne : S.Nonempty := hS'.map
      have h0S : (0 : Fin n) ∉ S := by
        intro h
        obtain ⟨w, -, hw⟩ := Finset.mem_map.mp h
        exact w.2 hw
      have hSsub : S ⊂ univ.erase 0 := by
        rw [Finset.ssubset_iff_of_subset]
        · obtain ⟨w, hw⟩ : ∃ w, w ∉ S' := by
            by_contra hc; push Not at hc
            exact hfull (Finset.eq_univ_of_forall hc)
          refine ⟨w.1, Finset.mem_erase.mpr ⟨w.2, Finset.mem_univ _⟩, ?_⟩
          intro h
          obtain ⟨w', hw', hww⟩ := Finset.mem_map.mp h
          exact hw (by rw [show w = w' from Subtype.ext hww.symm]; exact hw')
        · intro v hv
          exact Finset.mem_erase.mpr ⟨fun h => h0S (h ▸ hv), Finset.mem_univ _⟩
      have hcS : S.card = S'.card := Finset.card_map _
      have := hsubt S hSne hSsub
      rw [L_inside, split, hcS] at this
      have h1 : ∑ a : Wn n, (if (∀ v ∈ s(0, a.1), v ∈ S) then X s(0, a.1) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [if_neg (fun h => h0S (h 0 (Sym2.mem_mk_left _ _)))]
      rw [h1, zero_add] at this
      convert this using 1
      rw [inside_eq, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      have hiff : (∀ v ∈ e.map Subtype.val, v ∈ S) ↔ (∀ w ∈ e, w ∈ S') := by
        constructor
        · intro h w hw
          obtain ⟨w', hw', hww⟩ := Finset.mem_map.mp (h w.1 (Sym2.mem_map.mpr ⟨w, hw, rfl⟩))
          rw [show w = w' from Subtype.ext hww.symm]; exact hw'
        · intro h v hv
          obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hv
          exact Finset.mem_map_of_mem _ (h w hw)
      by_cases hc : ∀ w ∈ e, w ∈ S'
      · rw [if_pos hc, if_pos (hiff.mpr hc)]
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mp h))]
  have h1n : ((⟨1, by omega⟩ : Fin n)) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  haveI : Nonempty (Wn n) := ⟨⟨⟨1, by omega⟩, h1n⟩⟩
  have hyW' : ∑ e ∈ E (Wn n), y e = (Fintype.card (Wn n) : ℝ) - 1 := by
    rw [hyW, hcW]; ring
  obtain ⟨T, hT, hTle⟩ := ST y (fun e => D (e.map Subtype.val)) (fun e => hX0 _) hsub hyW'
  have hcard2 : 2 ≤ Fintype.card (Wn n) := by
    have : (2 : ℝ) ≤ Fintype.card (Wn n) := by
      rw [hcW]; have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact_mod_cast this
  have hu2 : ∑ a : Wn n, X s(0, a.1) = 2 := by rw [← hdeg0, h0]
  obtain ⟨a0, b0, hab, hAB⟩ := two_min (fun a : Wn n => X s(0, a.1))
    (fun a : Wn n => D s(0, a.1)) (fun a => hX0 _) (fun a => hX1 _) hu2 hcard2
  refine ⟨mk1 T a0 b0, mk1_oneTree T hT a0 b0 hab, ?_⟩
  rw [split, split]
  have hA : ∑ a : Wn n, D s(0, a.1) * ext (incidence (mk1 T a0 b0)) s(0, a.1) =
      D s(0, a0.1) + D s(0, b0.1) := by
    have : ∀ a : Wn n, D s(0, a.1) * ext (incidence (mk1 T a0 b0)) s(0, a.1) =
        (if a = a0 then D s(0, a.1) else 0) + (if a = b0 then D s(0, a.1) else 0) := by
      intro a
      rw [ext_inc _ _ (by rw [Sym2.mk_isDiag_iff]; exact fun h => a.2 h.symm)]
      by_cases h1 : a = a0
      · subst h1
        rw [if_pos ((mk1_edge0 T a b0 a).mpr (Or.inl rfl)), if_pos rfl, if_neg hab]; ring
      · by_cases h2 : a = b0
        · subst h2
          rw [if_pos ((mk1_edge0 T a0 a a).mpr (Or.inr rfl)), if_neg h1, if_pos rfl]; ring
        · rw [if_neg (fun h => by rcases (mk1_edge0 T a0 b0 a).mp h with h | h <;> contradiction),
            if_neg h1, if_neg h2]; ring
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  have hB : ∑ e ∈ E (Wn n), D (e.map Subtype.val) *
      ext (incidence (mk1 T a0 b0)) (e.map Subtype.val) =
      ∑ e ∈ E (Wn n), D (e.map Subtype.val) * (if e ∈ T.edgeSet then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro e he
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [ext_inc _ _ (by rwa [Sym2.isDiag_map Subtype.val_injective])]
    by_cases h : e ∈ T.edgeSet
    · rw [if_pos ((mk1_edgeW T a0 b0 e).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((mk1_edgeW T a0 b0 e).mp h')), if_neg h]
  rw [hA, hB]
  simp only [hydef] at hTle
  linarith

end X6HK


open Finset Classical
open HeldKarp.Ascent HeldKarp.Gap

namespace X6HK

theorem deg_inc {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    deg (incidence G) i = G.degree i := by
  unfold deg incidence
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter, ← SimpleGraph.card_incidenceFinset_eq_degree]
  congr 1
  refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨he.2, he.1⟩
  · intro e₁ _ e₂ _ h; exact Subtype.ext h
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    refine ⟨⟨e, G.not_isDiag_of_mem_edgeSet he.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨he.2, he.1⟩

theorem deg0_split {n : ℕ} [NeZero n] (x : Edge n → ℝ) :
    deg x 0 = ∑ a : Wn n, ext x s(0, a.1) := by
  rw [L_deg, split]
  have h2 : ∑ e ∈ E (Wn n), (if (0 : Fin n) ∈ e.map Subtype.val then
      ext x (e.map Subtype.val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg (not_mem_map_zero e)]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [if_pos (Sym2.mem_mk_left _ _)]

/-- an acyclic graph on a nonempty finite type has at most `|U| - 1` edges -/
theorem acyc_card {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U] (A : SimpleGraph U)
    [DecidableRel A.Adj] (hA : A.IsAcyclic) :
    (A.edgeFinset.card : ℝ) ≤ Fintype.card U - 1 := by
  obtain ⟨F, hAF, -, hF⟩ :=
    SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic le_top hA
  have h1 := hF.card_edgeFinset
  have h2 : A.edgeFinset.card ≤ F.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hAF)
  have : ((A.edgeFinset.card : ℕ) : ℝ) + 1 ≤ (Fintype.card U : ℝ) := by
    exact_mod_cast (by omega : A.edgeFinset.card + 1 ≤ Fintype.card U)
  linarith

theorem inc_mem {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph (Fin n)) (hG : IsOneTree G) :
    incidence G ∈ OneTreePolyhedron n := by
  obtain ⟨hT, hd⟩ := hG
  have hdeg : deg (incidence G) 0 = 2 := by rw [deg_inc, hd]; norm_num
  refine ⟨hdeg, ?_, ?_, ?_, ?_⟩
  · rw [L_total, split, ← deg0_split, hdeg]
    have h1 : ∑ e ∈ E (Wn n), ext (incidence G) (e.map Subtype.val) =
        ((G.induce {v : Fin n | v ≠ 0}).edgeFinset.card : ℝ) := by
      rw [card_edges_eq]
      apply Finset.sum_congr rfl
      intro e he
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [ext_inc _ _ (by rwa [Sym2.isDiag_map Subtype.val_injective])]
      have := mem_edgeSet_induce G (fun v => v ≠ 0) e
      by_cases h : e ∈ (G.induce {v : Fin n | v ≠ 0}).edgeSet
      · simp [this.mp h, h]
      · have h' : Sym2.map Subtype.val e ∉ G.edgeSet := fun h' => h (this.mpr h')
        simp [h]; exact h'
    rw [h1]
    have h2 := hT.card_edgeFinset
    have h3 := cardW hn
    have : ((G.induce {v : Fin n | v ≠ 0}).edgeFinset.card : ℝ) + 1 = Fintype.card (Wn n) := by
      exact_mod_cast h2
    linarith
  · intro S hS hSsub
    rw [L_inside]
    have hS0 : ∀ v ∈ S, v ≠ 0 := by
      intro v hv h; subst h
      exact (Finset.notMem_erase 0 univ) (hSsub.subset hv)
    have h1 : (∑ e ∈ E (Fin n), if (∀ v ∈ e, v ∈ S) then ext (incidence G) e else 0) =
        ∑ e ∈ univ.filter (fun e : Sym2 (Fin n) => ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ S),
          if e ∈ G.edgeSet then (1 : ℝ) else 0 := by
      rw [E, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hd : e.IsDiag
      · simp [hd]
      · rw [ext_inc _ _ hd]; simp [hd]
    rw [h1]
    have hacyc : (G.induce {v : Fin n | v ∈ S}).IsAcyclic := by
      have hle : ({v : Fin n | v ∈ S} : Set (Fin n)) ≤ {v : Fin n | v ≠ 0} :=
        fun v hv => hS0 v hv
      exact hT.isAcyclic.embedding (SimpleGraph.induceHomOfLE G hle)
    obtain ⟨v0, hv0⟩ := hS
    haveI : Nonempty (↥({v : Fin n | v ∈ S} : Set (Fin n))) := ⟨⟨v0, hv0⟩⟩
    have := acyc_card _ hacyc
    have hc : Fintype.card (↥({v : Fin n | v ∈ S} : Set (Fin n))) = S.card := by
      rw [Fintype.card_subtype]; congr 1; ext v; simp
    rw [hc] at this
    convert this using 1
    convert (card_induce G (fun v => v ∈ S)).symm
  · intro e; unfold incidence; split_ifs <;> norm_num
  · intro e; unfold incidence; split_ifs <;> norm_num

theorem inc_extreme {n : ℕ} [NeZero n] (G : SimpleGraph (Fin n))
    (hG : incidence G ∈ OneTreePolyhedron n) :
    incidence G ∈ Set.extremePoints ℝ (OneTreePolyhedron n) := by
  rw [mem_extremePoints]
  refine ⟨hG, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hseg
  have key : ∀ e, x1 e = incidence G e ∧ x2 e = incidence G e := by
    intro e
    have he := congrFun hx e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at he
    have h10 := hx1.2.2.2.2 e
    have h11 := hx1.2.2.2.1 e
    have h20 := hx2.2.2.2.2 e
    have h21 := hx2.2.2.2.1 e
    unfold incidence at he ⊢
    split_ifs at he ⊢
    · constructor <;> nlinarith [mul_nonneg ha.le (sub_nonneg.mpr h11),
        mul_nonneg hb.le (sub_nonneg.mpr h21)]
    · constructor <;> nlinarith [mul_nonneg ha.le h10, mul_nonneg hb.le h20]
  exact ⟨funext fun e => (key e).1, funext fun e => (key e).2⟩

theorem convexP {n : ℕ} [NeZero n] : Convex ℝ (OneTreePolyhedron n) := by
  intro x hx y hy a b ha hb hab
  have hdeg : ∀ i, deg (a • x + b • y) i = a * deg x i + b * deg y i := by
    intro i; unfold deg
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have htot : total (a • x + b • y) = a * total x + b * total y := by
    unfold total; simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hin : ∀ S, insideSum (a • x + b • y) S = a * insideSum x S + b * insideSum y S := by
    intro S; unfold insideSum; simp [Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdeg, hx0, hy0]; linear_combination 2 * hab
  · rw [htot, hx1, hy1]; linear_combination (n : ℝ) * hab
  · intro S hS hSs
    rw [hin]
    have h1 := hx2 S hS hSs
    have h2 := hy2 S hS hSs
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · intro e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hx3 e) ha, mul_le_mul_of_nonneg_left (hy3 e) hb]
  · intro e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_nonneg ha (hx4 e), mul_nonneg hb (hy4 e)]

theorem clm_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) :
    f z = ∑ i, f (Pi.single i 1) * z i := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Pi.single i (z i) : ι → ℝ) = z i • Pi.single i (1 : ℝ) by
    ext j; simp [Pi.single_apply], map_smul, smul_eq_mul, mul_comm]

theorem theorem_1 {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    Set.extremePoints ℝ (OneTreePolyhedron n) =
      incidence '' {G : SimpleGraph (Fin n) | IsOneTree G} := by
  set S := incidence '' {G : SimpleGraph (Fin n) | IsOneTree G}
  have hSP : S ⊆ OneTreePolyhedron n := by
    rintro _ ⟨G, hG, rfl⟩; exact inc_mem hn G hG
  apply Set.Subset.antisymm
  · intro x hx
    have hKP : convexHull ℝ S ⊆ OneTreePolyhedron n := convexHull_min hSP convexP
    have hxK : x ∈ convexHull ℝ S := by
      by_contra hxK
      have hcl : IsClosed (convexHull ℝ S) := (Set.Finite.isCompact_convexHull ℝ (Set.toFinite S)).isClosed
      obtain ⟨f, u, hfx, hfK⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ S) hcl hxK
      obtain ⟨G, hG, hle⟩ := core hn x hx.1 (ext (fun e => f (Pi.single e 1)))
      have h1 : f (incidence G) ≤ f x := by
        rw [clm_sum f (incidence G), clm_sum f x, L_lin, L_lin]
        exact hle
      have h2 := hfK (incidence G) (subset_convexHull ℝ S ⟨G, hG, rfl⟩)
      linarith
    have := inter_extremePoints_subset_extremePoints_of_subset (𝕜 := ℝ) hKP ⟨hxK, hx⟩
    exact extremePoints_convexHull_subset (𝕜 := ℝ) this
  · rintro _ ⟨G, hG, rfl⟩
    exact inc_extreme G (inc_mem hn G hG)

end X6HK


open Finset Classical
open HeldKarp.Ascent HeldKarp.Gap

namespace X6HK

theorem oneTree_exists {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ G : SimpleGraph (Fin n), IsOneTree G := by
  have h1 : (⟨1, by omega⟩ : Fin n) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  have h2 : (⟨2, by omega⟩ : Fin n) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  haveI : Nonempty (Wn n) := ⟨⟨⟨1, by omega⟩, h1⟩⟩
  obtain ⟨T, -, hT⟩ := (SimpleGraph.connected_top (V := Wn n)).exists_isTree_le
  refine ⟨mk1 T ⟨⟨1, by omega⟩, h1⟩ ⟨⟨2, by omega⟩, h2⟩, mk1_oneTree T hT _ _ ?_⟩
  intro h
  have := congrArg (fun w : Wn n => (w.1 : ℕ)) h
  simp at this

/-- `x ↦ Σ_i π_i (deg x i)` is linear with coefficients `Σ_{i ∈ e} π_i` -/
theorem pi_deg {n : ℕ} (π : Fin n → ℝ) (x : Edge n → ℝ) :
    ∑ i, π i * deg x i = ∑ e ∈ E (Fin n), (∑ i, if i ∈ e then π i else 0) * ext x e := by
  simp_rw [L_deg, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

theorem cost_eq {n : ℕ} (c : Sym2 (Fin n) → ℝ) (x : Edge n → ℝ) :
    cost c x = ∑ e ∈ E (Fin n), c e * ext x e := by
  unfold cost
  apply sum_edge
  intro e; rw [ext_val]

theorem weight_eq {n : ℕ} (c : Sym2 (Fin n) → ℝ) (G : SimpleGraph (Fin n)) :
    weight c G = cost c (incidence G) := by
  rw [cost_eq]
  unfold weight
  have : G.edgeFinset = (E (Fin n)).filter (fun e => e ∈ G.edgeSet) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨G.not_isDiag_of_mem_edgeSet h, h⟩, fun h => h.2⟩
  rw [this, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [ext_inc _ _ he]
  split_ifs <;> simp

theorem card_edges_oneTree {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsOneTree G) : ∑ i, ((G.degree i : ℝ) - 2) = 0 := by
  have h1 := (inc_mem hn G hG).2.1
  rw [L_total] at h1
  have h2 : ∑ e ∈ E (Fin n), ext (incidence G) e = (G.edgeFinset.card : ℝ) := by
    rw [card_edges_eq]
    apply Finset.sum_congr rfl
    intro e he
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [ext_inc _ _ he]
  have h3 := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have h4 : ∑ i, (G.degree i : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
    have : ((∑ i, G.degree i : ℕ) : ℝ) = ((2 * G.edgeFinset.card : ℕ) : ℝ) := by
      rw [h3]
    push_cast at this
    convert this using 2
  rw [Finset.sum_sub_distrib, h4, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [h1] at h2
  simp only [nsmul_eq_mul]
  linarith

theorem lagr_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π π' : Fin n → ℝ)
    (h : ∀ i : Fin n, i ≠ 0 → i ≠ lastV n → π i - π (lastV n) = π' i - π' (lastV n))
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) :
    lagrWeight c π G = lagrWeight c π' G := by
  unfold lagrWeight degExcess
  have hsum := card_edges_oneTree hn G hG
  set δn := π (lastV n) - π' (lastV n)
  have key : ∑ i, π i * ((G.degree i : ℝ) - 2) - ∑ i, π' i * ((G.degree i : ℝ) - 2) =
      δn * ∑ i, ((G.degree i : ℝ) - 2) +
        ∑ i, ((π i - π' i) - δn) * ((G.degree i : ℝ) - 2) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  have hz : ∑ i, ((π i - π' i) - δn) * ((G.degree i : ℝ) - 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h0 : i = 0
    · subst h0; rw [hG.2]; norm_num
    · by_cases hl : i = lastV n
      · subst hl; simp [δn]
      · have := h i h0 hl
        have : π i - π' i - δn = 0 := by simp only [δn]; linarith
        rw [this, zero_mul]
  rw [hsum, mul_zero, zero_add, hz] at key
  linarith

theorem bound_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π π' : Fin n → ℝ)
    (h : ∀ i : Fin n, i ≠ 0 → i ≠ lastV n → π i - π (lastV n) = π' i - π' (lastV n)) :
    oneTreeBound c π = oneTreeBound c π' := by
  unfold oneTreeBound
  congr 1
  ext t
  constructor
  · rintro ⟨G, hG, rfl⟩; exact ⟨G, hG, lagr_eq hn c π π' h G hG⟩
  · rintro ⟨G, hG, rfl⟩; exact ⟨G, hG, (lagr_eq hn c π π' h G hG).symm⟩

theorem w_lp_form {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) :
    (∀ π π' : Fin n → ℝ,
        (∀ i : Fin n, i ≠ 0 → i ≠ lastV n → π i - π (lastV n) = π' i - π' (lastV n)) →
        gap c π = gap c π') ∧
      (∀ π : Fin n → ℝ, π 0 = 0 → π (lastV n) = 0 →
        IsLeast ((fun x : Edge n → ℝ => cost c x +
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≠ 0 ∧ i ≠ lastV n),
              π i * (deg x i - 2)) '' OneTreePolyhedron n)
          (oneTreeBound c π)) := by
  refine ⟨?_, ?_⟩
  · intro π π' h
    rw [(gap_eq hn c π).2, (gap_eq hn c π').2, bound_eq hn c π π' h]
  · intro π h0 hl
    set L : (Edge n → ℝ) → ℝ := fun x => cost c x +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≠ 0 ∧ i ≠ lastV n), π i * (deg x i - 2)
    have hL : ∀ x, L x = ∑ e ∈ E (Fin n), (c e + ∑ i, if i ∈ e then π i else 0) * ext x e -
        2 * ∑ i, π i := by
      intro x
      simp only [L]
      rw [Finset.sum_filter]
      have : ∀ i : Fin n, (if i ≠ 0 ∧ i ≠ lastV n then π i * (deg x i - 2) else 0) =
          π i * deg x i - 2 * π i := by
        intro i
        split_ifs with hi
        · ring
        · push Not at hi
          by_cases hi0 : i = 0
          · subst hi0; rw [h0]; ring
          · rw [hi hi0, hl]; ring
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, pi_deg, cost_eq,
        ← Finset.mul_sum]
      have : ∑ e ∈ E (Fin n), (c e + ∑ i, if i ∈ e then π i else 0) * ext x e =
          ∑ e ∈ E (Fin n), c e * ext x e +
            ∑ e ∈ E (Fin n), (∑ i, if i ∈ e then π i else 0) * ext x e := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro e _; ring
      rw [this]; ring
    have hLG : ∀ G : SimpleGraph (Fin n), L (incidence G) = lagrWeight c π G := by
      intro G
      simp only [L]
      unfold lagrWeight degExcess
      rw [weight_eq, Finset.sum_filter]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [deg_inc]
      split_ifs with hi
      · rfl
      · push Not at hi
        by_cases hi0 : i = 0
        · subst hi0; rw [h0]; ring
        · rw [hi hi0, hl]; ring
    set Sset := {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ x = lagrWeight c π G}
    have hfin : Sset.Finite := by
      apply (Set.finite_range (fun G : SimpleGraph (Fin n) => lagrWeight c π G)).subset
      rintro t ⟨G, -, rfl⟩; exact ⟨G, rfl⟩
    obtain ⟨G1, hG1⟩ := oneTree_exists hn
    have hne : Sset.Nonempty := ⟨_, G1, hG1, rfl⟩
    have hmem := hne.csInf_mem hfin
    have hbdd := hfin.bddBelow
    refine ⟨?_, ?_⟩
    · obtain ⟨G0, hG0, heq⟩ := hmem
      exact ⟨incidence G0, inc_mem hn G0 hG0, by rw [hLG]; exact heq.symm⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨G, hG, hle⟩ := core hn x hx (fun e => c e + ∑ i, if i ∈ e then π i else 0)
      have h1 : L (incidence G) ≤ L x := by rw [hL, hL]; linarith
      have h2 : oneTreeBound c π ≤ lagrWeight c π G := csInf_le hbdd ⟨G, hG, rfl⟩
      rw [← hLG] at h2
      exact h2.trans h1

end X6HK


open Classical
open HeldKarp.Ascent HeldKarp.Gap

theorem solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) :
    (∀ π π' : Fin n → ℝ,
        (∀ i : Fin n, i ≠ 0 → i ≠ lastV n → π i - π (lastV n) = π' i - π' (lastV n)) →
        gap c π = gap c π') ∧
      (∀ π : Fin n → ℝ, π 0 = 0 → π (lastV n) = 0 →
        IsLeast ((fun x : Edge n → ℝ => cost c x +
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≠ 0 ∧ i ≠ lastV n),
              π i * (deg x i - 2)) '' OneTreePolyhedron n)
          (oneTreeBound c π)) :=
  X6HK.w_lp_form hn c
