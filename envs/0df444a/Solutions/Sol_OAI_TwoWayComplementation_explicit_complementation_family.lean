-- Prove2me | solution 1 for OAI.TwoWayComplementation.explicit_complementation_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:12:58.824448+00:00
-- url     : https://prove2.me/submissions/472acd8a-52f5-4d3a-bf12-b09d81f940dd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/ExplicitFamily.lean:L7-L33
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.explicit_complementation_family. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Main
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationBridge
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_TransitionBridge

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Eliminate the left block by replacing each finite excursion with one edge. -/
theorem blockRelation_star_right {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : β) :
    ((Sum.inr x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (Sum.inr x, c) ∈ relStar R) :
      match c with
      | .inl a => (x, a) ∈ relStar K ○ G ○ relStar E
      | .inr b => (x, b) ∈ relStar K := by
    induction hrun with
    | refl => exact .refl
    | @tail c d _ hcd ih =>
      cases c with
      | inl a =>
        obtain ⟨p, ⟨q, hxq, hqp⟩, hpa⟩ := ih
        cases d with
        | inl b => exact ⟨p, ⟨q, hxq, hqp⟩, hpa.tail hcd⟩
        | inr b => exact hxq.tail (Or.inr ⟨a, ⟨p, hqp, hpa⟩, hcd⟩)
      | inr a =>
        cases d with
        | inl b => exact ⟨b, ⟨a, ih, hcd⟩, .refl⟩
        | inr b => exact ih.tail (Or.inl hcd)
  constructor
  · exact hsound
  · intro hxy
    exact hxy.lift' (Sum.inr : β → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (by
        intro a b hab
        rcases hab with hH | ⟨q, ⟨p, hag, hpq⟩, hfb⟩
        · exact .single hH
        · have hmid := hpq.lift (Sum.inl : α → α ⊕ β)
            (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
          exact (hmid.head hag).tail hfb)

/-- A path from the left block first leaves it once, then makes arbitrary finite excursions. -/
theorem blockRelation_star_cross {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : α) (y : β) :
    ((Sum.inl x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar E ○ F ○ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (c, Sum.inr y) ∈ relStar R) :
      ∀ x, c = Sum.inl x → (x, y) ∈ relStar E ○ F ○ relStar K := by
    induction hrun using Relation.ReflTransGen.head_induction_on with
    | refl => intro _ heq; cases heq
    | @head c d hcd hdy ih =>
      intro x hcx
      subst c
      cases d with
      | inl a =>
        obtain ⟨u, ⟨v, hxv, hvu⟩, huy⟩ := ih a rfl
        exact ⟨u, ⟨v, hxv.head hcd, hvu⟩, huy⟩
      | inr b =>
        exact ⟨b, ⟨x, .refl, hcd⟩, (blockRelation_star_right E F G H b y).mp hdy⟩
  constructor
  · intro hxy
    exact hsound hxy x rfl
  · rintro ⟨v, ⟨u, hxu, huv⟩, hvy⟩
    have hleft := hxu.lift (Sum.inl : α → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
    have hcross : (Sum.inl x, Sum.inr v) ∈ relStar R := hleft.tail huv
    exact hcross.trans ((blockRelation_star_right E F G H v y).mpr hvy)

/-- A path lost after an edge replacement contains a lost edge between old path segments. -/
theorem relStar_lost_edge {α : Type*} (R S : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ relStar R) (hnot : (x, y) ∉ relStar S) :
    ∃ a b, (x, a) ∈ relStar R ∧ (a, b) ∈ R ∧ (a, b) ∉ S ∧ (b, y) ∈ relStar R := by
  classical
  induction hxy with
  | refl => exact (hnot Relation.ReflTransGen.refl).elim
  | @tail a b hxa hab ih =>
    by_cases hgood : (x, a) ∈ relStar S
    · refine ⟨a, b, hxa, hab, ?_, .refl⟩
      exact fun habS => hnot (hgood.tail habS)
    · obtain ⟨u, v, hxu, huv, hnuv, hva⟩ := ih hgood
      exact ⟨u, v, hxu, huv, hnuv, hva.tail hab⟩

/-- A lost alternating traversal has a lost edge, allowing earlier and later bounces. -/
theorem feedback_lost_edge {α : Type*} (E E' B : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ E ○ relStar (B ○ E))
    (hnot : (x, y) ∉ E' ○ relStar (B ○ E')) :
    ∃ a b, (x, a) ∈ relStar (E ○ B) ∧ (a, b) ∈ E ∧
      (a, b) ∉ E' ∧ (b, y) ∈ relStar (B ○ E) := by
  classical
  obtain ⟨z, hxz, hzy⟩ := hxy
  by_cases hfirst : (x, z) ∈ E'
  · have hnzy : (z, y) ∉ relStar (B ○ E') := fun h => hnot ⟨z, hfirst, h⟩
    obtain ⟨a, b, hza, ⟨c, hac, hcb⟩, hnab, hby⟩ :=
      relStar_lost_edge (B ○ E) (B ○ E') hzy hnzy
    have hprefix : (x, a) ∈ relStar (E ○ B) ○ E := by
      rw [← comp_relStar_rotate]
      exact ⟨z, hxz, hza⟩
    obtain ⟨d, hxd, hda⟩ := hprefix
    exact ⟨c, b, hxd.tail ⟨a, hda, hac⟩, hcb, fun h => hnab ⟨c, hac, h⟩, hby⟩
  · exact ⟨x, z, .refl, hxz, hfirst, hzy⟩

theorem feedback_insert {α : Type*} (E B : SetRel α α) :
    relStar (E ○ B) ○ E ○ relStar (B ○ E) = E ○ relStar (B ○ E) := by
  rw [← comp_relStar_rotate, SetRel.comp_assoc, relStar_comp_self]

/-- A bound for weighted classes with integer weights one and two. -/
theorem weighted_class_bound {α β : Type*} (X M : Finset α) (Y : Finset β)
    (R : β → α → Prop) (hM : M ⊆ X)
    (hunique : ∀ y ∈ Y, ∀ z ∈ Y, ∀ x ∈ X, R y x → R z x → y = z)
    (hcover : ∀ y ∈ Y,
      (∃ x ∈ X, x ∉ M ∧ R y x) ∨
        ∃ x ∈ X, ∃ z ∈ X, x ≠ z ∧ R y x ∧ R y z) :
    2 * Y.card + M.card ≤ 2 * X.card := by
  classical
  let F : β → Finset α := fun y => X.filter (R y)
  let w : α → ℕ := fun x => if x ∈ M then 1 else 2
  have hweight : ∀ y ∈ Y, 2 ≤ ∑ x ∈ F y, w x := by
    intro y hy
    rcases hcover y hy with ⟨x, hx, hxm, hxy⟩ | ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    · have h := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
        (show x ∈ F y from Finset.mem_filter.mpr ⟨hx, hxy⟩)
      simpa [w, hxm] using h
    · have hsub : ({x, z} : Finset α) ⊆ F y := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_filter.mpr ⟨hx, hxy⟩
        · have haeq := Finset.mem_singleton.mp ha
          subst a
          exact Finset.mem_filter.mpr ⟨hz, hzy⟩
      have h := Finset.sum_le_sum_of_subset hsub (f := w)
      have hxw : 1 ≤ w x := by unfold w; split_ifs <;> omega
      have hzw : 1 ≤ w z := by unfold w; split_ifs <;> omega
      simp only [Finset.sum_pair hxz] at h
      omega
  have hdisjoint : Set.PairwiseDisjoint (↑Y) F := by
    intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    obtain ⟨hx, hxy⟩ := Finset.mem_filter.mp hxy
    obtain ⟨_, hxz⟩ := Finset.mem_filter.mp hxz
    exact hne (hunique y hy z hz x hx hxy hxz)
  have hsum : 2 * Y.card ≤ ∑ x ∈ X, w x := by
    calc
      _ = ∑ _ ∈ Y, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, ∑ x ∈ F y, w x := Finset.sum_le_sum hweight
      _ = ∑ x ∈ Y.biUnion F, w x := (Finset.sum_biUnion hdisjoint).symm
      _ ≤ ∑ x ∈ X, w x := Finset.sum_le_sum_of_subset (by
        intro x hx
        obtain ⟨y, _, hxy⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_filter.mp hxy).1)
  have hfilter : X.filter (· ∈ M) = M := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hM hx, hx⟩⟩
  have hindicator : (∑ x ∈ X, if x ∈ M then 1 else 0) = M.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have htotal : (∑ x ∈ X, w x) + M.card = 2 * X.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ ∈ X, 2 := Finset.sum_congr rfl (fun x _ => by
        unfold w; split_ifs <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Every edge of a finite idempotent relation factors through a recurrent point. -/
theorem idempotent_relation_factor {α : Type*} [Finite α] (P : SetRel α α)
    (hP : P ○ P = P) {u v : α} (huv : (u, v) ∈ P) :
    ∃ p, (u, p) ∈ P ∧ (p, p) ∈ P ∧ (p, v) ∈ P := by
  classical
  have htrans {a b c : α} (hab : (a, b) ∈ P) (hbc : (b, c) ∈ P) :
      (a, c) ∈ P := hP ▸ (show (a, c) ∈ P ○ P from ⟨b, hab, hbc⟩)
  let T := {x : α // (x, v) ∈ P}
  have hnext : ∀ x : T, ∃ y : T, (x.val, y.val) ∈ P := by
    intro x
    have hx : (x.val, v) ∈ P ○ P := hP.symm ▸ x.property
    obtain ⟨y, hxy, hyv⟩ := hx
    exact ⟨⟨y, hyv⟩, hxy⟩
  choose f hf using hnext
  have hpath (x : T) (n : ℕ) : (x.val, (f^[n + 1] x).val) ∈ P := by
    induction n with
    | zero => exact hf x
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact htrans ih (hf _)
  let x : T := ⟨u, huv⟩
  obtain ⟨i, j, hij, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (fun n : ℕ => Set.mem_univ (f^[n] x))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hloop := hpath (f^[i] x) k
  rw [← Function.iterate_add_apply, Nat.add_comm] at hloop
  rw [← Nat.add_assoc, ← heq] at hloop
  refine ⟨(f^[i] x).val, ?_, hloop, (f^[i] x).property⟩
  cases i with
  | zero => exact hloop
  | succ i => exact hpath x i

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem inclusion_refl {m : ℕ} (a : Diagram m) : (a, a) ∈ inclusion m :=
  ⟨Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl⟩

theorem mem_port_through {m : ℕ} (e : Diagram m) (positive : Bool) (p q : Fin m) :
    ((!positive, p), (positive, q)) ∈ e.portRelation ↔ (p, q) ∈ e.through positive := by
  cases positive <;> rfl

theorem feedback_forward {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {p q : Fin m} :
    ((false, p), (true, q)) ∈ e.feedback R L ↔
      (p, q) ∈ relStar (e.left ○ R) ○ e.forward ○
        relStar (L ○ (e.right ∪ (e.backward ○ R ○ relStar (e.left ○ R) ○ e.forward))) := by
  let S := relStar (e.left ○ R)
  let P := e.right ∪ (e.backward ○ R ○ S ○ e.forward)
  let V := relStar (L ○ P)
  let E := e.portRelation
  let B := bounceRelation R L
  have hbound {a b : Bool × Fin m} (hab : (a, b) ∈ relStar (B ○ E)) (hb : b.1 = true) :
      (a.2, b.2) ∈ if a.1 then V else R ○ S ○ e.forward ○ V := by
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => simp only [hb, ite_true]; exact Relation.ReflTransGen.refl
    | @head a c hac _ ih =>
      obtain ⟨mid, hB, hE⟩ := hac
      obtain ⟨sa, x⟩ := a
      obtain ⟨sc, y⟩ := c
      obtain ⟨sm, z⟩ := mid
      obtain ⟨hside, hreturn⟩ := hB
      change sa = sm at hside
      subst sm
      cases sa <;> cases sc
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact ⟨t, ⟨u, ⟨z, hreturn, hvu.head ⟨y, hE, hyv⟩⟩, hut⟩, htb⟩
      · exact ⟨y, ⟨z, ⟨z, hreturn, .refl⟩, hE⟩, ih⟩
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact htb.head ⟨z, hreturn, Or.inr ⟨u, ⟨v, ⟨y, hE, hyv⟩, hvu⟩, hut⟩⟩
      · exact ih.head ⟨z, hreturn, Or.inl hE⟩
  constructor
  · rintro ⟨⟨side, x⟩, hfirst, hrest⟩
    have h := hbound hrest rfl
    cases side
    · obtain ⟨t, ⟨u, ⟨v, hxv, hvu⟩, hut⟩, htq⟩ := h
      exact ⟨t, ⟨u, hvu.head ⟨x, hfirst, hxv⟩, hut⟩, htq⟩
    · exact ⟨x, ⟨p, .refl, hfirst⟩, h⟩
  · intro hpq
    have hS {x y : Fin m} (hxy : (x, y) ∈ S) :
        ((false, x), (false, y)) ∈ relStar (E ○ B) := by
      exact hxy.lift (fun a => (false, a)) (fun _ _ ⟨z, hxz, hzy⟩ =>
        ⟨(false, z), hxz, rfl, hzy⟩)
    have hV {x y : Fin m} (hxy : (x, y) ∈ V) :
        ((true, x), (true, y)) ∈ relStar (B ○ E) := by
      apply hxy.lift' (fun a => (true, a))
      rintro a b ⟨z, haz, hzb⟩
      rcases hzb with hright | ⟨u, ⟨v, ⟨w, hzw, hwv⟩, hvu⟩, hub⟩
      · exact Relation.ReflTransGen.single ⟨(true, z), ⟨rfl, haz⟩, hright⟩
      · have hmid : ((false, w), (false, u)) ∈ B ○ relStar (E ○ B) :=
          ⟨(false, v), ⟨rfl, hwv⟩, hS hvu⟩
        rw [comp_relStar_rotate] at hmid
        obtain ⟨c, hwc, hcu⟩ := hmid
        have htail : ((false, w), (true, b)) ∈ relStar (B ○ E) :=
          hwc.tail ⟨(false, u), hcu, hub⟩
        have hstart : ((true, a), (false, w)) ∈ B ○ E :=
          ⟨(true, z), ⟨rfl, haz⟩, hzw⟩
        exact htail.head hstart
    obtain ⟨b, ⟨a, hpa, hab⟩, hbq⟩ := hpq
    have h : ((false, p), (true, q)) ∈ relStar (E ○ B) ○ E ○ relStar (B ○ E) :=
      ⟨(true, b), ⟨(false, a), hS hpa, hab⟩, hV hbq⟩
    rwa [feedback_insert] at h

theorem feedback_reflect_map {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} (h : ((s, p), (t, q)) ∈ e.feedback R L) :
    ((!s, p), (!t, q)) ∈ (reflect e).feedback L R := by
  have hE {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ (reflect e).portRelation := by
    obtain ⟨sa, a⟩ := a
    obtain ⟨sb, b⟩ := b
    cases sa <;> cases sb <;> exact hab
  have hB {a b : Bool × Fin m} (hab : (a, b) ∈ bounceRelation R L) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ bounceRelation L R := by
    obtain ⟨sa, x⟩ := a
    obtain ⟨sb, y⟩ := b
    obtain ⟨hside, hreturn⟩ := hab
    refine ⟨congrArg Bool.not hside, ?_⟩
    cases sa <;> exact hreturn
  obtain ⟨a, hfirst, hrest⟩ := h
  refine ⟨(!a.1, a.2), hE hfirst, ?_⟩
  exact hrest.lift (fun a => (!a.1, a.2))
    (p := fun a b => (a, b) ∈ bounceRelation L R ○ (reflect e).portRelation)
    (fun _ _ ⟨b, hab, hbc⟩ => ⟨(!b.1, b.2), hB hab, hE hbc⟩)

theorem mem_feedback_reflect {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} :
    ((s, p), (t, q)) ∈ (reflect e).feedback L R ↔
      ((!s, p), (!t, q)) ∈ e.feedback R L := by
  constructor
  · exact feedback_reflect_map (reflect e) L R
  · intro h
    simpa only [Bool.not_not] using feedback_reflect_map e R L h

theorem context_forward_iff {m : ℕ} (u e v : Diagram m) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).forward ↔
      ∃ a b, (p, a) ∈ u.forward ∧
        ((false, a), (true, b)) ∈ e.feedback u.right v.left ∧ (b, q) ∈ v.forward := by
  simp only [feedback_forward, comp, SetRel.comp_assoc, SetRel.mem_comp]
  aesop

theorem context_through_iff {m : ℕ} (u e v : Diagram m) (positive : Bool) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).through positive ↔
      ∃ a b, (p, a) ∈ (if positive then u.forward else v.backward) ∧
        ((!positive, a), (positive, b)) ∈ e.feedback u.right v.left ∧
        (b, q) ∈ (if positive then v.forward else u.backward) := by
  cases positive
  · have h := context_forward_iff (reflect v) (reflect e) (reflect u) (p := p) (q := q)
    have hd : comp (comp (reflect v) (reflect e)) (reflect u) =
        reflect (comp (comp u e) v) := by
      rw [comp_assoc, ← reflect_comp, ← reflect_comp]
    rw [hd] at h
    simp only [mem_feedback_reflect] at h
    exact h
  · exact context_forward_iff u e v

theorem context_surviving {m : ℕ} (d u e v : Diagram m) (positive : Bool) :
    d.surviving (comp (comp u e) v) positive =
      contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
  ext ⟨p, q⟩
  constructor
  · rintro ⟨b, ⟨a, hpa, hab⟩, hbq⟩
    obtain ⟨c, f, hac, hcf, hfb⟩ := (context_through_iff u e v positive).mp hab
    exact ⟨(positive, f), ⟨(!positive, c), ⟨rfl, a, hpa, hac⟩, hcf⟩,
      ⟨rfl, b, hfb, hbq⟩⟩
  · rintro ⟨⟨t, b⟩, ⟨⟨s, a⟩, ⟨hs, c, hpc, hca⟩, hab⟩, ⟨ht, f, hbf, hfq⟩⟩
    change s = !positive at hs
    change t = positive at ht
    subst s
    subst t
    exact ⟨f, ⟨c, hpc, (context_through_iff u e v positive).mpr ⟨a, b, hca, hab, hbf⟩⟩, hfq⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem corner_comp {m : ℕ} {e z w : Diagram m} (hz : z ∈ e.corner)
    (hw : w ∈ e.corner) : comp z w ∈ e.corner := by
  constructor
  · rw [← comp_assoc, hz.1]
  · rw [comp_assoc, hw.2]

theorem corner_pow_succ {m : ℕ} {e z : Diagram m} (hz : z ∈ e.corner) (k : ℕ) :
    z ^ (k + 1) ∈ e.corner := by
  induction k with
  | zero => simpa using hz
  | succ k ih => exact pow_succ z (k + 1) ▸ corner_comp ih hz

theorem nesting_refl {m : ℕ} {e : Diagram m} (he : comp e e = e) :
    (e, e) ∈ nesting m := ⟨he, he, he, he⟩

theorem nesting_trans {m : ℕ} {d e f : Diagram m}
    (hde : (d, e) ∈ nesting m) (hef : (e, f) ∈ nesting m) :
    (d, f) ∈ nesting m := by
  refine ⟨hde.1, hef.2.1, ?_, ?_⟩
  · calc
      comp d f = comp (comp d e) f := by rw [hde.2.2.1]
      _ = comp d e := by rw [comp_assoc, hef.2.2.1]
      _ = d := hde.2.2.1
  · calc
      comp f d = comp f (comp e d) := by rw [hde.2.2.2]
      _ = comp e d := by rw [← comp_assoc, hef.2.2.2]
      _ = d := hde.2.2.2

theorem comp_mono {m : ℕ} {a a' b b' : Diagram m}
    (ha : (a, a') ∈ inclusion m) (hb : (b, b') ∈ inclusion m) :
    (comp a b, comp a' b') ∈ inclusion m := by
  obtain ⟨haf, hab, hal, har⟩ := ha
  obtain ⟨hbf, hbb, hbl, hbr⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [comp] <;> gcongr

theorem through_loop_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ e.through positive = e.through positive := by
  cases positive
  · exact congrArg backward he
  · exact congrArg forward he

/-- Idempotence of the recurrence relation. -/
theorem recurrence_idempotent {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.recurrence positive = e.recurrence positive := by
  have hK : e.loopClosure positive ○ e.loopClosure positive = e.loopClosure positive := by
    cases positive <;> simp [loopClosure]
  unfold recurrence
  calc
    (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) ○
        (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) =
        e.loopClosure positive ○
          (e.through positive ○ (e.loopClosure positive ○ e.loopClosure positive) ○
            e.through positive) ○ e.loopClosure positive := by simp only [SetRel.comp_assoc]
    _ = e.loopClosure positive ○ e.through positive ○ e.loopClosure positive := by
      rw [hK, through_loop_through e he positive]

theorem corner_returns {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.left ⊆ z.left ∧ e.right ⊆ z.right := by
  constructor
  · rw [← congrArg left hz.1]
    exact Set.subset_union_left
  · rw [← congrArg right hz.2]
    exact Set.subset_union_left

/-- Positive through-edge absorption in a corner. -/
theorem corner_forward_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.forward ○ e.loopClosure true ○ z.forward ⊆ z.forward ∧
    z.forward ○ e.loopClosure true ○ e.forward ⊆ z.forward := by
  obtain ⟨hL, hR⟩ := corner_returns e z hz
  have hl : e.loopClosure true ⊆ relStar (z.left ○ e.right) :=
    relStar_mono (SetRel.comp_subset_comp_left hL)
  have hr : e.loopClosure true ⊆ relStar (e.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp_right hR)
  constructor
  · calc
      _ ⊆ e.forward ○ relStar (z.left ○ e.right) ○ z.forward := by gcongr
      _ = z.forward := congrArg forward hz.1
  · calc
      _ ⊆ z.forward ○ relStar (e.left ○ z.right) ○ e.forward := by gcongr
      _ = z.forward := congrArg forward hz.2

theorem corner_through_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ z.through positive ⊆ z.through positive ∧
    z.through positive ○ e.loopClosure positive ○ e.through positive ⊆ z.through positive := by
  cases positive
  · obtain ⟨hL, hR⟩ := corner_returns e z hz
    have hl : e.loopClosure false ⊆ relStar (e.right ○ z.left) :=
      relStar_mono (SetRel.comp_subset_comp_right hL)
    have hr : e.loopClosure false ⊆ relStar (z.right ○ e.left) :=
      relStar_mono (SetRel.comp_subset_comp_left hR)
    constructor
    · calc
        _ ⊆ e.backward ○ relStar (z.right ○ e.left) ○ z.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.2
    · calc
        _ ⊆ z.backward ○ relStar (e.right ○ z.left) ○ e.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.1
  · exact corner_forward_absorption e z hz

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

theorem surviving_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ e.surviving z positive ⊆ e.surviving z positive ∧
    e.surviving z positive ○ e.recurrence positive ⊆ e.surviving z positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  constructor
  · calc
      _ = e.loopClosure positive ○
          (e.through positive ○ e.loopClosure positive ○ z.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr
  · calc
      _ = e.loopClosure positive ○
          (z.through positive ○ e.loopClosure positive ○ e.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr

theorem recurrence_trans {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {x y z : Fin m}
    (hxy : (x, y) ∈ e.recurrence positive) (hyz : (y, z) ∈ e.recurrence positive) :
    (x, z) ∈ e.recurrence positive := by
  rw [← recurrence_idempotent e he positive]
  exact ⟨y, hxy, hyz⟩

theorem class_nonempty {m : ℕ} {e : Diagram m} {c : Bool × Set (Fin m)}
    (hc : c ∈ e.classes) : c.2.Nonempty := by
  obtain ⟨x, hx, hxc⟩ := hc
  exact ⟨x, hxc ▸ ⟨hx, hx⟩⟩

theorem class_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x y : Fin m}
    (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1 := by
  obtain ⟨p, _, hC⟩ := hc
  rw [hC] at hx hy
  exact ⟨recurrence_trans e he hx.2 hy.1, recurrence_trans e he hy.2 hx.1⟩

theorem class_eq_of_mem {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x : Fin m} (hx : x ∈ c.2) :
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1} := by
  ext y
  constructor
  · exact class_related e he hc hx
  · intro hy
    obtain ⟨p, _, hC⟩ := hc
    rw [hC] at hx ⊢
    exact ⟨recurrence_trans e he hx.1 hy.1, recurrence_trans e he hy.2 hx.2⟩

theorem class_eq_of_common {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c d : Bool × Set (Fin m)} (hc : c ∈ e.classes) (hd : d ∈ e.classes)
    (hsign : c.1 = d.1) {x : Fin m} (hx : x ∈ c.2) (hxd : x ∈ d.2) : c = d := by
  apply Prod.ext hsign
  rw [class_eq_of_mem e he hc hx, class_eq_of_mem e he hd hxd, hsign]

theorem surviving_loop_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x y : Fin m} (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, x) ∈ e.surviving z c.1 ↔ (y, y) ∈ e.surviving z c.1 := by
  obtain ⟨hxy, hyx⟩ := class_related e he hc hx hy
  obtain ⟨hl, hr⟩ := surviving_absorption e z hz c.1
  exact ⟨fun h => hr ⟨x, hl ⟨x, hyx, h⟩, hxy⟩,
    fun h => hr ⟨y, hl ⟨y, hxy, h⟩, hyx⟩⟩

theorem not_mem_missing_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x : Fin m} (hx : x ∈ c.2) :
    c ∉ e.missing z ↔ (x, x) ∈ e.surviving z c.1 := by
  classical
  change ¬ (c ∈ e.classes ∧ _) ↔ _
  simp only [hc, true_and, not_forall, not_not]
  exact ⟨fun ⟨y, hy, hyy⟩ => (surviving_loop_iff e z he hz hc hy hx).mp hyy,
    fun hxx => ⟨x, hx, hxx⟩⟩

theorem surviving_comp {m : ℕ} (e z w : Diagram m)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) (positive : Bool) :
    (if positive then e.surviving z positive ○ e.surviving w positive
      else e.surviving w positive ○ e.surviving z positive) ⊆
      e.surviving (comp z w) positive := by
  obtain ⟨hzL, hzR⟩ := corner_returns e z hz
  obtain ⟨hwL, hwR⟩ := corner_returns e w hw
  have hplus : e.loopClosure true ⊆ relStar (w.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp hwL hzR)
  have hminus : e.loopClosure false ⊆ relStar (z.right ○ w.left) :=
    relStar_mono (SetRel.comp_subset_comp hzR hwL)
  cases positive <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · calc
      _ = e.loopClosure false ○
          (w.backward ○ e.loopClosure false ○ z.backward) ○ e.loopClosure false := by
            simp only [surviving, through, Bool.false_eq_true, ite_false,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) false := by
        dsimp [surviving, through, comp]; gcongr
  · calc
      _ = e.loopClosure true ○
          (z.forward ○ e.loopClosure true ○ w.forward) ○ e.loopClosure true := by
            simp only [surviving, through, ite_true,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) true := by
        dsimp [surviving, through, comp]; gcongr

/-- A class can disappear from a product only if it disappears from a factor. -/
theorem missing_comp {m : ℕ} (e z w : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) :
    e.missing (comp z w) ⊆ e.missing z ∪ e.missing w := by
  classical
  intro c hc
  by_contra h
  obtain ⟨hnz, hnw⟩ := not_or.mp h
  obtain ⟨x, hx⟩ := class_nonempty hc.1
  have hzz := (not_mem_missing_iff e z he hz hc.1 hx).mp hnz
  have hww := (not_mem_missing_iff e w he hw hc.1 hx).mp hnw
  apply hc.2 x hx
  apply surviving_comp e z w hz hw c.1
  cases hs : c.1 <;> simp only [hs] at hzz hww ⊢ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨x, hww, hzz⟩
  · exact ⟨x, hzz, hww⟩

theorem missing_pow_succ {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (k : ℕ) : e.missing (z ^ (k + 1)) ⊆ e.missing z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (missing_comp e _ z he (corner_pow_succ hz k) hz).trans
      (Set.union_subset ih Set.Subset.rfl)

/-- There are at most two signed recurrent classes per boundary label. -/
theorem class_count {m : ℕ} (e : Diagram m) : e.classes.ncard ≤ 2 * m := by
  let f : Bool × Fin m → Bool × Set (Fin m) := fun p =>
    (p.1, {y | (p.2, y) ∈ e.recurrence p.1 ∧ (y, p.2) ∈ e.recurrence p.1})
  have hsub : e.classes ⊆ f '' Set.univ := by
    rintro ⟨positive, C⟩ ⟨x, _, hC⟩
    exact ⟨(positive, x), Set.mem_univ _, Prod.ext rfl hC.symm⟩
  calc
    e.classes.ncard ≤ (f '' Set.univ).ncard := Set.ncard_le_ncard hsub
    _ ≤ (Set.univ : Set (Bool × Fin m)).ncard := Set.ncard_image_le
    _ = 2 * m := by simp

theorem through_comp_recurrence {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.recurrence positive = e.through positive ○ e.loopClosure positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (· ○ e.loopClosure positive) (through_loop_through e he positive)

theorem recurrence_comp_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.through positive = e.loopClosure positive ○ e.through positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (e.loopClosure positive ○ ·) (through_loop_through e he positive)

theorem rectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) (p : Fin m) : e.rectangle positive p ⊆ e.through positive := by
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  rw [← through_loop_through e he positive]
  exact ⟨b, ⟨a, hua, hap.trans hpb⟩, hbv⟩

theorem rectangle_eq_of_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {p q : Fin m} (hpq : (p, q) ∈ e.recurrence positive)
    (hqp : (q, p) ∈ e.recurrence positive) :
    e.rectangle positive p = e.rectangle positive q := by
  have hleft : (e.through positive ○ e.loopClosure positive) ○ e.recurrence positive =
      e.through positive ○ e.loopClosure positive := by
    calc
      _ = e.through positive ○ e.recurrence positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := through_comp_recurrence e he positive
  have hright : e.recurrence positive ○ (e.loopClosure positive ○ e.through positive) =
      e.loopClosure positive ○ e.through positive := by
    calc
      _ = e.recurrence positive ○ e.through positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := recurrence_comp_through e he positive
  ext ⟨u, v⟩
  exact ⟨fun ⟨hup, hpv⟩ =>
    ⟨hleft ▸ (show (u, q) ∈ _ ○ e.recurrence positive from ⟨p, hup, hpq⟩),
      hright ▸ (show (q, v) ∈ e.recurrence positive ○ _ from ⟨p, hqp, hpv⟩)⟩,
    fun ⟨huq, hqv⟩ =>
    ⟨hleft ▸ (show (u, p) ∈ _ ○ e.recurrence positive from ⟨q, huq, hqp⟩),
      hright ▸ (show (p, v) ∈ e.recurrence positive ○ _ from ⟨q, hpq, hqv⟩)⟩⟩

/-- The recurrent rectangles cover every through edge, including for an empty boundary. -/
theorem rectangle_cover {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {u v : Fin m} (huv : (u, v) ∈ e.through positive) :
    ∃ p, (p, p) ∈ e.recurrence positive ∧ (u, v) ∈ e.rectangle positive p := by
  have hFPF : e.through positive ○ e.recurrence positive ○ e.through positive =
      e.through positive := by
    rw [through_comp_recurrence e he positive, through_loop_through e he positive]
  obtain ⟨b, ⟨a, hua, hab⟩, hbv⟩ := hFPF.symm ▸ huv
  obtain ⟨p, hap, hpp, hpb⟩ :=
    idempotent_relation_factor _ (recurrence_idempotent e he positive) hab
  refine ⟨p, hpp, ?_, ?_⟩
  · rw [← through_comp_recurrence e he positive]
    exact ⟨a, hua, hap⟩
  · rw [← recurrence_comp_through e he positive]
    exact ⟨b, hpb, hbv⟩

theorem rectangle_survives {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    {positive : Bool} {p : Fin m} (hp : (p, p) ∈ e.surviving z positive) :
    e.rectangle positive p ⊆ z.through positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  obtain ⟨d, ⟨c, hpc, hcd⟩, hdp⟩ := hp
  exact hr ⟨b, ⟨d, hl ⟨c, ⟨a, hua, hap.trans hpc⟩, hcd⟩, hdp.trans hpb⟩, hbv⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Transport ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

/-- Losing no recurrent class forces componentwise inclusion. -/
theorem inclusion_of_missing_empty {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hmissing : e.missing z = ∅) : (e, z) ∈ inclusion m := by
  have hthrough (positive : Bool) : e.through positive ⊆ z.through positive := by
    rintro ⟨u, v⟩ huv
    obtain ⟨p, hpp, hp⟩ := rectangle_cover e he huv
    let C : Bool × Set (Fin m) :=
      (positive, {y | (p, y) ∈ e.recurrence positive ∧ (y, p) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
    have hnC : C ∉ e.missing z := by rw [hmissing]; exact Set.notMem_empty _
    have hloop := (not_mem_missing_iff e z he hz hC ⟨hpp, hpp⟩).mp hnC
    exact rectangle_survives e z hz hloop hp
  exact ⟨hthrough true, hthrough false, corner_returns e z hz⟩

theorem classRectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (C : Bool × Set (Fin m)) : e.classRectangle C ⊆ e.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, _, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  exact (mem_port_through e C.1 a b).mpr (rectangle_subset e he C.1 p hab)

theorem classRectangle_cross {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c d : Bool × Fin m}
    (hab : (a, b) ∈ e.classRectangle C) (hcd : (c, d) ∈ e.classRectangle C) :
    (a, d) ∈ e.classRectangle C := by
  obtain ⟨ha, _, p, hp, hab⟩ := hab
  obtain ⟨_, hd, q, hq, hcd⟩ := hcd
  obtain ⟨hpq, hqp⟩ := class_related e he hC hp hq
  rw [← rectangle_eq_of_related e he hpq hqp] at hcd
  exact ⟨ha, hd, p, hp, hab.1, hcd.2⟩

theorem classRectangle_survives {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
    (hmissing : C ∉ e.missing z) : e.classRectangle C ⊆ z.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, hp, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  have hloop := (not_mem_missing_iff e z he hz hC hp).mp hmissing
  exact (mem_port_through z C.1 a b).mpr (rectangle_survives e z hz hloop hab)

theorem portRelation_covered {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
    (a, b) ∈ z.portRelation ∨ ∃ C ∈ e.missing z, (a, b) ∈ e.classRectangle C := by
  classical
  have hthrough (positive : Bool) {p q : Fin m} (hpq : (p, q) ∈ e.through positive) :
      ((!positive, p), (positive, q)) ∈ z.portRelation ∨
        ∃ C ∈ e.missing z, ((!positive, p), (positive, q)) ∈ e.classRectangle C := by
    obtain ⟨r, hrr, hrectangle⟩ := rectangle_cover e he hpq
    let C : Bool × Set (Fin m) :=
      (positive, {x | (r, x) ∈ e.recurrence positive ∧ (x, r) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨r, hrr, rfl⟩
    have hrect : ((!positive, p), (positive, q)) ∈ e.classRectangle C :=
      ⟨rfl, rfl, r, ⟨hrr, hrr⟩, hrectangle⟩
    by_cases hmissing : C ∈ e.missing z
    · exact Or.inr ⟨C, hmissing, hrect⟩
    · exact Or.inl (classRectangle_survives e z he hz hC hmissing hrect)
  obtain ⟨s, p⟩ := a
  obtain ⟨t, q⟩ := b
  cases s <;> cases t
  · exact Or.inl ((corner_returns e z hz).1 hab)
  · exact hthrough true hab
  · exact hthrough false hab
  · exact Or.inl ((corner_returns e z hz).2 hab)

theorem classInfluence_cross {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (positive : Bool) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c f : Fin m}
    (hab : (a, b) ∈ e.classInfluence d u v positive C)
    (hcf : (c, f) ∈ e.classInfluence d u v positive C) :
    (a, f) ∈ e.classInfluence d u v positive C := by
  obtain ⟨_, ⟨y, ⟨x, ⟨p, hap, hpx⟩, hxy⟩, _⟩, _⟩ := hab
  obtain ⟨q, ⟨y', ⟨_, ⟨_, _, _⟩, hx'y'⟩, hy'q⟩, hqf⟩ := hcf
  exact ⟨q, ⟨y', ⟨x, ⟨p, hap, hpx⟩, classRectangle_cross e he hC hxy hx'y'⟩, hy'q⟩, hqf⟩

theorem classInfluence_subset {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (hcontext : comp (comp u e) v = d) (positive : Bool) (C : Bool × Set (Fin m)) :
    e.classInfluence d u v positive C ⊆ d.recurrence positive := by
  have hC := classRectangle_subset e he C
  unfold classInfluence
  calc
    _ ⊆ contextEntry d u v positive ○ relStar (e.portRelation ○ bounceRelation u.right v.left) ○
        e.portRelation ○ relStar (bounceRelation u.right v.left ○ e.portRelation) ○
        contextExit d u v positive := by gcongr
    _ = contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
      simpa only [feedback, SetRel.comp_assoc] using
        congrArg (fun R => contextEntry d u v positive ○ R ○ contextExit d u v positive)
          (feedback_insert e.portRelation (bounceRelation u.right v.left))
    _ = d.recurrence positive := by rw [← context_surviving, hcontext]; rfl

theorem transportMarked_card {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    (e.transportMarked d u v J).ncard ≤ 2 * J.ncard := by
  classical
  have hwitness : ∀ D : e.transportMarked d u v J, ∃ C : J,
      ∃ x ∈ D.val.2, (x, x) ∈ e.classInfluence d u v D.val.1 C.val := by
    intro D
    obtain ⟨C, hCJ, x, hx, hloop⟩ := D.property.2
    exact ⟨⟨C, hCJ⟩, x, hx, hloop⟩
  choose color hcolor using hwitness
  let f : e.transportMarked d u v J → Bool × J := fun D => (D.val.1, color D)
  have hinj : Function.Injective f := by
    intro C D hCD
    have hsign : C.val.1 = D.val.1 := congrArg (fun p : Bool × J => p.1) hCD
    have hsame : color C = color D := congrArg Prod.snd hCD
    obtain ⟨x, hx, hxx⟩ := hcolor C
    obtain ⟨y, hy, hyy⟩ := hcolor D
    rw [← hsame, ← hsign] at hyy
    have hsub := classInfluence_subset e d u v he hcontext C.val.1 (color C).val
    have hxy := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hxx hyy)
    have hyx := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hyy hxx)
    have hyC : y ∈ C.val.2 := by
      rw [class_eq_of_mem d hd C.property.1 hx]
      exact ⟨hxy, hyx⟩
    exact Subtype.ext (class_eq_of_common d hd C.property.1 D.property.1 hsign hyC hy)
  have hBool : Nat.card Bool = 2 := by simp
  simpa only [Nat.card_prod, hBool, Nat.card_coe_set_eq] using
    Nat.card_le_card_of_injective f hinj

theorem missing_context_subset_marked {m : ℕ} (e d u v z : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (hz : z ∈ e.corner) (J : Set (Bool × Set (Fin m))) (hJz : e.missing z ⊆ J) :
    d.missing (comp (comp u z) v) ⊆ e.transportMarked d u v J := by
  intro D hD
  obtain ⟨x, hx⟩ := class_nonempty hD.1
  have hxx := (class_related d hd hD.1 hx hx).1
  have hloop : (x, x) ∈ d.surviving (comp (comp u e) v) D.1 := by
    rw [hcontext]
    exact hxx
  rw [context_surviving] at hloop
  obtain ⟨q, ⟨p, hentry, hfeedback⟩, hexit⟩ := hloop
  have hnot : (p, q) ∉ z.feedback u.right v.left := by
    intro hnew
    apply hD.2 x hx
    rw [context_surviving]
    exact ⟨q, ⟨p, hentry, hnew⟩, hexit⟩
  obtain ⟨a, b, hpa, hab, hnotab, hbq⟩ :=
    feedback_lost_edge e.portRelation z.portRelation (bounceRelation u.right v.left) hfeedback hnot
  obtain hnew | ⟨C, hC, hrect⟩ := portRelation_covered e z he hz hab
  · exact (hnotab hnew).elim
  · exact ⟨hD.1, C, hJz hC, x, hx,
      q, ⟨b, ⟨a, ⟨p, hentry, hpa⟩, hrect⟩, hbq⟩, hexit⟩

/-- One fixed target set covers every admissible replacement. -/
theorem transport {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    ∃ J' ⊆ d.classes, J'.ncard ≤ 2 * J.ncard ∧
      ∀ z ∈ e.corner, e.missing z ⊆ J → comp (comp u z) v ∈ d.corner →
        d.missing (comp (comp u z) v) ⊆ J' := by
  refine ⟨e.transportMarked d u v J, fun _ h => h.1,
    transportMarked_card e d u v he hd hcontext J hJ, ?_⟩
  intro z hz hJz _
  exact missing_context_subset_marked e d u v z he hd hcontext hz J hJz

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem loopClosure_subset_of_corner {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) : e.loopClosure positive ⊆ d.loopClosure positive := by
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  cases positive
  · exact relStar_mono (SetRel.comp_subset_comp hR hL)
  · exact relStar_mono (SetRel.comp_subset_comp hL hR)

/-- Two finite-path rearrangements for absorption under nesting. -/
theorem nested_forward_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner) :
    e.forward ○ d.loopClosure true ○ d.forward ⊆ d.loopClosure true ○ d.forward ∧
    d.forward ○ d.loopClosure true ○ e.forward ⊆ d.forward ○ d.loopClosure true := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  have hS : S ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_right hR)
  have hT : T ⊆ d.loopClosure true := relStar_mono (SetRel.comp_subset_comp_left hL)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hLd : e.left ∪ (e.forward ○ S ○ d.left ○ e.backward) = d.left :=
    congrArg left hd.1
  have hRd : e.right ∪ (e.backward ○ d.right ○ T ○ e.forward) = d.right :=
    congrArg right hd.2
  have hLpart : e.forward ○ S ○ d.left ○ e.backward ⊆ d.left :=
    Set.subset_union_right.trans hLd.le
  have hRpart : e.backward ○ d.right ○ T ○ e.forward ⊆ d.right :=
    Set.subset_union_right.trans hRd.le
  have hKleft : d.loopClosure true =
      S ○ relStar (d.left ○ e.backward ○ d.right ○ T ○ e.forward ○ S) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hRd]
    simp only [S, relComp_union, relStar_union, SetRel.comp_assoc]
  have hKright : d.loopClosure true =
      T ○ relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) := by
    change relStar (d.left ○ d.right) = _
    conv_lhs => rw [← hLd]
    simp only [T, union_relComp, relStar_union, SetRel.comp_assoc]
  have hleft : e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T ⊆
      d.loopClosure true := by
    calc
      _ ⊆ d.left ○ d.right ○ T := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, hxz, hzy⟩
        exact (hT hzy).head hxz
  have hright : S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward ⊆
      d.loopClosure true := by
    calc
      _ = S ○ d.left ○ (e.backward ○ d.right ○ T ○ e.forward) := by
        simp only [SetRel.comp_assoc]
      _ ⊆ S ○ d.left ○ d.right := by gcongr
      _ ⊆ d.loopClosure true := by
        rintro ⟨x, y⟩ ⟨z, ⟨p, hxp, hpz⟩, hzy⟩
        exact (hS hxp).tail ⟨z, hpz, hzy⟩
  have hleftStar : relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hleft hab) _ _ h
  have hrightStar : relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) ⊆
      d.loopClosure true := fun _ h =>
    Relation.reflTransGen_closed (fun _ _ hab => hright hab) _ _ h
  constructor
  · calc
      _ = relStar (e.forward ○ S ○ d.left ○ e.backward ○ d.right ○ T) ○
          (e.forward ○ S ○ d.forward) := by
        rw [hKleft]
        simpa only [SetRel.comp_assoc] using
          congrArg (· ○ d.forward)
            (comp_relStar_rotate (e.forward ○ S) (d.left ○ e.backward ○ d.right ○ T))
      _ ⊆ d.loopClosure true ○ d.forward := by rw [hF]; gcongr
  · calc
      _ = (d.forward ○ T ○ e.forward) ○
          relStar (S ○ d.left ○ e.backward ○ d.right ○ T ○ e.forward) := by
        rw [hKright]
        simpa only [SetRel.comp_assoc] using
          congrArg (d.forward ○ T ○ ·)
            (comp_relStar_rotate e.forward (S ○ d.left ○ e.backward ○ d.right ○ T)).symm
      _ ⊆ d.forward ○ d.loopClosure true := by rw [hF']; gcongr

theorem nested_through_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.loopClosure positive ○ d.through positive ⊆
      d.loopClosure positive ○ d.through positive ∧
    d.through positive ○ d.loopClosure positive ○ e.through positive ⊆
      d.through positive ○ d.loopClosure positive := by
  cases positive
  · have hreflect : reflect d ∈ (reflect e).corner :=
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩
    exact nested_forward_loop_absorption (reflect e) (reflect d) hreflect
  · exact nested_forward_loop_absorption e d hd

theorem nested_through_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.through positive ⊆ d.recurrence positive := by
  obtain ⟨hl, hr⟩ := nested_through_loop_absorption e d hd positive
  constructor
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_left (S := d.loopClosure positive) hl
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_right (R := d.loopClosure positive) hr

/-- Mixed recurrent relations are absorbed under nesting. -/
theorem nested_recurrence_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.recurrence positive ⊆ d.recurrence positive := by
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hl, hr⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
  have hPK : d.recurrence positive ○ d.loopClosure positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self]
  constructor
  · calc
      _ ⊆ d.loopClosure positive ○ e.through positive ○ d.loopClosure positive ○
          d.recurrence positive := by unfold recurrence; gcongr
      _ ⊆ d.recurrence positive := by
        rw [SetRel.comp_assoc, SetRel.comp_assoc, hKP]
        exact (SetRel.comp_subset_comp_right hl).trans hKP.le
  · calc
      _ ⊆ d.recurrence positive ○ d.loopClosure positive ○ e.through positive ○
          d.loopClosure positive := by unfold recurrence; simp only [SetRel.comp_assoc]; gcongr
      _ ⊆ d.recurrence positive := by
        rw [hPK]
        exact (SetRel.comp_subset_comp_left hr).trans hPK.le

theorem corner_forward_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {u v : Fin m} (huv : (u, v) ∈ d.forward) :
    ∃ p q, (p, p) ∈ e.recurrence true ∧ (q, q) ∈ e.recurrence true ∧
      (u, p) ∈ e.forward ○ e.loopClosure true ∧ (p, q) ∈ e.surviving d true ∧
      (q, v) ∈ e.loopClosure true ○ e.forward := by
  let S := relStar (d.left ○ e.right)
  let T := relStar (e.left ○ d.right)
  have hF : e.forward ○ S ○ d.forward = d.forward := congrArg forward hd.1
  have hF' : d.forward ○ T ○ e.forward = d.forward := congrArg forward hd.2
  have hsplit : e.forward ○ S ○ d.forward ○ T ○ e.forward = d.forward := by rw [hF, hF']
  have hw : (u, v) ∈ e.forward ○ S ○ d.forward ○ T ○ e.forward := by rw [hsplit]; exact huv
  obtain ⟨a, ⟨b, ⟨c, ⟨f, huf, hfc⟩, hcb⟩, hba⟩, hav⟩ := hw
  obtain ⟨p, hpp, ⟨hup, hpf⟩⟩ := rectangle_cover e he (positive := true) huf
  obtain ⟨q, hqq, ⟨haq, hqv⟩⟩ := rectangle_cover e he (positive := true) hav
  refine ⟨p, q, hpp, hqq, hup, ?_, hqv⟩
  obtain ⟨r, hpr, hrf⟩ := hpf
  obtain ⟨s, has, hsq⟩ := haq
  change (p, q) ∈ e.loopClosure true ○ d.forward ○ e.loopClosure true
  rw [← hsplit]
  exact ⟨s, ⟨r, hpr, ⟨a, ⟨b, ⟨c, ⟨f, hrf, hfc⟩, hcb⟩, hba⟩, has⟩⟩, hsq⟩

theorem corner_through_factor {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {u v : Fin m}
    (huv : (u, v) ∈ d.through positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (u, p) ∈ e.through positive ○ e.loopClosure positive ∧
      (p, q) ∈ e.surviving d positive ∧
      (q, v) ∈ e.loopClosure positive ○ e.through positive := by
  cases positive
  · exact corner_forward_factor (reflect e) (reflect d)
      (by rw [← reflect_comp, he])
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩ huv
  · exact corner_forward_factor e d he hd huv

/-- A recurrent loop in a nested corner contains two recurrent points of its parent. -/
theorem nested_recurrent_witness {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {x : Fin m}
    (hxx : (x, x) ∈ d.recurrence positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (x, p) ∈ d.recurrence positive ∧ (p, x) ∈ d.recurrence positive ∧
      (x, q) ∈ d.recurrence positive ∧ (q, x) ∈ d.recurrence positive ∧
      (p, q) ∈ e.surviving d positive := by
  obtain ⟨v, ⟨u, hxu, huv⟩, hvx⟩ := hxx
  obtain ⟨p, q, hpp, hqq, ⟨a, hua, hap⟩, hpq, ⟨b, hqb, hbv⟩⟩ :=
    corner_through_factor e d he hd huv
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hFP, hPF⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp, Set.Subset.rfl]
  have hPK : d.recurrence positive ○ d.loopClosure positive ⊆ d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self, Set.Subset.rfl]
  have hpqd : (p, q) ∈ d.recurrence positive :=
    (show e.surviving d positive ⊆ d.recurrence positive by
      unfold surviving recurrence; gcongr) hpq
  have hxpd : (x, p) ∈ d.recurrence positive :=
    hPK ⟨a, hPF ⟨u, hPK ⟨x, ⟨v, ⟨u, hxu, huv⟩, hvx⟩, hxu⟩, hua⟩, hK hap⟩
  have hpxd : (p, x) ∈ d.recurrence positive :=
    hPK ⟨v, hPF ⟨b, hPK ⟨q, hpqd, hK hqb⟩, hbv⟩, hvx⟩
  have hxqd : (x, q) ∈ d.recurrence positive :=
    hKP ⟨u, hxu, hFP ⟨a, hua, hKP ⟨p, hK hap, hpqd⟩⟩⟩
  have hqxd : (q, x) ∈ d.recurrence positive :=
    hKP ⟨b, hK hqb, hFP ⟨v, hbv, hKP ⟨x, hvx, ⟨v, ⟨u, hxu, huv⟩, hvx⟩⟩⟩⟩
  exact ⟨p, q, hpp, hqq, hxpd, hpxd, hxqd, hqxd, hpq⟩

/-- A new class contains a surviving old class or two distinct old classes. -/
theorem nested_class_containment {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    {c : Bool × Set (Fin m)} (hc : c ∈ d.classes) :
    (∃ C ∈ e.classes, C.1 = c.1 ∧ C.2 ⊆ c.2 ∧ C ∉ e.missing d) ∨
      ∃ C ∈ e.classes, ∃ D ∈ e.classes,
        C ≠ D ∧ C.1 = c.1 ∧ D.1 = c.1 ∧ C.2 ⊆ c.2 ∧ D.2 ⊆ c.2 := by
  classical
  obtain ⟨x, hx⟩ := class_nonempty hc
  have hxx := (class_related d hd hc hx hx).1
  obtain ⟨p, q, hpp, hqq, hxp, hpx, hxq, hqx, hpq⟩ :=
    nested_recurrent_witness e d he hde hxx
  let C : Bool × Set (Fin m) :=
    (c.1, {y | (p, y) ∈ e.recurrence c.1 ∧ (y, p) ∈ e.recurrence c.1})
  let D : Bool × Set (Fin m) :=
    (c.1, {y | (q, y) ∈ e.recurrence c.1 ∧ (y, q) ∈ e.recurrence c.1})
  have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
  have hD : D ∈ e.classes := ⟨q, hqq, rfl⟩
  obtain ⟨hPePd, hPdPe⟩ := nested_recurrence_absorption e d hde c.1
  have hCsub : C.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨p, hxp, hr.1⟩, hPePd ⟨p, hr.2, hpx⟩⟩
  have hDsub : D.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨q, hxq, hr.1⟩, hPePd ⟨q, hr.2, hqx⟩⟩
  by_cases hCD : C = D
  · left
    refine ⟨C, hC, rfl, hCsub, ?_⟩
    have hqC : q ∈ C.2 := by rw [hCD]; exact ⟨hqq, hqq⟩
    apply (not_mem_missing_iff e d he hde hC ⟨hpp, hpp⟩).mpr
    exact (surviving_absorption e d hde c.1).2 ⟨q, hpq, hqC.2⟩
  · exact Or.inr ⟨C, hC, D, hD, hCD, rfl, rfl, hCsub, hDsub⟩

theorem nested_unprotected_loss {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    (P : Set (Bool × Fin m)) (hmissing : e.missing d ⊆ e.unprotected P) :
    2 * (d.unprotected P).ncard + (e.missing d).ncard ≤ 2 * (e.unprotected P).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card]
  apply weighted_class_bound _ _ _
    (fun c C : Bool × Set (Fin m) => C.1 = c.1 ∧ C.2 ⊆ c.2)
  · simpa only [Set.Finite.toFinset_subset_toFinset] using hmissing
  · intro c hc d' hd' C hC hCc hCd
    obtain ⟨hc, _⟩ := (Set.Finite.mem_toFinset _).mp hc
    obtain ⟨hd', _⟩ := (Set.Finite.mem_toFinset _).mp hd'
    obtain ⟨hC, _⟩ := (Set.Finite.mem_toFinset _).mp hC
    obtain ⟨x, hx⟩ := class_nonempty hC
    exact class_eq_of_common d hd hc hd' (hCc.1.symm.trans hCd.1) (hCc.2 hx) (hCd.2 hx)
  · intro c hc
    obtain ⟨hc, hprotected⟩ := (Set.Finite.mem_toFinset _).mp hc
    have hcontained {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
        (hsign : C.1 = c.1) (hsub : C.2 ⊆ c.2) : C ∈ e.unprotected P := by
      refine ⟨hC, ?_⟩
      intro x hx
      rw [hsign]
      exact hprotected x (hsub hx)
    rcases nested_class_containment e d he hd hde hc with
      ⟨C, hC, hsign, hsub, hnC⟩ | ⟨C, hC, D, hD, hCD, hsignC, hsignD, hsubC, hsubD⟩
    · exact Or.inl ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsign hsub),
        by simpa only [Set.Finite.mem_toFinset] using hnC, hsign, hsub⟩
    · exact Or.inr ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsignC hsubC),
        D, (Set.Finite.mem_toFinset _).mpr (hcontained hD hsignD hsubD),
        hCD, ⟨hsignC, hsubC⟩, ⟨hsignD, hsubD⟩⟩

/-- A common initial missing set pays for all later losses. -/
theorem nested_chain_bound {m k : ℕ} (b : ℕ → Diagram m)
    (hidemp : ∀ j ≤ k, comp (b j) (b j) = b j)
    (hnest : ∀ j < k, (b (j + 1), b j) ∈ nesting m)
    (J : Set (Bool × Set (Fin m)))
    (hJ : ∀ j ≤ k, (b 0).missing (b j) ⊆ J) :
    ∑ j ∈ Finset.range k, ((b j).missing (b (j + 1))).ncard ≤ 2 * J.ncard := by
  classical
  have hbase : ∀ j ≤ k, (b j, b 0) ∈ nesting m := by
    intro j
    induction j with
    | zero => intro _; exact nesting_refl (hidemp 0 (Nat.zero_le _))
    | succ j ih =>
      intro hj
      exact nesting_trans (hnest j (by omega)) (ih (by omega))
  have hchoose : ∀ C : ↥((b 0).classes \ J), ∃ x, x ∈ C.val.2 :=
    fun C => class_nonempty C.property.1
  choose pick hpick using hchoose
  let P : Set (Bool × Fin m) := Set.range (fun C : ↥((b 0).classes \ J) => (C.val.1, pick C))
  have hinit : (b 0).unprotected P = J ∩ (b 0).classes := by
    ext C
    constructor
    · rintro ⟨hC, hCP⟩
      refine ⟨?_, hC⟩
      by_contra hnC
      let C' : ↥((b 0).classes \ J) := ⟨C, hC, hnC⟩
      exact hCP (pick C') (hpick C') ⟨C', rfl⟩
    · rintro ⟨hCJ, hC⟩
      refine ⟨hC, ?_⟩
      intro x hx hxP
      obtain ⟨D, hD⟩ := hxP
      have hsign : C.1 = D.val.1 := (congrArg (fun sx : Bool × Fin m => sx.1) hD).symm
      have hlabel : pick D = x := congrArg (fun sx : Bool × Fin m => sx.2) hD
      have heq : C = D.val := class_eq_of_common (b 0) (hidemp 0 (Nat.zero_le _))
        hC D.property.1 hsign hx (hlabel ▸ hpick D)
      exact D.property.2 (heq ▸ hCJ)
  have hprotected (j : ℕ) (hj : j ≤ k) (sx : Bool × Fin m) (hxP : sx ∈ P) :
      (sx.2, sx.2) ∈ (b 0).surviving (b j) sx.1 ∧
      (sx.2, sx.2) ∈ (b j).recurrence sx.1 := by
    obtain ⟨C, rfl⟩ := hxP
    have hcorner : b j ∈ (b 0).corner := ⟨(hbase j hj).2.2.2, (hbase j hj).2.2.1⟩
    have hnotmissing : C.val ∉ (b 0).missing (b j) := fun h => C.property.2 (hJ j hj h)
    have hloop := (not_mem_missing_iff (b 0) (b j) (hidemp 0 (Nat.zero_le _))
      hcorner C.property.1 (hpick C)).mp hnotmissing
    have hK := loopClosure_subset_of_corner (b 0) (b j) hcorner C.val.1
    refine ⟨hloop, ?_⟩
    exact (show (b 0).surviving (b j) C.val.1 ⊆ (b j).recurrence C.val.1 by
      unfold surviving recurrence; gcongr) hloop
  have hstep (j : ℕ) (hj : j < k) :
      2 * ((b (j + 1)).unprotected P).ncard + ((b j).missing (b (j + 1))).ncard ≤
        2 * ((b j).unprotected P).ncard := by
    have hjk : j ≤ k := hj.le
    have hj1k : j + 1 ≤ k := hj
    obtain ⟨_, _, hnextprev, hprevnext⟩ := hnest j hj
    apply nested_unprotected_loss (b j) (b (j + 1)) (hidemp j hjk)
      (hidemp (j + 1) hj1k) ⟨hprevnext, hnextprev⟩ P
    intro C hC
    refine ⟨hC.1, ?_⟩
    intro x hx hxP
    have hloop := (hprotected (j + 1) hj1k (C.1, x) hxP).1
    have hK := loopClosure_subset_of_corner (b 0) (b j)
      ⟨(hbase j hjk).2.2.2, (hbase j hjk).2.2.1⟩ C.1
    apply hC.2 x hx
    exact (show (b 0).surviving (b (j + 1)) C.1 ⊆ (b j).surviving (b (j + 1)) C.1 by
      unfold surviving; gcongr) hloop
  have hbudget : ∀ n ≤ k,
      (∑ j ∈ Finset.range n, ((b j).missing (b (j + 1))).ncard) +
        2 * ((b n).unprotected P).ncard ≤ 2 * ((b 0).unprotected P).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      rw [Finset.sum_range_succ]
      omega
  have hi : ((b 0).unprotected P).ncard ≤ J.ncard := by
    rw [hinit]
    exact Set.ncard_le_ncard Set.inter_subset_left
  have hb := hbudget k le_rfl
  omega

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Corners ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A finite nonempty subsemigroup contains an idempotent. -/
theorem finite_subsemigroup_idempotent {A : Type*} [Semigroup A] [Finite A]
    (S : Set A) (hne : S.Nonempty) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) :
    ∃ e ∈ S, IsIdempotentElem e := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact exists_idempotent_in_compact_subsemigroup (fun _ => continuous_of_discreteTopology)
    S hne (Set.toFinite S).isCompact hmul

/-- Every element of a finite monoid has an idempotent positive power. -/
theorem finite_idempotent_pow {A : Type*} [Monoid A] [Finite A] (a : A) :
    ∃ k : ℕ, 0 < k ∧ IsIdempotentElem (a ^ k) := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := finite_subsemigroup_idempotent
    (Set.range (fun k : ℕ => a ^ (k + 1))) ⟨a, 0, by simp⟩ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨i + j + 1, by simp only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩)
  exact ⟨k + 1, Nat.succ_pos _, hk⟩

/-- A multiplicative map preserves positive powers without any unitality assumption. -/
theorem map_positive_pow {A B : Type*} [Monoid A] [Monoid B]
    (f : A →ₙ* B) (a : A) (k : ℕ) : f (a ^ (k + 1)) = f a ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, map_mul, ih, ← pow_succ]

/-- A nested chain with a common missing-set budget. -/
theorem exists_nested_chain {A : Type*} [Monoid A] [Finite A] {m k : ℕ}
    (ι : A →ₙ* Diagram m) (b0 : A) (hb0 : IsIdempotentElem b0) (g : ℕ → A)
    (J : Set (Bool × Set (Fin m)))
    (hg : ∀ j < k, ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J) :
    ∃ b : ℕ → A, b 0 = b0 ∧
      (∀ j, IsIdempotentElem (b j)) ∧
      (∀ j, ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1)) ∧
      (∀ j, (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m) ∧
      (∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J) ∧
      ∑ j ∈ Finset.range k, ((ι (b j)).missing (ι (b (j + 1)))).ncard ≤ 2 * J.ncard := by
  classical
  choose power hpower using fun a : A => finite_idempotent_pow a
  let b : ℕ → A := Nat.rec b0 (fun j prev => (prev * g j * prev) ^ power (prev * g j * prev))
  have hzero : b 0 = b0 := rfl
  have hsucc (j : ℕ) : b (j + 1) = (b j * g j * b j) ^ power (b j * g j * b j) := rfl
  have hidemp (j : ℕ) : IsIdempotentElem (b j) := by
    cases j with
    | zero => exact hb0
    | succ j => exact (hpower _).2
  have hstep (j : ℕ) : ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hpower (b j * g j * b j)).1.ne'
    exact ⟨n, by rw [hsucc, hn]⟩
  have hmapidemp (j : ℕ) : Diagram.comp (ι (b j)) (ι (b j)) = ι (b j) := by
    exact (map_mul ι (b j) (b j)).symm.trans (congrArg ι (hidemp j).eq)
  have hnest (j : ℕ) : (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m := by
    obtain ⟨n, hn⟩ := hstep j
    have hcorner : ι (b j * g j * b j) ∈ (ι (b j)).corner := by
      constructor
      · change ι (b j) * ι (b j * g j * b j) = _
        rw [← map_mul, ← mul_assoc, ← mul_assoc, (hidemp j).eq]
      · change ι (b j * g j * b j) * ι (b j) = _
        rw [← map_mul, mul_assoc, (hidemp j).eq]
    have hpow := Diagram.corner_pow_succ hcorner n
    rw [← map_positive_pow, ← hn] at hpow
    exact ⟨hmapidemp (j + 1), hmapidemp j, hpow.2, hpow.1⟩
  have hbase (j : ℕ) : (ι (b j), ι b0) ∈ Diagram.nesting m := by
    induction j with
    | zero => exact Diagram.nesting_refl (hmapidemp 0)
    | succ j ih => exact Diagram.nesting_trans (hnest j) ih
  have hbudget : ∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J := by
    intro j
    induction j with
    | zero => intro _; rw [hzero, Diagram.missing_self]; exact Set.empty_subset _
    | succ j ih =>
      intro hj
      obtain ⟨n, hn⟩ := hstep j
      have hb : ι (b j) ∈ (ι b0).corner := ⟨(hbase j).2.2.2, (hbase j).2.2.1⟩
      have hgj := (hg j (by omega)).1
      have hbg := Diagram.corner_comp hb hgj
      have hpow := Diagram.missing_pow_succ (ι b0) (ι (b j * g j * b j))
        (hmapidemp 0) (by rw [map_mul, map_mul]; exact Diagram.corner_comp hbg hb) n
      rw [← map_positive_pow, ← hn] at hpow
      apply hpow.trans
      have hfirst := Diagram.missing_comp (ι b0) (ι (b j)) (ι (g j)) (hmapidemp 0) hb hgj
      have hsecond := Diagram.missing_comp (ι b0) (ι (b j) * ι (g j)) (ι (b j))
        (hmapidemp 0) hbg hb
      rw [map_mul, map_mul]
      exact hsecond.trans
        (Set.union_subset (hfirst.trans (Set.union_subset (ih (by omega)) (hg j (by omega)).2))
          (ih (by omega)))
  exact ⟨b, hzero, hidemp, hstep, hnest, hbudget,
    Diagram.nested_chain_bound (fun j => ι (b j)) (fun j _ => hmapidemp j)
      (fun j _ => hnest j) J (by simpa only [hzero] using hbudget)⟩

/-- An idempotent has a lift minimal in the nesting order. -/
theorem minimal_idempotent_lift {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) (q : M) (hq : IsIdempotentElem q) :
    ∃ d, IsIdempotentElem d ∧ θ d = q ∧
      ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d := by
  obtain ⟨a, ha⟩ := hθ q
  obtain ⟨d0, hd0q, hd0⟩ := finite_subsemigroup_idempotent
    {x | θ x = q} ⟨a, ha⟩ (by
      intro x hx y hy
      change θ (x * y) = q
      rw [map_mul, hx, hy, hq.eq])
  obtain ⟨d, ⟨hd, hdq⟩, hminimal⟩ := Set.exists_min_image
    {d | IsIdempotentElem d ∧ θ d = q}
    (fun d => (Subsemigroup.corner d : Set A).ncard) (Set.toFinite _) ⟨d0, hd0, hd0q⟩
  refine ⟨d, hd, hdq, ?_⟩
  intro e he heq hed hde
  have hsub : (Subsemigroup.corner e : Set A) ⊆ Subsemigroup.corner d := by
    rintro x ⟨y, rfl⟩
    apply (Subsemigroup.mem_corner_iff hd).mpr
    exact ⟨by simp only [← mul_assoc, hde], by simp only [mul_assoc, hed]⟩
  have heqcorner := Set.eq_of_subset_of_ncard_le hsub (hminimal e ⟨he, heq⟩)
  have hdin : d ∈ Subsemigroup.corner e := by
    change d ∈ (Subsemigroup.corner e : Set A)
    rw [heqcorner]
    exact (Subsemigroup.mem_corner_iff hd).mpr ⟨hd, hd⟩
  exact hed.symm.trans ((Subsemigroup.mem_corner_iff he).mp hdin).1

theorem cornerMap_surjective {A M : Type*} [Semigroup A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) {d : A} {q : M}
    (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    Function.Surjective (cornerMap θ hd hq hθd) := by
  intro y
  obtain ⟨x, hx⟩ := hθ y.val
  refine ⟨⟨d * x * d, x, rfl⟩, ?_⟩
  apply Subtype.ext
  change θ (d * x * d) = y.val
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp y.property
  rw [map_mul, map_mul, hθd, hx, hl, hr]

/-- At a minimal idempotent lift, every element with unit image is a unit. -/
theorem minimal_corner_reflects_units {A M : Type*} [Semigroup A] [Finite A] [Semigroup M]
    (θ : A →ₙ* M) {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q)
    (hθd : θ d = q)
    (hminimal : ∀ e, IsIdempotentElem e → θ e = q → e * d = e → d * e = e → e = d)
    (w : hd.Corner) (hw : IsUnit (cornerMap θ hd hq hθd w)) : IsUnit w := by
  obtain ⟨k, hk, hpow⟩ := finite_idempotent_pow w
  have hmapIdem : IsIdempotentElem (cornerMap θ hd hq hθd (w ^ k)) := by
    change _ * _ = _
    rw [← map_mul, hpow.eq]
  have hmapUnit : IsUnit (cornerMap θ hd hq hθd (w ^ k)) := by
    rw [map_pow]
    exact hw.pow k
  have hmapOne := (IsIdempotentElem.iff_eq_one_of_isUnit hmapUnit).mp hmapIdem
  have hθpow : θ (w ^ k).val = q := congrArg Subtype.val hmapOne
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hd).mp (w ^ k).property
  have hwd : (w ^ k).val = d := hminimal _ (congrArg Subtype.val hpow.eq) hθpow hr hl
  exact IsUnit.of_pow_eq_one (Subtype.ext hwd) hk.ne'

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Singleton contexts test an individual relation edge. -/
theorem singleton_context {α : Type*} (R : SetRel α α) (p q : α) :
    restrictedIdentity {p} ○ R ○ restrictedIdentity {q} =
      {(x, y) | x = p ∧ y = q ∧ (p, q) ∈ R} := by
  ext ⟨x, y⟩
  simp [SetRel.comp, restrictedIdentity]
  aesop

/-- Restriction-corner identities.
    The supporting relation `i` can be any idempotent with `iPi = i`. -/
theorem relation_corner_identities {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    let Q := P ○ i ○ P
    Q ○ Q = Q ∧ P ○ Q = Q ∧ Q ○ P = Q ∧
    Q ○ i = P ○ i ∧ i ○ Q = i ○ P ∧ i ○ Q ○ i = i := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  dsimp
  simp [SetRel.comp_assoc, hPP, hiPiR, hP, hiPi]

/-- Restriction and extension are inverse on the two supported corners. -/
theorem relation_corner_inverse {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    (∀ Z, (P ○ i ○ P) ○ Z ○ (P ○ i ○ P) = Z → P ○ (i ○ Z ○ i) ○ P = Z) ∧
    (∀ A, i ○ A ○ i = A →
      (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) = P ○ A ○ P ∧
      i ○ (P ○ A ○ P) ○ i = A) := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  constructor
  · intro Z hZ
    have hPZP : P ○ Z ○ P = Z := by
      conv_lhs => rw [← hZ]
      simpa only [SetRel.comp_assoc, hPP, hP] using hZ
    calc
      P ○ (i ○ Z ○ i) ○ P = P ○ (i ○ (P ○ Z ○ P) ○ i) ○ P := by rw [hPZP]
      _ = Z := by simpa only [SetRel.comp_assoc] using hZ
  · intro A hA
    constructor
    · calc
        (P ○ i ○ P) ○ (P ○ A ○ P) ○ (P ○ i ○ P) =
            P ○ (i ○ A ○ i) ○ P := by
              conv_lhs => rw [← hA]
              simp only [SetRel.comp_assoc, hPP, hiPiR]
        _ = P ○ A ○ P := by rw [hA]
    · conv_lhs => rw [← hA]
      simpa only [SetRel.comp_assoc, hiPiR, hiPi] using hA

/-- Extension preserves products on the supported relation corner. -/
theorem relation_corner_comp {α : Type*} (P i A B : SetRel α α)
    (hP : P ○ P = P) (hi : i ○ i = i) (hiPi : i ○ P ○ i = i)
    (hA : i ○ A ○ i = A) (hB : i ○ B ○ i = B) :
    (P ○ A ○ P) ○ (P ○ B ○ P) = P ○ (A ○ B) ○ P := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  have hii (R : SetRel α α) : i ○ (i ○ R) = i ○ R := by
    rw [← SetRel.comp_assoc, hi]
  conv_lhs => rw [← hA, ← hB]
  simpa only [SetRel.comp_assoc, hPP, hiPiR, hii] using
    congrArg (fun R => P ○ R ○ P) (congrArg₂ SetRel.comp hA hB)

namespace RelationMonoid

end RelationMonoid

/-- Extending a relation on a subset and restricting it again loses no pairs. -/
theorem relation_extend_restrict {H : Type*} (F : Set H) (R : SetRel F F) :
    {xy : F × F | (xy.1.val, xy.2.val) ∈ (Prod.map Subtype.val Subtype.val) '' R} = R := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    exact (Subtype.ext hax ▸ Subtype.ext hby ▸ hab)
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Extension of restriction is precisely the identity sandwich on the subset. -/
theorem relation_restrict_extend {H : Type*} (F : Set H) (R : SetRel H H) :
    (Prod.map Subtype.val Subtype.val) '' {xy : F × F | (xy.1.val, xy.2.val) ∈ R} =
      restrictedIdentity F ○ R ○ restrictedIdentity F := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.exists, Set.mem_ofPred_eq, Prod.map_apply, Prod.mk.injEq,
    SetRel.comp, restrictedIdentity]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨b.val, ⟨a.val, ⟨rfl, a.property⟩, hab⟩, rfl, b.property⟩
  · rintro ⟨b, ⟨a, ⟨rfl, hx⟩, hab⟩, rfl, hy⟩
    exact ⟨⟨x, hx⟩, ⟨b, hy⟩, hab, rfl, rfl⟩

/-- Extension of relations on a subset preserves path composition. -/
theorem relation_extend_comp {H : Type*} (F : Set H) (A B : SetRel F F) :
    (Prod.map Subtype.val Subtype.val) '' (A ○ B) =
      ((Prod.map Subtype.val Subtype.val) '' A) ○
        ((Prod.map Subtype.val Subtype.val) '' B) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, hac, hcb⟩, hxy⟩
    cases hxy
    exact ⟨c.val, ⟨(a, c), hac, rfl⟩, (c, b), hcb, rfl⟩
  · rintro ⟨z, ⟨⟨a, b⟩, hab, habxy⟩, ⟨⟨c, d⟩, hcd, hcdxy⟩⟩
    have hbc : b = c := Subtype.ext ((congrArg Prod.snd habxy).trans
      (congrArg Prod.fst hcdxy).symm)
    subst c
    have hax : a.val = x := congrArg Prod.fst habxy
    have hdy : d.val = y := congrArg Prod.snd hcdxy
    exact ⟨(a, d), ⟨b, hab, hcd⟩, Prod.ext hax hdy⟩

/-- The full relation monoid on a subset is the compressed relation corner. -/
theorem relation_corner_equiv {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : P ○ P = P) (hiPi : restrictedIdentity F ○ P ○ restrictedIdentity F =
      restrictedIdentity F) :
    ∃ hQ : IsIdempotentElem (RelationMonoid.ofRel (P ○ restrictedIdentity F ○ P)),
      ∃ ρ : hQ.Corner ≃* RelationMonoid F,
        ∀ Z, (ρ Z).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel} := by
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hQ : IsIdempotentElem (RelationMonoid.ofRel Q) :=
    RelationMonoid.ext (relation_corner_identities P i hP hiPi).1
  have hZ (Z : hQ.Corner) : Q ○ Z.val.toRel ○ Q = Z.val.toRel := by
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp Z.property
    exact congrArg RelationMonoid.toRel ((congrArg (· * RelationMonoid.ofRel Q) hl).trans hr)
  let extend (A : RelationMonoid F) : SetRel H H :=
    (Prod.map Subtype.val Subtype.val) '' A.toRel
  have hsupp (A : RelationMonoid F) : i ○ extend A ○ i = extend A := by
    rw [← relation_restrict_extend F, relation_extend_restrict]
  let f (Z : hQ.Corner) : RelationMonoid F :=
    .ofRel {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}
  let g (A : RelationMonoid F) : hQ.Corner :=
    ⟨.ofRel (P ○ extend A ○ P), (Subsemigroup.mem_corner_iff hQ).mpr (by
      have hs := (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.1
      change Q ○ (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P at hs
      have hQQ : Q ○ Q = Q := (relation_corner_identities P i hP hiPi).1
      constructor <;> apply RelationMonoid.ext
      · change Q ○ (P ○ extend A ○ P) = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [← SetRel.comp_assoc, hQQ] using hs
      · change (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [SetRel.comp_assoc, hQQ] using hs)⟩
  have hleft (Z : hQ.Corner) : g (f Z) = Z := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ ((Prod.map Subtype.val Subtype.val) ''
      {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}) ○ P = Z.val.toRel
    rw [relation_restrict_extend]
    exact (relation_corner_inverse P i hP hiPi).1 _ (hZ Z)
  have hright (A : RelationMonoid F) : f (g A) = A := by
    apply RelationMonoid.ext
    have hext : extend (f (g A)) = extend A := by
      change (Prod.map Subtype.val Subtype.val) '' {xy : F × F |
        (xy.1.val, xy.2.val) ∈ P ○ extend A ○ P} = extend A
      rw [relation_restrict_extend]
      exact (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.2
    have hinj : Function.Injective
        (Prod.map (Subtype.val : F → H) (Subtype.val : F → H)) :=
      fun _ _ h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact Set.image_injective.mpr hinj hext
  have hgmul (A B : RelationMonoid F) : g (A * B) = g A * g B := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ extend (A * B) ○ P = (P ○ extend A ○ P) ○ (P ○ extend B ○ P)
    have hext : extend (A * B) = extend A ○ extend B := relation_extend_comp F _ _
    rw [hext]
    exact (relation_corner_comp P i _ _ hP (restrictedIdentity_comp_self F)
      hiPi (hsupp A) (hsupp B)).symm
  let ρ : hQ.Corner ≃* RelationMonoid F :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      map_mul' := by
        intro Z W
        apply_fun g
        · rw [hgmul, hleft, hleft, hleft]
        · exact Function.LeftInverse.injective hright }
  exact ⟨hQ, ρ, fun _ => rfl⟩

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The image of a monoid lies in the diagram corner of its image identity. -/
theorem map_identity_corner {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (a : A) : ι a ∈ (ι 1).corner := by
  constructor
  · change ι 1 * ι a = ι a
    rw [← map_mul, one_mul]
  · change ι a * ι 1 = ι a
    rw [← map_mul, mul_one]

/-- The cardinality consequence of the uniform transport theorem. -/
theorem missing_context_card {m : ℕ} (e d u v z : Diagram m)
    (he : Diagram.comp e e = e) (hd : Diagram.comp d d = d)
    (hcontext : Diagram.comp (Diagram.comp u e) v = d) (hz : z ∈ e.corner)
    (hnew : Diagram.comp (Diagram.comp u z) v ∈ d.corner) :
    (d.missing (Diagram.comp (Diagram.comp u z) v)).ncard ≤ 2 * (e.missing z).ncard := by
  obtain ⟨J', _, hcard, hcover⟩ := Diagram.transport e d u v he hd hcontext
    (e.missing z) (fun _ h => h.1)
  exact (Set.ncard_le_ncard (hcover z hz Set.Subset.rfl hnew)).trans hcard

/-- Conjugating by a unit costs at most twice as many missing classes. -/
theorem conjugate_missing_bound {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (p : Aˣ) (a : A) :
    ((ι 1).missing (ι (p * a * (↑p⁻¹ : A)))).ncard ≤
      2 * ((ι 1).missing (ι a)).ncard := by
  have he : Diagram.comp (ι 1) (ι 1) = ι 1 := (map_identity_corner ι 1).1
  have hcontext : Diagram.comp (Diagram.comp (ι p) (ι 1)) (ι (↑p⁻¹ : A)) = ι 1 := by
    change ι p * ι 1 * ι (↑p⁻¹ : A) = ι 1
    rw [← map_mul, ← map_mul]
    simp
  have hnew : Diagram.comp (Diagram.comp (ι p) (ι a)) (ι (↑p⁻¹ : A)) ∈ (ι 1).corner := by
    change ι p * ι a * ι (↑p⁻¹ : A) ∈ (ι 1).corner
    rw [← map_mul, ← map_mul]
    exact map_identity_corner ι _
  have h := missing_context_card (ι 1) (ι 1) (ι p) (ι (↑p⁻¹ : A)) (ι a)
    he he hcontext (map_identity_corner ι a) hnew
  change ((ι 1).missing (ι p * ι a * ι (↑p⁻¹ : A))).ncard ≤ _ at h
  simpa only [map_mul] using h

/-- All pair products share one missing-set bound after sandwiching by an idempotent. -/
theorem common_pair_budget {A : Type*} [Monoid A] {m t c : ℕ}
    (ι : A →ₙ* Diagram m) (f : Bool × Fin t → A) (b0 : A) (hb0 : IsIdempotentElem b0)
    (hcost : ∀ p, ((ι 1).missing (ι (f p))).ncard ≤ 2 * c) :
    ∃ J0 ⊆ (ι b0).classes, J0.ncard ≤ 8 * t * c ∧
      ∀ i j, (ι b0).missing (ι (b0 * f (false, i) * f (true, j) * b0)) ⊆ J0 := by
  classical
  let J := ⋃ p, (ι 1).missing (ι (f p))
  have hJ : J ⊆ (ι 1).classes := by
    intro C hC
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hC
    exact hp.1
  have hcard : J.ncard ≤ 4 * t * c := by
    calc
      J.ncard ≤ ∑ p : Bool × Fin t, ((ι 1).missing (ι (f p))).ncard :=
        Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : Bool × Fin t, 2 * c := Finset.sum_le_sum (fun p _ => hcost p)
      _ = 4 * t * c := by simp; ring
  have he : Diagram.comp (ι 1) (ι 1) = ι 1 := (map_identity_corner ι 1).1
  have hd : Diagram.comp (ι b0) (ι b0) = ι b0 :=
    (map_mul ι b0 b0).symm.trans (congrArg ι hb0.eq)
  have hcontext : Diagram.comp (Diagram.comp (ι b0) (ι 1)) (ι b0) = ι b0 := by
    change ι b0 * ι 1 * ι b0 = ι b0
    rw [← map_mul, ← map_mul, mul_one, hb0.eq]
  obtain ⟨J0, hJ0, hcard0, hcover⟩ := Diagram.transport (ι 1) (ι b0) (ι b0) (ι b0)
    he hd hcontext J hJ
  refine ⟨J0, hJ0, by nlinarith, ?_⟩
  intro i j
  have hproduct : (ι 1).missing (ι (f (false, i) * f (true, j))) ⊆ J := by
    rw [map_mul]
    exact (Diagram.missing_comp (ι 1) _ _ he (map_identity_corner ι _)
      (map_identity_corner ι _)).trans (Set.union_subset
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (false, i))
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (true, j)))
  have hnew : Diagram.comp (Diagram.comp (ι b0) (ι (f (false, i) * f (true, j))))
      (ι b0) ∈ (ι b0).corner := by
    constructor
    · rw [← Diagram.comp_assoc, ← Diagram.comp_assoc, hd]
    · rw [Diagram.comp_assoc, hd]
  have h := hcover _ (map_identity_corner ι _) hproduct hnew
  change (ι b0).missing (ι b0 * ι (f (false, i) * f (true, j)) * ι b0) ⊆ J0 at h
  simpa only [map_mul, mul_assoc] using h

/-- Disjoint source and target sets prevent two added edges from being concatenated. -/
theorem bipartite_relation_comp {H : Type*} (F U V : Set H)
    (hU : U ⊆ F) (hV : V ⊆ F) (hUV : Disjoint U V)
    (E E' : SetRel H H) (hE : E ⊆ U ×ˢ V) (hE' : E' ⊆ U ×ˢ V) :
    (restrictedIdentity F ∪ E) ○ (restrictedIdentity F ∪ E') =
      restrictedIdentity F ∪ (E ∪ E') := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hxz | hxz, hzy | hzy⟩
    · exact Or.inl ⟨hxz.1.trans hzy.1, hxz.2⟩
    · exact Or.inr (Or.inr (hxz.1 ▸ hzy))
    · exact Or.inr (Or.inl (hzy.1 ▸ hxz))
    · exact (Set.disjoint_left.mp hUV (hE' hzy).1 (hE hxz).2).elim
  · rintro (hxy | hxy | hxy)
    · exact ⟨x, Or.inl ⟨rfl, hxy.2⟩, Or.inl hxy⟩
    · exact ⟨y, Or.inr hxy, Or.inl ⟨rfl, hV (hE hxy).2⟩⟩
    · exact ⟨x, Or.inl ⟨rfl, hU (hE' hxy).1⟩, Or.inr hxy⟩

/-- Removing the hub leaves exactly the desired pair between its two neighbours. -/
theorem hub_pair_relation {H : Type*} (u v z : H) (huz : u ≠ z) (hvz : v ≠ z) :
    restrictedIdentity {x | x ≠ z} ○ (SetRel.id ∪ {(u, z)}) ○
      (SetRel.id ∪ {(z, v)}) ○ restrictedIdentity {x | x ≠ z} =
        restrictedIdentity {x | x ≠ z} ∪ {(u, v)} := by
  ext ⟨a, b⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, restrictedIdentity, Prod.mk.injEq]
  aesop

/-- Permutation conjugation relabels both endpoints of every relation edge. -/
theorem permutation_conjugate_relation {H : Type*} (σ : Equiv.Perm H) (R : SetRel H H) :
    Function.graph σ ○ R ○ Function.graph σ.symm = {xy | (σ xy.1, σ xy.2) ∈ R} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨c, ⟨d, had, hdc⟩, hcb⟩
    change σ a = d at had
    change σ.symm c = b at hcb
    have hc : c = σ b := by rw [← hcb, σ.apply_symm_apply]
    rwa [← had, hc] at hdc
  · intro hab
    exact ⟨σ b, ⟨σ a, rfl, hab⟩, σ.symm_apply_apply b⟩

/-- Unit lifts move the initial added pair to any other ordered pair of distinct points. -/
theorem pair_conjugate {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hlift : ∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val)
    (a : A) (ha : IsIdempotentElem a) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (u v : H) (huv : u ≠ v) :
    ∃ s : A, IsIdempotentElem s ∧ (φ s).toRel = SetRel.id ∪ {(u, v)} ∧
      ((ι 1).missing (ι s)).ncard ≤ 2 * ((ι 1).missing (ι a)).ncard := by
  have hinj {r s : H} (hrs : r ≠ s) : Function.Injective (fun b : Bool => if b then s else r) := by
    intro b c h
    cases b <;> cases c <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun b : Bool => if b then v else u) (fun b : Bool => if b then y else x)
    (hinj huv) (hinj hxy)
  have hσu : σ u = x := by simpa using hσ false
  have hσv : σ v = y := by simpa using hσ true
  obtain ⟨p, hp⟩ := hlift σ
  have hunit : Units.map φ p = permutationUnit σ := Units.ext hp
  have hinv : φ (↑p⁻¹ : A) = (↑(permutationUnit σ)⁻¹ : RelationMonoid H) :=
    congrArg (fun q : (RelationMonoid H)ˣ => (↑q⁻¹ : RelationMonoid H)) hunit
  refine ⟨p * a * (↑p⁻¹ : A), ?_, ?_, conjugate_missing_bound ι p a⟩
  · change (↑p * a * ↑p⁻¹) * (↑p * a * ↑p⁻¹) = ↑p * a * ↑p⁻¹
    simp only [mul_assoc, Units.inv_mul_cancel_left, ← mul_assoc a a, ha.eq]
  · rw [map_mul, map_mul, hp, hinv, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul, himage]
    change Function.graph σ ○ (SetRel.id ∪ {(x, y)}) ○ Function.graph σ.symm = _
    rw [permutation_conjugate_relation, ← hσu, ← hσv]
    ext ⟨r, s⟩
    simp [SetRel.id, σ.injective.eq_iff]

/-- Restricting an idempotent sandwich preserves the new pair and supplies all unit lifts. -/
theorem smaller_relation_instance {A H : Type*} [Monoid A] [Finite A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H) (hφ : Function.Surjective φ)
    (b b' : A) (hb : IsIdempotentElem b) (hbb' : b * b' = b') (hb'b : b' * b = b')
    (F : Set H)
    (hiPi : restrictedIdentity F ○ (φ b).toRel ○ restrictedIdentity F = restrictedIdentity F)
    (x y : F)
    (hpair : restrictedIdentity F ○ (φ b').toRel ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x.val, y.val)}) :
    ∃ d : hb.Corner, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* RelationMonoid F,
      Function.Surjective ψ ∧
      (∀ σ : Equiv.Perm F, ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val) ∧
      (∀ w, (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel}) ∧
      ∃ v : hd.Corner, IsIdempotentElem v ∧ (ψ v).toRel = SetRel.id ∪ {(x, y)} ∧
        ((ι d.val).missing (ι v.val.val)).ncard ≤ 2 * ((ι b).missing (ι b')).ncard := by
  let P := (φ b).toRel
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hP : IsIdempotentElem (φ b) := by rw [IsIdempotentElem, ← map_mul, hb.eq]
  have hPP : P ○ P = P := congrArg RelationMonoid.toRel hP.eq
  obtain ⟨hQ, ρ, hρ⟩ := relation_corner_equiv P F hPP hiPi
  have hident := relation_corner_identities P i hPP hiPi
  let q : hP.Corner := ⟨.ofRel Q, (Subsemigroup.mem_corner_iff hP).mpr
    ⟨RelationMonoid.ext hident.2.1, RelationMonoid.ext hident.2.2.1⟩⟩
  have hq : IsIdempotentElem q := Subtype.ext hQ.eq
  let θ := cornerMap φ.toMulHom hb hP rfl
  have hθ : Function.Surjective θ := cornerMap_surjective φ.toMulHom hφ hb hP rfl
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ.toMulHom hθ q hq
  let γ := cornerMap θ.toMulHom hd hq hθd
  let equiv := (cornerFlatten hP q hq).trans ρ
  let ψ := equiv.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    equiv.surjective.comp (cornerMap_surjective θ.toMulHom hθ hd hq hθd)
  have hψrel (w : hd.Corner) :
      (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel} :=
    hρ _
  have hψunits (σ : Equiv.Perm F) : ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val := by
    obtain ⟨w, hw⟩ := hψ (permutationUnit σ).val
    have hunitψ : IsUnit (ψ w) := hw.symm ▸ (permutationUnit σ).isUnit
    have hunitγ : IsUnit (γ w) := by
      have h := hunitψ.map equiv.symm.toMonoidHom
      simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using h
    obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ.toMulHom hd hq hθd hminimal w hunitγ
    exact ⟨p, hp ▸ hw⟩
  have hdimage : φ d.val = RelationMonoid.ofRel Q := congrArg Subtype.val hθd
  let b'c : hb.Corner := ⟨b', (Subsemigroup.mem_corner_iff hb).mpr ⟨hbb', hb'b⟩⟩
  let w : hd.Corner := ⟨d * b'c * d, b'c, rfl⟩
  have hwimage : (ψ w).toRel = SetRel.id ∪ {(x, y)} := by
    rw [hψrel]
    change {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ (d.val * b' * d.val)).toRel} = _
    rw [map_mul, map_mul, hdimage, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
      RelationMonoid.toRel_ofRel]
    have habsorb : P ○ (φ b').toRel ○ P = (φ b').toRel := by
      change ((φ b * φ b') * φ b).toRel = _
      rw [← map_mul, ← map_mul, hbb', hb'b]
    have hsandwich : i ○ (Q ○ (φ b').toRel ○ Q) ○ i = i ∪ {(x.val, y.val)} := by
      calc
        i ○ (Q ○ (φ b').toRel ○ Q) ○ i =
            (i ○ Q) ○ (φ b').toRel ○ (Q ○ i) := by simp only [SetRel.comp_assoc]
        _ = i ○ (P ○ (φ b').toRel ○ P) ○ i := by
          rw [hident.2.2.2.1, hident.2.2.2.2.1]
          simp only [SetRel.comp_assoc]
        _ = i ∪ {(x.val, y.val)} := by rw [habsorb]; exact hpair
    ext ⟨r, s⟩
    have hmem : (r.val, s.val) ∈ i ○ (Q ○ (φ b').toRel ○ Q) ○ i ↔
        (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q := by
      simp [i, SetRel.comp, restrictedIdentity, r.property, s.property]
    change (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q ↔ (r, s) ∈ SetRel.id ∪ {(x, y)}
    rw [← hmem, hsandwich]
    simp [i, restrictedIdentity, SetRel.id, Subtype.ext_iff]
  have hiPair : IsIdempotentElem (ψ w) := by
    apply RelationMonoid.ext
    rw [RelationMonoid.toRel_mul, hwimage]
    ext ⟨r, s⟩
    simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
      SetRel.id, Prod.mk.injEq]
    aesop
  obtain ⟨k, hk, hv⟩ := finite_idempotent_pow w
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine ⟨d, hd, ψ, hψ, hψunits, hψrel, w ^ (k + 1), hv, ?_, ?_⟩
  · rw [map_pow, hiPair.pow_succ_eq, hwimage]
  · let ιb : hb.Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hid : Diagram.comp (ι d.val) (ι d.val) = ι d.val :=
      (map_mul ιb d d).symm.trans (congrArg ιb hd.eq)
    have hib : Diagram.comp (ι b) (ι b) = ι b :=
      (map_mul ι b b).symm.trans (congrArg ι hb.eq)
    obtain ⟨hbd, hdb⟩ := (Subsemigroup.mem_corner_iff hb).mp d.property
    have hcontext : Diagram.comp (Diagram.comp (ι d.val) (ι b)) (ι d.val) = ι d.val := by
      change ι d.val * ι b * ι d.val = ι d.val
      rw [← map_mul, hdb]
      exact hid
    have hb' : ι b' ∈ (ι b).corner :=
      ⟨(map_mul ι b b').symm.trans (congrArg ι hbb'),
        (map_mul ι b' b).symm.trans (congrArg ι hb'b)⟩
    have hw : ιd w ∈ (ι d.val).corner := map_identity_corner ιd w
    have htransport := missing_context_card (ι b) (ι d.val) (ι d.val) (ι d.val) (ι b')
      hib hid hcontext hb' (by
        change ι d.val * ι b' * ι d.val ∈ (ι d.val).corner
        rw [← map_mul, ← map_mul]
        exact hw)
    have hpow := Diagram.missing_pow_succ (ι d.val) (ιd w) hid hw k
    rw [← map_positive_pow] at hpow
    apply (Set.ncard_le_ncard hpow).trans
    change ((ι d.val).missing (ι (d.val * b' * d.val))).ncard ≤ _
    rw [map_mul, map_mul]
    exact htransport

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Retained ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Select the two 64-point families and a distinct hub. -/
theorem exists_hub_families {H : Type*} [Finite H] (hh : 129 ≤ Nat.card H) :
    ∃ u v : Fin 64 ↪ H, ∃ z : H,
      (∀ i j, u i ≠ v j) ∧ (∀ i, u i ≠ z) ∧ (∀ j, v j ≠ z) := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨e⟩ : Nonempty (Fin 129 ↪ H) := Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let u : Fin 64 ↪ H :=
    ⟨fun i => e ⟨i.val, by omega⟩,
      fun a b h => Fin.ext (congrArg (fun k : Fin 129 => k.val) (e.injective h))⟩
  let v : Fin 64 ↪ H := ⟨fun i => e ⟨64 + i.val, by omega⟩, by
    intro a b h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    apply Fin.ext
    change 64 + a.val = 64 + b.val at he
    omega⟩
  refine ⟨u, v, e 128, ?_, ?_, ?_⟩
  · intro i j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 64 + j.val at he
    omega
  · intro i h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 128 at he
    omega
  · intro j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change 64 + j.val = 128 at he
    omega

/-- Retaining a new pair and all external points removes exactly 127 points. -/
theorem retained_pair_set {H : Type*} [Finite H] (U V : Set H)
    (hU : U.ncard = 64) (hV : V.ncard = 64) (hUV : Disjoint U V)
    (z x y : H) (hzU : z ∉ U) (hzV : z ∉ V) (hx : x ∈ U) (hy : y ∈ V) :
    ∃ F : Set H, Nat.card F = Nat.card H - 127 ∧ x ∈ F ∧ y ∈ F ∧ z ∉ F ∧
      (∀ a ∈ U, a ∈ F → a = x) ∧ (∀ b ∈ V, b ∈ F → b = y) := by
  classical
  let S := insert z (U ∪ V)
  let F := ({x, y} : Set H) ∪ Sᶜ
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hUV (h ▸ hx) hy
  have hS : S.ncard = 129 := by
    rw [Set.ncard_insert_of_notMem (by simpa using And.intro hzU hzV),
      Set.ncard_union_eq hUV, hU, hV]
  have hpair : ({x, y} : Set H).ncard = 2 := by simp [hxy]
  have hpS : ({x, y} : Set H) ⊆ S := by
    rintro a (rfl | rfl) <;> simp [S, hx, hy]
  have hdisj : Disjoint ({x, y} : Set H) Sᶜ := Set.disjoint_left.mpr (fun _ ha hn => hn (hpS ha))
  have hF : F.ncard = Nat.card H - 127 := by
    rw [Set.ncard_union_eq hdisj, hpair, Set.ncard_compl, hS]
    have hh : 129 ≤ Nat.card H := by simpa only [hS] using Set.ncard_le_card S
    omega
  refine ⟨F, by simpa only [Nat.card_coe_set_eq] using hF, Or.inl (Or.inl rfl),
    Or.inl (Or.inr rfl), ?_, ?_, ?_⟩
  · rintro (h | h)
    · rcases h with rfl | rfl
      · exact hzU hx
      · exact hzV hy
    · exact h (by simp [S])
  · intro a ha hF
    rcases hF with (rfl | rfl) | hout
    · rfl
    · exact (Set.disjoint_left.mp hUV ha hy).elim
    · exact (hout (by simp [S, ha])).elim
  · intro b hb hF
    rcases hF with (rfl | rfl) | hout
    · exact (Set.disjoint_left.mp hUV hx hb).elim
    · rfl
    · exact (hout (by simp [S, hb])).elim

/-- Identity sandwiches restrict exactly the two endpoints. -/
theorem mem_restricted_sandwich {H : Type*} (F : Set H) (R : SetRel H H) (a b : H) :
    (a, b) ∈ restrictedIdentity F ○ R ○ restrictedIdentity F ↔
      a ∈ F ∧ b ∈ F ∧ (a, b) ∈ R := by
  simp only [SetRel.comp, restrictedIdentity, Set.mem_ofPred_eq]
  aesop

/-- Before its turn, the selected pair is absent from the retained restriction. -/
theorem retained_relation_identity {H : Type*} (U V F : Set H) (z x y : H)
    (hz : z ∉ F) (hx : ∀ a ∈ U, a ∈ F → a = x) (hy : ∀ b ∈ V, b ∈ F → b = y)
    (E : SetRel H H) (hE : E ⊆ U ×ˢ V) (hnew : (x, y) ∉ E) :
    restrictedIdentity F ○ (restrictedIdentity {a | a ≠ z} ∪ E) ○ restrictedIdentity F =
      restrictedIdentity F := by
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  constructor
  · rintro ⟨ha, hb, hid | hedge⟩
    · exact ⟨hid.1, ha⟩
    · exact (hnew (by simpa only [hx a (hE hedge).1 ha, hy b (hE hedge).2 hb] using hedge)).elim
  · rintro ⟨rfl, ha⟩
    exact ⟨ha, ha, Or.inl ⟨rfl, fun h => hz (h ▸ ha)⟩⟩

/-- At its turn, restriction adds precisely the selected pair to the retained identity. -/
theorem retained_relation_pair {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : restrictedIdentity F ○ P ○ restrictedIdentity F = restrictedIdentity F)
    (x y : H) (hx : x ∈ F) (hy : y ∈ F) :
    restrictedIdentity F ○ (P ∪ {(x, y)}) ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x, y)} := by
  rw [relComp_union, union_relComp, hP]
  congr 1
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  simp only [Set.mem_singleton_iff, Prod.mk.injEq]
  aesop

/-- The target doubles whenever the induction removes 127 points. -/
theorem lossBound_step {h : ℕ} (hh : 129 ≤ h) : lossBound h = 2 * lossBound (h - 127) := by
  have hexp : (h - 2) / 127 = (h - 127 - 2) / 127 + 1 := by omega
  simp only [lossBound, hexp, pow_succ, Nat.mul_comm]

/-- The numerical conclusion of summing the 4096 inductive lower bounds. -/
theorem amplification_arithmetic {h c : ℕ} (hh : 129 ≤ h) (δ : Fin 4096 → ℕ)
    (htotal : ∑ j, δ j ≤ 1024 * c)
    (hstep : ∀ j, lossBound (h - 127) ≤ 2 * δ j) : lossBound h ≤ c := by
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4096))) => hstep j)
  have hbound : 4096 * lossBound (h - 127) ≤ 2 * ∑ j, δ j := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.mul_sum] using hsum
  rw [lossBound_step hh]
  omega

/-- The base case detects the off-diagonal pair using rectangle coverage and order reversal. -/
theorem single_edge_base {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hreverse : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel)
    (a : A) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (hh : Nat.card H ≤ 128) :
    lossBound (Nat.card H) ≤ ((ι 1).missing (ι a)).ncard := by
  have hsmall : lossBound (Nat.card H) = 1 := by
    have he : (Nat.card H - 2) / 127 = 0 := by omega
    simp [lossBound, he]
  rw [hsmall]
  by_contra h
  have hempty : (ι 1).missing (ι a) = ∅ := (Set.ncard_eq_zero).mp (by omega)
  have hinclusion := Diagram.inclusion_of_missing_empty (ι 1) (ι a)
    (map_identity_corner ι 1).1 (map_identity_corner ι a) hempty
  have hedge : (x, y) ∈ (φ a).toRel := by rw [himage]; exact Or.inr rfl
  have hid := hreverse 1 a hinclusion hedge
  rw [map_one, RelationMonoid.toRel_one] at hid
  exact hxy hid

/-- Every positive power of a sandwich is absorbed by its idempotent outer factor. -/
theorem sandwich_power_absorption {A : Type*} [Monoid A] (b a : A)
    (hb : IsIdempotentElem b) (k : ℕ) :
    b * (b * a * b) ^ (k + 1) = (b * a * b) ^ (k + 1) ∧
      (b * a * b) ^ (k + 1) * b = (b * a * b) ^ (k + 1) := by
  have hl : b * (b * a * b) = b * a * b := by rw [← mul_assoc, ← mul_assoc, hb.eq]
  have hr : b * a * b * b = b * a * b := by rw [mul_assoc, hb.eq]
  induction k with
  | zero => simpa using And.intro hl hr
  | succ k ih =>
    constructor
    · rw [pow_succ, ← mul_assoc, ih.1]
    · rw [pow_succ, mul_assoc, hr]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ImageBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace TwoWayComplementation

universe u v

open scoped SetRel

/-- Exponential cost of a single edge for every finite source monoid and label type. -/
theorem single_edge_cost (h : ℕ) :
    ∀ {A : Type u} {H : Type v} [Monoid A] [Finite A] [Finite H] {m : ℕ},
      Nat.card H = h → 2 ≤ h →
      ∀ (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H), Function.Surjective φ →
      (∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel) →
      (∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val) →
      ∀ a, IsIdempotentElem a → ∀ x y : H, x ≠ y →
      (φ a).toRel = SetRel.id ∪ {(x, y)} →
      lossBound h ≤ ((ι 1).missing (ι a)).ncard := by
  classical
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro A H _ _ _ m hH hh ι φ hφ hreverse hlift a ha x y hxy himage
    by_cases hsmall : h ≤ 128
    · simpa only [hH] using single_edge_base ι φ hreverse a x y hxy himage (by omega)
    have hlarge : 129 ≤ h := by omega
    obtain ⟨u, v, z, huv, huz, hvz⟩ := exists_hub_families (H := H) (by omega)
    choose s hs hsimage hscost using fun i =>
      pair_conjugate ι φ hlift a ha x y hxy himage (u i) z (huz i)
    choose s' hs' hsimage' hscost' using fun j =>
      pair_conjugate ι φ hlift a ha x y hxy himage z (v j) (hvz j).symm
    let f : Bool × Fin 64 → A := fun p => if p.1 then s' p.2 else s p.2
    let c := ((ι 1).missing (ι a)).ncard
    have hcost (p : Bool × Fin 64) : ((ι 1).missing (ι (f p))).ncard ≤ 2 * c := by
      obtain ⟨b, i⟩ := p
      cases b
      · exact hscost i
      · exact hscost' i
    let T : Set H := {w | w ≠ z}
    let P0 := restrictedIdentity T
    have hP0 : IsIdempotentElem (RelationMonoid.ofRel P0) :=
      RelationMonoid.ext (restrictedIdentity_comp_self T)
    obtain ⟨b0, hb0, hb0image, _⟩ := minimal_idempotent_lift φ.toMulHom hφ
      (RelationMonoid.ofRel P0) hP0
    have hφb0 : (φ b0).toRel = P0 := congrArg RelationMonoid.toRel hb0image
    obtain ⟨J0, _, hJcard, hJ⟩ := common_pair_budget ι f b0 hb0 hcost
    let index : Fin 4096 ≃ Fin 64 × Fin 64 := (finProdFinEquiv (m := 64) (n := 64)).symm
    let edge : Fin 4096 → H × H := fun r => (u (index r).1, v (index r).2)
    have hedgeinj : Function.Injective edge := by
      intro r s h
      apply index.injective
      exact Prod.ext (u.injective (congrArg Prod.fst h)) (v.injective (congrArg Prod.snd h))
    let E (j : ℕ) : SetRel H H := edge '' {r : Fin 4096 | r.val < j}
    let P (j : ℕ) := P0 ∪ E j
    let U := Set.range u
    let V := Set.range v
    have hUV : Disjoint U V := by
      apply Set.disjoint_left.mpr
      rintro w ⟨i, rfl⟩ ⟨j, heq⟩
      exact huv i j heq.symm
    have hUT : U ⊆ T := by rintro w ⟨i, rfl⟩; exact huz i
    have hVT : V ⊆ T := by rintro w ⟨j, rfl⟩; exact hvz j
    have hE (j : ℕ) : E j ⊆ U ×ˢ V := by
      rintro _ ⟨r, _, rfl⟩
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have he (r : Fin 4096) : {edge r} ⊆ U ×ˢ V := by
      rintro w rfl
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have hnew (r : Fin 4096) : edge r ∉ E r.val := by
      rintro ⟨s, hs, heq⟩
      change s.val < r.val at hs
      exact (hedgeinj heq ▸ hs).false
    have hEsucc (r : Fin 4096) : E (r.val + 1) = E r.val ∪ {edge r} := by
      have hidx : {s : Fin 4096 | s.val < r.val + 1} =
          {s : Fin 4096 | s.val < r.val} ∪ {r} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro hs
          by_cases hlt : s.val < r.val
          · exact Or.inl hlt
          · exact Or.inr (Fin.ext (by omega))
        · rintro (hlt | rfl) <;> omega
      change edge '' _ = _
      rw [hidx, Set.image_union, Set.image_singleton]
    have hPidemp (j : ℕ) : P j ○ P j = P j := by
      simpa only [P, Set.union_self] using
        bipartite_relation_comp T U V hUT hVT hUV (E j) (E j) (hE j) (hE j)
    let g (j : ℕ) : A := if hj : j < 4096 then
      b0 * s (index ⟨j, hj⟩).1 * s' (index ⟨j, hj⟩).2 * b0 else b0
    have hgimage (r : Fin 4096) : (φ (g r.val)).toRel = P0 ∪ {edge r} := by
      simp only [g, dite_eq_left r.isLt, map_mul, RelationMonoid.toRel_mul,
        hφb0, hsimage, hsimage']
      exact hub_pair_relation _ _ z (huz _) (hvz _)
    have hgbudget : ∀ j < 4096,
        ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J0 := by
      intro j hj
      simp only [g, dite_eq_left hj]
      constructor
      · constructor
        · change ι b0 * ι _ = _
          rw [← map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, hb0.eq]
        · change ι _ * ι b0 = _
          rw [← map_mul, mul_assoc, hb0.eq]
      · exact hJ _ _
    obtain ⟨b, hbzero, hbidemp, hbpower, _, _, htotal⟩ :=
      exists_nested_chain ι b0 hb0 g J0 hgbudget
    have hbimage : ∀ j ≤ 4096, (φ (b j)).toRel = P j := by
      intro j
      induction j with
      | zero => intro _; simp [hbzero, hφb0, P, E]
      | succ j hj =>
        intro hjle
        let r : Fin 4096 := ⟨j, by omega⟩
        have hprev := hj (by omega)
        have hnext : φ (b j * g j * b j) = RelationMonoid.ofRel (P (j + 1)) := by
          apply RelationMonoid.ext
          rw [map_mul, map_mul, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
            hprev, hgimage r, RelationMonoid.toRel_ofRel]
          change (P0 ∪ E j) ○ (P0 ∪ {edge r}) ○ (P0 ∪ E j) = P0 ∪ E (j + 1)
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _ (hE j) (he r)]
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _
            (Set.union_subset (hE j) (he r)) (hE j)]
          rw [show E (j + 1) = E j ∪ {edge r} from hEsucc r]
          rw [Set.union_right_comm (E j) {edge r} (E j), Set.union_self]
        obtain ⟨n, hn⟩ := hbpower j
        rw [hn, map_pow, hnext]
        have hi : IsIdempotentElem (RelationMonoid.ofRel (P (j + 1))) :=
          RelationMonoid.ext (hPidemp (j + 1))
        rw [hi.pow_succ_eq, RelationMonoid.toRel_ofRel]
    let δ (r : Fin 4096) := ((ι (b r.val)).missing (ι (b (r.val + 1)))).ncard
    have hsum : ∑ r, δ r ≤ 1024 * c := by
      have heq : ∑ r, δ r =
          ∑ j ∈ Finset.range 4096, ((ι (b j)).missing (ι (b (j + 1)))).ncard := by
        exact Fin.sum_univ_eq_sum_range
          (fun j => ((ι (b j)).missing (ι (b (j + 1)))).ncard) 4096
      rw [heq]
      omega
    apply amplification_arithmetic hlarge δ hsum
    intro r
    obtain ⟨F, hFcard, hxF, hyF, hzF, hUF, hVF⟩ := retained_pair_set U V
      (by simpa [U] using Set.ncard_range_of_injective u.injective)
      (by simpa [V] using Set.ncard_range_of_injective v.injective) hUV z
      (edge r).1 (edge r).2
      (by rintro ⟨i, hi⟩; exact huz i hi)
      (by rintro ⟨j, hj⟩; exact hvz j hj)
      ⟨(index r).1, rfl⟩ ⟨(index r).2, rfl⟩
    have hrestrict : restrictedIdentity F ○ (φ (b r.val)).toRel ○ restrictedIdentity F =
        restrictedIdentity F := by
      rw [hbimage _ r.isLt.le]
      exact retained_relation_identity U V F z _ _ hzF hUF hVF (E r.val) (hE r.val) (hnew r)
    have hrestrict' : restrictedIdentity F ○ (φ (b (r.val + 1))).toRel ○
        restrictedIdentity F = restrictedIdentity F ∪ {edge r} := by
      rw [hbimage _ r.isLt, show P (r.val + 1) = P r.val ∪ {edge r} from
        (congrArg (P0 ∪ ·) (hEsucc r)).trans (Set.union_assoc _ _ _).symm]
      have hp : restrictedIdentity F ○ P r.val ○ restrictedIdentity F = restrictedIdentity F := by
        rwa [hbimage _ r.isLt.le] at hrestrict
      exact retained_relation_pair (P r.val) F hp _ _ hxF hyF
    obtain ⟨n, hn⟩ := hbpower r.val
    have habsorb := sandwich_power_absorption (b r.val) (g r.val) (hbidemp r.val) n
    rw [← hn] at habsorb
    obtain ⟨d, hd, ψ, hψ, hliftψ, hψrel, w, hw, hwimage, hwcost⟩ :=
      smaller_relation_instance ι φ hφ (b r.val) (b (r.val + 1)) (hbidemp r.val)
        habsorb.1 habsorb.2 F hrestrict ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩ hrestrict'
    let ιb : (hbidemp r.val).Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hreverseψ : ∀ s t, (ιd s, ιd t) ∈ Diagram.inclusion m →
        (ψ t).toRel ⊆ (ψ s).toRel := by
      intro s t hst
      rw [hψrel, hψrel]
      exact fun _ hp => hreverse s.val.val t.val.val hst hp
    have hlow := ih (h - 127) (by omega) (A := hd.Corner) (H := F)
      (by omega) (by omega) ιd ψ hψ hreverseψ hliftψ w hw
      ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩
      (fun heq => huv (index r).1 (index r).2 (congrArg Subtype.val heq)) hwimage
    exact hlow.trans hwcost

/-- A surjection has a unital identity corner with unit lifts for every target unit. -/
theorem minimal_unital_corner {A M : Type*} [Semigroup A] [Finite A] [Monoid M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) :
    ∃ d : A, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* M,
      Function.Surjective ψ ∧ (∀ w, ψ w = θ w.val) ∧
      ∀ u : Mˣ, ∃ p : hd.Cornerˣ, ψ p = u.val := by
  have h1 : IsIdempotentElem (1 : M) := by simp [IsIdempotentElem]
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ hθ 1 h1
  let ε : h1.Corner ≃* M :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, (Subsemigroup.mem_corner_iff h1).mpr ⟨one_mul x, mul_one x⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let γ := cornerMap θ hd h1 hθd
  let ψ := ε.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    ε.surjective.comp (cornerMap_surjective θ hθ hd h1 hθd)
  refine ⟨d, hd, ψ, hψ, fun _ => rfl, ?_⟩
  intro u
  obtain ⟨w, hw⟩ := hψ u.val
  have hu : IsUnit (ψ w) := hw.symm ▸ u.isUnit
  have hγ : IsUnit (γ w) := by
    have hu' := hu.map ε.symm.toMonoidHom
    simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hu'
  obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ hd h1 hθd hminimal w hγ
  exact ⟨p, hp ▸ hw⟩

/-- Identity plus a single pair is always an idempotent relation. -/
theorem identity_pair_idempotent {H : Type*} (x y : H) :
    IsIdempotentElem (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) := by
  apply RelationMonoid.ext
  change (SetRel.id ∪ {(x, y)}) ○ (SetRel.id ∪ {(x, y)}) = SetRel.id ∪ {(x, y)}
  ext ⟨r, s⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, Prod.mk.injEq]
  aesop

/-- A surjective order-reversing multiplicative image has exponential cost. -/
theorem order_reversing_image_bound_finite {H : Type*} [Finite H]
    (m : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ Nat.card H)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel H H) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound (Nat.card H) ≤ 2 * m := by
  classical
  let S0 : Submonoid (Diagram m) :=
    { carrier := S
      one_mem' := hidentity
      mul_mem' := by
        intro a b ha hb
        change Diagram.comp a b ∈ S
        exact hclosed ha hb }
  let θ : S0 →ₙ* RelationMonoid H :=
    { toFun := fun x => .ofRel (φ ⟨x.val, x.property⟩)
      map_mul' := fun a b => RelationMonoid.ext (hmul ⟨a.val, a.property⟩ ⟨b.val, b.property⟩) }
  have hθ : Function.Surjective θ := by
    intro R
    obtain ⟨x, hx⟩ := hsurj R.toRel
    exact ⟨⟨x.val, x.property⟩, RelationMonoid.ext hx⟩
  obtain ⟨e, he, ψ, hψ, hψval, hunit⟩ := minimal_unital_corner θ hθ
  let ι : he.Corner →ₙ* Diagram m :=
    { toFun := fun w => w.val.val
      map_mul' := fun _ _ => rfl }
  have hrev : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (ψ b).toRel ⊆ (ψ a).toRel := by
    intro a b hab
    rw [hψval, hψval]
    exact hreverse ⟨a.val.val, a.val.property⟩ ⟨b.val.val, b.val.property⟩ hab
  let := Fintype.ofFinite H
  obtain ⟨pair⟩ : Nonempty (Fin 2 ↪ H) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let x := pair 0
  let y := pair 1
  have hxy : x ≠ y := fun heq => by
    have := congrArg Fin.val (pair.injective heq)
    norm_num at this
  obtain ⟨a, ha, haimage, _⟩ := minimal_idempotent_lift ψ.toMulHom hψ
    (RelationMonoid.ofRel (SetRel.id ∪ {(x, y)})) (identity_pair_idempotent x y)
  have hcost := single_edge_cost (Nat.card H) rfl hh ι ψ hψ hrev
    (fun σ => hunit (permutationUnit σ)) a ha x y hxy
    (congrArg RelationMonoid.toRel haimage)
  exact hcost.trans ((Set.ncard_le_ncard (show (ι 1).missing (ι a) ⊆ (ι 1).classes from
    fun _ h => h.1)).trans (Diagram.class_count (ι 1)))

/-- The order-reversing image bound for a finite label domain. -/
theorem order_reversing_image_bound
    (m h : ℕ) (_hm : 1 ≤ m) (hh : 2 ≤ h)
    (S : Set (Diagram m)) (hidentity : Diagram.identity m ∈ S)
    (hclosed : ∀ ⦃a b⦄, a ∈ S → b ∈ S → Diagram.comp a b ∈ S)
    (φ : S → SetRel (Fin h) (Fin h)) (hsurj : Function.Surjective φ)
    (hmul : ∀ a b : S,
      φ ⟨Diagram.comp a.val b.val, hclosed a.property b.property⟩ = φ a ○ φ b)
    (hreverse : ∀ a b : S, (a.val, b.val) ∈ Diagram.inclusion m → φ b ⊆ φ a) :
    lossBound h ≤ 2 * m := by
  simpa only [Nat.card_fin] using order_reversing_image_bound_finite (H := Fin h) m _hm
    (by simpa using hh) S hidentity hclosed φ hsurj hmul hreverse

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Only the first tape position carries the left endmarker. -/
theorem tapeSymbol_left_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 0 ↔ p.val = 0 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

/-- Only the last original tape position carries the right endmarker. -/
theorem tapeSymbol_right_iff {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    tapeSymbol w p = Sum.inl 1 ↔ p.val = w.length + 1 := by
  unfold tapeSymbol
  split_ifs <;> simp_all

namespace TwoNFA

theorem reindex_language {Sigma Q Q' : Type*} (A : TwoNFA Sigma Q) (e : Q ≃ Q') :
    (A.reindex e).language = A.language := by
  ext w
  constructor
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e.symm q, p), haccept, ?_⟩
    have h := hrun.lift (fun c : Q' × Fin (w.length + 2) => (e.symm c.1, c.2))
      (p := fun c d => (c, d) ∈ A.step w) (fun _ _ h => h)
    simpa only [Function.onFun, reindex, relStar, Set.mem_ofPred_eq, Equiv.symm_apply_apply] using h
  · rintro ⟨⟨q, p⟩, haccept, hrun⟩
    refine ⟨(e q, p), ?_, ?_⟩
    · simpa only [reindex, Set.mem_preimage, Equiv.symm_apply_apply] using haccept
    · exact hrun.lift (fun c : Q × Fin (w.length + 2) => (e c.1, c.2))
        (fun c d h => by
          simpa only [Function.onFun, step, reindex, Set.mem_ofPred_eq,
            Equiv.symm_apply_apply] using h)

theorem augmentConfig_injective {Q : Type*} {n : ℕ} :
    Function.Injective (augmentConfig : Q × Fin n → Option Q × Fin (n + 1)) := by
  intro a b hab
  have hstate : some a.1 = some b.1 := congrArg Prod.fst hab
  have hpos : a.2.val = b.2.val :=
    congrArg (fun p : Option Q × Fin (n + 1) => p.2.val) hab
  exact Prod.ext (Option.some.inj hstate) (Fin.ext hpos)

/-- Before entering the fresh state, every augmented finite path is an original run. -/
theorem augmented_run_cases {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    {c : Option Q × Fin (w.length + 3)}
    (hrun : (augmentConfig (A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.augmentedStep w)) :
    w ∈ A.language ∨ ∃ x : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ ((A.initial, ⟨0, by omega⟩), x) ∈ relStar (A.step w) := by
  induction hrun with
  | refl => exact Or.inr ⟨(A.initial, ⟨0, by omega⟩), rfl, .refl⟩
  | @tail c d _ hstep ih =>
    rcases ih with haccept | ⟨x, rfl, hxrun⟩
    · exact Or.inl haccept
    rcases hstep with ⟨y, z, hxy, rfl, hyz⟩ | ⟨q, p, hxq, _, hq⟩ | ⟨hnone, _, _⟩
    · have hxy' : x = y := augmentConfig_injective hxy
      exact Or.inr ⟨z, rfl, (hxy' ▸ hxrun).tail hyz⟩
    · have hxq' : x = (q, p) := augmentConfig_injective hxq
      exact Or.inl ⟨(q, p), hq, hxq' ▸ hxrun⟩
    · exact (Option.some_ne_none _ hnone).elim

/-- The fresh state can sweep from any position to the designated right exit. -/
theorem augmented_sink_exit {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (p : Fin (w.length + 3)) :
    ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
  have hsweep : ∀ k, ∀ p : Fin (w.length + 3), p.val + k = w.length + 2 →
      ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      have hlast : p = ⟨w.length + 2, by omega⟩ := Fin.ext (by omega)
      rw [hlast]
      exact .refl
    | succ k ih =>
      intro p hp
      let next : Fin (w.length + 3) := ⟨p.val + 1, by omega⟩
      have hnext : next.val + k = w.length + 2 := by dsimp [next]; omega
      exact (ih next hnext).head (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  exact hsweep (w.length + 2 - p.val) p (by omega)

/-- Finite acceptance is equivalent to reaching the designated augmented exit. -/
theorem augmented_acceptance {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    w ∈ A.language ↔
      (augmentConfig (A.initial, ⟨0, by omega⟩), (none, ⟨w.length + 2, by omega⟩)) ∈
        relStar (A.augmentedStep w) := by
  constructor
  · rintro ⟨c, hc, hrun⟩
    have hlift := hrun.lift augmentConfig
      (p := fun c d => (c, d) ∈ A.augmentedStep w)
      (fun x y h => Or.inl ⟨x, y, rfl, rfl, h⟩)
    have hjump : (augmentConfig c, (none, c.2.castSucc)) ∈ A.augmentedStep w :=
      Or.inr (Or.inl ⟨c.1, c.2, rfl, rfl, hc⟩)
    exact (hlift.tail hjump).trans (A.augmented_sink_exit w c.2.castSucc)
  · intro hrun
    rcases A.augmented_run_cases w hrun with h | ⟨c, heq, _⟩
    · exact h
    · have hnone : (none : Option Q) = some c.1 :=
        congrArg (fun p : Option Q × Fin (w.length + 3) => p.1) heq
      cases hnone

/-- The global augmented graph is exactly the graph of the local moves and head displacement. -/
theorem augmentedStep_local_iff {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (c d : Option Q × Fin (w.length + 3)) :
    (c, d) ∈ A.augmentedStep w ↔
      ∃ p : Fin (w.length + 2), c.2 = p.castSucc ∧ ∃ move : Fin 3,
        (c.1, d.1) ∈ A.augmentedMove (tapeSymbol w p) move ∧
        (d.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 := by
  constructor
  · rintro (⟨⟨q, p⟩, ⟨r, t⟩, rfl, rfl, hstep⟩ |
      ⟨q, p, rfl, rfl, hq⟩ | ⟨hc, hd, hpos⟩)
    · obtain ⟨move, htrans, hpos⟩ := hstep
      change (t.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hpos
      refine ⟨p, rfl, move, ⟨htrans, ?_, ?_⟩, hpos⟩
      · intro hleft hmove
        have hp := (tapeSymbol_left_iff w p).mp hleft
        have hm := congrArg Fin.val hmove
        simp only [Fin.val_zero] at hm
        omega
      · intro hright hmove
        have hp := (tapeSymbol_right_iff w p).mp hright
        have hm := congrArg Fin.val hmove
        norm_num at hm
        omega
    · exact ⟨p, rfl, 1, ⟨hq, rfl⟩, by simp⟩
    · let p : Fin (w.length + 2) := ⟨c.2.val, by have := d.2.isLt; omega⟩
      refine ⟨p, Fin.ext rfl, 2, ?_, ?_⟩
      · rw [hc, hd]
        exact rfl
      · dsimp [p]
        omega
  · rintro ⟨p, hpos, move, hlocal, hdisp⟩
    obtain ⟨cq, cp⟩ := c
    obtain ⟨dq, dp⟩ := d
    change cp = p.castSucc at hpos
    subst cp
    change (dp.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
    cases cq with
    | none =>
      cases dq with
      | none =>
        change move = 2 at hlocal
        subst move
        exact Or.inr (Or.inr ⟨rfl, rfl, by simp only [Fin.val_castSucc]; norm_num at hdisp; omega⟩)
      | some r => exact hlocal.elim
    | some q =>
      cases dq with
      | none =>
        change q ∈ A.accepting ∧ move = 1 at hlocal
        obtain ⟨hq, rfl⟩ := hlocal
        refine Or.inr (Or.inl ⟨q, p, rfl, ?_, hq⟩)
        congr 1
        apply Fin.ext
        change dp.val = p.val
        norm_num at hdisp
        omega
      | some r =>
        change (r, move) ∈ A.transition q (tapeSymbol w p) ∧
          (tapeSymbol w p = Sum.inl 0 → move ≠ 0) ∧
          (tapeSymbol w p = Sum.inl 1 → move ≠ 2) at hlocal
        have hdp : dp.val < w.length + 2 := by
          by_contra hn
          have hdpval : dp.val = w.length + 2 := by omega
          have hpval : p.val = w.length + 1 := by have := move.isLt; omega
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          exact hlocal.2.2 ((tapeSymbol_right_iff w p).mpr hpval) hm
        refine Or.inl ⟨(q, p), (r, ⟨dp.val, hdp⟩), rfl, ?_, move, hlocal.1, hdisp⟩
        exact Prod.ext rfl (Fin.ext rfl)

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Source ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem relationProduct_append {H : Type*} (u v : List (SetRel H H)) :
    relationProduct (u ++ v) = relationProduct u ○ relationProduct v := by
  induction u with
  | nil => simp [relationProduct]
  | cons R u ih => simpa [relationProduct, SetRel.comp_assoc] using congrArg (R ○ ·) ih

theorem sourceProductive_of_step {H : Type*} (w : List (SetRel H H))
    {c d : Option (Option H) × Fin (w.length + 2)}
    (hstep : (c, d) ∈ (sourceAutomaton H).step w) (hd : d ∈ sourceProductive w) :
    c ∈ sourceProductive w := by
  obtain ⟨cs, ci⟩ := c
  obtain ⟨ds, di⟩ := d
  obtain ⟨move, htransition, hpos⟩ := hstep
  change (ds, move) ∈ (sourceAutomaton H).transition cs (tapeSymbol w ci) at htransition
  change (di.val : ℤ) = (ci.val : ℤ) + (move.val : ℤ) - 1 at hpos
  cases cs with
  | none =>
    by_cases hleft : ci.val = 0
    · have hex : ∃ p, ds = some (some p) ∧ move = 2 := by
        simpa [sourceAutomaton, tapeSymbol, hleft] using htransition
      obtain ⟨p, hds, hmove⟩ := hex
      subst ds
      subst move
      have hdi : di.val = 1 := by norm_num at hpos; omega
      obtain ⟨_, q, hpq⟩ := hd
      exact ⟨hleft, (p, q), by simpa [hdi] using hpq⟩
    · by_cases hright : ci.val = w.length + 1 <;>
        simp [sourceAutomaton, tapeSymbol, hleft, hright] at htransition
  | some state =>
    cases state with
    | none =>
      change (ds, move) ∈ (∅ : Set (Option (Option H) × Fin 3)) at htransition
      exact htransition.elim
    | some p =>
      by_cases hleft : ci.val = 0
      · simp [sourceAutomaton, tapeSymbol, hleft] at htransition
      · by_cases hright : ci.val = w.length + 1
        · change 1 ≤ ci.val ∧ ∃ q, (p, q) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, p, ?_⟩
          simp [hright, relationProduct]
        · have hex : ∃ q, (p, q) ∈ w[ci.val - 1]'(by omega) ∧
              ds = some (some q) ∧ move = 2 := by
            simpa [sourceAutomaton, tapeSymbol, hleft, hright] using htransition
          obtain ⟨q, hpq, hds, hmove⟩ := hex
          subst ds
          subst move
          have hdi : di.val = ci.val + 1 := by norm_num at hpos; omega
          obtain ⟨_, r, hqr⟩ := hd
          change 1 ≤ ci.val ∧ ∃ r, (p, r) ∈ relationProduct (w.drop (ci.val - 1))
          refine ⟨by omega, r, ?_⟩
          rw [List.drop_eq_getElem_cons (show ci.val - 1 < w.length from by omega)]
          change (p, r) ∈ w[ci.val - 1] ○ relationProduct (w.drop (ci.val - 1 + 1))
          refine ⟨q, hpq, ?_⟩
          simpa only [hdi, Nat.add_sub_cancel,
            Nat.sub_add_cancel (show 1 ≤ ci.val by omega)] using hqr

theorem sourceAutomaton_sound {H : Type*} (w : List (SetRel H H))
    (hw : w ∈ (sourceAutomaton H).language) : (relationProduct w).Nonempty := by
  obtain ⟨c, hc, hrun⟩ := hw
  have hproductive : c ∈ sourceProductive w := by
    change c.1 ∈ ({some none} : Set (Option (Option H))) at hc
    have hstate : c.1 = some none := hc
    simp only [sourceProductive, Set.mem_ofPred_eq, hstate]
  have hback : ∀ {c d}, (c, d) ∈ relStar ((sourceAutomaton H).step w) →
      d ∈ sourceProductive w → c ∈ sourceProductive w := by
    intro c d h
    induction h with
    | refl => exact id
    | tail _ hstep ih => exact fun hd => ih (sourceProductive_of_step w hstep hd)
  exact (hback hrun hproductive).2

theorem sourceAutomaton_suffix_run {H : Type*} (w : List (SetRel H H))
    (u v : List (SetRel H H)) (hw : w = u ++ v) {p q : H}
    (hpq : (p, q) ∈ relationProduct v) :
    ((some (some p), ⟨u.length + 1, by simp [hw]⟩),
      (some none, ⟨w.length + 1, by omega⟩)) ∈ relStar ((sourceAutomaton H).step w) := by
  induction v generalizing u p with
  | nil =>
    have hlen : w.length = u.length := by simp [hw]
    apply Relation.ReflTransGen.single
    refine ⟨1, ?_, ?_⟩
    · simp [sourceAutomaton, tapeSymbol, hlen]
    · simp [hlen]
  | cons R v ih =>
    obtain ⟨r, hpr, hrq⟩ := hpq
    have hlen : w.length = u.length + (v.length + 1) := by simp [hw]
    have hw' : w = (u ++ [R]) ++ v := by
      simpa only [List.append_assoc, List.singleton_append] using hw
    have htail := ih (u ++ [R]) hw' hrq
    apply htail.head
    refine ⟨2, ?_, ?_⟩
    · have hsymbol : tapeSymbol w ⟨u.length + 1, by omega⟩ = Sum.inr R := by
        simp [tapeSymbol, hw, List.getElem_append_right]
      change (some (some r), (2 : Fin 3)) ∈
        (sourceAutomaton H).transition (some (some p)) (tapeSymbol w _)
      rw [hsymbol]
      exact ⟨r, hpr, rfl⟩
    · simp [List.length_append]
      omega

/-- The explicit machine recognizes nonempty relation products. -/
theorem sourceAutomaton_language (H : Type*) :
    (sourceAutomaton H).language = sourceLanguage H := by
  ext w
  constructor
  · exact sourceAutomaton_sound w
  · rintro ⟨⟨p, q⟩, hpq⟩
    refine ⟨(some none, ⟨w.length + 1, by omega⟩), rfl, ?_⟩
    have hrun := sourceAutomaton_suffix_run w [] w (by simp) hpq
    apply hrun.head
    refine ⟨2, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · norm_num

/-- The source language on `h` labels is recognized using exactly `h + 2` states. -/
theorem sourceLanguage_state_bound (H : Type*) [Fintype H] :
    ∃ A : TwoNFA (SetRel H H) (Fin (Fintype.card H + 2)), A.language = sourceLanguage H := by
  classical
  let e : Option (Option H) ≃ Fin (Fintype.card H + 2) :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  refine ⟨(sourceAutomaton H).reindex e, ?_⟩
  rw [TwoNFA.reindex_language, sourceAutomaton_language]

/-- Singleton letters on the two sides test one edge of a word's relation product. -/
theorem singleton_word_context {H : Type*} (w : List (SetRel H H)) (p q : H) :
    (relationProduct ([restrictedIdentity {p}] ++ w ++ [restrictedIdentity {q}])).Nonempty ↔
      (p, q) ∈ relationProduct w := by
  rw [relationProduct_append, relationProduct_append]
  simp only [relationProduct, List.foldr_cons, List.foldr_nil, SetRel.comp_id]
  rw [singleton_context]
  constructor
  · rintro ⟨⟨x, y⟩, _, _, hpq⟩
    exact hpq
  · intro hpq
    exact ⟨(p, q), rfl, rfl, hpq⟩

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Recognition ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Singleton contexts force reversal of relation inclusion. -/
theorem word_diagram_order_reversal {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty)
    {u v : List (SetRel H H)} (huv : (τ u, τ v) ∈ Diagram.inclusion m) :
    relationProduct v ⊆ relationProduct u := by
  classical
  rintro ⟨p, q⟩ hpq
  by_contra hn
  let left := [restrictedIdentity {p}]
  let right := [restrictedIdentity {q}]
  have hU : ¬ (relationProduct (left ++ u ++ right)).Nonempty :=
    fun h => hn ((singleton_word_context u p q).mp h)
  have hV : (relationProduct (left ++ v ++ right)).Nonempty :=
    (singleton_word_context v p q).mpr hpq
  have hcontext : (τ (left ++ u ++ right), τ (left ++ v ++ right)) ∈ Diagram.inclusion m := by
    simp only [hmul]
    exact Diagram.comp_mono (Diagram.comp_mono (Diagram.inclusion_refl _) huv)
      (Diagram.inclusion_refl _)
  have hmarked := Diagram.comp_mono
    (Diagram.comp_mono (Diagram.inclusion_refl l) hcontext) (Diagram.inclusion_refl r)
  exact (hlanguage _).mp (hmarked.1 ((hlanguage _).mpr hU)) hV

/-- The relation product descends to the diagram image by singleton-context tests. -/
theorem diagram_relation_image {H : Type*} {m : ℕ}
    (τ : List (SetRel H H) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) :
    ∃ S : Submonoid (Diagram m), ∃ φ : S →* RelationMonoid H,
      Function.Surjective φ ∧
      (∀ z w : S, (z.val, w.val) ∈ Diagram.inclusion m → (φ w).toRel ⊆ (φ z).toRel) := by
  classical
  let S : Submonoid (Diagram m) :=
    { carrier := Set.range τ
      one_mem' := ⟨[], hzero⟩
      mul_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u ++ v, hmul u v⟩ }
  have hword (z : S) : ∃ w, τ w = z.val := z.property
  choose word hwordeq using hword
  have hwell {u v : List (SetRel H H)} (huv : τ u = τ v) :
      relationProduct u = relationProduct v := by
    apply Set.Subset.antisymm
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
    · apply word_diagram_order_reversal τ hmul l r a b hlanguage
      rw [huv]
      exact Diagram.inclusion_refl _
  have hvalue (z : S) (w : List (SetRel H H)) (hw : τ w = z.val) :
      relationProduct (word z) = relationProduct w := hwell ((hwordeq z).trans hw.symm)
  let φ : S →* RelationMonoid H :=
    { toFun := fun z => .ofRel (relationProduct (word z))
      map_one' := by
        apply RelationMonoid.ext
        exact hvalue 1 [] hzero
      map_mul' := by
        intro z w
        apply RelationMonoid.ext
        change relationProduct (word (z * w)) = relationProduct (word z) ○ relationProduct (word w)
        rw [hvalue (z * w) (word z ++ word w) (by rw [hmul, hwordeq, hwordeq]; rfl)]
        exact relationProduct_append _ _ }
  refine ⟨S, φ, ?_, ?_⟩
  · intro R
    refine ⟨⟨τ [R.toRel], [R.toRel], rfl⟩, ?_⟩
    apply RelationMonoid.ext
    change relationProduct (word _) = R.toRel
    rw [hvalue _ [R.toRel] rfl]
    simp [relationProduct]
  · intro z w hzw
    change relationProduct (word w) ⊆ relationProduct (word z)
    apply word_diagram_order_reversal τ hmul l r a b hlanguage
    rwa [hwordeq, hwordeq]

/-- Recognition of relation-product emptiness forces the image theorem's state bound. -/
theorem diagram_recognition_lower_bound (h m : ℕ) (hh : 2 ≤ h) (hm : 1 ≤ m)
    (τ : List (SetRel (Fin h) (Fin h)) → Diagram m)
    (hzero : τ [] = Diagram.identity m)
    (hmul : ∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v))
    (l r : Diagram m) (a b : Fin m)
    (hlanguage : ∀ w, (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward ↔
      ¬ (relationProduct w).Nonempty) : lossBound h ≤ 2 * m := by
  obtain ⟨S, φ, hsurj, hreverse⟩ := diagram_relation_image τ hzero hmul l r a b hlanguage
  apply order_reversing_image_bound m h hm hh S S.one_mem (by
    intro z w hz hw
    change z * w ∈ S
    exact S.mul_mem hz hw)
    (fun z => (φ z).toRel)
  · intro R
    obtain ⟨z, hz⟩ := hsurj (RelationMonoid.ofRel R)
    exact ⟨z, congrArg RelationMonoid.toRel hz⟩
  · intro z w
    change (φ (z * w)).toRel = (φ z).toRel ○ (φ w).toRel
    rw [map_mul, RelationMonoid.toRel_mul]
  · exact hreverse

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Network ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem wordDiagram_append {Sigma : Type*} {m : ℕ} (d : Sigma → Diagram m)
    (u v : List Sigma) :
    wordDiagram d (u ++ v) = Diagram.comp (wordDiagram d u) (wordDiagram d v) := by
  change ((u ++ v).map d).prod = (u.map d).prod * (v.map d).prod
  rw [List.map_append, List.prod_append]

/-- Swap the two vertex blocks without changing the finite-path semantics. -/
theorem blockRelation_star_swap {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : α ⊕ β) :
    (x.swap, y.swap) ∈ relStar (blockRelation H G F E) ↔
      (x, y) ∈ relStar (blockRelation E F G H) := by
  have hs {a b : α ⊕ β} :
      (a.swap, b.swap) ∈ blockRelation H G F E ↔ (a, b) ∈ blockRelation E F G H := by
    cases a <;> cases b <;> rfl
  constructor
  · intro h
    have h' := h.lift Sum.swap (p := fun a b => (a, b) ∈ blockRelation E F G H)
      (fun a b hab => by cases a <;> cases b <;> exact hab)
    change Relation.ReflTransGen (fun a b => (a, b) ∈ blockRelation E F G H) x y
    simpa only [Function.onFun, Sum.swap_swap] using h'
  · exact fun h => h.lift Sum.swap (fun _ _ hab => hs.mpr hab)

/-- The left-left version of block elimination. -/
theorem blockRelation_star_left {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : α) :
    (Sum.inl x, Sum.inl y) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (E ∪ (F ○ relStar H ○ G)) := by
  rw [← blockRelation_star_swap]
  exact blockRelation_star_right H G F E x y

/-- The right-left version of block elimination. -/
theorem blockRelation_star_back {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : β) (y : α) :
    (Sum.inr x, Sum.inl y) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar H ○ G ○ relStar (E ∪ (F ○ relStar H ○ G)) := by
  rw [← blockRelation_star_swap]
  exact blockRelation_star_cross H G F E x y

/-- Eliminate an internal graph while retaining arbitrary repeated feedback at its entry. -/
theorem relStar_entry_feedback {Q V : Type*} (I : SetRel Q V) (E : SetRel V V)
    (O R : SetRel V Q) (X : SetRel Q Q) :
    I ○ relStar (E ∪ (R ○ X ○ I)) ○ O =
      relStar (I ○ relStar E ○ R ○ X) ○ (I ○ relStar E ○ O) := by
  have hrotate := comp_relStar_rotate (I ○ relStar E) (R ○ X)
  simpa only [relStar_union, SetRel.comp_assoc] using congrArg (· ○ O) hrotate

/-- Internal paths either avoid the feedback edge or use it after a first internal segment. -/
theorem relStar_general_feedback {Q V : Type*} (I J : SetRel Q V) (E : SetRel V V)
    (O R : SetRel V Q) (X : SetRel Q Q) :
    I ○ relStar (E ∪ (R ○ X ○ J)) ○ O =
      (I ○ relStar E ○ O) ∪
        (I ○ relStar E ○ R ○ relStar (X ○ J ○ relStar E ○ R) ○ X ○ J ○ relStar E ○ O) := by
  have hu := relStar_comp_unfold (R : SetRel V Q) (X ○ J ○ relStar E)
  have hexpand := congrArg (fun K => I ○ relStar E ○ K ○ O) hu
  simpa only [relStar_union, relComp_union, union_relComp, SetRel.comp_id,
    SetRel.comp_assoc] using hexpand

namespace Network

/-- Joining path networks implements exactly the four diagram multiplication formulas. -/
theorem summary_join {m : ℕ} {V W : Type*} (N : Network m V) (M : Network m W) :
    (N.join M).summary = Diagram.comp N.summary M.summary := by
  have hF : (N.join M).summary.forward =
      N.leftIn ○ (relStar N.edge ○ (N.rightOut ○ M.leftIn) ○
        relStar (M.edge ∪ ((M.leftOut ○ N.rightIn) ○ relStar N.edge ○
          (N.rightOut ○ M.leftIn)))) ○ M.rightOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_cross _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, hab, hby⟩
      obtain ⟨a, hxa, hab⟩ := hab
      exact ⟨Sum.inr b, ⟨Sum.inl a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_cross _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hB : (N.join M).summary.backward =
      M.rightIn ○ (relStar M.edge ○ (M.leftOut ○ N.rightIn) ○
        relStar (N.edge ∪ ((N.rightOut ○ M.leftIn) ○ relStar M.edge ○
          (M.leftOut ○ N.rightIn)))) ○ N.leftOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_back _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, hab, hby⟩
      obtain ⟨a, hxa, hab⟩ := hab
      exact ⟨Sum.inl b, ⟨Sum.inr a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_back _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hL : (N.join M).summary.left =
      N.leftIn ○ relStar (N.edge ∪ ((N.rightOut ○ M.leftIn) ○ relStar M.edge ○
        (M.leftOut ○ N.rightIn))) ○ N.leftOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_left _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, ⟨a, hxa, hab⟩, hby⟩
      exact ⟨Sum.inl b, ⟨Sum.inl a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_left _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hR : (N.join M).summary.right =
      M.rightIn ○ relStar (M.edge ∪ ((M.leftOut ○ N.rightIn) ○ relStar N.edge ○
        (N.rightOut ○ M.leftIn))) ○ M.rightOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_right _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, ⟨a, hxa, hab⟩, hby⟩
      exact ⟨Sum.inr b, ⟨Sum.inr a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_right _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  apply Diagram.ext
  · rw [hF]
    have hf := relStar_entry_feedback M.leftIn M.edge M.rightOut M.leftOut
      (N.rightIn ○ relStar N.edge ○ N.rightOut)
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      congrArg ((N.leftIn ○ relStar N.edge ○ N.rightOut) ○ ·) hf
  · rw [hB]
    have hb := relStar_entry_feedback N.rightIn N.edge N.leftOut N.rightOut
      (M.leftIn ○ relStar M.edge ○ M.leftOut)
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      congrArg ((M.rightIn ○ relStar M.edge ○ M.leftOut) ○ ·) hb
  · rw [hL]
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      relStar_general_feedback N.leftIn N.rightIn N.edge N.leftOut N.rightOut
        (M.leftIn ○ relStar M.edge ○ M.leftOut)
  · rw [hR]
    have hr := relStar_general_feedback M.rightIn M.leftIn M.edge M.rightOut M.leftOut
      (N.rightIn ○ relStar N.edge ○ N.rightOut)
    have hrot := comp_relStar_rotate (N.rightIn ○ relStar N.edge ○ N.rightOut)
      (M.leftIn ○ relStar M.edge ○ M.leftOut)
    calc
      _ = M.summary.right ∪ (M.summary.backward ○
          relStar (N.summary.right ○ M.summary.left) ○ N.summary.right ○
            M.summary.forward) := by
        simpa only [summary, SetRel.comp_assoc] using hr
      _ = _ := by
        simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
          congrArg (fun K => M.summary.right ∪ (M.summary.backward ○ K ○
            M.summary.forward)) hrot.symm

end Network

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Chain ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace ChainNode

end ChainNode

/-- The path summary of a cell chain is the product of its cell diagrams. -/
theorem chainNetwork_summary {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma) :
    (chainNetwork moves w last).summary =
      wordDiagram (fun a => cellDiagram m (moves a 1) (moves a 2) (moves a 0)) (w ++ [last]) := by
  induction w with
  | nil =>
    change (cellNetwork (moves last)).summary = _
    simp [Network.summary, cellNetwork, cellDiagram, wordDiagram, SetRel.id_comp]
  | cons a w ih =>
    change ((cellNetwork (moves a)).join (chainNetwork moves w last)).summary = _
    rw [Network.summary_join, ih]
    simp only [Network.summary, cellNetwork, SetRel.id_comp, cellDiagram, wordDiagram,
      List.cons_append, List.map_cons, List.prod_cons]
    rfl

/-- Entrances attach exactly to the first and last cells with their unchanged labels. -/
theorem chainNetwork_entrances {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q : Fin m) (c : ChainNode m w.length) :
    ((q, c) ∈ (chainNetwork moves w last).leftIn ↔ c.position = 0 ∧ q = c.label) ∧
    ((q, c) ∈ (chainNetwork moves w last).rightIn ↔ c.position = w.length ∧ q = c.label) := by
  induction w with
  | nil =>
    change (q = c ↔ 0 = 0 ∧ q = c) ∧ (q = c ↔ 0 = 0 ∧ q = c)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ 0 = 0 ∧ q = r) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔ 0 = w.length + 1 ∧ q = r)
      simp [eq_comm]
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ c.position + 1 = 0 ∧ q = c.label) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔
            c.position + 1 = w.length + 1 ∧ q = c.label)
      simpa using (ih c).2

/-- Only the endpoint cells can exit a chain, using the appropriate moving transition. -/
theorem chainNetwork_exits {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) (q : Fin m) :
    ((c, q) ∈ (chainNetwork moves w last).leftOut ↔
      c.position = 0 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
    ((c, q) ∈ (chainNetwork moves w last).rightOut ↔
      c.position = w.length ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2) := by
  induction w with
  | nil =>
    change ((c, q) ∈ moves last 0 ↔ 0 = 0 ∧ (c, q) ∈ moves last 0) ∧
      ((c, q) ∈ moves last 2 ↔ 0 = 0 ∧ (c, q) ∈ moves last 2)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ 0 = 0 ∧ (r, q) ∈ moves a 0) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            0 = w.length + 1 ∧ (r, q) ∈ moves a 2)
      simp
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ c.position + 1 = 0 ∧
            (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            c.position + 1 = w.length + 1 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2)
      simpa using (ih c).2

/-- Internal edges are precisely local transitions that stay within the chain. -/
theorem chainNetwork_edges {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) :
    (c, d) ∈ (chainNetwork moves w last).edge ↔
      ∃ move : Fin 3, (c.label, d.label) ∈ moves (chainSymbol w last c) move ∧
        (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1 := by
  induction w with
  | nil =>
    change (c, d) ∈ moves last 1 ↔
      ∃ move : Fin 3, (c, d) ∈ moves last move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
    constructor
    · exact fun h => ⟨1, h, by norm_num⟩
    · rintro ⟨move, h, hp⟩
      have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
      simpa only [hm] using h
  | cons a w ih =>
    cases c with
    | inl q =>
      cases d with
      | inl r =>
        change (q, r) ∈ moves a 1 ↔
          ∃ move : Fin 3, (q, r) ∈ moves a move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
        constructor
        · exact fun h => ⟨1, h, by norm_num⟩
        · rintro ⟨move, h, hp⟩
          have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
          simpa only [hm] using h
      | inr d =>
        change (q, d) ∈ moves a 2 ○ (chainNetwork moves w last).leftIn ↔ _
        constructor
        · rintro ⟨r, hqr, hrd⟩
          obtain ⟨hp, hq⟩ := (chainNetwork_entrances moves w last r d).1.mp hrd
          exact ⟨2, hq ▸ hqr, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change ((d.position + 1 : ℕ) : ℤ) = 0 + (move.val : ℤ) - 1 at hp
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          have hd : d.position = 0 := by have := move.isLt; omega
          refine ⟨d.label, ?_, (chainNetwork_entrances moves w last d.label d).1.mpr ⟨hd, rfl⟩⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
    | inr c =>
      cases d with
      | inl r =>
        change (c, r) ∈ (chainNetwork moves w last).leftOut ○ SetRel.id ↔ _
        rw [SetRel.comp_id]
        constructor
        · intro h
          obtain ⟨hp, hq⟩ := (chainNetwork_exits moves w last c r).1.mp h
          exact ⟨0, hq, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change (0 : ℤ) = ((c.position + 1 : ℕ) : ℤ) + (move.val : ℤ) - 1 at hp
          have hm : move = 0 := Fin.ext (by omega)
          have hc : c.position = 0 := by omega
          refine (chainNetwork_exits moves w last c r).1.mpr ⟨hc, ?_⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
      | inr d =>
        change (c, d) ∈ (chainNetwork moves w last).edge ↔ _
        rw [ih c d]
        simp only [ChainNode.label, chainSymbol, ChainNode.position, Nat.cast_add, Nat.cast_one]
        constructor <;> rintro ⟨move, h, hp⟩ <;> exact ⟨move, h, by omega⟩

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Tape ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Chain symbols agree with ordinary zero-based lookup of the nonempty symbol list. -/
theorem chainSymbol_getElem {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) :
    chainSymbol w last c = (w ++ [last])[c.position]'(by
      have := c.position_le
      simp only [List.length_append, List.length_singleton]
      omega) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases c with
    | inl q => rfl
    | inr c => simpa only [chainSymbol, ChainNode.position, List.cons_append,
        List.getElem_cons_succ] using ih c

/-- Lookup of the explicitly marked list agrees with the automaton's tape lookup. -/
theorem marked_getElem {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    ((Sum.inl 0 : Fin 2 ⊕ Sigma) :: (w.map Sum.inr ++ [Sum.inl 1]))[p.val]'(by simp; omega) =
      tapeSymbol w p := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | zero => rfl
  | succ p =>
    by_cases h : p = w.length
    · subst p
      simp [tapeSymbol]
    · have hlt : p < w.length := by omega
      rw [List.getElem_cons_succ, List.getElem_append_left (by simpa using hlt),
        List.getElem_map]
      simp [tapeSymbol, h]

/-- A graph equivalence transports finite paths in both directions. -/
theorem relStar_equiv_iff {V W : Type*} (e : V ≃ W) (R : SetRel V V) (S : SetRel W W)
    (h : ∀ x y, (e x, e y) ∈ S ↔ (x, y) ∈ R) (x y : V) :
    (e x, e y) ∈ relStar S ↔ (x, y) ∈ relStar R := by
  constructor
  · intro hrun
    have hlift := hrun.lift e.symm (p := fun a b => (a, b) ∈ R) (by
      intro a b hab
      apply (h (e.symm a) (e.symm b)).mp
      simpa only [Equiv.apply_symm_apply] using hab)
    change Relation.ReflTransGen (fun a b => (a, b) ∈ R) x y
    simpa only [Function.onFun, Equiv.symm_apply_apply] using hlift
  · exact fun hrun => hrun.lift e (fun a b hab => (h a b).mpr hab)

/-- A terminal block with no outgoing edges is reached by an internal path and one exit. -/
theorem blockRelation_terminal {V Q : Type*} (E : SetRel V V) (O : SetRel V Q)
    (c : V) (q : Q) :
    (Sum.inl c, Sum.inr q) ∈ relStar (blockRelation E O ∅ ∅) ↔
      (c, q) ∈ relStar E ○ O := by
  rw [blockRelation_star_cross]
  simp only [SetRel.empty_comp, Set.empty_union, relStar_empty, SetRel.comp_id]

/-- A cell's scanned symbol depends only on its position. -/
theorem chainSymbol_position {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) (hp : c.position = d.position) :
    chainSymbol w last c = chainSymbol w last d := by
  rw [chainSymbol_getElem, chainSymbol_getElem]
  simp only [hp]

/-- The joined network with terminal exits has exactly the bounded tape's local edges. -/
theorem chainStep_exitEquiv {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (x y : ChainNode m w.length ⊕ Fin m) :
    (ChainNode.exitEquiv m w.length x, ChainNode.exitEquiv m w.length y) ∈
        chainStep moves w last ↔
      (x, y) ∈ blockRelation (chainNetwork moves w last).edge
        (chainNetwork moves w last).rightOut ∅ ∅ := by
  cases x with
  | inl c =>
    cases y with
    | inl d =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, d.label) ∈ moves (chainSymbol w last a) move ∧
            (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, d) ∈ (chainNetwork moves w last).edge
      rw [chainNetwork_edges]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        exact ⟨move, (chainSymbol_position w last a c hp.symm) ▸ h, hd⟩
      · rintro ⟨move, h, hd⟩
        exact ⟨c, rfl, move, h, hd⟩
    | inr q =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, q) ∈ moves (chainSymbol w last a) move ∧
            ((w.length + 1 : ℕ) : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, q) ∈ (chainNetwork moves w last).rightOut
      rw [(chainNetwork_exits moves w last c q).2]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        have hc := c.position_le
        have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
        refine ⟨by have := move.isLt; omega, ?_⟩
        simpa only [← chainSymbol_position w last c a hp, hm] using h
      · rintro ⟨hp, h⟩
        exact ⟨c, rfl, 2, h, by rw [hp]; push_cast; omega⟩
  | inr q =>
    change (∃ a : ChainNode m w.length, w.length + 1 = a.position ∧ _) ↔ _
    constructor
    · rintro ⟨a, hp, _⟩
      have := a.position_le
      omega
    · intro h
      cases y <;> exact h.elim

/-- The designated forward edge of a diagram product is exactly a successful tape run. -/
theorem chainStep_recognition {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q r : Fin m) :
    ((q, ⟨0, by omega⟩), (r, ⟨w.length + 1, by omega⟩)) ∈ relStar (chainStep moves w last) ↔
      (q, r) ∈ (chainNetwork moves w last).summary.forward := by
  obtain ⟨c, hq, hp⟩ := ChainNode.coordinates_surjective (n := w.length) q 0 (Nat.zero_le _)
  have hstart : ChainNode.exitEquiv m w.length (Sum.inl c) = (q, ⟨0, by omega⟩) :=
    Prod.ext hq (Fin.ext hp)
  have hend : ChainNode.exitEquiv m w.length (Sum.inr r) =
      (r, ⟨w.length + 1, by omega⟩) := rfl
  rw [← hstart, ← hend, relStar_equiv_iff (ChainNode.exitEquiv m w.length)
    (blockRelation (chainNetwork moves w last).edge (chainNetwork moves w last).rightOut ∅ ∅)
    (chainStep moves w last) (chainStep_exitEquiv moves w last), blockRelation_terminal]
  constructor
  · rintro ⟨d, hcd, hdr⟩
    exact ⟨d, ⟨c, (chainNetwork_entrances moves w last q c).1.mpr ⟨hp, hq.symm⟩,
      hcd⟩, hdr⟩
  · rintro ⟨d, ⟨c', hqc, hcd⟩, hdr⟩
    obtain ⟨hp', hq'⟩ := (chainNetwork_entrances moves w last q c').1.mp hqc
    have hc : c' = c := c'.coordinates_injective c (hp'.trans hp.symm) (hq'.symm.trans hq.symm)
    exact ⟨d, hc ▸ hcd, hdr⟩

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Representation ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Every 2NFA has an exact diagram representation with one additional state label. -/
theorem TwoNFA.diagram_representation {Sigma : Type*} {s : ℕ} (A : TwoNFA Sigma (Fin s)) :
    ∃ τ : List Sigma → Diagram (s + 1), ∃ l r : Diagram (s + 1), ∃ a b : Fin (s + 1),
      τ [] = Diagram.identity (s + 1) ∧
      (∀ u v, τ (u ++ v) = Diagram.comp (τ u) (τ v)) ∧
      (∀ w, w ∈ A.language ↔ (a, b) ∈ (Diagram.comp (Diagram.comp l (τ w)) r).forward) := by
  let e := finSuccEquiv s
  let moves (symbol : Fin 2 ⊕ Sigma) (move : Fin 3) : SetRel (Fin (s + 1)) (Fin (s + 1)) :=
    {qr | (e qr.1, e qr.2) ∈ A.augmentedMove symbol move}
  let d (symbol : Fin 2 ⊕ Sigma) := cellDiagram (s + 1)
    (moves symbol 1) (moves symbol 2) (moves symbol 0)
  let a := e.symm (some A.initial)
  let b := e.symm none
  refine ⟨wordDiagram (fun symbol => d (Sum.inr symbol)), d (Sum.inl 0), d (Sum.inl 1),
    a, b, wordDiagram_nil _, wordDiagram_append _, ?_⟩
  intro w
  let cells : List (Fin 2 ⊕ Sigma) := Sum.inl 0 :: w.map Sum.inr
  let ec : (Fin (s + 1) × Fin (cells.length + 2)) ≃
      (Option (Fin s) × Fin (w.length + 3)) :=
    Equiv.prodCongr e (finCongr (by simp [cells]))
  have hread (c : ChainNode (s + 1) cells.length) (p : Fin (w.length + 2))
      (hp : c.position = p.val) : chainSymbol cells (Sum.inl 1) c = tapeSymbol w p := by
    rw [chainSymbol_getElem]
    simpa only [cells, List.cons_append, hp] using marked_getElem w p
  have hstep (x y : Fin (s + 1) × Fin (cells.length + 2)) :
      (ec x, ec y) ∈ A.augmentedStep w ↔ (x, y) ∈ chainStep moves cells (Sum.inl 1) := by
    rw [A.augmentedStep_local_iff]
    constructor
    · rintro ⟨p, hp, move, hmove, hdisp⟩
      have hpx : p.val = x.2.val := (congrArg Fin.val hp).symm
      have hbound : p.val ≤ cells.length := by simp [cells]; omega
      obtain ⟨c, _, hc⟩ := ChainNode.coordinates_surjective x.1 p.val hbound
      refine ⟨c, hpx.symm.trans hc.symm, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (chainSymbol cells (Sum.inl 1) c) move
        rw [hread c p hc]
        exact hmove
      · change (y.2.val : ℤ) = (p.val : ℤ) + (move.val : ℤ) - 1 at hdisp
        rwa [hpx] at hdisp
    · rintro ⟨c, hpos, move, hmove, hdisp⟩
      have hc : c.position < w.length + 2 := by
        have hbound := c.position_le
        simp only [cells, List.length_cons, List.length_map] at hbound
        omega
      let p : Fin (w.length + 2) := ⟨c.position, hc⟩
      refine ⟨p, Fin.ext hpos, move, ?_, ?_⟩
      · change (e x.1, e y.1) ∈ A.augmentedMove (tapeSymbol w p) move
        rw [← hread c p rfl]
        exact hmove
      · change (y.2.val : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1
        rwa [hpos] at hdisp
  have hstart : ec (a, ⟨0, by omega⟩) =
      TwoNFA.augmentConfig (A.initial, ⟨0, by omega⟩) :=
    Prod.ext (e.apply_symm_apply _) (Fin.ext rfl)
  have hend : ec (b, ⟨cells.length + 1, by omega⟩) =
      (none, ⟨w.length + 2, by omega⟩) := by
    apply Prod.ext (e.apply_symm_apply _)
    apply Fin.ext
    change cells.length + 1 = w.length + 2
    simp [cells]
  have hpaths := relStar_equiv_iff ec (chainStep moves cells (Sum.inl 1))
    (A.augmentedStep w) hstep (a, ⟨0, by omega⟩) (b, ⟨cells.length + 1, by omega⟩)
  rw [hstart, hend, ← A.augmented_acceptance w] at hpaths
  rw [hpaths, chainStep_recognition, chainNetwork_summary]
  have hprod : wordDiagram d (cells ++ [Sum.inl 1]) =
      Diagram.comp (Diagram.comp (d (Sum.inl 0))
        (wordDiagram (fun symbol => d (Sum.inr symbol)) w)) (d (Sum.inl 1)) := by
    simp only [wordDiagram, cells, List.cons_append, List.map_cons, List.map_append,
      List.prod_cons, List.prod_append, List.map_map, List.map_nil, List.prod_nil, mul_one]
    exact (mul_assoc _ _ _).symm
  change (a, b) ∈ (wordDiagram d (cells ++ [Sum.inl 1])).forward ↔ _
  rw [hprod]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ExplicitFamily ----
namespace OAI

namespace TwoWayComplementation

/-- An explicit liveness witness and its complementation lower bound. -/
theorem explicit_complementation_family (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      A.language = sourceLanguage (Fin (n - 2)) ∧
      (∀ (Q : Type*) [Fintype Q],
        ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) Q,
        B.language = A.languageᶜ →
          (1 / 2 : ℝ) * 2 ^ ((n - 4) / 127) - 1 ≤ (Fintype.card Q : ℝ)) := by
  obtain ⟨A, hA⟩ := sourceLanguage_state_bound (Fin (n - 2))
  have hsize : Fintype.card (Fin (n - 2)) + 2 = n := by simp; omega
  let A' := A.reindex (finCongr hsize)
  have hAlang : A'.language = sourceLanguage (Fin (n - 2)) := by
    rw [TwoNFA.reindex_language, hA]
  refine ⟨A', hAlang, ?_⟩
  intro Q _ B hB
  let B' := B.reindex (Fintype.equivFin Q)
  obtain ⟨τ, l, r, a, b, hzero, hmul, hrecognition⟩ := B'.diagram_representation
  have hbound := diagram_recognition_lower_bound (n - 2) (Fintype.card Q + 1)
    (by omega) (by omega) τ hzero hmul l r a b (by
      intro w
      rw [← hrecognition w, TwoNFA.reindex_language, hB, hAlang]
      rfl)
  have hnat : 2 ^ ((n - 4) / 127) ≤ 2 * (Fintype.card Q + 1) := by
    simpa only [lossBound, Nat.sub_sub, Nat.reduceAdd] using hbound
  have hreal : (2 : ℝ) ^ ((n - 4) / 127) ≤ 2 * ((Fintype.card Q : ℝ) + 1) := by
    exact_mod_cast hnat
  linarith

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.explicit_complementation_family := @_root_.OAI.TwoWayComplementation.explicit_complementation_family
