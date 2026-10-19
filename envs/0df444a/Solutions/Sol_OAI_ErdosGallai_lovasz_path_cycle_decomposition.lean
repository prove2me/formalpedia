-- Prove2me | solution 1 for OAI.ErdosGallai.lovasz_path_cycle_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:10.661635+00:00
-- url     : https://prove2.me/submissions/3eaa7c14-eb65-474f-b5e5-7b055bf7dd83

import Mathlib
import Definitions.Def_OAIQWEGC000

section
-- module Solutions.OAIQW_ErdosGallai.Compat
namespace OAI.ErdosGallai
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.ErdosGallai
end

section
-- module Solutions.OAIQW_ErdosGallai.Lovasz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56 cycleUniverse57 cycleUniverse58 cycleUniverse59 cycleUniverse60 cycleUniverse61 cycleUniverse62 cycleUniverse63 cycleUniverse64 cycleUniverse65 cycleUniverse66 cycleUniverse67 cycleUniverse68 cycleUniverse69 cycleUniverse70 cycleUniverse71 cycleUniverse72 cycleUniverse73 cycleUniverse74 cycleUniverse75 cycleUniverse76 cycleUniverse77 cycleUniverse78 cycleUniverse79 cycleUniverse80 cycleUniverse81 cycleUniverse82 cycleUniverse83 cycleUniverse84 cycleUniverse85

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Lovasz
universe u
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma starActive_source {V : Type cycleUniverse2} {S : Set V} {R : V → V → Prop}
    {v : V} (hv : v ∈ S) : StarActive S R v :=
  ⟨v, hv, .refl⟩

lemma starActive_step {V : Type cycleUniverse3} {S : Set V} {R : V → V → Prop}
    {v w : V} (hv : StarActive S R v) (h : R v w) : StarActive S R w := by
  obtain ⟨a, ha, hr⟩ := hv
  exact ⟨a, ha, hr.tail h⟩

lemma starActive_iff {V : Type cycleUniverse4} {S : Set V} {R : V → V → Prop} {v : V} :
    StarActive S R v ↔ v ∈ S ∨ ∃ w, StarActive S R w ∧ R w v := by
  constructor
  · rintro ⟨a, ha, hr⟩
    rcases hr.cases_tail with rfl | ⟨w, hw, h⟩
    · exact Or.inl ha
    · exact Or.inr ⟨w, ⟨a, ha, hw⟩, h⟩
  · rintro (h | ⟨w, hw, h⟩)
    · exact starActive_source h
    · exact starActive_step hw h

lemma starActive_subset {V : Type cycleUniverse6} {S T : Set V} {R : V → V → Prop}
    (hS : S ⊆ T) (hR : ∀ a b, R a b → b ∈ T) :
    {v | StarActive S R v} ⊆ T := by
  rintro v ⟨a, ha, hr⟩
  rcases hr.cases_tail with rfl | ⟨w, _, h⟩
  · exact hS ha
  · exact hR w v h

lemma star_inj {V : Type cycleUniverse8} {x a b : V} : s(x,a) = s(x,b) ↔ a = b := by
  rw [Sym2.eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, h'⟩)
    · exact h
    · exact h'.trans h
  · intro h; exact Or.inl ⟨rfl, h⟩

lemma PathPiece.ends_ne {V : Type cycleUniverse10} {G : SimpleGraph V} (P : PathPiece G) :
    P.start ≠ P.finish := by
  intro h
  have hz := (P.isPath.nil_iff_eq.mpr h).length_eq_zero
  have := P.positive
  omega

namespace Arm
variable {V : Type cycleUniverse14} {G : SimpleGraph V} {x : V}

lemma join_edges (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    (A.join B hd).walk.edgeSet =
      A.walk.edgeSet ∪ B.walk.edgeSet ∪ {s(x,A.near), s(x,B.near)} := by
  simp only [join, Walk.edgeSet_append, Walk.edgeSet_reverse, Walk.edgeSet_cons]
  ext e
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

lemma near_ne (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support) :
    A.near ≠ B.near := by
  intro h
  exact List.disjoint_left.mp hd A.walk.start_mem_support (by simpa only [h] using B.walk.start_mem_support)

lemma far_ne_center (A : Arm G x) : A.far ≠ x := by
  intro h
  apply A.avoids
  simpa only [h] using A.walk.end_mem_support

lemma star_not_mem (A : Arm G x) (v : V) : s(x,v) ∉ A.walk.edgeSet := by
  intro he
  exact A.avoids (Walk.mem_support_iff_exists_mem_edges.mpr
    (Or.inr ⟨s(x,v), he, by simp⟩))

lemma orient_disjoint (A B : Arm G x) (p q : Prop)
    (ha : p → G.Adj x A.far) (hb : q → G.Adj x B.far)
    (hd : A.walk.support.Disjoint B.walk.support) :
    (A.orient p ha).walk.support.Disjoint (B.orient q hb).walk.support := by
  rw [List.disjoint_left]
  intro v hv hw
  exact List.disjoint_left.mp hd ((A.mem_orient_support p ha v).mp hv)
    ((B.mem_orient_support q hb v).mp hw)

end Arm

namespace Frame
variable {V : Type cycleUniverse16} {G : SimpleGraph V} {x : V}

lemma endpoint_ne_center (F : Frame G x) (p : F.Port) : F.endpoint p ≠ x := by
  cases F with
  | away P hx =>
    cases p
    · change P.start ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.start_mem_support
    · change P.finish ≠ x
      intro h; apply hx; simpa only [← h] using P.walk.end_mem_support
  | tip A => exact A.far_ne_center
  | through A B hd => cases p <;> exact Arm.far_ne_center _

lemma port_iff_endpoint (F : Frame G x) (v : V) :
    (∃ p : F.Port, F.endpoint p = v) ↔
      (F.path.start = v ∨ F.path.finish = v) ∧ v ≠ x := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨?_, (F.endpoint_ne_center p)⟩
    cases F with
    | away P hx => cases p <;> simp [endpoint, path]
    | tip A => exact Or.inr rfl
    | through A B hd => cases p <;> simp [endpoint, path, Arm.join]
  · rintro ⟨he, hx⟩
    cases F with
    | away P hp =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩
    | tip A =>
      rcases he with he | he
      · exact (hx he.symm).elim
      · exact ⟨(), he⟩
    | through A B hd =>
      rcases he with he | he
      · exact ⟨false, he⟩
      · exact ⟨true, he⟩

lemma exit_edge (F : Frame G x) (p : F.Port) (v : V) (h : F.exit p = some v) :
    s(x,v) ∈ F.path.walk.edgeSet := by
  cases F with
  | away P hx => cases h
  | tip A => cases h
  | through A B hd =>
    cases p
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)
    · cases h
      rw [path, Arm.join_edges]
      exact Or.inr (by simp)

lemma inserted_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop) :
    (Frame.away P hx).inserted active =
      (if active false then {s(x,P.start)} else ∅) ∪
      (if active true then {s(x,P.finish)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma inserted_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop) :
    (Frame.tip A).inserted active = if active () then {s(x,A.far)} else ∅ := by
  ext e
  by_cases h : active () <;> simp [inserted, endpoint, Port, h]

lemma inserted_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).inserted active =
      (if active false then {s(x,A.far)} else ∅) ∪
      (if active true then {s(x,B.far)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [inserted, endpoint, Port, Bool.exists_bool, h0, h1, or_comm]

lemma removed_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop) :
    (Frame.through A B hd).removed active =
      (if active false then {s(x,A.near)} else ∅) ∪
      (if active true then {s(x,B.near)} else ∅) := by
  ext e
  by_cases h0 : active false <;> by_cases h1 : active true <;>
    simp [removed, exit, Port, Bool.exists_bool, h0, h1, or_comm]

end Frame

lemma replace_two_attachments {E : Type cycleUniverse17} (B : Set E) (e f a b : E)
    (he : e ∉ B) (hf : f ∉ B) (hne : e ≠ f) (p q : Prop) [Decidable p] [Decidable q] :
    ((B ∪ {e,f}) \ ((if p then {e} else ∅) ∪ (if q then {f} else ∅))) ∪
      ((if p then {a} else ∅) ∪ (if q then {b} else ∅)) =
      B ∪ {if p then a else e, if q then b else f} := by
  classical
  ext z
  by_cases hp : p <;> by_cases hq : q <;>
    simp only [hp, hq, ↓reduceIte, Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false] <;> aesop

namespace Frame
variable {V : Type cycleUniverse18} {G : SimpleGraph V} {x : V}

lemma modify_through (A B : Arm G x) (hd : A.walk.support.Disjoint B.walk.support)
    (active : (Frame.through A B hd).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.through A B hd).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.through A B hd).path.walk.edgeSet \ (Frame.through A B hd).removed active) ∪
        (Frame.through A B hd).inserted active := by
  have ha : active false → G.Adj x A.far := hadj false
  have hb : active true → G.Adj x B.far := hadj true
  let A' := A.orient (active false) ha
  let B' := B.orient (active true) hb
  have hd' : A'.walk.support.Disjoint B'.walk.support :=
    A.orient_disjoint B _ _ _ _ hd
  refine ⟨Piece.ofPath (A'.join B' hd'), ?_⟩
  have he : s(x,A.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hf : s(x,B.near) ∉ A.walk.edgeSet ∪ B.walk.edgeSet := by
    rintro (he | he)
    · exact A.star_not_mem _ he
    · exact B.star_not_mem _ he
  have hne : s(x,A.near) ≠ s(x,B.near) := fun h => A.near_ne B hd (star_inj.mp h)
  change (A'.join B' hd').walk.edgeSet = _
  rw [inserted_through, removed_through]
  change (A'.join B' hd').walk.edgeSet = ((A.join B hd).walk.edgeSet \ _) ∪ _
  rw [Arm.join_edges, Arm.join_edges]
  dsimp only [A', B']
  simp only [Arm.orient_edges, Arm.orient_near]
  have hh := (replace_two_attachments _ _ _ s(x,A.far) s(x,B.far) he hf hne
    (active false) (active true)).symm
  by_cases h0 : active false <;> by_cases h1 : active true
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simpa [h0, h1] using hh
  · simp [h0, h1]

lemma modify_tip (A : Arm G x) (active : (Frame.tip A).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.tip A).endpoint p))
    (hnew : ∀ p, active p → s(x,(Frame.tip A).endpoint p) ∉
      (Frame.tip A).path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.tip A).path.walk.edgeSet \ (Frame.tip A).removed active) ∪
        (Frame.tip A).inserted active := by
  rw [removed_tip, inserted_tip, Set.sdiff_empty]
  by_cases ha : active ()
  · have haG : G.Adj x A.far := hadj () ha
    have he : s(A.far,x) ∉ A.tip.walk.edges := by
      intro he
      exact hnew () ha (Sym2.eq_swap ▸ he)
    let c : G.Walk A.far A.far := Walk.cons haG.symm A.tip.walk
    have hc : c.IsCycle := Path.cons_isCycle ⟨A.tip.walk,A.tip.isPath⟩ _ he
    refine ⟨Piece.ofCycle c hc, ?_⟩
    change c.edgeSet = _
    dsimp only [c, Arm.tip, path]
    simp only [Walk.edgeSet_cons, ha, ↓reduceIte]
    rw [Sym2.eq_swap]
    ext e
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  · refine ⟨Piece.ofPath A.tip, ?_⟩
    simp [Piece.ofPath, path, ha]

lemma modify_away (P : PathPiece G) (hx : x ∉ P.walk.support)
    (active : (Frame.away P hx).Port → Prop)
    (hadj : ∀ p, active p → G.Adj x ((Frame.away P hx).endpoint p)) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      ((Frame.away P hx).path.walk.edgeSet \ (Frame.away P hx).removed active) ∪
        (Frame.away P hx).inserted active := by
  rw [removed_away, inserted_away, Set.sdiff_empty]
  change ∃ Q : Piece G, Q.walk.edgeSet = P.walk.edgeSet ∪ _
  by_cases h0 : active false
  · have h0G : G.Adj x P.start := hadj false h0
    let q : G.Walk x P.finish := Walk.cons h0G P.walk
    have hq : q.IsPath := P.isPath.cons hx
    by_cases h1 : active true
    · have he : s(P.finish,x) ∉ q.edges := by
        intro he
        have hh := hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
        have hp := P.positive
        simp only [q, Walk.length_cons] at hh
        omega
      have h1G : G.Adj x P.finish := hadj true h1
      let c : G.Walk P.finish P.finish := Walk.cons h1G.symm q
      have hc : c.IsCycle := Path.cons_isCycle ⟨q,hq⟩ _ he
      refine ⟨Piece.ofCycle c hc, ?_⟩
      change c.edgeSet = _
      simp only [c, q, Walk.edgeSet_cons, h0, h1, ↓reduceIte]
      rw [Sym2.eq_swap]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · let Q : PathPiece G := ⟨x, P.finish, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, h0, h1, ↓reduceIte, Set.union_empty]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
  · by_cases h1 : active true
    · have h1G : G.Adj x P.finish := hadj true h1
      let q : G.Walk x P.start := Walk.cons h1G P.walk.reverse
      have hq : q.IsPath := P.isPath.reverse.cons (by simpa using hx)
      let Q : PathPiece G := ⟨x, P.start, q, hq, by simp [q]⟩
      refine ⟨Piece.ofPath Q, ?_⟩
      change q.edgeSet = _
      simp only [q, Walk.edgeSet_cons, Walk.edgeSet_reverse, h0, h1, ↓reduceIte,
        Set.empty_union]
      ext e
      simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
      tauto
    · refine ⟨Piece.ofPath P, ?_⟩
      simp [Piece.ofPath, h0, h1]

theorem modify (F : Frame G x) (active : F.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (F.endpoint p))
    (hnew : ∀ p, active p → F.exit p = none → s(x,F.endpoint p) ∉ F.path.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet = (F.path.walk.edgeSet \ F.removed active) ∪
      F.inserted active := by
  cases F with
  | away P hx => exact modify_away P hx active hadj
  | through A B hd => exact modify_through A B hd active hadj
  | tip A => exact modify_tip A active hadj (fun p hp => hnew p hp rfl)

end Frame

theorem rewire_partition {E : Type cycleUniverse19} {I : Type cycleUniverse20} (old remove add : I → Set E) (fresh : Set E)
    (hsub : ∀ i, remove i ⊆ old i)
    (hold : Pairwise fun i j => Disjoint (old i) (old j))
    (hadd : Pairwise fun i j => Disjoint (add i) (add j))
    (hfresh : Disjoint fresh (⋃ i, old i))
    (hbalance : (⋃ i, add i) = (⋃ i, remove i) ∪ fresh) :
    Pairwise (fun i j => Disjoint ((old i \ remove i) ∪ add i)
      ((old j \ remove j) ∪ add j)) ∧
    (⋃ i, ((old i \ remove i) ∪ add i)) = (⋃ i, old i) ∪ fresh := by
  have hcross : ∀ i j, Disjoint (old i \ remove i) (add j) := by
    intro i j
    apply Set.disjoint_left.mpr
    rintro e ⟨hei, hnot⟩ hej
    have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
      rw [← hbalance]
      exact Set.mem_iUnion.mpr ⟨j, hej⟩
    rcases hh with hh | hh
    · obtain ⟨l, hel⟩ := Set.mem_iUnion.mp hh
      by_cases hil : i = l
      · subst l; exact hnot hel
      · exact Set.disjoint_left.mp (hold hil) hei (hsub l hel)
    · exact Set.disjoint_left.mp hfresh hh (Set.mem_iUnion.mpr ⟨i, hei⟩)
  constructor
  · intro i j hij
    exact Disjoint.union_left
      (Disjoint.union_right ((hold hij).mono Set.sdiff_subset Set.sdiff_subset) (hcross i j))
      (Disjoint.union_right (hcross j i).symm (hadd hij))
  · ext e
    constructor
    · intro he
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      rcases hi with hi | hi
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi.1⟩)
      · have hh : e ∈ (⋃ l, remove l) ∪ fresh := by
          rw [← hbalance]
          exact Set.mem_iUnion.mpr ⟨i, hi⟩
        rcases hh with hh | hh
        · obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hh
          exact Or.inl (Set.mem_iUnion.mpr ⟨l, hsub l hl⟩)
        · exact Or.inr hh
    · rintro (he | he)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        by_cases hr : e ∈ remove i
        · have hh : e ∈ ⋃ l, add l := by
            rw [hbalance]
            exact Or.inl (Set.mem_iUnion.mpr ⟨i, hr⟩)
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hh
          exact Set.mem_iUnion.mpr ⟨j, Or.inr hj⟩
        · exact Set.mem_iUnion.mpr ⟨i, Or.inl ⟨hi, hr⟩⟩
      · have hh : e ∈ ⋃ l, add l := by rw [hbalance]; exact Or.inr he
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hh
        exact Set.mem_iUnion.mpr ⟨i, Or.inr hi⟩

namespace Centered
variable {V : Type cycleUniverse22} {G : SimpleGraph V} {x : V}

lemma exit_edge (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    s(x,v) ∈ K.piece.walk.edgeSet := by
  cases K with
  | path F => exact F.exit_edge p v h
  | cycle c hc => exact p.elim

lemma exit_adj (K : Centered G x) (p : K.Port) (v : V) (h : K.exit p = some v) :
    G.Adj x v := by
  exact G.mem_edgeSet.mp (K.piece.walk.edges_subset_edgeSet (K.exit_edge p v h))

lemma exit_none_all (K : Centered G x) (p : K.Port) (h : K.exit p = none) :
    ∀ q, K.exit q = none := by
  cases K with
  | cycle c hc => exact p.elim
  | path F =>
    cases F with
    | away P hx => exact fun _ => rfl
    | tip A => exact fun _ => rfl
    | through A B hd => cases p <;> cases h

lemma removed_subset (K : Centered G x) (active : K.Port → Prop) :
    K.removed active ⊆ K.piece.walk.edgeSet := by
  rintro e ⟨p, hp, v, hv, rfl⟩
  exact K.exit_edge p v hv

lemma modify (K : Centered G x) (active : K.Port → Prop)
    (hadj : ∀ p, active p → G.Adj x (K.endpoint p))
    (hnew : ∀ p, active p → K.exit p = none →
      s(x,K.endpoint p) ∉ K.piece.walk.edgeSet) :
    ∃ Q : Piece G, Q.walk.edgeSet =
      (K.piece.walk.edgeSet \ K.removed active) ∪ K.inserted active := by
  cases K with
  | path F => exact F.modify active hadj hnew
  | cycle c hc =>
    refine ⟨.ofCycle c hc, ?_⟩
    have hr : (Centered.cycle c hc).removed active = ∅ := by
      ext e; simp only [removed, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    have hi : (Centered.cycle c hc).inserted active = ∅ := by
      ext e; simp only [inserted, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      exact ⟨fun ⟨p, _⟩ => p.elim, False.elim⟩
    simp only [hr, hi, Set.sdiff_empty, Set.union_empty]
    rfl

end Centered

theorem restore_selected {V : Type cycleUniverse23} {I : Type cycleUniverse24} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (selected : Set (Σ i, (K i).Port))
    (hinj : Set.InjOn (fun z : Σ i, (K i).Port => (K z.1).endpoint z.2) selected)
    (hcov : ∀ v, G.Adj x v → ∃ z ∈ selected, (K z.1).endpoint z.2 = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let R : V → V → Prop := fun a b => ∃ z ∈ selected,
    (K z.1).endpoint z.2 = a ∧ (K z.1).exit z.2 = some b
  let active : (i : I) → (K i).Port → Prop := fun i p =>
    (⟨i,p⟩ : Σ j, (K j).Port) ∈ selected ∧ StarActive S R ((K i).endpoint p)
  have hactive_adj : ∀ v, StarActive S R v → G.Adj x v := by
    intro v hv
    exact starActive_subset (T := {v | G.Adj x v}) hS
      (by rintro a b ⟨z, _, _, hz⟩; exact (K z.1).exit_adj z.2 b hz) hv
  have hbalance : (⋃ i, (K i).inserted (active i)) =
      (⋃ i, (K i).removed (active i)) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
    ext e
    constructor
    · intro he
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp he
      rcases (starActive_iff.mp hp.2) with hs | ⟨w, hw, z, hz, hzw, hzv⟩
      · exact Or.inr ⟨_, hs, rfl⟩
      · exact Or.inl (Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzw.symm ▸ hw⟩,
          _, hzv, rfl⟩)
    · rintro (he | ⟨v, hv, rfl⟩)
      · obtain ⟨i, p, hp, v, hpv, rfl⟩ := Set.mem_iUnion.mp he
        have hv : StarActive S R v := starActive_step hp.2 ⟨⟨i,p⟩, hp.1, rfl, hpv⟩
        obtain ⟨z, hz, hzv⟩ := hcov v (hactive_adj v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ hv⟩, congrArg (s(x,·)) hzv.symm⟩
      · obtain ⟨z, hz, hzv⟩ := hcov v (hS v hv)
        exact Set.mem_iUnion.mpr ⟨z.1, z.2, ⟨hz, hzv.symm ▸ starActive_source hv⟩,
          congrArg (s(x,·)) hzv.symm⟩
  have hadd : Pairwise fun i j =>
      Disjoint ((K i).inserted (active i)) ((K j).inserted (active j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro e ⟨p, hp, he⟩ ⟨q, hq, hf⟩
    have h : (⟨i,p⟩ : Σ l, (K l).Port) = ⟨j,q⟩ :=
      hinj hp.1 hq.1 (star_inj.mp (he.symm.trans hf))
    exact hij (congrArg Sigma.fst h)
  have hnew : ∀ i p, active i p → (K i).exit p = none →
      s(x,(K i).endpoint p) ∉ (K i).piece.walk.edgeSet := by
    intro i p hp hn he
    have ha : s(x,(K i).endpoint p) ∈ ⋃ j, (K j).inserted (active j) :=
      Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩
    rw [hbalance] at ha
    rcases ha with ha | ha
    · obtain ⟨j, q, hq, v, hqv, hev⟩ := Set.mem_iUnion.mp ha
      have hej : s(x,(K i).endpoint p) ∈ (K j).piece.walk.edgeSet :=
        hev ▸ (K j).exit_edge q v hqv
      have hij : i = j := by
        by_contra h; exact Set.disjoint_left.mp (hold h) he hej
      subst j
      rw [(K i).exit_none_all p hn q] at hqv
      cases hqv
    · exact Set.disjoint_left.mp hfresh ha (Set.mem_iUnion.mpr ⟨i, he⟩)
  choose Q hQ using fun i => (K i).modify (active i)
    (fun p hp => hactive_adj _ hp.2) (hnew i)
  have hh := rewire_partition (fun i => (K i).piece.walk.edgeSet)
    (fun i => (K i).removed (active i)) (fun i => (K i).inserted (active i))
    {e | ∃ v ∈ S, e = s(x,v)} (fun i => (K i).removed_subset _) hold hadd hfresh hbalance
  refine ⟨Q, ?_, ?_⟩
  · simpa only [hQ] using hh.1
  · simpa only [hQ] using hh.2

theorem restore_star {V : Type cycleUniverse25} {I : Type cycleUniverse26} (G : SimpleGraph V) (x : V)
    (K : I → Centered G x) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hold : Pairwise fun i j => Disjoint (K i).piece.walk.edgeSet (K j).piece.walk.edgeSet)
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} (⋃ i, (K i).piece.walk.edgeSet))
    (hcov : ∀ v, G.Adj x v → ∃ i p, (K i).endpoint p = v) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) =
        (⋃ i, (K i).piece.walk.edgeSet) ∪ {e | ∃ v ∈ S, e = s(x,v)} := by
  let T := {v // G.Adj x v}
  have hh : ∀ v : T, ∃ z : Σ i, (K i).Port, (K z.1).endpoint z.2 = v.val := by
    intro v
    obtain ⟨i,p,h⟩ := hcov v.val v.property
    exact ⟨⟨i,p⟩,h⟩
  choose f hf using hh
  apply restore_selected G x K S hS hold hfresh (Set.range f)
  · rintro z ⟨v,rfl⟩ w ⟨u,rfl⟩ he
    have hvu : v = u := Subtype.ext ((hf v).symm.trans (he.trans (hf u)))
    exact congrArg f hvu
  · intro v hv
    exact ⟨f ⟨v,hv⟩, ⟨⟨v,hv⟩, rfl⟩, hf ⟨v,hv⟩⟩

lemma PathPiece.exists_frame {V : Type cycleUniverse28} {G : SimpleGraph V} (P : PathPiece G) (x : V) :
    ∃ F : Frame G x, F.path.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, (F.path.start = v ∨ F.path.finish = v) ↔ (P.start = v ∨ P.finish = v) := by
  classical
  by_cases hx : x ∈ P.walk.support
  · obtain ⟨q,r,hq,hr,hqr⟩ := P.isPath.mem_support_iff_exists_append.mp hx
    have hp : (q.append r).IsPath := hqr ▸ P.isPath
    by_cases hqn : q.Nil
    · have hx : P.start = x := hqn.eq
      have hrn : ¬r.Nil := by
        intro hn; exact P.ends_ne (hx.trans hn.eq)
      let A := Arm.fromWalk r hr hrn
      refine ⟨.tip A, ?_, ?_⟩
      · change A.tip.walk.edgeSet = P.walk.edgeSet
        rw [Arm.fromWalk_tip_edges]
        rw [hqr, Walk.edgeSet_append]
        simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hqn]
      · intro v
        change (x = v ∨ A.far = v) ↔ _
        simp only [A, Arm.fromWalk_far, hx]
    · by_cases hrn : r.Nil
      · have hx : x = P.finish := hrn.eq
        have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        refine ⟨.tip A, ?_, ?_⟩
        · change A.tip.walk.edgeSet = P.walk.edgeSet
          rw [Arm.fromWalk_tip_edges, Walk.edgeSet_reverse]
          rw [hqr, Walk.edgeSet_append]
          simp [Walk.edgeSet, Walk.edges_eq_nil.mpr hrn]
        · intro v
          change (x = v ∨ A.far = v) ↔ _
          simp only [A, Arm.fromWalk_far, hx, or_comm]
      · have hqnr : ¬q.reverse.Nil := by simpa using hqn
        let A := Arm.fromWalk q.reverse hq.reverse hqnr
        let B := Arm.fromWalk r hr hrn
        have hd : A.walk.support.Disjoint B.walk.support := by
          rw [Arm.fromWalk_support, Arm.fromWalk_support]
          have hd := hp.disjoint_support_of_append hrn
          rw [Walk.support_tail_of_not_nil r hrn] at hd
          apply List.disjoint_left.mpr
          intro v hv hw
          exact List.disjoint_left.mp hd
            (by simpa using (List.mem_of_mem_tail hv : v ∈ q.reverse.support)) hw
        refine ⟨.through A B hd, ?_, ?_⟩
        · change ((Walk.cons A.adj A.walk).reverse.append (Walk.cons B.adj B.walk)).edgeSet = _
          rw [Walk.edgeSet_append, Walk.edgeSet_reverse]
          change A.tip.walk.edgeSet ∪ B.tip.walk.edgeSet = _
          rw [Arm.fromWalk_tip_edges, Arm.fromWalk_tip_edges, Walk.edgeSet_reverse,
            hqr, Walk.edgeSet_append]
        · intro v
          change (A.far = v ∨ B.far = v) ↔ _
          simp only [A, B, Arm.fromWalk_far]
  · exact ⟨.away P hx, rfl, fun _ => Iff.rfl⟩

namespace Piece
variable {V : Type cycleUniverse29} {G H : SimpleGraph V}

lemma isTrail (P : Piece G) : P.walk.IsTrail := by
  rcases P.simple with hp | ⟨h,hc⟩
  · exact hp.1.isTrail
  · exact (P.walk.isTrail_copy rfl h).mp hc.isTrail

lemma exists_centered (P : Piece G) (x : V) :
    ∃ K : Centered G x, K.piece.walk.edgeSet = P.walk.edgeSet ∧
      ∀ v, P.start ≠ P.finish → (P.start = v ∨ P.finish = v) → v ≠ x →
        ∃ p, K.endpoint p = v := by
  rcases P with ⟨a,b,w,hs⟩
  rcases hs with hp | ⟨hb,hc⟩
  · let Q : PathPiece G := ⟨a,b,w,hp.1,hp.2⟩
    obtain ⟨F,he,hv⟩ := Q.exists_frame x
    refine ⟨.path F, he, ?_⟩
    intro v _ he hx
    exact (F.port_iff_endpoint v).mpr ⟨(hv v).mpr he, hx⟩
  · subst b
    refine ⟨.cycle w (by simpa using hc), rfl, ?_⟩
    exact fun _ hn => (hn rfl).elim
end Piece

theorem trail_partition_degree_sum {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse32} {I : Type cycleUniverse33} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

lemma endpoint_of_odd {V : Type cycleUniverse34} {I : Type cycleUniverse35} [Fintype V] [Fintype I]
    (H : SimpleGraph V) (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet)
    (v : V) (hv : Odd (H.degree v)) :
    ∃ i, (P i).start ≠ (P i).finish ∧ ((P i).start = v ∨ (P i).finish = v) := by
  classical
  have ho := (trail_partition_even_degree_iff H (fun i => (P i).walk)
    (fun i => (P i).isTrail) hd hc v).not.mp (Nat.not_even_iff_odd.mpr hv)
  have hp : 0 < (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card := by
    by_contra hn
    have hz : (Finset.univ.filter
      (fun i => (P i).start ≠ (P i).finish ∧ (v = (P i).start ∨ v = (P i).finish))).card = 0 := by omega
    exact ho (hz ▸ ⟨0, rfl⟩)
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
  exact ⟨i, (Finset.mem_filter.mp hi).2.1, by
    simpa only [eq_comm] using (Finset.mem_filter.mp hi).2.2⟩

theorem restore_partition {V : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G) (x : V) (S : Set V)
    (hS : ∀ v ∈ S, G.Adj x v)
    (hedges : G.edgeSet = H.edgeSet ∪ {e | ∃ v ∈ S, e = s(x,v)})
    (hfresh : Disjoint {e | ∃ v ∈ S, e = s(x,v)} H.edgeSet)
    (hodd : ∀ v, G.Adj x v → Odd (H.degree v))
    (P : I → Piece H)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = H.edgeSet) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  choose K hk hv using fun i => ((P i).mapLe hHG).exists_centered x
  have he : ∀ i, (K i).piece.walk.edgeSet = (P i).walk.edgeSet := by
    intro i; exact (hk i).trans ((P i).mapLe_edges hHG)
  have hKC : (⋃ i, (K i).piece.walk.edgeSet) = H.edgeSet := by simpa only [he] using hc
  obtain ⟨Q,hQ,hQC⟩ := restore_star G x K S hS
    (by simpa only [he] using hd) (by rwa [hKC]) (by
      intro v hxv
      obtain ⟨i, hi, hiv⟩ := endpoint_of_odd H P hd hc v (hodd v hxv)
      obtain ⟨p,hp⟩ := hv i v (by simpa using hi) (by simpa using hiv) hxv.ne.symm
      exact ⟨i,p,hp⟩)
  exact ⟨Q,hQ,by simpa only [hKC, ← hedges] using hQC⟩

lemma activeOrder_mono {V : Type cycleUniverse39} [Fintype V] {G H : SimpleGraph V} (h : H ≤ G) :
    activeOrder H ≤ activeOrder G := by
  apply Finset.card_le_card
  intro v hv
  exact Set.mem_toFinset.mpr (SimpleGraph.support_mono h (Set.mem_toFinset.mp hv))

lemma evenStar_subset {V : Type cycleUniverse44} [Fintype V] (G : SimpleGraph V) (x : V) :
    evenStarEdges G x ⊆ G.edgeSet := by
  rintro e ⟨y,hy,rfl⟩; exact hy.1

lemma deleteEvenStar_neighbor_even {V : Type cycleUniverse45} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = (G.neighborFinset v).erase x := by
  classical
  ext w
  rw [Finset.mem_erase, (deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  constructor
  · rintro ⟨hvw, hn⟩
    refine ⟨?_,hvw⟩
    intro hw; subst w
    exact hn ⟨v,⟨hxv,he⟩, Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨hw,hvw⟩
    refine ⟨hvw, ?_⟩
    rintro ⟨y,_,h⟩
    rcases h with ⟨h,_⟩ | ⟨_,h⟩
    · exact hxv.ne h.symm
    · exact hw h

lemma deleteEvenStar_neighbor_odd {V : Type cycleUniverse46} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) (he : ¬Even (G.degree v)) :
    (deleteEvenStar G x).neighborFinset v = G.neighborFinset v := by
  classical
  ext w
  rw [(deleteEvenStar G x).mem_neighborFinset, G.mem_neighborFinset]
  rw [deleteEvenStar, SimpleGraph.deleteEdges_adj]
  simp only [evenStarEdges, Set.mem_ofPred_eq, evenStarVertices, Sym2.eq_iff]
  refine ⟨fun h => h.1, fun hw => ⟨hw, ?_⟩⟩
  rintro ⟨y,hy,h⟩
  rcases h with ⟨h,_⟩ | ⟨h,_⟩
  · exact hxv.ne h.symm
  · subst y; exact he hy.2

lemma deleteEvenStar_neighbor_degree {V : Type cycleUniverse47} [Fintype V] (G : SimpleGraph V)
    (x v : V) (hxv : G.Adj x v) : Odd ((deleteEvenStar G x).degree v) := by
  classical
  by_cases he : Even (G.degree v)
  · have hcard := Finset.card_erase_add_one (s := G.neighborFinset v)
      (a := x) (by simpa using hxv.symm)
    rw [← deleteEvenStar_neighbor_even G x v hxv he,
      G.card_neighborFinset_eq_degree, (deleteEvenStar G x).card_neighborFinset_eq_degree] at hcard
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1, by omega⟩
  · rw [← (deleteEvenStar G x).card_neighborFinset_eq_degree v,
      deleteEvenStar_neighbor_odd G x v hxv he, G.card_neighborFinset_eq_degree]
    exact Nat.not_even_iff_odd.mp he

lemma deleteEvenStar_edges {V : Type cycleUniverse48} [Fintype V] (G : SimpleGraph V) (x : V) :
    G.edgeSet = (deleteEvenStar G x).edgeSet ∪ evenStarEdges G x := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges,
    Set.sdiff_union_of_subset (evenStar_subset G x)]

lemma deleteEvenStar_fresh {V : Type cycleUniverse49} [Fintype V] (G : SimpleGraph V) (x : V) :
    Disjoint (evenStarEdges G x) (deleteEvenStar G x).edgeSet := by
  rw [deleteEvenStar, SimpleGraph.edgeSet_deleteEdges]
  exact Set.disjoint_sdiff_right

lemma deleteEvenStar_lt {V : Type cycleUniverse50} [Fintype V] (G : SimpleGraph V) (x y : V)
    (hxy : G.Adj x y) (he : Even (G.degree y)) :
    (deleteEvenStar G x).edgeFinset.card < G.edgeFinset.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro e he
    exact G.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono
      (show deleteEvenStar G x ≤ G from G.deleteEdges_le _)
      ((deleteEvenStar G x).mem_edgeFinset.mp he))
  · intro h
    have hh : s(x,y) ∈ (deleteEvenStar G x).edgeFinset := h.symm ▸ G.mem_edgeFinset.mpr hxy
    have hf : s(x,y) ∈ evenStarEdges G x := ⟨y,⟨hxy,he⟩,rfl⟩
    exact Set.disjoint_left.mp (deleteEvenStar_fresh G x) hf (SimpleGraph.mem_edgeFinset.mp hh)

theorem even_vertex_step {V : Type cycleUniverse51} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph V, H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (hpos : ∃ y, 0 < G.degree y ∧ Even (G.degree y)) : HasPartition G := by
  classical
  obtain ⟨y,hy,he⟩ := hpos
  obtain ⟨x,hxy⟩ := (G.degree_pos_iff_exists_adj y).mp hy
  let H := deleteEvenStar G x
  obtain ⟨k,P,hd,hc,hk⟩ := hIH H (deleteEvenStar_lt G x y hxy.symm he)
  obtain ⟨Q,hQ,hQC⟩ := restore_partition G H (G.deleteEdges_le _) x
    (evenStarVertices G x) (fun _ h => h.1) (deleteEvenStar_edges G x)
    (deleteEvenStar_fresh G x) (deleteEvenStar_neighbor_degree G x) P hd hc
  exact ⟨k,Q,hQ,hQC,hk.trans (activeOrder_mono (G.deleteEdges_le _))⟩

lemma single_edge_piece {V : Type cycleUniverse52} (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : Piece G, P.walk.edgeSet = {e} := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    let P : PathPiece G := ⟨a,b,Walk.cons hab Walk.nil,
      (Walk.IsPath.nil).cons (by simpa using hab.ne), by simp⟩
    exact ⟨.ofPath P, by simp [Piece.ofPath, P]⟩

lemma partition_single_edges {V : Type cycleUniverse53} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Fin G.edgeFinset.card → Piece G,
      (Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet) ∧
      (⋃ i, (P i).walk.edgeSet) = G.edgeSet := by
  classical
  choose P hP using fun e : G.edgeSet => single_edge_piece G e.val e.property
  let e : G.edgeSet ≃ Fin G.edgeFinset.card := (Fintype.equivFin G.edgeSet).trans
    (finCongr (G.card_edgeSet))
  refine ⟨fun i => P (e.symm i), ?_, ?_⟩
  · intro i j hij
    rw [hP, hP]
    exact Set.disjoint_singleton.mpr (fun h => hij (e.symm.injective (Subtype.ext h)))
  · ext z
    simp only [Set.mem_iUnion,hP,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩; exact (e.symm i).property
    · intro hz
      exact ⟨e ⟨z,hz⟩, by simp⟩

lemma matching_partition {V : Type cycleUniverse54} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 1) : HasPartition G := by
  classical
  obtain ⟨P,hd,hc⟩ := partition_single_edges G
  refine ⟨_,P,hd,hc,?_⟩
  rw [← G.sum_degrees_support_eq_twice_card_edges]
  simpa [activeOrder] using Finset.sum_le_sum (s := G.support.toFinset)
    (f := fun v => G.degree v) (g := fun _ => 1) (fun v _ => hdeg v)

@[simp] lemma half_none_some {V : Type cycleUniverse62} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj none (some a) ↔ a = y := by
  rw [halfSubdivision, SimpleGraph.deleteEdges_adj]
  simp only [subdivision_none_some, Set.mem_singleton_iff, star_inj, Option.some.injEq]
  aesop

@[simp] lemma half_some_none {V : Type cycleUniverse63} (G : SimpleGraph V) (x y a : V) (hxy : x ≠ y) :
    (halfSubdivision G x y).Adj (some a) none ↔ a = y := by
  rw [(halfSubdivision G x y).adj_comm, half_none_some G x y a hxy]

lemma option_degree_some {V : Type cycleUniverse64} [Fintype V] (K : SimpleGraph (Option V)) (v : V) :
    K.degree (some v) = (Finset.univ.filter (fun u : V => K.Adj (some v) (some u))).card +
      if K.Adj (some v) none then 1 else 0 := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  omega

lemma option_degree_none {V : Type cycleUniverse65} [Fintype V] (K : SimpleGraph (Option V)) :
    K.degree none = (Finset.univ.filter (fun u : V => K.Adj none (some u))).card := by
  classical
  rw [← K.card_neighborFinset_eq_degree, K.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

lemma subdivision_old_neighbors {V : Type cycleUniverse66} [Fintype V] (G : SimpleGraph V)
    (x y v : V) :
    (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) =
      if v = x then (G.neighborFinset v).erase y else
      if v = y then (G.neighborFinset v).erase x else G.neighborFinset v := by
  classical
  ext u
  by_cases hx : v = x
  · subst v
    simp [eq_comm, and_comm]
    aesop
  · by_cases hy : v = y
    · subst v
      simp [hx,  eq_comm, and_comm]
      tauto
    · simp [hx, hy]

lemma subdivision_degree {V : Type cycleUniverse67} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (subdivision G x y).degree (some v) = G.degree v := by
  classical
  rw [option_degree_some, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy]

lemma subdivision_degree_none {V : Type cycleUniverse68} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (subdivision G x y).degree none = 2 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (subdivision G x y).Adj none (some u)) =
      {x,y} := by ext u; simp
  rw [he]
  simp [hxy.ne]

lemma half_degree {V : Type cycleUniverse69} [Fintype V] (G : SimpleGraph V)
    (x y v : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).degree (some v) + (if v = x then 1 else 0) = G.degree v := by
  classical
  rw [option_degree_some]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj (some v) (some u)) =
      (Finset.univ.filter fun u : V => (subdivision G x y).Adj (some v) (some u)) := by
    ext u; simp
  rw [he, subdivision_old_neighbors]
  by_cases hx : v = x
  · subst v
    simpa [hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset x) (a := y)
      (by simpa using hxy)
  · by_cases hy : v = y
    · subst v
      simpa [hx, hxy.ne] using Finset.card_erase_add_one (s := G.neighborFinset y) (a := x)
        (by simpa using hxy.symm)
    · simp [hx,hy,half_some_none G x y v hxy.ne]

lemma half_degree_none {V : Type cycleUniverse70} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) : (halfSubdivision G x y).degree none = 1 := by
  classical
  rw [option_degree_none]
  have he : (Finset.univ.filter fun u : V => (halfSubdivision G x y).Adj none (some u)) =
      {y} := by ext u; simp [half_none_some G x y u hxy.ne]
  rw [he]
  simp

lemma subdivision_edge_count {V : Type cycleUniverse71} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (subdivision G x y).edgeFinset.card = G.edgeFinset.card + 1 := by
  classical
  have hd := (subdivision G x y).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option, subdivision_degree_none G x y hxy] at hd
  simp_rw [subdivision_degree G x y _ hxy] at hd
  rw [G.sum_degrees_eq_twice_card_edges] at hd
  omega

lemma half_edge_count {V : Type cycleUniverse72} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    (halfSubdivision G x y).edgeFinset.card = G.edgeFinset.card := by
  classical
  have he : (halfSubdivision G x y).edgeFinset =
      (subdivision G x y).edgeFinset.erase s(none,some x) := by
    ext e
    rw [(halfSubdivision G x y).mem_edgeFinset, Finset.mem_erase,
      (subdivision G x y).mem_edgeFinset]
    simp [halfSubdivision, SimpleGraph.edgeSet_deleteEdges, and_comm]
  rw [he, Finset.card_erase_of_mem, subdivision_edge_count G x y hxy]
  · omega
  · exact (subdivision G x y).mem_edgeFinset.mpr (Or.inl rfl)

lemma subdivision_activeOrder {V : Type cycleUniverse73} [Fintype V] (G : SimpleGraph V)
    (x y : V) (hxy : G.Adj x y) :
    activeOrder (subdivision G x y) = activeOrder G + 1 := by
  classical
  have he : (subdivision G x y).support.toFinset =
      insert none (G.support.toFinset.image Option.some) := by
    ext v
    cases v with
    | none => simp [← SimpleGraph.degree_pos_iff_mem_support, subdivision_degree_none G x y hxy]
    | some v =>
      simp only [Set.mem_toFinset, Finset.mem_insert, Option.some_ne_none, Finset.mem_image,
        Option.some.injEq, false_or, exists_eq_right]
      rw [← (subdivision G x y).degree_pos_iff_mem_support,
        subdivision_degree G x y v hxy, G.degree_pos_iff_mem_support]
  dsimp [activeOrder]
  rw [he, Finset.card_insert_of_notMem, Finset.card_image_of_injective]
  · exact Option.some_injective V
  · simp

lemma suppress_path {V : Type cycleUniverse74} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    {a b : V} (p : (subdivision G x y).Walk (some a) (some b)) (hp : p.IsPath) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.support = p.support.filterMap id ∧
      ∀ e : Sym2 V, e ∈ q.edgeSet ↔
        e.map Option.some ∈ p.edgeSet ∨ (e = s(x,y) ∧ s(none,some x) ∈ p.edgeSet) := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    cases p with
    | nil =>
      refine ⟨.nil, by simp, by simp, ?_⟩
      intro e
      simp
    | @cons _ v _ h p =>
      have ht : p.IsPath := hp.of_cons
      have ha : some a ∉ p.support := (Walk.cons_isPath_iff _ _ |>.mp hp).2
      cases v with
      | some c =>
        obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht rfl
        have hac : G.Adj a c := (subdivision_some G x y a c).mp h |>.1
        refine ⟨.cons hac q, hq.cons ?_, ?_, ?_⟩
        · intro ha'
          apply ha
          rw [hqs] at ha'
          simpa using ha'
        · simp [hqs]
        · intro e
          have hinj : Function.Injective (Sym2.map (Option.some : V → Option V)) :=
            Sym2.map.injective (Option.some_injective V)
          have he : e.map Option.some = s(some a,some c) ↔ e = s(a,c) :=
            by simpa only [Sym2.map_mk] using (hinj.eq_iff (a := e) (b := s(a,c)))
          have hnedge : s(none,some x) ≠ s(some a,some c) := by simp []
          simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he, hnedge, false_or, hqe]
          tauto
      | none =>
        cases p with
        | @cons _ v _ h' p =>
          cases v with
          | none => exact (h'.ne rfl).elim
          | some c =>
            have hac : a ≠ c := by
              intro he
              apply ha
              simp [he]
            have hae : a = x ∨ a = y := (subdivision_some_none G x y a).mp h
            have hce : c = x ∨ c = y := (subdivision_none_some G x y c).mp h'
            have hexy : s(a,c) = s(x,y) := by
              rcases hae with rfl | rfl <;> rcases hce with rfl | rfl
              · exact (hac rfl).elim
              · rfl
              · exact Sym2.eq_swap
              · exact (hac rfl).elim
            have hacG : G.Adj a c := G.mem_edgeSet.mp (hexy.symm ▸ hxy)
            obtain ⟨q,hq,hqs,hqe⟩ := ih p.length (by simp only [Walk.length_cons] at hn; omega) p ht.of_cons rfl
            refine ⟨.cons hacG q, hq.cons ?_, ?_, ?_⟩
            · intro ha'
              apply ha
              have hh : some a ∈ p.support := by rw [hqs] at ha'; simpa using ha'
              simp [hh]
            · simp [hqs]
            · intro e
              have he1 : e.map Option.some ≠ s(some a,none) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have he2 : e.map Option.some ≠ s(none,some c) := by
                induction e using Sym2.inductionOn with | _ u v => simp []
              have hn : s(none,some x) = s(some a,none) ∨
                  s(none,some x) = s(none,some c) := by
                rcases hae with rfl | hay
                · exact Or.inl Sym2.eq_swap
                · rcases hce with rfl | hcy
                  · exact Or.inr rfl
                  · exact (hac (hay.trans hcy.symm)).elim
              simp only [Walk.edgeSet_cons, Set.mem_insert_iff, he1, he2, false_or,
                hexy, hqe]
              tauto

lemma tight_partition_endpoints {V : Type cycleUniverse75} {I : Type cycleUniverse76} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (P : I → Piece G) (S : Finset V)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v)) (hk : 2 * Fintype.card I ≤ S.card) :
    ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ∈ S ∧ (P i).finish ∈ S := by
  classical
  let endpoint : I × Bool → V := fun z => if z.2 then (P z.1).start else (P z.1).finish
  have he : ∀ v : S, ∃ z : I × Bool, endpoint z = v := by
    intro v
    obtain ⟨i,_, h | h⟩ := endpoint_of_odd G P hd hc v (ho v v.property)
    · exact ⟨(i,true),h⟩
    · exact ⟨(i,false),h⟩
  choose pick hpick using he
  have hinj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    exact (hpick v).symm.trans ((congrArg endpoint hvw).trans (hpick w))
  have hsurj : Function.Surjective pick := by
    by_contra hn
    have hh := Fintype.card_lt_of_injective_not_surjective pick hinj hn
    simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hh
    omega
  have hendinj : Function.Injective endpoint := by
    intro z t heq
    obtain ⟨v,rfl⟩ := hsurj z
    obtain ⟨w,rfl⟩ := hsurj t
    have hvw : v = w := Subtype.ext (by simpa only [hpick] using heq)
    exact congrArg pick hvw
  have hmem : ∀ z, endpoint z ∈ S := by
    intro z
    obtain ⟨v,rfl⟩ := hsurj z
    rw [hpick]
    exact v.property
  intro i
  refine ⟨?_, hmem (i,true), hmem (i,false)⟩
  intro heq
  have hh := hendinj (show endpoint (i,true) = endpoint (i,false) from heq)
  have := congrArg Prod.snd hh
  contradiction

lemma representative_mem {V : Type cycleUniverse78} (G : SimpleGraph V) (x y : V) (_hxy : G.Adj x y)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    subdivisionRepresentative x y e ∈ (subdivision G x y).edgeSet := by
  classical
  by_cases h : e = s(x,y)
  · simp [subdivisionRepresentative, h]
  · rw [subdivisionRepresentative, ite_eq_right h]
    induction e using Sym2.ind with
    | _ a b => exact ⟨he,h⟩

lemma suppress_piece {V : Type cycleUniverse79} (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : Piece (subdivision G x y)) (hne : P.start ≠ P.finish)
    (ha : P.start ≠ none) (hb : P.finish ≠ none) :
    ∃ Q : Piece G, ∀ e, e ∈ Q.walk.edgeSet ↔ subdivisionRepresentative x y e ∈ P.walk.edgeSet := by
  classical
  rcases P with ⟨a,b,p,hp⟩
  cases a with
  | none => exact (ha rfl).elim
  | some a =>
    cases b with
    | none => exact (hb rfl).elim
    | some b =>
      have hab : a ≠ b := fun h => hne (congrArg some h)
      have hpath : p.IsPath := by
        rcases hp with h | ⟨h,_⟩
        · exact h.1
        · exact (hne h.symm).elim
      obtain ⟨q,hq,_,hqe⟩ := suppress_path G x y hxy p hpath
      have hpos : 0 < q.length := by
        by_contra hn
        exact hab (Walk.eq_of_length_eq_zero (by omega : q.length = 0))
      refine ⟨.ofPath ⟨a,b,q,hq,hpos⟩, ?_⟩
      intro e
      change e ∈ q.edgeSet ↔ _
      rw [hqe]
      by_cases he : e = s(x,y)
      · subst e
        have hn : (s(x,y) : Sym2 V).map some ∉ p.edgeSet := by
          intro h
          have hh := p.edges_subset_edgeSet h
          exact hh.2 rfl
        simp only [subdivisionRepresentative, ite_true, hn, false_or, true_and]
      · simp [subdivisionRepresentative, he]

lemma suppress_partition {V : Type cycleUniverse80} {I : Type cycleUniverse81} [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (P : I → Piece (subdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (subdivision G x y).edgeSet)
    (hp : ∀ i, (P i).start ≠ (P i).finish ∧ (P i).start ≠ none ∧ (P i).finish ≠ none) :
    ∃ Q : I → Piece G,
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = G.edgeSet := by
  classical
  choose Q hQ using fun i => suppress_piece G x y hxy (P i) (hp i).1 (hp i).2.1 (hp i).2.2
  refine ⟨Q, ?_, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr fun e hei hej =>
      Set.disjoint_left.mp (hd hij) ((hQ i e).mp hei) ((hQ j e).mp hej)
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => (Q i).walk.edges_subset_edgeSet
    · intro e he
      have hrep := representative_mem G x y hxy e he
      rw [← hc] at hrep
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hrep
      exact Set.mem_iUnion.mpr ⟨i,(hQ i e).mpr hi⟩

lemma even_activeOrder {V : Type cycleUniverse82} [Fintype V] (G : SimpleGraph V)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) : Even (activeOrder G) := by
  classical
  have he : G.support.toFinset = Finset.univ.filter (fun v => Odd (G.degree v)) := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      ← G.degree_pos_iff_mem_support]
    refine ⟨ho v, ?_⟩
    rintro ⟨k,hk⟩
    omega
  simpa only [activeOrder, he] using G.even_card_odd_degree_vertices

lemma half_restore {V : Type cycleUniverse83} {I : Type cycleUniverse84} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v))
    (P : I → Piece (halfSubdivision G x y))
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = (halfSubdivision G x y).edgeSet) :
    ∃ Q : I → Piece (subdivision G x y),
      (Pairwise fun i j => Disjoint (Q i).walk.edgeSet (Q j).walk.edgeSet) ∧
      (⋃ i, (Q i).walk.edgeSet) = (subdivision G x y).edgeSet := by
  classical
  have he : {e : Sym2 (Option V) | ∃ v ∈ ({none} : Set (Option V)), e = s(some x,v)} =
      {s(none,some x)} := by
    ext e
    simp [Sym2.eq_swap]
  apply restore_partition (subdivision G x y) (halfSubdivision G x y)
    ((subdivision G x y).deleteEdges_le _) (some x) {none}
    (by intro v hv; rcases hv with rfl; exact Or.inl rfl) ?_ ?_ ?_ P hd hc
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    symm
    apply Set.sdiff_union_of_subset
    intro e he
    rcases he with rfl
    exact Or.inl rfl
  · rw [he, halfSubdivision, SimpleGraph.edgeSet_deleteEdges]
    exact Set.disjoint_sdiff_right
  · intro v hv
    cases v with
    | none => rw [half_degree_none G x y hxy]; exact ⟨0,rfl⟩
    | some v =>
      have hxv : G.Adj x v := hv.1
      have hh := half_degree G x y v hxy
      rw [ite_eq_right hxv.ne.symm, add_zero] at hh
      rw [hh]
      exact ho v ((G.degree_pos_iff_exists_adj v).mpr ⟨x,hxv.symm⟩)

theorem odd_vertex_step {V : Type cycleUniverse85} [Fintype V] (G : SimpleGraph V)
    (hIH : ∀ H : SimpleGraph (Option V), H.edgeFinset.card < G.edgeFinset.card → HasPartition H)
    (ho : ∀ v, 0 < G.degree v → Odd (G.degree v)) (x : V) (hx : 3 ≤ G.degree x) :
    HasPartition G := by
  classical
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp (by omega)
  have hp : ∃ v, 0 < (halfSubdivision G x y).degree v ∧
      Even ((halfSubdivision G x y).degree v) := by
    refine ⟨some x, ?_, ?_⟩
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      omega
    · have hd := half_degree G x y x hxy
      simp only [ite_true] at hd
      obtain ⟨k,hk⟩ := ho x (by omega)
      exact ⟨k,by omega⟩
  obtain ⟨k,P,hd,hc,hk⟩ := even_vertex_step (halfSubdivision G x y)
    (fun H hh => hIH H (by rwa [half_edge_count G x y hxy] at hh)) hp
  have hbound : 2 * k ≤ activeOrder G + 1 := by
    have hm := activeOrder_mono ((subdivision G x y).deleteEdges_le {s(none,some x)})
    rw [subdivision_activeOrder G x y hxy] at hm
    exact hk.trans hm
  have hk' : 2 * k ≤ activeOrder G := by
    obtain ⟨a,ha⟩ := even_activeOrder G ho
    omega
  obtain ⟨Q,hQ,hQC⟩ := half_restore G x y hxy ho P hd hc
  let S := G.support.toFinset.image Option.some
  have hScard : S.card = activeOrder G := by
    exact Finset.card_image_of_injective _ (Option.some_injective V)
  have hSodd : ∀ v ∈ S, Odd ((subdivision G x y).degree v) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [subdivision_degree G x y w hxy]
    exact ho w ((G.degree_pos_iff_mem_support w).mpr (Set.mem_toFinset.mp hw))
  have hends := tight_partition_endpoints (subdivision G x y) Q S hQ hQC hSodd
    (by simpa only [Fintype.card_fin, hScard] using hk')
  have hnon : ∀ i, (Q i).start ≠ (Q i).finish ∧
      (Q i).start ≠ none ∧ (Q i).finish ≠ none := by
    intro i
    refine ⟨(hends i).1, ?_, ?_⟩
    · intro h
      have hh := (hends i).2.1
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
    · intro h
      have hh := (hends i).2.2
      simp only [h, S, Finset.mem_image, Option.some_ne_none, and_false, exists_false] at hh
  obtain ⟨R,hR,hRC⟩ := suppress_partition G x y hxy Q hQ hQC hnon
  exact ⟨k,R,hR,hRC,hk'⟩

theorem path_cycle_partition {V : Type u} [Fintype V] (G : SimpleGraph V) : HasPartition G := by
  classical
  suffices ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
      H.edgeFinset.card = n → HasPartition H by
    exact this G.edgeFinset.card V G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ H hcount
    by_cases he : ∃ v, 0 < H.degree v ∧ Even (H.degree v)
    · exact even_vertex_step H (fun K hk => ih K.edgeFinset.card (by omega) W K rfl) he
    · have ho : ∀ v, 0 < H.degree v → Odd (H.degree v) := by
        intro v hv
        exact Nat.not_even_iff_odd.mp (fun hev => he ⟨v,hv,hev⟩)
      by_cases hm : ∀ v, H.degree v ≤ 1
      · exact matching_partition H hm
      · push Not at hm
        obtain ⟨x,hx⟩ := hm
        have hx3 : 3 ≤ H.degree x := by
          obtain ⟨k,hk⟩ := ho x (by omega)
          omega
        exact odd_vertex_step H
          (fun K hk => ih K.edgeFinset.card (by omega) (Option W) K rfl) ho x hx3

end
end ErdosGallai.Lovasz

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EndpointPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_decomposition_oai {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V)),
      (∀ i, (∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 0 < p.length ∧ parts i = p.edgeSet) ∨
        (∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ parts i = p.edgeSet)) ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
      (⋃ i, parts i) = G.edgeSet ∧ 2 * k ≤ Fintype.card V := by
  classical
  obtain ⟨k,P,hd,hc,hk⟩ := Lovasz.path_cycle_partition G
  refine ⟨k,fun i => (P i).walk.edgeSet,?_,hd,hc,?_⟩
  · intro i
    rcases (P i).simple with hp | ⟨h,hcy⟩
    · exact Or.inl ⟨(P i).start,(P i).finish,(P i).walk,hp.1,hp.2,rfl⟩
    · exact Or.inr ⟨(P i).start,(P i).walk.copy rfl h,hcy,by simp⟩
  · exact hk.trans (Finset.card_le_univ _)

end
end ErdosGallai

end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ErdosGallai.lovasz_path_cycle_decomposition_oai.{u_1} := @OAI.ErdosGallai.lovasz_path_cycle_decomposition_oai.{u_1}
