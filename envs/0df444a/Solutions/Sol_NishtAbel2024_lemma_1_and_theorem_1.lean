-- Prove2me | solution 1 for NishtAbel2024.lemma_1_and_theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:45:13.414357+00:00
-- url     : https://prove2.me/submissions/199820c9-5589-48ae-9c02-b37a00c2e390

import Mathlib
import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics
import Theorems.Thm_OAI_SeparableQuotient_InfiniteRamsey_homogeneous_subset

set_option linter.unnecessarySeqFocus false

-- GraphCompat

namespace NishtAbel2024

private theorem fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind

private theorem edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx

private theorem fold_choose_optional {α : Type} (f : α → Option EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (f x)) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = some r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (f x)) h
    cases a <;> cases hfx : f x <;> cases r <;> simp_all [EdgeRel.combine] <;> grind

private theorem comp_edge_witness (G₁ G₂ : InvGraph) (i j : Nat)
    (hi : i < G₁.leftArity) (hj : j < G₂.rightArity) (r : EdgeRel)
    (h : (G₁.comp G₂).edgeAt i j = some r) :
    ∃ k < G₁.rightArity, ∃ r₁ r₂,
      G₁.edgeAt i k = some r₁ ∧ G₂.edgeAt k j = some r₂ ∧
      EdgeRel.seq r₁ r₂ = r := by
  have he := edgeAt_mem (G₁.comp G₂) i j r h
  simp only [InvGraph.comp, InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range] at he
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
  rcases he with ⟨i', _, j', _, r', hf, rfl, rfl, rfl⟩
  have step (acc : Option EdgeRel) (k : Nat) :
      (match G₁.edgeAt i' k, G₂.edgeAt k j' with
       | some a, some b => EdgeRel.combine acc (some (a.seq b))
       | _, _ => acc) =
      EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) := by
    cases acc with
    | none => cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
    | some a => cases a <;> cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
  have heq : (fun acc k => match G₁.edgeAt i' k, G₂.edgeAt k j' with
      | some a, some b => EdgeRel.combine acc (some (a.seq b))
      | _, _ => acc) =
      (fun acc k => EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b))) := by
    funext acc k
    exact step acc k
  have samefold := congrArg (fun f => List.foldl f none (List.range G₁.rightArity)) heq
  have hf' := samefold.symm.trans hf
  have hw := fold_choose_optional (fun k => do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) (List.range G₁.rightArity) none r' hf'
  simp only [reduceCtorEq, false_or, List.mem_range] at hw
  rcases hw with ⟨k, hk, hk'⟩
  cases e₁ : G₁.edgeAt i' k <;> cases e₂ : G₂.edgeAt k j' <;> simp_all <;> grind

theorem graph_compat {S : Type} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (G₁ G₂ : InvGraph) (a b c : List S)
    (h₁ : ConformsToGraph ltRel leRel G₁ a b)
    (h₂ : ConformsToGraph ltRel leRel G₂ b c) :
    ConformsToGraph ltRel leRel (G₁.comp G₂) a c := by
  rcases h₁ with ⟨ha, hb₁, h₁⟩
  rcases h₂ with ⟨hb₂, hc, h₂⟩
  refine ⟨ha, hc, ?_⟩
  intro i j hi hj
  constructor
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .lt h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .le h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind

end NishtAbel2024

-- CanonicalLookup

namespace NishtAbel2024

theorem canonical_mem (n m i j : Nat) (f : Nat → Nat → Option EdgeRel) (r : EdgeRel) :
    (i, j, r) ∈ InvGraph.canonicalEdges n m f ↔ i < n ∧ j < m ∧ f i j = some r := by
  simp [InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff, Prod.mk.injEq]

private theorem fold_ne_none {α : Type} (f : α → EdgeRel) (xs : List α) (r : EdgeRel) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) (some r) ≠ none := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    cases r <;> cases h : f x <;> simp_all [EdgeRel.combine]

private theorem fold_eq_none_iff {α : Type} (f : α → EdgeRel) (xs : List α) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) none = none ↔ xs = [] := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
    have hn := fold_ne_none f xs (f x)
    cases h : f x <;> simpa [EdgeRel.combine, h] using hn

private theorem canonical_fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind

private theorem canonical_edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := canonical_fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx

private theorem edgeAt_ne_none_of_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (hm : (i, j, r) ∈ G.edges) : G.edgeAt i j ≠ none := by
  intro h
  have hf := (fold_eq_none_iff (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j))).mp h
  have hm' : (i, j, r) ∈ G.edges.filter (fun e => e.1 == i && e.2.1 == j) := by
    simp [hm]
  rw [hf] at hm'
  exact List.not_mem_nil hm'

theorem canonical_lookup (n m : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    (InvGraph.mk n m (InvGraph.canonicalEdges n m f)).edgeAt i j = f i j := by
  let G : InvGraph := ⟨n, m, InvGraph.canonicalEdges n m f⟩
  change G.edgeAt i j = f i j
  cases he : G.edgeAt i j with
  | none =>
    cases hf : f i j with
    | none => rfl
    | some r =>
      have hm : (i, j, r) ∈ G.edges := (canonical_mem n m i j f r).2 ⟨hi, hj, hf⟩
      exact False.elim (edgeAt_ne_none_of_mem G i j r hm he)
  | some r =>
    have hm : (i, j, r) ∈ G.edges := canonical_edgeAt_mem G i j r he
    exact ((canonical_mem n m i j f r).1 hm).2.2.symm

end NishtAbel2024

-- GraphAssoc

namespace NishtAbel2024

/-- Composition of optional edge labels; absence absorbs composition. -/
def edgeMul : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some a, some b => some (a.seq b)
  | _, _ => none

theorem edgeMul_assoc (a b c : Option EdgeRel) :
    edgeMul (edgeMul a b) c = edgeMul a (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_assoc (a b c : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) c = EdgeRel.combine a (EdgeRel.combine b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_comm (a b : Option EdgeRel) :
    EdgeRel.combine a b = EdgeRel.combine b a := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rfl

theorem edgeMul_left_distrib (a b c : Option EdgeRel) :
    edgeMul a (EdgeRel.combine b c) = EdgeRel.combine (edgeMul a b) (edgeMul a c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_right_distrib (a b c : Option EdgeRel) :
    edgeMul (EdgeRel.combine a b) c = EdgeRel.combine (edgeMul a c) (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_sum_right (a : Option EdgeRel) (xs : List (Option EdgeRel)) :
    edgeMul a (xs.foldr EdgeRel.combine none) =
      (xs.map (edgeMul a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_left_distrib, ih]

theorem edgeMul_sum_left (xs : List (Option EdgeRel)) (a : Option EdgeRel) :
    edgeMul (xs.foldr EdgeRel.combine none) a =
      (xs.map (fun x => edgeMul x a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_right_distrib, ih]

theorem combine_interchange (a b c d : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) (EdgeRel.combine c d) =
    EdgeRel.combine (EdgeRel.combine a c) (EdgeRel.combine b d) := by
  rw [combine_assoc, ← combine_assoc b c d, combine_comm b c, combine_assoc, ← combine_assoc]

theorem sum_map_combine {α : Type} (xs : List α) (f g : α → Option EdgeRel) :
    (xs.map (fun x => EdgeRel.combine (f x) (g x))).foldr EdgeRel.combine none =
    EdgeRel.combine ((xs.map f).foldr EdgeRel.combine none) ((xs.map g).foldr EdgeRel.combine none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    exact combine_interchange _ _ _ _

theorem finite_sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Option EdgeRel) :
    (xs.map (fun x => (ys.map (f x)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none =
    (ys.map (fun y => (xs.map (fun x => f x y)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_nil, List.foldr_nil] at ih
      simp only [List.map_nil, List.foldr_nil, List.map_cons, List.foldr_cons]
      rw [← ih]
      rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ← sum_map_combine]

theorem combine_none_right (a : Option EdgeRel) : EdgeRel.combine a none = a := by
  rcases a with _ | (_ | _) <;> rfl

theorem combine_foldl_eq_foldr (xs : List (Option EdgeRel)) :
    xs.foldl EdgeRel.combine none = xs.foldr EdgeRel.combine none := by
  have h : ∀ acc, xs.foldl EdgeRel.combine acc = EdgeRel.combine acc (xs.foldr EdgeRel.combine none) := by
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.foldr_nil, combine_none_right]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.foldr_cons, ih, combine_assoc]
  rw [h none]
  rcases xs.foldr EdgeRel.combine none with _ | (_ | _) <;> rfl

/-- Without compatible middle arities, associativity can fail, even for finite graphs. -/
theorem comp_not_assoc_without_arity :
    ∃ G₁ G₂ G₃ : InvGraph, (G₁.comp G₂).comp G₃ ≠ G₁.comp (G₂.comp G₃) := by
  refine ⟨⟨1, 1, [(0, 0, .le)]⟩, ⟨0, 1, [(0, 0, .le)]⟩, ⟨1, 1, [(0, 0, .le)]⟩, ?_⟩
  decide

def edgeSum (n : Nat) (f : Nat → Option EdgeRel) : Option EdgeRel :=
  ((List.range n).map f).foldr EdgeRel.combine none

theorem edgeSum_congr {n : Nat} {f g : Nat → Option EdgeRel}
    (h : ∀ i < n, f i = g i) : edgeSum n f = edgeSum n g := by
  unfold edgeSum
  congr 1
  apply List.map_congr_left
  intro x hx
  exact h x (List.mem_range.mp hx)

theorem matrix_assoc (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (_hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j)))
    (i j : Nat) (hi : i < A.leftArity) (hj : j < C.rightArity) :
    edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) ((B.comp C).edgeAt k j)) =
    edgeSum B.rightArity (fun k => edgeMul ((A.comp B).edgeAt i k) (C.edgeAt k j)) := by
  calc
    _ = edgeSum A.rightArity (fun k => edgeSum B.rightArity (fun l => edgeMul (A.edgeAt i k) (edgeMul (B.edgeAt k l) (C.edgeAt l j)))) := by
      apply edgeSum_congr
      intro k hk
      rw [compLookup B C k j (hab ▸ hk) hj]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using edgeMul_sum_right (A.edgeAt i k) ((List.range B.rightArity).map (fun l => edgeMul (B.edgeAt k l) (C.edgeAt l j)))
    _ = edgeSum B.rightArity (fun l => edgeSum A.rightArity (fun k => edgeMul (edgeMul (A.edgeAt i k) (B.edgeAt k l)) (C.edgeAt l j))) := by
      unfold edgeSum
      simp only [edgeMul_assoc]
      exact finite_sum_swap _ _ _
    _ = _ := by
      apply edgeSum_congr
      intro l hl
      rw [compLookup A B i l hi hl]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using (edgeMul_sum_left ((List.range A.rightArity).map (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k l))) (C.edgeAt l j)).symm

def compEdges (A B : InvGraph) (i j : Nat) : Option EdgeRel :=
  (List.range A.rightArity).foldl
    (fun acc k => match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) none

theorem compEdges_eq (A B : InvGraph) (i j : Nat) :
    compEdges A B i j = edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
  unfold compEdges edgeSum
  have hstep : ∀ acc k, (match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) = EdgeRel.combine acc (edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
    intro acc k
    rcases acc with _ | (_ | _) <;> rcases A.edgeAt i k with _ | (_ | _) <;> rcases B.edgeAt k j with _ | (_ | _) <;> rfl
  simp only [hstep, ← List.foldl_map, combine_foldl_eq_foldr]

theorem comp_def (A B : InvGraph) :
    A.comp B = ⟨A.leftArity, B.rightArity, InvGraph.canonicalEdges A.leftArity B.rightArity (compEdges A B)⟩ := rfl

theorem comp_assoc_of_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j))) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  rw [comp_def (A.comp B) C, comp_def A (B.comp C)]
  simp only [InvGraph.comp, InvGraph.mk.injEq, true_and]
  change InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges (A.comp B) C) =
    InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges A (B.comp C))
  unfold InvGraph.canonicalEdges
  apply List.flatMap_congr
  intro i hi
  apply List.filterMap_congr
  intro j hj
  have hi' : i < A.leftArity := List.mem_range.mp hi
  have hj' : j < C.rightArity := List.mem_range.mp hj
  have h := (matrix_assoc A B C hab hbc compLookup i j hi' hj').symm
  rw [compEdges_eq, compEdges_eq]
  change Option.map _ (edgeSum B.rightArity _) = Option.map _ (edgeSum A.rightArity _)
  rw [h]

theorem comp_assoc_of_canonical_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (lookup : ∀ (l r : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat),
      i < l → j < r → (InvGraph.mk l r (InvGraph.canonicalEdges l r f)).edgeAt i j = f i j) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  apply comp_assoc_of_lookup A B C hab hbc
  intro X Y i j hi hj
  rw [comp_def, lookup X.leftArity Y.rightArity (compEdges X Y) i j hi hj, compEdges_eq]

theorem comp_assoc_compatible (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  exact comp_assoc_of_canonical_lookup A B C hab hbc canonical_lookup

end NishtAbel2024

-- FiniteGraphs

namespace NishtAbel2024

instance : Finite EdgeRel := Finite.of_injective (fun e : EdgeRel => match e with | .lt => false | .le => true) (by intro a b h; cases a <;> cases b <;> simp_all)

def graphFromCode (N : Nat) (a b : Fin (N+1)) (m : Fin N → Fin N → Option EdgeRel) : InvGraph :=
  ⟨a.val, b.val, InvGraph.canonicalEdges a.val b.val fun i j =>
    if hi : i < N then if hj : j < N then m ⟨i, hi⟩ ⟨j, hj⟩ else none else none⟩

theorem finite_normalized_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ G = G.normalize}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, hnorm⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => G.edgeAt i.val j.val), ?_⟩
  dsimp [graphFromCode]
  calc
    _ = G.normalize := by
      simp only [InvGraph.normalize, InvGraph.mk.injEq, true_and]
      unfold InvGraph.canonicalEdges
      apply List.flatMap_congr
      intro i hi
      apply List.filterMap_congr
      intro j hj
      have hiN : i < N := by simp only [List.mem_range] at hi; omega
      have hjN : j < N := by simp only [List.mem_range] at hj; omega
      simp [hiN, hjN]
    _ = G := hnorm.symm

end NishtAbel2024

-- ClosureFinite

namespace NishtAbel2024

def CanonicalGraph (G : InvGraph) : Prop :=
  ∃ lookup, G.edges = InvGraph.canonicalEdges G.leftArity G.rightArity lookup

theorem closure_invariants (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    G.leftArity = 𝒢.arity g ∧ G.rightArity = 𝒢.arity f ∧ CanonicalGraph G := by
  induction h with
  | @base f g G hmem =>
    have hg := hwf.2 f g G hmem
    refine ⟨?_, ?_, ?_⟩
    · simpa [InvGraph.normalize] using hg.1
    · simpa [InvGraph.normalize] using hg.2.1
    · exact ⟨G.edgeAt, rfl⟩
  | @comp f h g G₁ G₂ h₁ h₂ ih₁ ih₂ =>
    exact ⟨ih₁.1, ih₂.2.1, ⟨_, rfl⟩⟩

theorem finite_canonical_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ CanonicalGraph G}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, lookup, hlookup⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => lookup i.val j.val), ?_⟩
  dsimp [graphFromCode]
  cases G with
  | mk left right edges =>
    simp only [InvGraph.mk.injEq, true_and] at *
    rw [hlookup]
    unfold InvGraph.canonicalEdges
    apply List.flatMap_congr
    intro i hi
    apply List.filterMap_congr
    intro j hj
    have hiN : i < N := by simp only [List.mem_range] at hi; omega
    have hjN : j < N := by simp only [List.mem_range] at hj; omega
    simp [hiN, hjN]

theorem closure_support (𝒢 : InvGraphFamily) (dom : List FunName)
    (hsupp : ∀ f g, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    f ∈ dom ∧ g ∈ dom := by
  induction h with
  | base hmem => exact hsupp _ _ (List.ne_nil_of_mem hmem)
  | comp _ _ ih₁ ih₂ => exact ⟨ih₂.1, ih₁.2⟩

private theorem arity_bounded (arity : FunName → Nat) (dom : List FunName) (f : FunName)
    (hf : f ∈ dom) : arity f ≤ (dom.map arity).foldr max 0 := by
  induction dom with
  | nil => simp at hf
  | cons a dom ih =>
    simp only [List.mem_cons] at hf
    simp only [List.map_cons, List.foldr_cons]
    rcases hf with rfl | hf
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hf) (Nat.le_max_right _ _)

theorem finite_closure_graphs (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf) :
    {G : InvGraph | ∃ f g, InvGraphClosure 𝒢 f g G}.Finite := by
  obtain ⟨dom, hsupp⟩ := hwf.1
  let N := (dom.map 𝒢.arity).foldr max 0
  apply (finite_canonical_graphs N).subset
  intro G hG
  obtain ⟨f, g, hg⟩ := hG
  obtain ⟨hgf, hgg⟩ := closure_support 𝒢 dom hsupp hg
  obtain ⟨hl, hr, hc⟩ := closure_invariants 𝒢 hwf hg
  exact ⟨hl ▸ arity_bounded 𝒢.arity dom g hgg,
         hr ▸ arity_bounded 𝒢.arity dom f hgf, hc⟩

end NishtAbel2024

-- RamseyBridge

namespace NishtAbel2024

theorem homogeneous_pair_subsequence {C : Type} [Finite C] (c : Nat → Nat → C)
    (ramsey : ∀ (color : Finset Nat → C), ∃ (M : Set Nat) (b : C), M.Infinite ∧
      ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (color : C), StrictMono seq ∧
      ∀ i j, i < j → c (seq i) (seq j) = color := by
  classical
  let pairColor (s : Finset Nat) : C :=
    if h : s.Nonempty then c (s.min' h) (s.max' h) else c 0 0
  obtain ⟨M, color, hinf, hcolor⟩ := ramsey pairColor
  refine ⟨Nat.nth (fun n => n ∈ M), color, Nat.nth_strictMono hinf, ?_⟩
  intro i j hij
  have hlt := (Nat.nth_strictMono (p := fun n => n ∈ M) hinf) hij
  have ha := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf i
  have hb := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf j
  have hsub : (↑({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat) : Set Nat) ⊆ M := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff] using And.intro ha hb
  have hcard : ({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat).card = 2 :=
    Finset.card_pair (ne_of_lt hlt)
  have hc := hcolor _ hsub hcard
  simpa [pairColor, Finset.min'_pair, Finset.max'_pair, min_eq_left (le_of_lt hlt),
    max_eq_right (le_of_lt hlt)] using hc

end NishtAbel2024

-- IdempotentRamsey

namespace NishtAbel2024

/-- Ramsey extraction of a homogeneous idempotent interval value. -/
theorem homogeneous_idempotent_intervals {Name Graph Carrier : Type} [Finite Name] [Finite Graph]
    (name : Nat → Name) (graph : Nat → Nat → Graph) (val : Graph → Carrier)
    (comp : Carrier → Carrier → Carrier)
    (hcomp : ∀ i j k, i < j → j < k → val (graph i k) = comp (val (graph j k)) (val (graph i j)))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (f : Name) (G : Graph), StrictMono seq ∧
      (∀ i, name (seq i) = f) ∧
      (∀ i j, i < j → graph (seq i) (seq j) = G) ∧ comp (val G) (val G) = val G := by
  obtain ⟨seq, v, hmono, hpair⟩ :=
    homogeneous_pair_subsequence (fun i j => (name i, name j, graph i j)) ramsey
  refine ⟨seq, v.1, v.2.2, hmono, ?_, ?_, ?_⟩
  · intro i
    exact congrArg (fun p : Name × Name × Graph => p.1) (hpair i (i + 1) (Nat.lt_succ_self i))
  · intro i j hij
    exact congrArg (fun p : Name × Name × Graph => p.2.2) (hpair i j hij)
  · have h01 : graph (seq 0) (seq 1) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 1 (by decide))
    have h12 : graph (seq 1) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 1 2 (by decide))
    have h02 : graph (seq 0) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 2 (by decide))
    calc
      comp (val v.2.2) (val v.2.2) = comp (val (graph (seq 1) (seq 2))) (val (graph (seq 0) (seq 1))) := by rw [h12, h01]
      _ = val (graph (seq 0) (seq 2)) := (hcomp _ _ _ (hmono (by decide)) (hmono (by decide))).symm
      _ = val v.2.2 := by rw [h02]

end NishtAbel2024

-- SCTWellFounded

namespace NishtAbel2024

/-- A homogeneous chain with a strict diagonal contradicts ordinal well-foundedness. -/
theorem no_infinite_strict_diagonal_chain {S : Type} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (G : InvGraph) (s : Nat → List S) (k : Nat)
    (hk : k < G.leftArity) (hedge : G.edgeAt k k = some .lt)
    (hchain : ∀ n, ConformsToGraph ltRel leRel G (s (n + 1)) (s n)) : False := by
  have hlen : ∀ n, k < (s (n + 1)).length := by
    intro n
    simpa only [(hchain n).1] using hk
  let chain : Nat → S := fun n => (s (n + 1)).get ⟨k, hlen n⟩
  have hdescending : ∀ n, ltRel (chain (n + 1)) (chain n) := by
    intro n
    exact ((hchain (n + 1)).2.2 k k (hlen (n + 1)) (hlen n)).1 hedge
  have impossible (x : S) (hacc : Acc ltRel x) : ∀ n, chain n = x → False := by
    induction hacc with
    | intro x _ ih =>
      intro n hn
      exact ih (chain (n + 1)) (hn ▸ hdescending n) (n + 1) rfl
  exact impossible (chain 0) (wf.apply (chain 0)) 0 rfl

/-- An idempotent graph in a valid closure cannot label an infinite conforming chain. -/
theorem no_infinite_idempotent_chain {S : Type} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (f : FunName) (G : InvGraph) (closed : InvGraphClosure family f f G)
    (idempotent : G.comp G = G) (s : Nat → List S)
    (hchain : ∀ n, ConformsToGraph ltRel leRel G (s (n + 1)) (s n)) : False := by
  obtain ⟨k, hk, hedge⟩ := valid.2 f G closed idempotent
  exact no_infinite_strict_diagonal_chain ltRel leRel wf G s k hk hedge hchain

end NishtAbel2024

-- SCTRamseyContradiction

namespace NishtAbel2024

/-- Once finite interval colors have the concatenation, closure and conformance
properties, Ramsey's theorem rules out an infinite invocation chain. -/
theorem no_chain_from_interval_coloring {S Name Graph : Type}
    [Finite Name] [Finite Graph]
    (ltRel leRel : S → S → Prop) (wf : WellFounded ltRel)
    (family : InvGraphFamily) (valid : SCTValid family)
    (name : Nat → Name) (nameVal : Name → FunName)
    (graph : Nat → Nat → Graph) (graphVal : Graph → InvGraph)
    (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      graphVal (graph i k) = (graphVal (graph j k)).comp (graphVal (graph i j)))
    (hclosed : ∀ i j, i < j →
      InvGraphClosure family (nameVal (name i)) (nameVal (name j)) (graphVal (graph i j)))
    (hconform : ∀ i j, i < j →
      ConformsToGraph ltRel leRel (graphVal (graph i j)) (sizes j) (sizes i))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  obtain ⟨seq, f, G, hmono, hname, hgraph, hidem⟩ :=
    homogeneous_idempotent_intervals name graph graphVal InvGraph.comp hcomp ramsey
  have hclose : InvGraphClosure family (nameVal f) (nameVal f) (graphVal G) := by
    have h := hclosed (seq 0) (seq 1) (hmono (by decide))
    rw [hname 0, hname 1, hgraph 0 1 (by decide)] at h
    exact h
  apply no_infinite_idempotent_chain ltRel leRel wf family valid (nameVal f) (graphVal G) hclose hidem (fun n => sizes (seq n))
  intro n
  have h := hconform (seq n) (seq (n + 1)) (hmono (Nat.lt_succ_self n))
  rw [hgraph n (n + 1) (Nat.lt_succ_self n)] at h
  exact h

end NishtAbel2024

-- SCTFiniteIntervals

namespace NishtAbel2024

/-- Instantiate the finite-color contradiction with actual invocation graphs. -/
theorem no_chain_from_finite_intervals {S : Type} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (dom : List FunName) (name : Nat → FunName) (hdom : ∀ n, name n ∈ dom)
    (interval : Nat → Nat → InvGraph) (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      interval i k = (interval j k).comp (interval i j))
    (hclosed : ∀ i j, i < j → InvGraphClosure family (name i) (name j) (interval i j))
    (hconform : ∀ i j, i < j →
      ConformsToGraph ltRel leRel (interval i j) (sizes j) (sizes i))
    (ramsey : ∀ {C : Type} [Finite C] (color : Finset Nat → C),
      ∃ (M : Set Nat) (b : C), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  classical
  let names : Set FunName := {f | f ∈ dom}
  let : Finite names := dom.finite_toSet.to_subtype
  let graphs : Set InvGraph := {G | ∃ f g, InvGraphClosure family f g G}
  let : Finite graphs := (finite_closure_graphs family valid.1).to_subtype
  let coloredName (n : Nat) : names := ⟨name n, hdom n⟩
  let coloredGraph (i j : Nat) : graphs :=
    if h : i < j then ⟨interval i j, ⟨name i, name j, hclosed i j h⟩⟩
    else ⟨interval 0 1, ⟨name 0, name 1, hclosed 0 1 (by decide)⟩⟩
  apply no_chain_from_interval_coloring ltRel leRel wf family valid coloredName Subtype.val coloredGraph Subtype.val sizes
  · intro i j k hij hjk
    simpa [coloredGraph, hij, hjk, lt_trans hij hjk] using hcomp i j k hij hjk
  · intro i j hij
    simpa [coloredName, coloredGraph, hij] using hclosed i j hij
  · intro i j hij
    simpa [coloredGraph, hij] using hconform i j hij
  · exact ramsey

end NishtAbel2024

-- OrdinalRelations

namespace NishtAbel2024

theorem size_lt_implies_le (a b : SizeOrd) : SizeOrd.lt a b → SizeOrd.le a b := by
  simp_all only [SizeOrd.lt, SizeOrd.le]; omega

theorem size_le_trans (a b c : SizeOrd) : SizeOrd.le a b → SizeOrd.le b c → SizeOrd.le a c := by
  simp_all only [SizeOrd.le]; omega

theorem size_lt_le_trans (a b c : SizeOrd) : SizeOrd.lt a b → SizeOrd.le b c → SizeOrd.lt a c := by
  simp_all only [SizeOrd.lt, SizeOrd.le]; omega

theorem size_le_lt_trans (a b c : SizeOrd) : SizeOrd.le a b → SizeOrd.lt b c → SizeOrd.lt a c := by
  simp_all only [SizeOrd.lt, SizeOrd.le]; omega

end NishtAbel2024

-- ChainCollapse

namespace NishtAbel2024

 theorem chain_collapse {S : Type} (ltRel leRel : S → S → Prop)
    (compat : ∀ (G₁ G₂ : InvGraph) (a b c : List S),
      ConformsToGraph ltRel leRel G₁ a b →
      ConformsToGraph ltRel leRel G₂ b c →
      ConformsToGraph ltRel leRel (G₁.comp G₂) a c)
    (G₁ : InvGraph) (Gs : List InvGraph) (s₀ sₙ : List S) (mid : List (List S))
    (hlen : mid.length = Gs.length)
    (hchain : ∀ (k : Nat) (hk : k < (G₁ :: Gs).length)
       (hk1 : k < ([s₀] ++ mid ++ [sₙ]).length)
       (hk2 : k + 1 < ([s₀] ++ mid ++ [sₙ]).length),
       ConformsToGraph ltRel leRel ((G₁ :: Gs).get ⟨k, hk⟩)
         (([s₀] ++ mid ++ [sₙ]).get ⟨k, hk1⟩)
         (([s₀] ++ mid ++ [sₙ]).get ⟨k + 1, hk2⟩)) :
    ConformsToGraph ltRel leRel (Gs.foldl InvGraph.comp G₁) s₀ sₙ := by
  induction Gs generalizing G₁ s₀ mid with
  | nil =>
    cases mid with
    | nil =>
      simpa using hchain 0 (by simp) (by simp) (by simp)
    | cons x xs => simp at hlen
  | cons G₂ Gs ih =>
    cases mid with
    | nil => simp at hlen
    | cons s₁ mid =>
      have hfirst : ConformsToGraph ltRel leRel G₁ s₀ s₁ := by
        simpa using hchain 0 (by simp) (by simp) (by simp)
      have hnext : ∀ (k : Nat) (hk : k < (G₂ :: Gs).length)
          (hk1 : k < ([s₁] ++ mid ++ [sₙ]).length)
          (hk2 : k + 1 < ([s₁] ++ mid ++ [sₙ]).length),
          ConformsToGraph ltRel leRel ((G₂ :: Gs).get ⟨k, hk⟩)
            (([s₁] ++ mid ++ [sₙ]).get ⟨k, hk1⟩)
            (([s₁] ++ mid ++ [sₙ]).get ⟨k + 1, hk2⟩) := by
        intro k hk hk1 hk2
        simpa using hchain (k+1) (by simpa using hk) (by simpa using hk1) (by simpa using hk2)
      have hsecond : ConformsToGraph ltRel leRel G₂ s₁ (match mid with | [] => sₙ | x :: _ => x) := by
        have := hnext 0 (by simp) (by simp) (by simp)
        cases mid <;> simpa using this
      apply ih (G₁ := G₁.comp G₂) (s₀ := s₀) (mid := mid)
      · simpa using hlen
      · intro k hk hk1 hk2
        cases k with
        | zero =>
          cases mid <;> simpa using compat G₁ G₂ s₀ s₁ _ hfirst hsecond
        | succ k =>
          have h := hnext (k+1) (by simpa using hk) (by simpa using hk1) (by simpa using hk2)
          simpa using h

end NishtAbel2024

-- OrdinalChain

namespace NishtAbel2024

theorem ordinal_chain_collapse (G₁ : InvGraph) (Gs : List InvGraph)
    (s₀ sₙ : List SizeOrd) (mid : List (List SizeOrd))
    (hlen : mid.length = Gs.length)
    (hchain : ∀ (k : Nat) (hk : k < (G₁ :: Gs).length)
      (hk1 : k < ([s₀] ++ mid ++ [sₙ]).length)
      (hk2 : k + 1 < ([s₀] ++ mid ++ [sₙ]).length),
      OrdConformsToGraph ((G₁ :: Gs).get ⟨k, hk⟩)
        (([s₀] ++ mid ++ [sₙ]).get ⟨k, hk1⟩)
        (([s₀] ++ mid ++ [sₙ]).get ⟨k + 1, hk2⟩)) :
    OrdConformsToGraph (Gs.foldl InvGraph.comp G₁) s₀ sₙ :=
  chain_collapse SizeOrd.lt SizeOrd.le
    (graph_compat SizeOrd.lt SizeOrd.le size_lt_implies_le size_le_trans
      size_lt_le_trans size_le_lt_trans) G₁ Gs s₀ sₙ mid hlen hchain

end NishtAbel2024

-- Intervals

namespace NishtAbel2024

/-- `segment g i n` composes the `n + 1` consecutive graphs starting at `i`.
The later graph is on the left because it compares callee sizes to caller sizes. -/
def segment (g : Nat → InvGraph) (i : Nat) : Nat → InvGraph
  | 0 => g i
  | n + 1 => (g (i + n + 1)).comp (segment g i n)

def interval (g : Nat → InvGraph) (i j : Nat) : InvGraph :=
  segment g i (j - i - 1)

theorem step_graphs (family : InvGraphFamily) (valid : SCTValid family)
    (s : Nat → SCTState) (h : ∀ i, SCTStep family (s i) (s (i + 1))) :
    ∃ g : Nat → InvGraph,
      (∀ i, InvGraphClosure family (s i).fn (s (i + 1)).fn (g i)) ∧
      (∀ i, OrdConformsToGraph (g i) (s (i + 1)).sizes (s i).sizes) := by
  classical
  choose g hg hc using h
  refine ⟨g, ?_, hc⟩
  intro i
  have hn := (valid.1.2 (s i).fn (s (i + 1)).fn (g i) (hg i)).2.2
  simpa only [← hn] using (InvGraphClosure.base (hg i))

theorem segment_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i n : Nat) :
    InvGraphClosure family (name i) (name (i + n + 1)) (segment g i n) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using InvGraphClosure.comp (hbase (i + n + 1)) ih

theorem interval_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i j : Nat) (hij : i < j) :
    InvGraphClosure family (name i) (name j) (interval g i j) := by
  have h := segment_closed family name g hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_conforms {S : Type} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsToGraph ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i n : Nat) :
    ConformsToGraph ltRel leRel (segment g i n) (sizes (i + n + 1)) (sizes i) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using
      graph_compat ltRel leRel hle htt htl hlt (g (i + n + 1)) (segment g i n)
        (sizes (i + n + 1 + 1)) (sizes (i + n + 1)) (sizes i) (hbase (i + n + 1)) ih

theorem interval_conforms {S : Type} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsToGraph ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j : Nat) (hij : i < j) :
    ConformsToGraph ltRel leRel (interval g i j) (sizes j) (sizes i) := by
  have h := segment_conforms ltRel leRel hle htt htl hlt g sizes hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_arities (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (i n : Nat) :
    (segment g i n).leftArity = arity (i + n + 1) ∧
    (segment g i n).rightArity = arity i := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, InvGraph.comp, Nat.add_assoc] using ⟨(hbase (i + n + 1)).1, ih.2⟩

theorem segment_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i n m : Nat) :
    segment g i (n + m + 1) = (segment g (i + n + 1) m).comp (segment g i n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (g (i + (n + m + 1) + 1)).comp (segment g i (n + m + 1)) =
      ((g ((i + n + 1) + m + 1)).comp (segment g (i + n + 1) m)).comp (segment g i n)
    rw [ih]
    have idx : i + (n + m + 1) + 1 = i + n + 1 + m + 1 := by omega
    rw [idx]
    apply Eq.symm
    apply assoc
    · exact (hbase _).2.trans (segment_arities g arity hbase (i + n + 1) m).1.symm
    · exact (segment_arities g arity hbase (i + n + 1) m).2.trans
        (segment_arities g arity hbase i n).1.symm

theorem interval_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have h := segment_concat g arity hbase assoc i (j - i - 1) (k - j - 1)
  have hstart : i + (j - i - 1) + 1 = j := by omega
  have hlen : (j - i - 1) + (k - j - 1) + 1 = k - i - 1 := by omega
  simpa [interval, hstart, hlen] using h

theorem interval_concat_of_conforms {S : Type} (ltRel leRel : S → S → Prop)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsToGraph ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have harity : ∀ i, (g i).leftArity = (sizes (i + 1)).length ∧
      (g i).rightArity = (sizes i).length := by
    intro i
    exact ⟨(hbase i).1.symm, (hbase i).2.1.symm⟩
  exact interval_concat g (fun i => (sizes i).length) harity comp_assoc_compatible i j k hij hjk
end NishtAbel2024

-- NoChain

/-- To establish well-foundedness it is enough to rule out descending sequences. -/
theorem wellFounded_of_no_descending_sequence {α : Type} (r : α → α → Prop)
    (h : ∀ f : ℕ → α, (∀ n, r (f (n + 1)) (f n)) → False) : WellFounded r :=
  wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h f hf⟩

-- SCTFinal

namespace NishtAbel2024

theorem sct_call_rel_well_founded (family : InvGraphFamily) (valid : SCTValid family) :
    WellFounded (SCTCallRel family) := by
  apply wellFounded_of_no_descending_sequence
  intro states steps
  obtain ⟨dom, hsupport⟩ := valid.1.1
  obtain ⟨g, hclosed, hconforms⟩ := step_graphs family valid states steps
  have hnames : ∀ n, (states n).fn ∈ dom := by
    intro n
    exact (closure_support family dom hsupport (hclosed n)).1
  apply no_chain_from_finite_intervals SizeOrd.lt SizeOrd.le SizeOrd.lt_wf
    family valid dom (fun n => (states n).fn) hnames (interval g) (fun n => (states n).sizes)
  · exact interval_concat_of_conforms SizeOrd.lt SizeOrd.le g (fun n => (states n).sizes) hconforms
  · exact interval_closed family (fun n => (states n).fn) g hclosed
  · exact interval_conforms SizeOrd.lt SizeOrd.le size_lt_implies_le size_le_trans
      size_lt_le_trans size_le_lt_trans g (fun n => (states n).sizes) hconforms
  · intro C _ color
    obtain ⟨M, b, _, hInf, hcolor⟩ :=
      OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset 2 color Set.univ Set.infinite_univ
    exact ⟨M, b, hInf, hcolor⟩

end NishtAbel2024

-- MilestoneAssembly

namespace NishtAbel2024

/-- Lemma 1 (Soundness of composition, p. 34), Corollary (Collapsing of finite chains, p. 34),
and Theorem 1 (Soundness of `G`, pp. 34–35):
1. (**Lemma 1**) For any type `S` equipped with transitive relations `ltRel, leRel : S → S → Prop`
   such that `ltRel` implies `leRel` and `ltRel`/`leRel` compose transitively into `ltRel`, if
   `a⃗ ≺_{G₁} b⃗` and `b⃗ ≺_{G₂} c⃗`, then `a⃗ ≺_{G₁ ∘ G₂} c⃗`.
2. (**Corollary**) For any non-empty chain of invocation graphs `G₁ :: Gs` and ordinal tuples
   `s₀ :: s₁ :: ... :: sₙ` of matching length `(G₁ :: Gs).length + 1` where each adjacent step
   satisfies `OrdConformsToGraph`, the endpoints conform to `Gs.foldl InvGraph.comp G₁`.
3. (**Theorem 1**) If `⊢ 𝒢` (`SCTValid 𝒢`), then `SCT_𝒢` (`SCTCallRel 𝒢`) is well-founded. -/
theorem milestone_from_wf
    (hwf : ∀ 𝒢 : InvGraphFamily, SCTValid 𝒢 → WellFounded (SCTCallRel 𝒢)) :
    (∀ {S : Type} (ltRel leRel : S → S → Prop),
      (∀ x y, ltRel x y → leRel x y) →
      (∀ x y z, leRel x y → leRel y z → leRel x z) →
      (∀ x y z, ltRel x y → leRel y z → ltRel x z) →
      (∀ x y z, leRel x y → ltRel y z → ltRel x z) →
      ∀ (G₁ G₂ : InvGraph) (a b c : List S),
        ConformsToGraph ltRel leRel G₁ a b →
        ConformsToGraph ltRel leRel G₂ b c →
        ConformsToGraph ltRel leRel (G₁.comp G₂) a c) ∧
    (∀ (G₁ : InvGraph) (Gs : List InvGraph) (s₀ sₙ : List SizeOrd) (mid : List (List SizeOrd)),
      let graphs := G₁ :: Gs
      let chain := [s₀] ++ mid ++ [sₙ]
      mid.length = Gs.length →
      (∀ (k : Nat) (hk : k < graphs.length)
         (hk1 : k < chain.length) (hk2 : k + 1 < chain.length),
        OrdConformsToGraph (graphs.get ⟨k, hk⟩) (chain.get ⟨k, hk1⟩) (chain.get ⟨k + 1, hk2⟩)) →
      OrdConformsToGraph (Gs.foldl InvGraph.comp G₁) s₀ sₙ) ∧
    (∀ 𝒢 : InvGraphFamily,
      SCTValid 𝒢 →
      WellFounded (SCTCallRel 𝒢)) := by
  exact ⟨fun ltRel leRel hle htt htl hlt => graph_compat ltRel leRel hle htt htl hlt,
    fun G₁ Gs s₀ sₙ mid hlen hchain => ordinal_chain_collapse G₁ Gs s₀ sₙ mid hlen hchain, hwf⟩

end NishtAbel2024

open NishtAbel2024

/-- Lemma 1 (Soundness of composition, p. 34), Corollary (Collapsing of finite chains, p. 34),
and Theorem 1 (Soundness of `G`, pp. 34–35):
1. (**Lemma 1**) For any type `S` equipped with transitive relations `ltRel, leRel : S → S → Prop`
   such that `ltRel` implies `leRel` and `ltRel`/`leRel` compose transitively into `ltRel`, if
   `a⃗ ≺_{G₁} b⃗` and `b⃗ ≺_{G₂} c⃗`, then `a⃗ ≺_{G₁ ∘ G₂} c⃗`.
2. (**Corollary**) For any non-empty chain of invocation graphs `G₁ :: Gs` and ordinal tuples
   `s₀ :: s₁ :: ... :: sₙ` of matching length `(G₁ :: Gs).length + 1` where each adjacent step
   satisfies `OrdConformsToGraph`, the endpoints conform to `Gs.foldl InvGraph.comp G₁`.
3. (**Theorem 1**) If `⊢ 𝒢` (`SCTValid 𝒢`), then `SCT_𝒢` (`SCTCallRel 𝒢`) is well-founded. -/
theorem solution :
    (∀ {S : Type} (ltRel leRel : S → S → Prop),
      (∀ x y, ltRel x y → leRel x y) →
      (∀ x y z, leRel x y → leRel y z → leRel x z) →
      (∀ x y z, ltRel x y → leRel y z → ltRel x z) →
      (∀ x y z, leRel x y → ltRel y z → ltRel x z) →
      ∀ (G₁ G₂ : InvGraph) (a b c : List S),
        ConformsToGraph ltRel leRel G₁ a b →
        ConformsToGraph ltRel leRel G₂ b c →
        ConformsToGraph ltRel leRel (G₁.comp G₂) a c) ∧
    (∀ (G₁ : InvGraph) (Gs : List InvGraph) (s₀ sₙ : List SizeOrd) (mid : List (List SizeOrd)),
      let graphs := G₁ :: Gs
      let chain := [s₀] ++ mid ++ [sₙ]
      mid.length = Gs.length →
      (∀ (k : Nat) (hk : k < graphs.length)
         (hk1 : k < chain.length) (hk2 : k + 1 < chain.length),
        OrdConformsToGraph (graphs.get ⟨k, hk⟩) (chain.get ⟨k, hk1⟩) (chain.get ⟨k + 1, hk2⟩)) →
      OrdConformsToGraph (Gs.foldl InvGraph.comp G₁) s₀ sₙ) ∧
    (∀ 𝒢 : InvGraphFamily,
      SCTValid 𝒢 →
      WellFounded (SCTCallRel 𝒢)) := by
  exact milestone_from_wf sct_call_rel_well_founded

