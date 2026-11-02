-- Prove2me | solution 1 for NishtAbel2024.lexicographic_invocation_graphs_sct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:30:52.288103+00:00
-- url     : https://prove2.me/submissions/5dffa624-2251-4263-ba01-f85ca03b6b07

import Definitions.Def_NishtAbel2024_Syntax


namespace NishtAbel2024

theorem canonical_mem (n m i j : Nat) (f : Nat → Nat → Option EdgeRel) (r : EdgeRel) :
    (i, j, r) ∈ InvGraph.canonicalEdges n m f ↔ i < n ∧ j < m ∧ f i j = some r := by
  simp [InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff, Prod.mk.injEq]
  grind

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
    have hm : (i, j, r) ∈ G.edges := edgeAt_mem G i j r he
    exact ((canonical_mem n m i j f r).1 hm).2.2.symm

end NishtAbel2024


namespace NishtAbel2024.LexGraphBase

theorem getD_eq_elem (ms : List Nat) (k : Nat) (hk : k < ms.length) :
    ms.getD k 0 = ms[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem idxOf_getD (ms : List Nat) (h : ms.Nodup) (k : Nat) (hk : k < ms.length) :
    ms.idxOf? (ms.getD k 0) = some k := by
  rw [getD_eq_elem ms k hk]
  apply List.idxOf?_eq_some_iff.mpr
  refine ⟨hk, rfl, ?_⟩
  intro j hj he
  have hjlen : j < ms.length := by omega
  have heq : j = k := (List.getElem_inj (h₀ := hjlen) (h₁ := hk) h).mp he
  omega

theorem normalized_lookup (G : InvGraph) (i j : Nat)
    (hi : i < G.leftArity) (hj : j < G.rightArity) :
    G.normalize.edgeAt i j = G.edgeAt i j := by
  exact canonical_lookup G.leftArity G.rightArity G.edgeAt i j hi hj

theorem lex_lookup (ms : List Nat) (arity step i j : Nat) (hi : i < arity) (hj : j < arity) :
    (lexInvGraph ms arity step).edgeAt i j =
      (if i == j then
        match ms.idxOf? i with
        | some pos => if pos < step then some .le else if pos == step then some .lt else none
        | none => none
       else none) := by
  exact canonical_lookup arity arity _ i j hi hj

theorem lex_normalized_arities (ms : List Nat) (arity step : Nat) :
    (lexInvGraph ms arity step).normalize.leftArity = arity ∧
      (lexInvGraph ms arity step).normalize.rightArity = arity := by
  exact ⟨rfl, rfl⟩

theorem lex_graph_strict (ms : List Nat) (arity k : Nat)
    (hnd : ms.Nodup) (hb : ∀ i ∈ ms, i < arity) (hk : k < ms.length) :
    ((lexInvGraph ms arity k).normalize).edgeAt (ms.getD k 0) (ms.getD k 0) = some .lt := by
  have he : ms.getD k 0 = ms[k] := getD_eq_elem ms k hk
  have hbound : ms.getD k 0 < arity := by rw [he]; exact hb _ (List.getElem_mem hk)
  rw [normalized_lookup _ _ _ hbound hbound, lex_lookup _ _ _ _ _ hbound hbound]
  rw [idxOf_getD ms hnd k hk]
  simp

theorem lex_graph_earlier (ms : List Nat) (arity k t : Nat)
    (hnd : ms.Nodup) (hb : ∀ i ∈ ms, i < arity)
    (hk : k < ms.length) (ht : t < k) :
    ((lexInvGraph ms arity k).normalize).edgeAt (ms.getD t 0) (ms.getD t 0) = some .le := by
  have htlen : t < ms.length := by omega
  have he : ms.getD t 0 = ms[t] := getD_eq_elem ms t htlen
  have hbound : ms.getD t 0 < arity := by rw [he]; exact hb _ (List.getElem_mem htlen)
  rw [normalized_lookup _ _ _ hbound hbound, lex_lookup _ _ _ _ _ hbound hbound]
  rw [idxOf_getD ms hnd t htlen]
  simp [ht]

end NishtAbel2024.LexGraphBase


namespace NishtAbel2024.LexComposition

private def edgeMul : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some a, some b => some (a.seq b)
  | _, _ => none

private def edgeSum (n : Nat) (f : Nat → Option EdgeRel) : Option EdgeRel :=
  ((List.range n).map f).foldr EdgeRel.combine none

private theorem combine_assoc (a b c : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) c = EdgeRel.combine a (EdgeRel.combine b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

private theorem combine_none_right (a : Option EdgeRel) : EdgeRel.combine a none = a := by
  rcases a with _ | (_ | _) <;> rfl

private theorem combine_foldl_eq_foldr (xs : List (Option EdgeRel)) :
    xs.foldl EdgeRel.combine none = xs.foldr EdgeRel.combine none := by
  have h : ∀ acc, xs.foldl EdgeRel.combine acc = EdgeRel.combine acc (xs.foldr EdgeRel.combine none) := by
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.foldr_nil, combine_none_right]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.foldr_cons, ih, combine_assoc]
  rw [h none]
  rcases xs.foldr EdgeRel.combine none with _ | (_ | _) <;> rfl

private def compEdges (A B : InvGraph) (i j : Nat) : Option EdgeRel :=
  (List.range A.rightArity).foldl
    (fun acc k => match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) none

private theorem compEdges_eq (A B : InvGraph) (i j : Nat) :
    compEdges A B i j = edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
  unfold compEdges edgeSum
  have hstep : ∀ acc k, (match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) = EdgeRel.combine acc (edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
    intro acc k
    rcases acc with _ | (_ | _) <;> rcases A.edgeAt i k with _ | (_ | _) <;> rcases B.edgeAt k j with _ | (_ | _) <;> rfl
  simp only [hstep, ← List.foldl_map, combine_foldl_eq_foldr]

private theorem comp_def (A B : InvGraph) :
    A.comp B = ⟨A.leftArity, B.rightArity, InvGraph.canonicalEdges A.leftArity B.rightArity (compEdges A B)⟩ := rfl

private theorem foldr_some_ne_none (xs : List (Option EdgeRel)) (r : EdgeRel)
    (h : some r ∈ xs) : xs.foldr EdgeRel.combine none ≠ none := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases x with
    | none =>
      simp only [List.foldr_cons]
      have hx : some r ∈ xs := by simpa using h
      have ht := ih hx
      cases he : xs.foldr EdgeRel.combine none with
      | none => exact (ht he).elim
      | some s => cases s <;> simp [EdgeRel.combine]
    | some s =>
      cases s <;> cases he : xs.foldr EdgeRel.combine none with
      | none => simp [List.foldr_cons, he, EdgeRel.combine]
      | some s => cases s <;> simp [List.foldr_cons, he, EdgeRel.combine]

private theorem foldr_lt_of_mem (xs : List (Option EdgeRel))
    (h : some .lt ∈ xs) : xs.foldr EdgeRel.combine none = some .lt := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with h | h
    · subst x
      simp [EdgeRel.combine]
    · have ht := ih h
      cases x with
      | none => simp [List.foldr_cons, ht, EdgeRel.combine]
      | some r => cases r <;> simp [List.foldr_cons, ht, EdgeRel.combine]

theorem edgeSum_has_edge {n k : Nat} {f : Nat → Option EdgeRel} {r : EdgeRel}
    (hk : k < n) (h : f k = some r) : ∃ s, edgeSum n f = some s := by
  have hm : some r ∈ (List.range n).map f :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, h⟩
  have hn := foldr_some_ne_none ((List.range n).map f) r hm
  cases he : edgeSum n f with
  | none => exact False.elim (hn he)
  | some s => exact ⟨s, rfl⟩

theorem edgeSum_has_lt {n k : Nat} {f : Nat → Option EdgeRel}
    (hk : k < n) (h : f k = some .lt) : edgeSum n f = some .lt := by
  apply foldr_lt_of_mem
  exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, h⟩

theorem comp_diagonal_has_edge {A B : InvGraph} {i : Nat} {r s : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some r) (hB : B.edgeAt i i = some s) :
    ∃ t, (A.comp B).edgeAt i i = some t := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_edge hiM (r := r.seq s)
  simp [edgeMul, hA, hB]

theorem comp_diagonal_strict_left {A B : InvGraph} {i : Nat} {s : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some .lt) (hB : B.edgeAt i i = some s) :
    (A.comp B).edgeAt i i = some .lt := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_lt hiM
  simp [edgeMul, hA, hB, EdgeRel.seq]

theorem comp_diagonal_strict_right {A B : InvGraph} {i : Nat} {r : EdgeRel}
    (hiA : i < A.leftArity) (hiM : i < A.rightArity) (hiB : i < B.rightArity)
    (hA : A.edgeAt i i = some r) (hB : B.edgeAt i i = some .lt) :
    (A.comp B).edgeAt i i = some .lt := by
  rw [comp_def, canonical_lookup _ _ _ _ _ hiA hiB, compEdges_eq]
  apply edgeSum_has_lt hiM
  cases r <;> simp [edgeMul, hA, hB, EdgeRel.seq]

end NishtAbel2024.LexComposition


namespace NishtAbel2024.LexicographicEmbedding
open LexComposition

/-- A graph contains the non-strict prefix and a strict first decrease
    required by a lexicographic measure. -/
def LexWitness (m : List Nat) (n : Nat) (G : InvGraph) : Prop :=
  G.leftArity = n ∧ G.rightArity = n ∧
    ∃ k, k < m.length ∧
      G.edgeAt (m.getD k 0) (m.getD k 0) = some .lt ∧
      ∀ t, t < k → ∃ r, G.edgeAt (m.getD t 0) (m.getD t 0) = some r

private theorem getD_mem {m : List Nat} {k : Nat} (hk : k < m.length) :
    m.getD k 0 ∈ m := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, List.getElem_mem]

private theorem flatMap_congr {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

private theorem filterMap_congr {α β : Type} (xs : List α) (f g : α → Option β)
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filterMap_cons]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

theorem canonical_normalized (n : Nat) (f : Nat → Nat → Option EdgeRel) :
    (InvGraph.mk n n (InvGraph.canonicalEdges n n f)).normalize =
      InvGraph.mk n n (InvGraph.canonicalEdges n n f) := by
  simp only [InvGraph.normalize, InvGraph.mk.injEq, true_and]
  unfold InvGraph.canonicalEdges
  apply flatMap_congr
  intro i hi
  apply filterMap_congr
  intro j hj
  change Option.map (fun r => (i, j, r))
    ((InvGraph.mk n n (InvGraph.canonicalEdges n n f)).edgeAt i j) = _
  rw [canonical_lookup n n f i j (List.mem_range.mp hi) (List.mem_range.mp hj)]

/-- Composition preserves the earliest of the two strict positions. -/
theorem lexWitness_comp {m : List Nat} {n : Nat} {A B : InvGraph}
    (hbound : ∀ i ∈ m, i < n) (hA : LexWitness m n A) (hB : LexWitness m n B) :
    LexWitness m n (A.comp B) := by
  obtain ⟨hAl, hAr, k, hk, hAk, hApre⟩ := hA
  obtain ⟨hBl, hBr, l, hl, hBl', hBpre⟩ := hB
  have hindex : ∀ t, t < m.length → m.getD t 0 < n := by
    intro t ht
    exact hbound _ (getD_mem ht)
  refine ⟨hAl, hBr, ?_⟩
  by_cases hkl : k ≤ l
  · refine ⟨k, hk, ?_, ?_⟩
    · have h := hindex k hk
      have hBedge : ∃ r, B.edgeAt (m.getD k 0) (m.getD k 0) = some r := by
        by_cases heq : k = l
        · subst l
          exact ⟨.lt, hBl'⟩
        · exact hBpre k (Nat.lt_of_le_of_ne hkl heq)
      obtain ⟨r, hr⟩ := hBedge
      apply comp_diagonal_strict_left (i := m.getD k 0) (s := r)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hAk
      · exact hr
    · intro t ht
      have ht' : t < m.length := Nat.lt_trans ht hk
      have h := hindex t ht'
      obtain ⟨r, hr⟩ := hApre t ht
      obtain ⟨s, hs⟩ := hBpre t (Nat.lt_of_lt_of_le ht hkl)
      apply comp_diagonal_has_edge (r := r) (s := s)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hs
  · have hlk : l < k := Nat.lt_of_not_ge hkl
    refine ⟨l, hl, ?_, ?_⟩
    · have h := hindex l hl
      obtain ⟨r, hr⟩ := hApre l hlk
      apply comp_diagonal_strict_right (i := m.getD l 0) (r := r)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hBl'
    · intro t ht
      have ht' : t < m.length := Nat.lt_trans ht hl
      have h := hindex t ht'
      obtain ⟨r, hr⟩ := hApre t (Nat.lt_trans ht hlk)
      obtain ⟨s, hs⟩ := hBpre t ht
      apply comp_diagonal_has_edge (r := r) (s := s)
      · simpa [hAl] using h
      · simpa [hAr] using h
      · simpa [hBr] using h
      · exact hr
      · exact hs

theorem lex_family_arity_wf (dom : List FunName) (n : Nat) (m : List Nat) :
    (lexInvGraphFamily dom n m).ArityWf := by
  constructor
  · refine ⟨dom, ?_⟩
    intro f g hg
    by_cases h : f ∈ dom ∧ g ∈ dom
    · exact h
    · simp [lexInvGraphFamily, h] at hg
  · intro f g G hG
    simp only [lexInvGraphFamily] at hG ⊢
    split at hG
    next h =>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hG
      simp only [lexInvGraph]
      refine ⟨True.intro, True.intro, ?_⟩
      exact (canonical_normalized n _).symm
    next h => simp at hG

theorem lex_graph_witness (m : List Nat) (n k : Nat) (hnd : m.Nodup)
    (hbound : ∀ i ∈ m, i < n) (hk : k < m.length) :
    LexWitness m n (lexInvGraph m n k).normalize := by
  refine ⟨rfl, rfl, k, hk, LexGraphBase.lex_graph_strict m n k hnd hbound hk, ?_⟩
  intro t ht
  exact ⟨.le, LexGraphBase.lex_graph_earlier m n k t hnd hbound hk ht⟩

theorem lex_closure_witness {dom : List FunName} {n : Nat} {m : List Nat}
    (hnd : m.Nodup) (hbound : ∀ i ∈ m, i < n) {f g : FunName} {G : InvGraph}
    (hG : InvGraphClosure (lexInvGraphFamily dom n m) f g G) :
    LexWitness m n G := by
  induction hG with
  | base h =>
    simp only [lexInvGraphFamily] at h
    split at h
    next =>
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
      exact lex_graph_witness m n k hnd hbound (List.mem_range.mp hk)
    next => simp at h
  | comp _ _ ih₁ ih₂ => exact lexWitness_comp hbound ih₁ ih₂

theorem lex_family_sct (dom : List FunName) (n : Nat) (m : List Nat)
    (hnd : m.Nodup) (hbound : ∀ i ∈ m, i < n) :
    SCTValid (lexInvGraphFamily dom n m) := by
  refine ⟨lex_family_arity_wf dom n m, ?_⟩
  intro f G hG _
  obtain ⟨hl, _, k, hk, hstrict, _⟩ := lex_closure_witness hnd hbound hG
  refine ⟨m.getD k 0, ?_, hstrict⟩
  rw [hl]
  exact hbound _ (getD_mem hk)


end NishtAbel2024.LexicographicEmbedding

open NishtAbel2024

/-- The lexicographic invocation-graph family satisfies size-change termination. -/
theorem solution :
    ∀ (dom : List FunName) (n : Nat) (m : List Nat),
      m.Nodup → (∀ i ∈ m, i < n) → SCTValid (lexInvGraphFamily dom n m) := by
  intro dom n m hnd hbound
  exact LexicographicEmbedding.lex_family_sct dom n m hnd hbound
