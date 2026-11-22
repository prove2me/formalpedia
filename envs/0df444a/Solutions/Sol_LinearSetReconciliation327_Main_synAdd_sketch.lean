-- Prove2me | solution 1 for LinearSetReconciliation327.Main.synAdd_sketch
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-21T10:05:48.668389+00:00
-- url     : https://prove2.me/submissions/c0fb700e-7d03-424e-aa2c-f896299cd7a4

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework

/-!
# Sketch linearity: `Node.synAdd` is the sketch of the symmetric difference

`Node.decode`'s `recursive` case hands each child the payload

```
Node.synAdd (child s) (Node.sketch CR (child s) (r.2 s) (sch.column r.1 x s))
                       (Node.sketch CR (child s) (r.2 s) P_s)
```

i.e. *the syntactic sum of two sketches*, whereas the child's correctness law
(`hint_decode_correct`, and `Node.decode`'s own recursion) is stated at
`Node.sketch CR (child s) (r.2 s) (sch.exactChildInput r.1 x J s)`.  `synAdd_sketch`
identifies the two: the sketch of a symmetric difference is the `synAdd` of the
sketches, so the child's payload *is* a legitimate child input.

This is `F₂`-linearity of the whole tree, proved by induction on `T`.  Its two
ingredients are `sketch_symmDiff` (a `cr` node: the syndrome is a sum of parities,
`odd_card_symmDiff`) and `column_symmDiff` (a `direct`/`recursive` node: the column
map is additive, via `rowImage_symmDiff` and `codeword`-linearity `code_linear`,
smuggled through `rowsWhere_add` of `ZMod 2`).

Extracted verbatim (spans asserted to be substrings of the source) from
`Solutions/_65_decode_correct.lean` §12.3 and its §1/§6 helpers; that module is a
`Solutions/` file and `import Solutions.*` is not available to a submission, which
is why the development has to be re-published as a platform theorem.
-/

set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

open Classical in
/-- The row-local image is additive in the set, for a nonempty row (`m > 0`): two coordinates with the
same row and the same local index coincide, so membership is unique and parity is preserved. -/
lemma rowImage_symmDiff (N m : ℕ) (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S S' : Finset ℕ) :
    rowImage N m π j (symmDiff S S') = symmDiff (rowImage N m π j S) (rowImage N m π j S') := by
  classical
  have key : ∀ i i' : Fin N, (π i).val % m = (π i').val % m →
      (π i).val / m = (π i').val / m → i = i' := by
    intro i i' h1 h2
    have e1 := Nat.div_add_mod (π i).val m
    have e2 := Nat.div_add_mod (π i').val m
    have e : (π i).val = (π i').val := by
      rw [h1, h2] at e1
      rw [e1] at e2
      exact e2
    exact π.injective (Fin.ext e)
  ext a
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_symmDiff]
  constructor
  · rintro ⟨i, ⟨hi, hj⟩, ha⟩
    rcases hi with ⟨hS, hS'⟩ | ⟨hS, hS'⟩
    · left
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
    · right
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
  · rintro (⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩ | ⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩)
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inl ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inr ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩

/-- `ZMod 2` has only the values `0` and `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : ZMod.val a < 2 := ZMod.val_lt a
  have hcast : ((ZMod.val a : ℕ) : ZMod 2) = a := ZMod.natCast_zmod_val a
  have h : ZMod.val a = 0 ∨ ZMod.val a = 1 := by omega
  rcases h with h | h
  · left
    rw [← hcast, h]
    simp
  · right
    rw [← hcast, h]
    simp

/-- In `ZMod 2`, `a + b = 1` is exactly "one of `a`, `b` is `1` and the other `0`". -/
lemma zmod2_add_eq_one_iff (a b : ZMod 2) :
    a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    decide

open Classical in
/-- At one node, the support `{j : A_j + B_j = 1}` is the symmetric difference of the supports of
`A` and of `B`. -/
lemma rowsWhere_add (sch : RowScheme) (A B : Fin sch.m → ZMod 2) :
    sch.rowsWhere (fun j => A j + B j = 1) =
      symmDiff (sch.rowsWhere (fun j => A j = 1)) (sch.rowsWhere (fun j => B j = 1)) := by
  classical
  ext a
  simp only [RowScheme.rowsWhere, mem_symmDiff, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (zmod2_add_eq_one_iff (A i) (B i)).1 hi with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · left
      refine ⟨⟨i, hA, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hB] at hi'
      exact zero_ne_one hi'
    · right
      refine ⟨⟨i, hB, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hA] at hi'
      exact zero_ne_one hi'
  · rintro (⟨⟨i, hi, hv⟩, hnot⟩ | ⟨⟨i, hi, hv⟩, hnot⟩)
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      left
      refine ⟨hi, ?_⟩
      rcases zmod2_eq_zero_or_one (B i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      right
      refine ⟨?_, hi⟩
      rcases zmod2_eq_zero_or_one (A i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot

open Classical in
/-- The paper's column `C_s(x)` is additive in `x` (for an empty row scheme both sides are empty). -/
lemma column_symmDiff (sch : RowScheme) (lr : sch.LocalSeed) (x y : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr (symmDiff x y) s = symmDiff (sch.column lr x s) (sch.column lr y s) := by
  classical
  rcases Nat.eq_zero_or_pos sch.m with hm | hm
  · have hempty : (univ : Finset (Fin sch.m)) = ∅ := by
      have hc : (univ : Finset (Fin sch.m)).card = 0 := by simp [hm]
      exact Finset.card_eq_zero.mp hc
    simp [RowScheme.column, RowScheme.rowsWhere, hempty]
  · unfold RowScheme.column
    have hrow : ∀ j, sch.rowOf lr (symmDiff x y) j = symmDiff (sch.rowOf lr x j) (sch.rowOf lr y j) :=
      fun j => rowImage_symmDiff sch.N sch.m hm lr.1 j x y
    have hcode : ∀ j, sch.code j (lr.2 j) (sch.rowOf lr (symmDiff x y) j) s =
        sch.code j (lr.2 j) (sch.rowOf lr x j) s + sch.code j (lr.2 j) (sch.rowOf lr y j) s := by
      intro j
      rw [hrow j, sch.code_linear]
    simp only [hcode]
    exact rowsWhere_add sch _ _

/-- Filtering commutes with the symmetric difference. -/
lemma filter_symmDiff (p : ℕ → Prop) [DecidablePred p] (A B : Finset ℕ) :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) := by
  classical
  ext a
  simp only [mem_symmDiff, mem_filter]
  tauto

/-- The parity of a symmetric-difference cardinality is the XOR of the two parities (each coordinate
in the intersection contributes twice). -/
lemma odd_card_symmDiff (A B : Finset ℕ) :
    Odd (symmDiff A B).card ↔ (Odd A.card ∧ ¬ Odd B.card) ∨ (Odd B.card ∧ ¬ Odd A.card) := by
  classical
  have hdisj1 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hdisj2 : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hdisj3 : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).1
  have hAB : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, sup_eq_union]
    exact Finset.card_union_of_disjoint hdisj1
  have hA : A.card = (A \ B).card + (A ∩ B).card := by
    have hunion : A \ B ∪ A ∩ B = A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc A.card = (A \ B ∪ A ∩ B).card := by rw [hunion]
      _ = (A \ B).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj2
  have hB : B.card = (B \ A).card + (A ∩ B).card := by
    have hunion : B \ A ∪ A ∩ B = B := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc B.card = (B \ A ∪ A ∩ B).card := by rw [hunion]
      _ = (B \ A).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj3
  rw [hAB, hA, hB, Nat.odd_add, Nat.odd_add, Nat.odd_add, ← Nat.not_odd_iff_even,
    ← Nat.not_odd_iff_even]
  tauto

open Classical in
/-- The CR syndrome `CR_{N,t} x` is additive in `x` (each row of the syndrome is one syndrome bit). -/
lemma sketch_symmDiff (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    CR.sketch N t (symmDiff x y) = symmDiff (CR.sketch N t x) (CR.sketch N t y) := by
  classical
  ext r
  have hfilt : (symmDiff x y).filter (fun i => r ∈ CR.col N t i) =
      symmDiff (x.filter fun i => r ∈ CR.col N t i) (y.filter fun i => r ∈ CR.col N t i) :=
    filter_symmDiff _ x y
  simp only [CRFamily.sketch, hfilt, mem_symmDiff, mem_filter, mem_range, true_and,
    odd_card_symmDiff]
  tauto

/-- The sketch is additive: `sketch a + sketch b = sketch (a + b)`.  This is what turns the child's
stored payload `sketch C_s + sketch P_s` in `Node.decode`'s `recursive` case into
`sketch (exactChildInput)`, i.e. into a legitimate child input. -/
theorem synAdd_sketch (CR : CRFamily) (T : Node) :
    ∀ (r : Node.Seed T) (a b : Finset ℕ),
      Node.synAdd T (Node.sketch CR T r a) (Node.sketch CR T r b)
        = Node.sketch CR T r (symmDiff a b) := by
  induction T with
  | store N =>
      intro r a b
      rfl
  | cr N t =>
      intro r a b
      simp only [Node.synAdd, Node.sketch]
      exact (sketch_symmDiff CR N t a b).symm
  | direct sch t =>
      intro r a b
      simp only [Node.synAdd, Node.sketch]
      refine Prod.ext ?_ ?_
      · funext s
        exact (column_symmDiff sch r a b s).symm
      · exact (sketch_symmDiff CR sch.N t a b).symm
  | recursive sch t Xs Ys child ih =>
      intro r a b
      simp only [Node.synAdd, Node.sketch]
      refine Prod.ext ?_ ?_
      · funext s
        exact (ih s (r.2 s) (sch.column r.1 a s) (sch.column r.1 b s)).trans
          (by rw [← column_symmDiff sch r.1 a b s])
      · exact (sketch_symmDiff CR sch.N t a b).symm

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Sketch linearity (submission wrapper): the `synAdd` of two sketches is the sketch of the
symmetric difference. -/
theorem solution (CR : CRFamily) (T : Node) :
    ∀ (r : Node.Seed T) (a b : Finset ℕ),
      Node.synAdd T (Node.sketch CR T r a) (Node.sketch CR T r b)
        = Node.sketch CR T r (symmDiff a b) :=
  LinearSetReconciliation327.Main.synAdd_sketch CR T
