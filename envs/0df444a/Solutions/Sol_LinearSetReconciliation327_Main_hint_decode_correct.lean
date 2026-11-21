-- Prove2me | solution 1 for LinearSetReconciliation327.Main.hint_decode_correct
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-20T13:10:06.701829+00:00
-- url     : https://prove2.me/submissions/cc4898db-c776-4852-85b9-50b319e7c1f1

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_NodeValidity

open scoped ENNReal
open Finset

set_option autoImplicit false

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


/-! ## 6. The CR syndrome is additive -/

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


/-! ## 8. The hint matrix `H`

`H r` is the flattened sketch: the support of `x`, flattened through `bitVal`, for the tree seed
obtained from the public seed `r`.  The seed splitting itself is built in section 8b below. -/

/-- The support of a `ZMod 2` vector over `[N]`, as the `Finset ℕ` on which `Node.sketch` acts. -/
def support {N : ℕ} (x : Fin N → ZMod 2) : Finset ℕ := (univ.filter fun i => x i = 1).image Fin.val


/-- The column of a singleton input is a subset of `[m]`. -/
lemma column_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr x s ⊆ range sch.m := by
  intro v hv
  unfold RowScheme.column RowScheme.rowsWhere at hv
  rw [mem_image] at hv
  obtain ⟨j, -, rfl⟩ := hv
  exact mem_range.mpr j.isLt


/-! # 12.  `Node.decode` correctness, and `hgood` for Theorem 5.1's conjunct 8

`uuu51` reduced conjunct 8 to the semantic hypothesis

```
hgood : ∀ i : Fin N, (i.val ∈ Φ (cnt - 1) ↔ x i = 1)
```

where `Φ (cnt - 1)` is the set returned by the last schedule call — the root's residual `CR` call,
which is last because `decSched` appends it after the children (`decSched` `.recursive` case) and
`hintP.tree` never returns `.store`.  No *per-call* contract can imply `hgood` (a contract on one call
cannot see the union of the calls' sets), so it must come from the **assembly**: when every node's
decode succeeds, the tree decode reconstructs `x`.

This section supplies exactly that:

* `decode_sketch` — `Node.decode CR T r (Node.sketch CR T r x) J = some x` under the per-node
  hypotheses `WF`, `AllBounds`, `AllValid` and `CR.Recovers`.  The proof is a recursion mirroring
  `Node.decode`: `store` is `rfl`, `cr` is `CR.dec`, and `direct` / `recursive` say "the stored
  columns (resp. the children) yield the exact transcript, hence the assembled estimate is
  `exactEstimate`, hence the residual's error has weight `Z ≤ t` and `CR.Recovers` finishes".
* `AllValid` — `Valid` at every node — plus `allValid_of_valid`: the root's `Valid` together with
  `WF` and `AllBounds` *already* gives it (`U_s ≤ X_s`, `V_s ≤ Y_s` turn the child's input into a
  valid instance), so it is **not** an extra assumption.
* `hgood_of_decode` / `hgood_lastCall` — `hgood`, and the proof that its only non-per-node input is
  the *interface equation* identifying `Φ (cnt - 1)` with the decode's answer.

## 12.1  Membership, counting and `ZMod 2` helpers -/

/-- Membership in `rowsWhere`: the image is injective. -/
lemma mem_rowsWhere {sch : RowScheme} (P : Fin sch.m → Prop) (j : Fin sch.m) :
    j.val ∈ sch.rowsWhere P ↔ P j := by
  classical
  unfold RowScheme.rowsWhere
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j', hj', hv⟩
    have hP : P j' := by
      have h2 := hj'
      simp only [Finset.mem_filter] at h2
      exact h2.2
    have hjj : j' = j := Fin.ext hv
    rwa [hjj] at hP
  · intro h
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩


/-- `rowsWhere` lands in `[m]`. -/
lemma rowsWhere_subset_range (sch : RowScheme) (P : Fin sch.m → Prop) :
    sch.rowsWhere P ⊆ Finset.range sch.m := by
  intro a ha
  unfold RowScheme.rowsWhere at ha
  rw [Finset.mem_image] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact Finset.mem_range.mpr j.isLt


/-- A symmetric difference stays inside `[N]`. -/
lemma symmDiff_subset_range {N : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N) :
    symmDiff A B ⊆ Finset.range N := by
  intro a ha
  rcases Finset.mem_symmDiff.mp ha with ⟨h, -⟩ | ⟨h, -⟩
  · exact hA h
  · exact hB h


/-- The column membership, unfolded: row `j` is in `C_s(x)` iff its codeword bit is `1`. -/
lemma mem_column_iff (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.column lr x s ↔ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := by
  classical
  unfold RowScheme.column
  exact mem_rowsWhere _ j


/-- A membership indicator over a set whose membership is a codeword bit. -/
lemma ite_mem_code {S : Finset ℕ} {a : ℕ} {c : ZMod 2} (h : a ∈ S ↔ c = 1) :
    (if a ∈ S then (1 : ZMod 2) else 0) = c := by
  by_cases hS : a ∈ S
  · rw [if_pos hS]; exact (h.mp hS).symm
  · rw [if_neg hS]
    rcases zmod2_eq_zero_or_one c with hc | hc
    · exact hc.symm
    · exact absurd (h.mpr hc) hS


/-- Counting `[m]`-membership: for `S ⊆ [m]`, the `Fin m` filter and `S` have the same cardinality. -/
lemma card_fin_filter_eq {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card = S.card := by
  classical
  have himg : (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val) = S := by
    ext a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h2 := hj
      simp only [Finset.mem_filter] at h2
      exact h2.2
    · intro ha
      refine ⟨⟨a, Finset.mem_range.mp (hS ha)⟩, ?_, rfl⟩
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha⟩
  have hc : ((Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val)).card
      = (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  rw [← hc, himg]


/-- `Finset.filter` does not depend on which `DecidablePred` instance is used. -/
lemma filter_congr_dec {α : Type} (p : α → Prop) (d₁ d₂ : DecidablePred p) (s : Finset α) :
    @Finset.filter α p d₁ s = @Finset.filter α p d₂ s := by
  ext a
  rw [@Finset.mem_filter α p d₁ s a, @Finset.mem_filter α p d₂ s a]


/-- `|J_s| = U_s`: both count the rows whose prediction is `⊥`.  The two filters are built by
different definitions and hence carry different `DecidablePred` instances, so they are compared
through `filter_congr_dec`. -/
lemma exactHint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) :
    (sch.exactHint lr x J s).card = sch.U lr x J s := by
  have key : ∀ (d : DecidablePred fun j : Fin sch.m => sch.exactPred lr x J s j = none),
      (sch.exactHint lr x J s).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card := by
    intro d
    unfold RowScheme.exactHint RowScheme.rowsWhere
    rw [← show (@Finset.filter (Fin sch.m)
          (fun j => sch.exactPred lr x J s j = none)
          (fun a => Classical.propDecidable (sch.exactPred lr x J s a = none))
          Finset.univ).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card from
      congrArg Finset.card (filter_congr_dec _ _ d Finset.univ)]
    exact Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  unfold RowScheme.U
  exact key _


/-- `ZMod 2` has no third value: `b ≠ c ↔ ¬ ((c = 1) ↔ (b = 1))`. -/
lemma zmod2_ne_iff_not_iff (b c : ZMod 2) :
    b ≠ c ↔ ¬ ((c = 1) ↔ (b = 1)) := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp


/-- The pointwise shape of `(C_s + P_s) \ J_s`: a wrong prediction. -/
lemma symmDiff_sdiff_hint_iff (p : Option (ZMod 2)) (c : ZMod 2) :
    (¬ ((c = 1) ↔ (p = some 1)) ∧ p ≠ none) ↔ ∃ b, p = some b ∧ b ≠ c := by
  constructor
  · rintro ⟨hiff, hne⟩
    obtain ⟨b, hb⟩ : ∃ b, p = some b := by
      cases p with
      | none => exact absurd rfl hne
      | some b => exact ⟨b, rfl⟩
    refine ⟨b, hb, ?_⟩
    rw [hb, Option.some.injEq] at hiff
    exact (zmod2_ne_iff_not_iff b c).mpr hiff
  · rintro ⟨b, hb, hne⟩
    subst hb
    refine ⟨?_, by simp⟩
    rw [Option.some.injEq]
    exact (zmod2_ne_iff_not_iff b c).mp hne


/-- `|(C_s + P_s) \ J_s| = V_s`: a coordinate is in the difference iff its prediction is wrong. -/
lemma exactChild_diff_hint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    ((sch.exactChildInput lr x J s) \ (sch.exactHint lr x J s)).card = sch.V lr x J s := by
  classical
  have hD : (sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ⊆ Finset.range sch.m :=
    fun a ha => (symmDiff_subset_range (column_subset_range sch lr x s)
      (rowsWhere_subset_range sch _)) (Finset.mem_sdiff.mp ha).1
  have hstep : ∀ j : Fin sch.m,
      (j.val ∈ sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ↔
        ∃ b, sch.exactPred lr x J s j = some b ∧
          b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s := by
    intro j
    have hcol : j.val ∈ sch.column lr x s ↔
        sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := mem_column_iff sch lr x s j
    have hP : j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := by
      unfold RowScheme.exactP
      exact mem_rowsWhere _ j
    have hH : j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := by
      unfold RowScheme.exactHint
      exact mem_rowsWhere _ j
    have hs : (j.val ∈ symmDiff (sch.column lr x s) (sch.exactP lr x J s)) ↔
        ¬ ((j.val ∈ sch.column lr x s) ↔ (j.val ∈ sch.exactP lr x J s)) := by
      rw [Finset.mem_symmDiff]
      tauto
    unfold RowScheme.exactChildInput
    rw [Finset.mem_sdiff, hs, hcol, hP, hH]
    exact symmDiff_sdiff_hint_iff _ _
  rw [← card_fin_filter_eq hD]
  have hVdef : sch.V lr x J s =
      (Finset.univ.filter fun j : Fin sch.m => ∃ b, sch.exactPred lr x J s j = some b ∧
        b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s).card := rfl
  rw [hVdef]
  exact congrArg Finset.card (Finset.ext fun j => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstep j)


/-! ## 12.2  `symmDiff`, `assemble` and `Valid` helpers -/

/-- Cancelling a symmetric difference: `A Δ (B Δ A) = B`. -/
lemma symmDiff_self_cancel (A B : Finset ℕ) : symmDiff A (symmDiff B A) = B := by
  ext a
  simp only [Finset.mem_symmDiff]
  tauto


/-- The assembled vector lands in `[N]`. -/
lemma assemble_subset_range (N m : ℕ) (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) :
    assemble N m π est ⊆ Finset.range N := by
  intro a ha
  rw [assemble, Finset.mem_image] at ha
  obtain ⟨i, -, rfl⟩ := ha
  exact Finset.mem_range.mpr i.isLt


/-- The assembled row estimates land in `[N]`. -/
lemma assembled_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (pref : Fin sch.m → List (ZMod 2)) :
    sch.assembled lr J pref ⊆ Finset.range sch.N :=
  assemble_subset_range sch.N sch.m lr.1 _


/-- The capacity bound of a valid instance: `|x| ≤ X + Y`. -/
lemma Valid.card_le {N X Y : ℕ} {x J : Finset ℕ} (h : Node.Valid N X Y x J) :
    x.card ≤ X + Y := by
  obtain ⟨-, -, hJ, hx⟩ := h
  have h1 : (x \ J).card + (x ∩ J).card = x.card := Finset.card_sdiff_add_card_inter x J
  have h2 : (x ∩ J).card ≤ J.card := Finset.card_le_card Finset.inter_subset_right
  omega


/-- The universe bound of a valid instance: `|x| ≤ N`. -/
lemma Valid.card_le_N {N X Y : ℕ} {x J : Finset ℕ} (h : Node.Valid N X Y x J) :
    x.card ≤ N := by
  have h1 : x.card ≤ (Finset.range N).card := Finset.card_le_card h.1
  rwa [Finset.card_range] at h1


/-! ## 12.3  `Node.synAdd` is the sketch of the symmetric difference -/

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


/-! ## 12.4  The running column prefix, and the fold of `decodeColumns`

At a `recursive` node the decoder folds `decodeColumn` over the columns.  The invariant is that after
`k` columns the prefix is the true transcript truncated at `k`; `colPref` is that list, and
`decodeColumns_of_step` turns the per-column exactness into exactness of the whole fold. -/

/-- The true transcript truncated at `k` columns. -/
def colPref (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (k : ℕ) :
    Fin sch.m → List (ZMod 2) :=
  fun j => (List.take k (List.finRange sch.ℓ)).map (sch.code j (lr.2 j) (sch.rowOf lr x j))


/-- The prefix starts empty. -/
lemma colPref_zero (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) :
    colPref sch lr x 0 = fun _ => [] := rfl


/-- One more index of `List.finRange`. -/
lemma take_finRange_succ (n k : ℕ) (hk : k < n) :
    List.take (k + 1) (List.finRange n) = List.take k (List.finRange n) ++ [⟨k, hk⟩] := by
  have hL : k < (List.finRange n).length := by simpa using hk
  rw [List.take_add_one, List.getElem?_eq_getElem hL, List.getElem_finRange]
  show List.take k (List.finRange n) ++ [Fin.cast _ ⟨k, hL⟩]
      = List.take k (List.finRange n) ++ [⟨k, hk⟩]
  exact congrArg (fun z => List.take k (List.finRange n) ++ [z]) (Fin.ext rfl)


/-- One more column of `colPref`. -/
lemma colPref_succ (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (k : ℕ)
    (hk : k < sch.ℓ) (j : Fin sch.m) :
    colPref sch lr x (k + 1) j
      = colPref sch lr x k j ++ [sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨k, hk⟩] := by
  unfold colPref
  rw [take_finRange_succ sch.ℓ k hk, List.map_append]
  rfl


/-- At the end the running prefix is the whole true transcript. -/
lemma colPref_full (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) :
    colPref sch lr x sch.ℓ = fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ := by
  funext j
  have htake : List.take sch.ℓ (List.finRange sch.ℓ) = List.finRange sch.ℓ :=
    List.take_of_length_le (le_of_eq (List.length_finRange (n := sch.ℓ)))
  show (List.take sch.ℓ (List.finRange sch.ℓ)).map
      (sch.code j (lr.2 j) (sch.rowOf lr x j))
    = sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ
  simp only [RowScheme.truePrefix, htake]


/-- One `decodeColumn` step, when the child decoder is exact on the exact inputs.  The hypothesis
`hchild` is what the induction hypothesis of `decode_sketch` supplies at a `recursive` node. -/
theorem decodeColumn_colPref (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ)) (x : Finset ℕ)
    (hchild : ∀ s : Fin sch.ℓ,
      childDec s (sch.exactP lr x J s) (sch.exactHint lr x J s)
        = some (sch.exactChildInput lr x J s))
    (k : ℕ) (hk : k < sch.ℓ) :
    sch.decodeColumn lr J childDec (colPref sch lr x k) ⟨k, hk⟩
      = some (colPref sch lr x (k + 1)) := by
  -- `Ps`/`Js` of `decodeColumn` *are* `exactP`/`exactHint` at `⟨k, hk⟩`: same predictions, same
  -- prefix (`colPref … k` is `truePrefix … k`).
  have key : sch.decodeColumn lr J childDec (colPref sch lr x k) ⟨k, hk⟩
      = (childDec ⟨k, hk⟩ (sch.exactP lr x J ⟨k, hk⟩) (sch.exactHint lr x J ⟨k, hk⟩)).map
          (fun Dhat j => colPref sch lr x k j ++
            [if j.val ∈ symmDiff (sch.exactP lr x J ⟨k, hk⟩) Dhat then 1 else 0]) := rfl
  have hcancel : symmDiff (sch.exactP lr x J ⟨k, hk⟩) (sch.exactChildInput lr x J ⟨k, hk⟩)
      = sch.column lr x ⟨k, hk⟩ := by
    show symmDiff (sch.exactP lr x J ⟨k, hk⟩)
        (symmDiff (sch.column lr x ⟨k, hk⟩) (sch.exactP lr x J ⟨k, hk⟩))
      = sch.column lr x ⟨k, hk⟩
    exact symmDiff_self_cancel _ _
  have hbit : ∀ j : Fin sch.m,
      (if j.val ∈ sch.column lr x ⟨k, hk⟩ then (1 : ZMod 2) else 0)
        = sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨k, hk⟩ :=
    fun j => ite_mem_code (mem_column_iff sch lr x ⟨k, hk⟩ j)
  rw [key, hchild ⟨k, hk⟩, Option.map_some]
  refine congrArg some ?_
  show (fun j => colPref sch lr x k j ++ [if j.val ∈ symmDiff (sch.exactP lr x J ⟨k, hk⟩)
      (sch.exactChildInput lr x J ⟨k, hk⟩) then 1 else 0]) = colPref sch lr x (k + 1)
  funext j
  rw [colPref_succ sch lr x k hk j, hcancel]
  exact congrArg (fun z => colPref sch lr x k j ++ [z]) (hbit j)


/-- A one-element list fold. -/
lemma foldlM_singleton {β α : Type} (f : β → α → Option β) (b : β) (a : α) :
    List.foldlM f b [a] = f b a := by
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases f b a with
  | none => rfl
  | some c => rfl


/-- Folding `decodeColumn` over the first `n` columns. -/
theorem foldlM_take_colPref (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ)) (x : Finset ℕ)
    (hstep : ∀ (k : ℕ) (hk : k < sch.ℓ),
      sch.decodeColumn lr J childDec (colPref sch lr x k) ⟨k, hk⟩
        = some (colPref sch lr x (k + 1))) :
    ∀ (n : ℕ), n ≤ sch.ℓ →
      (List.take n (List.finRange sch.ℓ)).foldlM (sch.decodeColumn lr J childDec)
        (colPref sch lr x 0) = some (colPref sch lr x n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hn' : n < sch.ℓ := by omega
      have h1 : List.foldlM (sch.decodeColumn lr J childDec) (colPref sch lr x n)
          [⟨n, hn'⟩] = some (colPref sch lr x (n + 1)) := by
        rw [foldlM_singleton]
        exact hstep n hn'
      rw [take_finRange_succ sch.ℓ n hn', List.foldlM_append, ih (by omega)]
      exact h1


/-- The whole `decodeColumns`, when every column step is exact. -/
theorem decodeColumns_of_step (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ)) (x : Finset ℕ)
    (hstep : ∀ (k : ℕ) (hk : k < sch.ℓ),
      sch.decodeColumn lr J childDec (colPref sch lr x k) ⟨k, hk⟩
        = some (colPref sch lr x (k + 1))) :
    sch.decodeColumns lr J childDec = some (colPref sch lr x sch.ℓ) := by
  have htake : List.take sch.ℓ (List.finRange sch.ℓ) = List.finRange sch.ℓ :=
    List.take_of_length_le (le_of_eq (List.length_finRange (n := sch.ℓ)))
  show (List.finRange sch.ℓ).foldlM (sch.decodeColumn lr J childDec) (fun _ => [])
    = some (colPref sch lr x sch.ℓ)
  rw [← colPref_zero sch lr x, ← htake]
  exact foldlM_take_colPref sch lr J childDec x hstep sch.ℓ le_rfl


/-- **`AllValid` is not an extra assumption**: the root's `Valid`, `WF` and `AllBounds` already give
it.  At a `recursive` node the child receives `C_s + P_s` with hint `J_s`; the bounds `U_s ≤ X_s`,
`V_s ≤ Y_s` are exactly `|J_s| ≤ X_s` and `|(C_s + P_s) \ J_s| ≤ Y_s`, so the child's instance is
valid, and the child's universe is `sch.m` by `WF`. -/
theorem allValid_of_valid :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → Node.Valid T.N X Y x J →
        AllValid X Y T r x J := by
  intro T
  induction T with
  | store N =>
      intro X Y r x J _ _ _
      trivial
  | cr N t =>
      intro X Y r x J _ _ hV
      exact hV
  | direct sch t =>
      intro X Y r x J _ _ hV
      exact hV
  | recursive sch t Xs Ys child ih =>
      intro X Y r x J hWF hB hV
      obtain ⟨htN, hWFc⟩ := hWF
      obtain ⟨hZ, hUV⟩ := hB
      refine ⟨hV, ?_⟩
      intro s
      apply ih s (Xs s) (Ys s) (r.2 s) (sch.exactChildInput r.1 x J s)
        (sch.exactHint r.1 x J s) (hWFc s).2 (hUV s).2.2
      rw [(hWFc s).1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact symmDiff_subset_range (column_subset_range sch r.1 x s)
          (rowsWhere_subset_range sch _)
      · exact rowsWhere_subset_range sch _
      · have h1 := exactHint_card sch r.1 x J s
        have h2 := (hUV s).1
        omega
      · have h1 := exactChild_diff_hint_card sch r.1 x J s
        have h2 := (hUV s).2.1
        omega


/-! ## 12.6  `Node.decode` correctness -/

/-- **`Node.decode` correctness.**  If the capacities are well formed at every node (`WF`), the
exact-execution bounds hold at every node (`AllBounds`), every node's input is a valid instance
(`AllValid`), and the `CR` family recovers every sparse vector (`CR.Recovers`), then decoding the
sketch of `x` returns `x`.

The recursion mirrors `Node.decode`:

* `store`: the payload *is* `x`;
* `cr`: `CR.Recovers` at `(N, t)`, using `x ⊆ [N]` and `|x| ≤ min N (X + Y) ≤ t`;
* `direct`: the stored columns are the true columns, so the assembled estimate is `exactEstimate`,
  the residual error is `x Δ exactEstimate` with weight `Z ≤ t`, and `CR.Recovers` finishes;
* `recursive`: the same, except that the exact transcript comes from the children's decodes
  (`decodeColumns_of_step`), each of which is exact by the induction hypothesis. -/
theorem decode_sketch (CR : CRFamily) (hRec : CR.Recovers) :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → AllValid X Y T r x J →
        Node.decode CR T r (Node.sketch CR T r x) J = some x := by
  intro T
  induction T with
  | store N =>
      intro X Y r x J _ _ _
      rfl
  | cr N t =>
      intro X Y r x J hWF _ hV
      obtain ⟨htN, hmin⟩ := hWF
      have hVc : Node.Valid N X Y x J := hV
      obtain ⟨hx, -, -, -⟩ := hVc
      show CR.dec N t (CR.sketch N t x) = some x
      refine hRec N t htN x hx ?_
      have h1 : x.card ≤ X + Y := Valid.card_le hV
      have h2 : x.card ≤ N := Valid.card_le_N hV
      have h3 : x.card ≤ min N (X + Y) := Nat.le_min.mpr ⟨h2, h1⟩
      omega
  | direct sch t =>
      intro X Y r x J hWF hB hV
      have htN : t ≤ sch.N := hWF
      obtain ⟨hx, -, -, -⟩ := hV
      have hZ : sch.Z r x J ≤ t := hB
      have hpref : (fun j : Fin sch.m =>
            (List.finRange sch.ℓ).map
              (fun s => if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0))
          = fun j => sch.truePrefix j (r.2 j) (sch.rowOf r x j) sch.ℓ := by
        funext j
        have htake : List.take sch.ℓ (List.finRange sch.ℓ) = List.finRange sch.ℓ :=
          List.take_of_length_le (le_of_eq (List.length_finRange (n := sch.ℓ)))
        show (List.finRange sch.ℓ).map
            (fun s => if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0)
          = sch.truePrefix j (r.2 j) (sch.rowOf r x j) sch.ℓ
        simp only [RowScheme.truePrefix, htake]
        refine List.map_congr_left ?_
        intro s _
        exact ite_mem_code (mem_column_iff sch r x s j)
      have hxe : sch.assembled r J (fun j : Fin sch.m =>
            (List.finRange sch.ℓ).map fun s =>
              if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0)
          = sch.exactEstimate r x J := by
        rw [hpref]
        rfl
      have hXe : sch.exactEstimate r x J ⊆ Finset.range sch.N :=
        assembled_subset_range sch r J _
      have hsub : symmDiff x (sch.exactEstimate r x J) ⊆ Finset.range sch.N :=
        symmDiff_subset_range hx hXe
      have hcard : (symmDiff x (sch.exactEstimate r x J)).card ≤ t := hZ
      have hdec := hRec sch.N t htN (symmDiff x (sch.exactEstimate r x J)) hsub hcard
      show Node.residual CR sch.N t (CR.sketch sch.N t x)
        (sch.assembled r J (fun j : Fin sch.m =>
          (List.finRange sch.ℓ).map fun s =>
            if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0)) = some x
      rw [hxe]
      unfold Node.residual
      rw [← sketch_symmDiff CR sch.N t x (sch.exactEstimate r x J), hdec,
        Option.map_some, Option.some.injEq]
      exact symmDiff_self_cancel _ _
  | recursive sch t Xs Ys child ih =>
      intro X Y r x J hWF hB hV
      obtain ⟨htN, hWFc⟩ := hWF
      obtain ⟨hZ, hUV⟩ := hB
      obtain ⟨hVx, hVc⟩ := hV
      show (sch.decodeColumns r.1 J (fun s Ps Js => Node.decode CR (child s) (r.2 s)
          (Node.synAdd (child s)
            (Node.sketch CR (child s) (r.2 s) (sch.column r.1 x s))
            (Node.sketch CR (child s) (r.2 s) Ps)) Js)).bind
        (fun pref => Node.residual CR sch.N t (CR.sketch sch.N t x)
          (sch.assembled r.1 J pref)) = some x
      set childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ) :=
        fun s Ps Js => Node.decode CR (child s) (r.2 s)
          (Node.synAdd (child s)
            (Node.sketch CR (child s) (r.2 s) (sch.column r.1 x s))
            (Node.sketch CR (child s) (r.2 s) Ps)) Js with hcd
      have hchild : ∀ s : Fin sch.ℓ,
          childDec s (sch.exactP r.1 x J s) (sch.exactHint r.1 x J s)
            = some (sch.exactChildInput r.1 x J s) := by
        intro s
        simp only [hcd]
        rw [synAdd_sketch]
        exact ih s (Xs s) (Ys s) (r.2 s) (sch.exactChildInput r.1 x J s)
          (sch.exactHint r.1 x J s) (hWFc s).2 (hUV s).2.2 (hVc s)
      have hstep : ∀ (k : ℕ) (hk : k < sch.ℓ),
          sch.decodeColumn r.1 J childDec (colPref sch r.1 x k) ⟨k, hk⟩
            = some (colPref sch r.1 x (k + 1)) :=
        fun k hk => decodeColumn_colPref sch r.1 J childDec x hchild k hk
      have hcols : sch.decodeColumns r.1 J childDec = some (colPref sch r.1 x sch.ℓ) :=
        decodeColumns_of_step sch r.1 J childDec x hstep
      rw [hcols]
      show Node.residual CR sch.N t (CR.sketch sch.N t x)
          (sch.assembled r.1 J (colPref sch r.1 x sch.ℓ)) = some x
      have hxe : sch.assembled r.1 J (colPref sch r.1 x sch.ℓ) = sch.exactEstimate r.1 x J := by
        rw [colPref_full]
        rfl
      have hXe : sch.exactEstimate r.1 x J ⊆ Finset.range sch.N :=
        assembled_subset_range sch r.1 J _
      have hsub : symmDiff x (sch.exactEstimate r.1 x J) ⊆ Finset.range sch.N :=
        symmDiff_subset_range hVx.1 hXe
      have hcard : (symmDiff x (sch.exactEstimate r.1 x J)).card ≤ t := hZ
      have hdec := hRec sch.N t htN (symmDiff x (sch.exactEstimate r.1 x J)) hsub hcard
      rw [hxe]
      unfold Node.residual
      rw [← sketch_symmDiff CR sch.N t x (sch.exactEstimate r.1 x J), hdec,
        Option.map_some, Option.some.injEq]
      exact symmDiff_self_cancel _ _


/-! ## 12.7  `hgood`

`hgood` is the statement that the last schedule call's decoded set is the support of `x`.  The last
call is the root's residual `CR` call (`decSched` appends it last at both `direct` and `recursive`
nodes), and the residual's output is *literally* `Node.decode`'s output:

* `cr` root: the only call is `CR.dec N t (CR.sketch N t x)`, and `decode` returns it;
* `direct` / `recursive` root: the residual returns `x̂ + CR.dec (a + CR x̂)`, and `decode` returns
  that.

So `hgood` has exactly one input beyond `decode_sketch`: the identification
`Φ (cnt - 1) = (Node.decode …).getD ∅`, i.e. the statement that `CrOutSpec`'s `Φ` at the last index
*is* the residual's output.  `hgood_lastCall` records the assumption-free form. -/

/-- Membership in a `ZMod 2` vector's support. -/
lemma mem_support {N : ℕ} (x : Fin N → ZMod 2) (i : Fin N) :
    i.val ∈ support x ↔ x i = 1 := by
  classical
  unfold support
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hv⟩
    have h2 := hj
    simp only [Finset.mem_filter] at h2
    have hji : j = i := Fin.ext hv
    rw [hji] at h2
    exact h2.2
  · intro h
    exact ⟨i, by
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩, rfl⟩


/-- **`hgood`**, Theorem 5.1 conjunct 8's remaining semantic hypothesis.

`hdec` is `decode_sketch` (the per-node success hypotheses); `hΦ` is the interface equation
identifying the last schedule call's set with the decode's answer.  Note that `hΦ` is *not* implied
by `hdec`: it is the statement that the last schedule item is the root's residual call and that the
call emits the residual's (not the raw `CR.dec`'s) set.  `hgood_lastCall` removes it by substituting
the right-hand side. -/
theorem hgood_of_decode (CR : CRFamily) (T : Node) (r : Node.Seed T) (J : Finset ℕ)
    {N : ℕ} (x : Fin N → ZMod 2) (Φ : ℕ → Finset ℕ) (cnt : ℕ)
    (hΦ : Φ (cnt - 1) = (Node.decode CR T r (Node.sketch CR T r (support x)) J).getD ∅)
    (hdec : Node.decode CR T r (Node.sketch CR T r (support x)) J = some (support x)) :
    ∀ i : Fin N, (i.val ∈ Φ (cnt - 1) ↔ x i = 1) := by
  intro i
  rw [hΦ, hdec]
  exact mem_support x i


/-- **`hgood` from the per-node hypotheses.**  Every semantic ingredient comes from
`decode_sketch`; the only remaining input is the interface equation `hΦ`. -/
theorem hgood_of_correct (CR : CRFamily) (hRec : CR.Recovers) (T : Node) (r : Node.Seed T)
    (J : Finset ℕ) (X Y : ℕ) {N : ℕ} (x : Fin N → ZMod 2) (Φ : ℕ → Finset ℕ) (cnt : ℕ)
    (hWF : Node.WF T X Y) (hB : Node.AllBounds T r (support x) J)
    (hV : AllValid X Y T r (support x) J)
    (hΦ : Φ (cnt - 1) = (Node.decode CR T r (Node.sketch CR T r (support x)) J).getD ∅) :
    ∀ i : Fin N, (i.val ∈ Φ (cnt - 1) ↔ x i = 1) :=
  hgood_of_decode CR T r J x Φ cnt hΦ
    (decode_sketch CR hRec T X Y r (support x) J hWF hB hV)


end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- `Node.decode` correctness (Theorem 6.5 conjunct 8): submission wrapper. -/
theorem solution (CR : CRFamily) (hRec : CR.Recovers) :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → AllValid X Y T r x J →
        Node.decode CR T r (Node.sketch CR T r x) J = some x :=
  LinearSetReconciliation327.Main.decode_sketch CR hRec
