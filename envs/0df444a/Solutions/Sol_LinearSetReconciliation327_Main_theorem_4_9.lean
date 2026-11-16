-- Prove2me | solution 1 for LinearSetReconciliation327.Main.theorem_4_9
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T14:31:19.128178+00:00
-- url     : https://prove2.me/submissions/a020a857-2f82-4e8d-9fbe-60f728cccfc7

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! ## Elementary helpers on row images, assembly and symmetric differences -/

open Classical in
lemma mem_rowImage {N m : ℕ} {π : Equiv.Perm (Fin N)} {j : ℕ} {S : Finset ℕ} {y : ℕ} :
    y ∈ rowImage N m π j S ↔
      ∃ i : Fin N, i.val ∈ S ∧ (π i).val % m = j ∧ (π i).val / m = y := by
  rw [rowImage, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Finset.mem_filter] at hi
    exact ⟨i, hi.2.1, hi.2.2, rfl⟩
  · rintro ⟨i, hS, hmod, hdiv⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hS, hmod⟩, hdiv⟩

open Classical in
lemma mem_assemble {N m : ℕ} {π : Equiv.Perm (Fin N)} {est : ℕ → Finset ℕ} {n : ℕ} :
    n ∈ assemble N m π est ↔
      ∃ i : Fin N, i.val = n ∧ (π i).val / m ∈ est ((π i).val % m) := by
  rw [assemble, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, rfl, h⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩, rfl⟩

open Classical in
lemma assemble_rowImage {N m : ℕ} (_hm : 0 < m) (π : Equiv.Perm (Fin N)) {x : Finset ℕ}
    (hx : x ⊆ range N) : assemble N m π (fun j => rowImage N m π j x) = x := by
  ext n
  rw [mem_assemble]
  constructor
  · rintro ⟨i, rfl, h⟩
    rw [mem_rowImage] at h
    obtain ⟨i', hi'x, hmod, hdiv⟩ := h
    have h1 := Nat.div_add_mod (π i').val m
    have h2 := Nat.div_add_mod (π i).val m
    rw [hmod, hdiv] at h1
    have : (π i').val = (π i).val := h1.symm.trans h2
    have hii : i' = i := π.injective (Fin.ext this)
    rwa [hii] at hi'x
  · intro hn
    have hnN : n < N := by simpa using hx hn
    refine ⟨⟨n, hnN⟩, rfl, ?_⟩
    rw [mem_rowImage]
    exact ⟨⟨n, hnN⟩, hn, rfl, rfl⟩

/-! ## Characteristic two arithmetic in `ZMod 2` -/

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h2 : (a.val : ZMod 2) = a := ZMod.natCast_zmod_val a
  have hv := ZMod.val_lt a
  rcases (show a.val = 0 ∨ a.val = 1 from by omega) with h0 | h1
  · left; rw [← h2, h0]; simp
  · right; rw [← h2, h1]; simp

lemma zmod2_add_eq_one_iff (a b : ZMod 2) :
    a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (b = 1 ∧ a = 0) := by
  rcases zmod2_cases a with ha | ha <;> rcases zmod2_cases b with hb | hb <;>
    subst ha <;> subst hb <;> simp [CharTwo.add_self_eq_zero]

lemma zmod2_eq_zero_iff_not_one (a : ZMod 2) : a = 0 ↔ ¬ a = 1 := by
  constructor
  · intro h h1
    rw [h] at h1
    exact absurd h1 (by decide)
  · intro h
    rcases zmod2_cases a with h0 | h1
    · exact h0
    · exact absurd h1 h

open Classical in
lemma zmod2_if (c : ZMod 2) : (if c = 1 then (1 : ZMod 2) else 0) = c := by
  rcases zmod2_cases c with h | h <;> simp [h]

/-! ## Basic set-theoretic helpers -/

open Classical in
lemma assemble_subset_range {N m : ℕ} (π : Equiv.Perm (Fin N)) (est : ℕ → Finset ℕ) :
    assemble N m π est ⊆ range N := by
  intro n hn
  rw [mem_assemble] at hn
  obtain ⟨i, rfl, _⟩ := hn
  exact Finset.mem_range.mpr i.isLt

open Classical in
lemma rowImage_subset_range {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (S : Finset ℕ) :
    rowImage N m π j S ⊆ range N := by
  intro n hn
  rw [mem_rowImage] at hn
  obtain ⟨i, _, _, hdiv⟩ := hn
  rw [← hdiv]
  exact Finset.mem_range.mpr (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (π i).isLt)

open Classical in
/-- Membership in `rowsWhere`, for a natural number index. -/
lemma mem_rowsWhere (sch : RowScheme) (P : Fin sch.m → Prop) {n : ℕ} :
    n ∈ RowScheme.rowsWhere sch P ↔ ∃ j : Fin sch.m, P j ∧ j.val = n := by
  unfold RowScheme.rowsWhere
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩

open Classical in
lemma rowsWhere_subset_range (sch : RowScheme) (P : Fin sch.m → Prop) :
    RowScheme.rowsWhere sch P ⊆ range sch.m := by
  intro n hn
  rw [mem_rowsWhere] at hn
  obtain ⟨j, _, rfl⟩ := hn
  exact Finset.mem_range.mpr j.isLt

/-- A logical skeleton: a unique-witness existential distributes over the "exclusive or". -/
lemma xor_exists {α : Type*} (P Q R : α → Prop)
    (huniq : ∀ i i', R i → R i' → i = i') :
    (∃ i, (P i ∧ ¬ Q i ∨ Q i ∧ ¬ P i) ∧ R i) ↔
      ((∃ i, P i ∧ R i) ∧ ¬ (∃ i, Q i ∧ R i)) ∨
      ((∃ i, Q i ∧ R i) ∧ ¬ (∃ i, P i ∧ R i)) := by
  constructor
  · rintro ⟨i, (⟨hP, hQ⟩ | ⟨hQ, hP⟩), hR⟩
    · left
      refine ⟨⟨i, hP, hR⟩, ?_⟩
      rintro ⟨i', hQ', hR'⟩
      have h : i' = i := huniq i' i hR' hR
      exact hQ (h ▸ hQ')
    · right
      refine ⟨⟨i, hQ, hR⟩, ?_⟩
      rintro ⟨i', hP', hR'⟩
      have h : i' = i := huniq i' i hR' hR
      exact hP (h ▸ hP')
  · rintro (⟨⟨i, hP, hR⟩, hQ⟩ | ⟨⟨i, hQ, hR⟩, hP⟩)
    · exact ⟨i, Or.inl ⟨hP, fun hqi => hQ ⟨i, hqi, hR⟩⟩, hR⟩
    · exact ⟨i, Or.inr ⟨hQ, fun hpi => hP ⟨i, hpi, hR⟩⟩, hR⟩

open Classical in
/-- The row image is additive in the set variable. -/
lemma rowImage_symmDiff {N m : ℕ} (π : Equiv.Perm (Fin N)) (j : ℕ) (x y : Finset ℕ) :
    rowImage N m π j (symmDiff x y) = symmDiff (rowImage N m π j x) (rowImage N m π j y) := by
  classical
  ext n
  simp only [mem_rowImage, mem_symmDiff]
  refine xor_exists (fun i : Fin N => i.val ∈ x) (fun i => i.val ∈ y)
    (fun i => (π i).val % m = j ∧ (π i).val / m = n) ?_
  rintro i i' ⟨h1, h2⟩ ⟨h1', h2'⟩
  apply π.injective
  apply Fin.ext
  have e1 : (π i).val = m * n + j := by
    have h := Nat.div_add_mod (π i).val m
    rw [h2, h1] at h
    exact h.symm
  have e2 : (π i').val = m * n + j := by
    have h := Nat.div_add_mod (π i').val m
    rw [h2', h1'] at h
    exact h.symm
  rw [e1, e2]

open Classical in
/-- The column support is additive in the set variable. -/
lemma column_symmDiff (sch : RowScheme) (lr : sch.LocalSeed) (x y : Finset ℕ)
    (s : Fin sch.ℓ) :
    sch.column lr (symmDiff x y) s = symmDiff (sch.column lr x s) (sch.column lr y s) := by
  classical
  have hrow : ∀ j : Fin sch.m, sch.rowOf lr (symmDiff x y) j
      = symmDiff (sch.rowOf lr x j) (sch.rowOf lr y j) := fun j =>
    rowImage_symmDiff lr.1 j.val x y
  have hpar : ∀ j : Fin sch.m,
      (sch.code j (lr.2 j) (sch.rowOf lr (symmDiff x y) j) s = 1) ↔
      ((sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 ∧
          ¬ sch.code j (lr.2 j) (sch.rowOf lr y j) s = 1) ∨
        (sch.code j (lr.2 j) (sch.rowOf lr y j) s = 1 ∧
          ¬ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1)) := by
    intro j
    rw [hrow j, sch.code_linear j (lr.2 j) (sch.rowOf lr x j) (sch.rowOf lr y j) s,
      zmod2_add_eq_one_iff, ← zmod2_eq_zero_iff_not_one, ← zmod2_eq_zero_iff_not_one]
  have hcol : sch.column lr (symmDiff x y) s
      = RowScheme.rowsWhere sch (fun j =>
          (sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 ∧
            ¬ sch.code j (lr.2 j) (sch.rowOf lr y j) s = 1) ∨
          (sch.code j (lr.2 j) (sch.rowOf lr y j) s = 1 ∧
            ¬ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1)) := by
    unfold RowScheme.column
    congr 1
    funext j
    exact propext (hpar j)
  ext n
  rw [hcol]
  simp only [RowScheme.column, mem_rowsWhere, mem_symmDiff]
  refine xor_exists (fun j : Fin sch.m => sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1)
    (fun j => sch.code j (lr.2 j) (sch.rowOf lr y j) s = 1) (fun j => j.val = n) ?_
  rintro i i' h h'
  exact Fin.ext (h.trans h'.symm)

/-! ## Linearity of the sketches -/

open Classical in
lemma odd_filter_symmDiff (C D : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Odd ((symmDiff C D).filter P).card ↔
      (Odd (C.filter P).card ∧ ¬ Odd (D.filter P).card) ∨
      (Odd (D.filter P).card ∧ ¬ Odd (C.filter P).card) := by
  classical
  have hcast : ∀ S : Finset ℕ,
      ((S.filter P).card : ZMod 2) = ∑ v ∈ S, (if P v then (1 : ZMod 2) else 0) := by
    intro S
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    exact Finset.sum_filter P (fun _ => (1 : ZMod 2))
  have hsum := sum_symmDiff_char_two (A := ZMod 2)
    (fun a => CharTwo.add_self_eq_zero a) C D (fun v => if P v then (1 : ZMod 2) else 0)
  have key : (((symmDiff C D).filter P).card : ZMod 2)
      = ((C.filter P).card : ZMod 2) + ((D.filter P).card : ZMod 2) := by
    rw [hcast, hcast, hcast, hsum]
  rw [← ZMod.natCast_eq_one_iff_odd (n := ((symmDiff C D).filter P).card), key]
  conv_rhs => simp only [← ZMod.natCast_eq_one_iff_odd, ← zmod2_eq_zero_iff_not_one]
  exact zmod2_add_eq_one_iff _ _

open Classical in
/-- The `CR` sketch is additive in the set variable. -/
lemma sketch_symmDiff (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    CR.sketch N t (symmDiff x y) = symmDiff (CR.sketch N t x) (CR.sketch N t y) := by
  classical
  ext r
  simp only [CRFamily.sketch, Finset.mem_filter, Finset.mem_range, Finset.mem_symmDiff]
  by_cases hr : r < CR.rows N t
  · simp only [hr, true_and]
    exact odd_filter_symmDiff x y (fun i => r ∈ CR.col N t i)
  · simp [hr]

open Classical in
/-- The sketch of a tree is additive with respect to `synAdd`. -/
theorem sketch_synAdd (CR : CRFamily) :
    ∀ (T : Node) (x y : Finset ℕ) (r : T.Seed),
      T.sketch CR r (symmDiff x y) = T.synAdd (T.sketch CR r x) (T.sketch CR r y) := by
  intro T
  induction T with
  | store N => intro x y r; rfl
  | cr N t => intro x y r; exact sketch_symmDiff CR N t x y
  | direct sch t =>
      intro x y r
      simp only [Node.sketch, Node.synAdd]
      rw [sketch_symmDiff CR sch.N t x y]
      refine Prod.ext ?_ ?_
      · funext s
        exact column_symmDiff sch r x y s
      · rfl
  | recursive sch t Xs Ys child ih =>
      intro x y r
      obtain ⟨lr, rc⟩ := r
      simp only [Node.sketch, Node.synAdd]
      rw [sketch_symmDiff CR sch.N t x y]
      refine Prod.ext ?_ ?_
      · funext s
        simp only []
        rw [column_symmDiff sch lr x y s]
        exact ih s (sch.column lr x s) (sch.column lr y s) (rc s)
      · rfl

/-! ## Cardinality of the exact hint and the "valid child" facts -/

open Classical in
lemma exactHint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) : (sch.exactHint lr x J s).card = sch.U lr x J s := by
  unfold RowScheme.exactHint RowScheme.U RowScheme.rowsWhere
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  apply Finset.ext
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
lemma exactHint_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) : sch.exactHint lr x J s ⊆ range sch.m := by
  unfold RowScheme.exactHint
  exact rowsWhere_subset_range sch _

open Classical in
lemma exactChildInput_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) : sch.exactChildInput lr x J s ⊆ range sch.m := by
  intro n hn
  rw [RowScheme.exactChildInput, mem_symmDiff] at hn
  rcases hn with ⟨h, _⟩ | ⟨h, _⟩
  · exact rowsWhere_subset_range sch (fun j => sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1) h
  · exact rowsWhere_subset_range sch (fun j => sch.exactPred lr x J s j = some 1) h

open Classical in
lemma mem_column_iff (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.column lr x s ↔ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := by
  rw [RowScheme.column, mem_rowsWhere]
  constructor
  · rintro ⟨j', h, hj'⟩
    have hje : j' = j := Fin.ext hj'
    rwa [hje] at h
  · intro h
    exact ⟨j, h, rfl⟩

open Classical in
lemma mem_exactP_iff (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := by
  rw [RowScheme.exactP, mem_rowsWhere]
  constructor
  · rintro ⟨j', h, hj'⟩
    have hje : j' = j := Fin.ext hj'
    rwa [hje] at h
  · intro h
    exact ⟨j, h, rfl⟩

open Classical in
lemma mem_exactHint_iff (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := by
  rw [RowScheme.exactHint, mem_rowsWhere]
  constructor
  · rintro ⟨j', h, hj'⟩
    have hje : j' = j := Fin.ext hj'
    rwa [hje] at h
  · intro h
    exact ⟨j, h, rfl⟩

open Classical in
/-- Every row that is in the child's input but not in the child's hint is a wrong prediction. -/
lemma exactChildInput_sdiff_hint_subset (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    sch.exactChildInput lr x J s \ sch.exactHint lr x J s ⊆
      RowScheme.rowsWhere sch (fun j => ∃ b, sch.exactPred lr x J s j = some b ∧
        b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s) := by
  intro n hn
  rw [Finset.mem_sdiff, RowScheme.exactChildInput, mem_symmDiff] at hn
  obtain ⟨hCP, hhint⟩ := hn
  rw [mem_rowsWhere]
  rcases hCP with ⟨hC, hP⟩ | ⟨hP, hC⟩
  · obtain ⟨j, hcode, hj⟩ := (mem_rowsWhere sch
        (fun j => sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1)).mp hC
    have hne : sch.exactPred lr x J s j ≠ none := by
      intro h
      have hmem : j.val ∈ sch.exactHint lr x J s := (mem_exactHint_iff sch lr x J s j).mpr h
      rw [hj] at hmem
      exact hhint hmem
    obtain ⟨b, hb⟩ : ∃ b, sch.exactPred lr x J s j = some b := by
      cases h : sch.exactPred lr x J s j with
      | none => exact absurd h hne
      | some b => exact ⟨b, rfl⟩
    have hb1 : b ≠ 1 := by
      intro h1
      have hmem : j.val ∈ sch.exactP lr x J s :=
        (mem_exactP_iff sch lr x J s j).mpr (by rw [hb, h1])
      rw [hj] at hmem
      exact hP hmem
    exact ⟨j, ⟨b, hb, by rw [hcode]; exact hb1⟩, hj⟩
  · obtain ⟨j, hp, hj⟩ := (mem_rowsWhere sch
        (fun j => sch.exactPred lr x J s j = some 1)).mp hP
    have hncol : j.val ∉ sch.column lr x s := by rw [hj]; exact hC
    rw [mem_column_iff] at hncol
    have hcode0 : sch.code j (lr.2 j) (sch.rowOf lr x j) s = 0 := by
      rcases zmod2_cases _ with h | h
      · exact h
      · exact absurd h hncol
    exact ⟨j, ⟨1, hp, by rw [hcode0]; exact one_ne_zero⟩, hj⟩

open Classical in
/-- The children's `Y` bound holds at the exact input and hint. -/
lemma exactChildInput_sdiff_hint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    (sch.exactChildInput lr x J s \ sch.exactHint lr x J s).card ≤ sch.V lr x J s := by
  refine le_trans (Finset.card_le_card (exactChildInput_sdiff_hint_subset sch lr x J s)) ?_
  unfold RowScheme.V RowScheme.rowsWhere
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  apply le_of_eq
  congr 1
  apply Finset.ext
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- The exact row estimate is contained in the universe. -/
lemma assembled_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (pref : Fin sch.m → List (ZMod 2)) : sch.assembled lr J pref ⊆ range sch.N :=
  assemble_subset_range lr.1 _

open Classical in
lemma exactEstimate_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) :
    sch.exactEstimate lr x J ⊆ range sch.N :=
  assembled_subset_range sch lr J _

open Classical in
/-- If every column is decoded correctly, so is the whole node. -/
lemma decodeColumns_eq_true (sch : RowScheme) (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ)) (x : Finset ℕ)
    (hstep : ∀ (s : Fin sch.ℓ) (pref : Fin sch.m → List (ZMod 2)),
      (∀ j, pref j = sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) s.val) →
      sch.decodeColumn lr J childDec pref s =
        some (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) (s.val + 1))) :
    sch.decodeColumns lr J childDec =
      some (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ) := by
  classical
  have key : ∀ k ≤ sch.ℓ,
      List.foldlM (sch.decodeColumn lr J childDec) (fun _ => ([] : List (ZMod 2)))
        ((List.finRange sch.ℓ).take k) =
        some (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [RowScheme.truePrefix]
    | succ k ih =>
        intro hk
        have hk' : k < sch.ℓ := Nat.lt_of_succ_le hk
        have hidx : k < (List.finRange sch.ℓ).length := by
          rw [List.length_finRange]; exact hk'
        have hget : (List.finRange sch.ℓ)[k]'hidx = ⟨k, hk'⟩ := by
          rw [List.getElem_finRange]
          exact Fin.ext rfl
        have htake : (List.finRange sch.ℓ).take (k + 1)
            = (List.finRange sch.ℓ).take k ++ [⟨k, hk'⟩] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hidx, hget]
          rfl
        rw [htake, List.foldlM_append, ih (Nat.le_of_lt hk')]
        simpa using (hstep ⟨k, hk'⟩
          (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) k) (fun j => rfl))
  unfold RowScheme.decodeColumns
  rw [← List.take_of_length_le (show (List.finRange sch.ℓ).length ≤ sch.ℓ by simp)]
  exact key sch.ℓ (le_refl _)

/-! Part (i) of Theorem 4.9: if all the capacity bounds of the subtree hold, the node recovers `x`. -/
set_option maxHeartbeats 1000000 in
theorem decode_eq_of_allBounds (CR : CRFamily) (hCR : CR.Recovers) :
    ∀ (T : Node) (X Y : ℕ) (r : T.Seed) (x J : Finset ℕ),
      T.WF X Y → Node.Valid T.N X Y x J → T.AllBounds r x J →
      T.decode CR r (T.sketch CR r x) J = some x := by
  classical
  intro T
  induction T with
  | store N =>
      intro X Y r x J hWF hvalid hAll
      rfl
  | cr N t =>
      intro X Y r x J hWF hvalid hAll
      simp only [Node.WF] at hWF
      obtain ⟨hxN, hJN, hJcard, hYcard⟩ := hvalid
      have hcardN : x.card ≤ N := by
        have h := Finset.card_le_card hxN
        simpa [Node.N] using h
      have hcardXY : x.card ≤ X + Y := by
        have hsub : x = (x \ J) ∪ (x ∩ J) := by
          ext i
          simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          tauto
        have hdisj : Disjoint (x \ J) (x ∩ J) := by
          rw [Finset.disjoint_left]
          intro a ha hb
          exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
        rw [hsub, Finset.card_union_of_disjoint hdisj]
        have h1 : (x ∩ J).card ≤ J.card := Finset.card_le_card Finset.inter_subset_right
        omega
      have hcard : x.card ≤ t := le_trans (le_min hcardN hcardXY) hWF.2
      simpa only [Node.decode, Node.sketch] using hCR N t hWF.1 x hxN hcard
  | direct sch t =>
      intro X Y r x J hWF hvalid hAll
      simp only [Node.WF] at hWF
      obtain ⟨hxN, hJN, hJcard, hYcard⟩ := hvalid
      have hpref : (fun j : Fin sch.m => (List.finRange sch.ℓ).map
            (fun s => if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0))
          = fun j => sch.truePrefix j (r.2 j) (sch.rowOf r x j) sch.ℓ := by
        funext j
        have hfun : (fun s : Fin sch.ℓ => if j.val ∈ sch.column r x s then (1 : ZMod 2) else 0)
            = fun s => sch.code j (r.2 j) (sch.rowOf r x j) s := by
          funext s
          have hiff := mem_column_iff sch r x s j
          by_cases h : j.val ∈ sch.column r x s
          · rw [if_pos h, hiff.mp h]
          · have hc : ¬ (sch.code j (r.2 j) (sch.rowOf r x j) s = 1) := fun h1 => h (hiff.mpr h1)
            have h0 : sch.code j (r.2 j) (sch.rowOf r x j) s = 0 := by
              rcases zmod2_cases _ with h' | h'
              · exact h'
              · exact absurd h' hc
            rw [if_neg h, h0]
        rw [hfun, RowScheme.truePrefix, List.take_of_length_le (by simp)]
      rw [Node.decode, Node.sketch]
      rw [hpref]
      change Node.residual CR sch.N t (CR.sketch sch.N t x) (sch.exactEstimate r x J) = some x
      unfold Node.residual
      rw [← sketch_symmDiff CR sch.N t x (sch.exactEstimate r x J)]
      have hsub : symmDiff x (sch.exactEstimate r x J) ⊆ range sch.N := by
        intro n hn
        rw [mem_symmDiff] at hn
        rcases hn with ⟨h, _⟩ | ⟨h, _⟩
        · exact hxN h
        · exact exactEstimate_subset_range sch r x J h
      rw [hCR sch.N t hWF (symmDiff x (sch.exactEstimate r x J)) hsub hAll]
      simp only [Option.map_some, Option.some.injEq]
      rw [symmDiff_comm x (sch.exactEstimate r x J)]
      exact symmDiff_symmDiff_cancel_left _ _
  | recursive sch t Xs Ys child ih =>
      intro X Y r x J hWF hvalid hAll
      simp only [Node.WF] at hWF
      obtain ⟨hWFt, hWFchild⟩ := hWF
      obtain ⟨hxN, hJN, hJcard, hYcard⟩ := hvalid
      let lr : sch.LocalSeed := r.1
      let rc : (s : Fin sch.ℓ) → (child s).Seed := r.2
      simp only [Node.AllBounds] at hAll
      obtain ⟨hZ, hU⟩ := hAll
      have hvalid_child : ∀ s, Node.Valid (child s).N (Xs s) (Ys s)
          (sch.exactChildInput lr x J s) (sch.exactHint lr x J s) := by
        intro s
        have hNm : (child s).N = sch.m := (hWFchild s).1
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hNm]
          exact exactChildInput_subset_range sch lr x J s
        · rw [hNm]
          exact exactHint_subset_range sch lr x J s
        · rw [exactHint_card]
          exact (hU s).1
        · exact le_trans (exactChildInput_sdiff_hint_card sch lr x J s) (hU s).2.1
      let childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ) := fun s Ps Js =>
        Node.decode CR (child s) (rc s)
          (Node.synAdd (child s) (Node.sketch CR (child s) (rc s) (sch.column lr x s))
            (Node.sketch CR (child s) (rc s) Ps)) Js
      have hchild : ∀ s : Fin sch.ℓ,
          childDec s (sch.exactP lr x J s) (sch.exactHint lr x J s)
            = some (sch.exactChildInput lr x J s) := by
        intro s
        rw [show childDec s (sch.exactP lr x J s) (sch.exactHint lr x J s)
            = Node.decode CR (child s) (rc s)
              (Node.synAdd (child s) (Node.sketch CR (child s) (rc s) (sch.column lr x s))
                (Node.sketch CR (child s) (rc s) (sch.exactP lr x J s)))
              (sch.exactHint lr x J s) from rfl]
        rw [← sketch_synAdd CR (child s) (sch.column lr x s) (sch.exactP lr x J s) (rc s)]
        exact ih s (Xs s) (Ys s) (rc s) (sch.exactChildInput lr x J s) (sch.exactHint lr x J s)
          ((hWFchild s).2) (hvalid_child s) ((hU s).2.2)
      have hstep : ∀ (s : Fin sch.ℓ) (pref : Fin sch.m → List (ZMod 2)),
          (∀ j, pref j = sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) s.val) →
          sch.decodeColumn lr J childDec pref s =
            some (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) (s.val + 1)) := by
        intro s pref hpref
        have hPs : (fun j : Fin sch.m => sch.predict j (lr.2 j) (sch.rowOf lr J j) (pref j) = some 1)
            = (fun j => sch.exactPred lr x J s j = some 1) := by
          funext j
          rw [hpref j, RowScheme.exactPred]
        have hJs : (fun j : Fin sch.m => sch.predict j (lr.2 j) (sch.rowOf lr J j) (pref j) = none)
            = (fun j => sch.exactPred lr x J s j = none) := by
          funext j
          rw [hpref j, RowScheme.exactPred]
        dsimp only [RowScheme.decodeColumn, childDec]
        simp only [hPs, hJs]
        change (childDec s (sch.exactP lr x J s) (sch.exactHint lr x J s)).map
          (fun Dhat j => pref j ++ [if j.val ∈
            symmDiff (sch.exactP lr x J s) Dhat then (1 : ZMod 2) else 0])
          = some (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) (s.val + 1))
        rw [hchild s, Option.map_some]
        congr 1
        funext j
        have hsym : symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s)
            = sch.column lr x s := by
          rw [RowScheme.exactChildInput,
            symmDiff_comm (sch.column lr x s) (sch.exactP lr x J s)]
          exact symmDiff_symmDiff_cancel_left _ _
        have hbit : (if j.val ∈ symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s)
            then (1 : ZMod 2) else 0) = sch.code j (lr.2 j) (sch.rowOf lr x j) s := by
          by_cases hmem : j.val ∈ symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s)
          · rw [if_pos hmem]
            have hc : j.val ∈ sch.column lr x s := by rwa [← hsym]
            exact ((mem_column_iff sch lr x s j).mp hc).symm
          · rw [if_neg hmem]
            have hc : j.val ∉ sch.column lr x s := by rwa [← hsym]
            rw [mem_column_iff sch lr x s j] at hc
            rcases zmod2_cases (sch.code j (lr.2 j) (sch.rowOf lr x j) s) with h | h
            · exact h.symm
            · exact absurd h hc
        rw [hbit, hpref j]
        simp only [RowScheme.truePrefix]
        have hidx : s.val < (List.finRange sch.ℓ).length := by
          rw [List.length_finRange]; exact s.isLt
        have hget : (List.finRange sch.ℓ)[s.val]'hidx = s := by
          rw [List.getElem_finRange]
          exact Fin.ext rfl
        have htake : (List.finRange sch.ℓ).take (s.val + 1)
            = (List.finRange sch.ℓ).take s.val ++ [s] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hidx, hget]
          rfl
        rw [htake, List.map_append, List.map_singleton]
      have hdc := decodeColumns_eq_true sch lr J childDec x hstep
      rw [Node.decode, Node.sketch]
      change (sch.decodeColumns lr J childDec).bind (fun pref =>
        Node.residual CR sch.N t (CR.sketch sch.N t x) (sch.assembled lr J pref)) = some x
      rw [hdc]
      simp only [Option.bind_some]
      change Node.residual CR sch.N t (CR.sketch sch.N t x) (sch.exactEstimate lr x J) = some x
      unfold Node.residual
      rw [← sketch_symmDiff CR sch.N t x (sch.exactEstimate lr x J)]
      have hsub : symmDiff x (sch.exactEstimate lr x J) ⊆ range sch.N := by
        intro n hn
        rw [mem_symmDiff] at hn
        rcases hn with ⟨h, _⟩ | ⟨h, _⟩
        · exact hxN h
        · exact exactEstimate_subset_range sch lr x J h
      rw [hCR sch.N t hWFt (symmDiff x (sch.exactEstimate lr x J)) hsub hZ]
      simp only [Option.map_some, Option.some.injEq]
      rw [symmDiff_comm x (sch.exactEstimate lr x J)]
      exact symmDiff_symmDiff_cancel_left _ _

/-! ## Uniform probability estimates (part (ii) of Theorem 4.9) -/

def seedNonempty : (T : Node) → Nonempty (Node.Seed T)
  | .store _ => ⟨()⟩
  | .cr _ _ => ⟨()⟩
  | .direct sch _ =>
      ⟨((Equiv.refl (Fin sch.N), fun _ => Classical.choice (inferInstance : Nonempty sch.Rand)) :
        sch.LocalSeed)⟩
  | .recursive sch _ _ _ child =>
      ⟨((Equiv.refl (Fin sch.N), fun _ => Classical.choice (inferInstance : Nonempty sch.Rand)),
        fun s => Classical.choice (seedNonempty (child s)))⟩

instance (T : Node) : Nonempty (Node.Seed T) := seedNonempty T

open Classical in
/-- `prU` as a ratio of cardinalities, for an explicitly given decidability instance. -/
lemma prU_eq_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    prU P = ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  unfold prU
  exact congrArg (fun n : ℕ => (n : ℝ) / (Fintype.card α : ℝ))
    (congrArg Finset.card (Finset.filter_congr_decidable Finset.univ P _))

open Classical in
lemma prU_mono {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    prU P ≤ prU Q := by
  rw [prU_eq_card P, prU_eq_card Q]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact h a ha
  exact_mod_cast Finset.card_le_card hsub

open Classical in
lemma prU_nonneg {α : Type} [Fintype α] (P : α → Prop) : 0 ≤ prU P := by
  rw [prU_eq_card P]
  positivity

open Classical in
lemma prU_false {α : Type} [Fintype α] : prU (fun _ : α => False) = 0 := by
  rw [prU_eq_card (fun _ : α => False)]
  simp

open Classical in
lemma prU_true {α : Type} [Fintype α] [Nonempty α] : prU (fun _ : α => True) = 1 := by
  rw [prU_eq_card (fun _ : α => True)]
  simp only [Finset.filter_true, Finset.card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

open Classical in
lemma prU_or_le {α : Type} [Fintype α] [Nonempty α] (P Q : α → Prop) :
    prU (fun a => P a ∨ Q a) ≤ prU P + prU Q := by
  have hcard : (Finset.univ.filter (fun a => P a ∨ Q a)).card
      ≤ (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
    have hsub : Finset.univ.filter (fun a => P a ∨ Q a)
        ⊆ (Finset.univ.filter P) ∪ (Finset.univ.filter Q) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ha ⊢
      exact ha
    calc (Finset.univ.filter (fun a => P a ∨ Q a)).card
        ≤ ((Finset.univ.filter P) ∪ (Finset.univ.filter Q)).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  calc prU (fun a => P a ∨ Q a)
      = ((Finset.univ.filter (fun a => P a ∨ Q a)).card : ℝ) / (Fintype.card α : ℝ) :=
        prU_eq_card _
    _ ≤ (((Finset.univ.filter P).card + (Finset.univ.filter Q).card : ℕ) : ℝ)
          / (Fintype.card α : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)
          + ((Finset.univ.filter Q).card : ℝ) / (Fintype.card α : ℝ) := by
        push_cast
        ring
    _ = prU P + prU Q := by rw [prU_eq_card P, prU_eq_card Q]

open Classical in
lemma prU_le_sum {α ι : Type} [Fintype α] [Nonempty α] (P : α → Prop)
    (s : Finset ι) (Q : ι → α → Prop) (h : ∀ a, P a → ∃ i ∈ s, Q i a) :
    prU P ≤ ∑ i ∈ s, prU (Q i) := by
  have hsub : Finset.univ.filter P ⊆ s.biUnion (fun i => Finset.univ.filter (Q i)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨i, hi, hia⟩ := h a ha
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [hia]⟩
  have hcard : (Finset.univ.filter P).card ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := by
    calc (Finset.univ.filter P).card
        ≤ (s.biUnion (fun i => Finset.univ.filter (Q i))).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ s, (Finset.univ.filter (Q i)).card := Finset.card_biUnion_le
  calc prU P = ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := prU_eq_card P
    _ ≤ (∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ)) / (Fintype.card α : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = ∑ i ∈ s, ((Finset.univ.filter (Q i)).card : ℝ) / (Fintype.card α : ℝ) := by
        rw [Finset.sum_div]
    _ = ∑ i ∈ s, prU (Q i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [prU_eq_card (Q i)]

open Classical in
lemma prU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop)
    [DecidablePred P] :
    prU (fun a => P (e a)) = prU P := by
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hf : Fintype.card {a : α // P (e a)} = Fintype.card {b : β // P b} :=
    Fintype.card_congr (e.subtypeEquiv (fun a => Iff.rfl))
  rw [prU_eq_card (fun a => P (e a)), prU_eq_card P, hcard,
    ← Fintype.card_subtype (fun a : α => P (e a)), ← Fintype.card_subtype P, hf]

open Classical in
lemma card_prod_filter {α β : Type} [Fintype α] [Fintype β] (R : α × β → Prop) :
    (Finset.univ.filter R).card = ∑ a : α, (Finset.univ.filter (fun b => R (a, b))).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

open Classical in
lemma prU_prod_eq {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (R : α × β → Prop) :
    prU R = (∑ a : α, prU (fun b : β => R (a, b))) / (Fintype.card α : ℝ) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    have h := Fintype.card_pos (α := α); exact_mod_cast h.ne'
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    have h := Fintype.card_pos (α := β); exact_mod_cast h.ne'
  have hS : ((Finset.univ.filter R).card : ℝ)
      = ∑ a : α, ((Finset.univ.filter (fun b => R (a, b))).card : ℝ) := by
    rw [card_prod_filter R]; push_cast; rfl
  have hR : ∀ a : α, prU (fun b : β => R (a, b))
      = ((Finset.univ.filter (fun b => R (a, b))).card : ℝ) * ((Fintype.card β : ℝ))⁻¹ := by
    intro a
    rw [prU_eq_card (fun b => R (a, b)), div_eq_mul_inv]
  rw [prU_eq_card R, hS, Fintype.card_prod, Nat.cast_mul]
  simp only [div_eq_mul_inv, hR]
  rw [← Finset.sum_mul, mul_inv_rev, mul_assoc]

open Classical in
lemma prU_prod_fst {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (P : α → Prop) : prU (fun p : α × β => P p.1) = prU P := by
  have hfilt : (Finset.univ.filter (fun p : α × β => P p.1))
      = (Finset.univ.filter P) ×ˢ (Finset.univ : Finset β) := by
    ext p
    simp
  rw [prU_eq_card (fun p : α × β => P p.1), prU_eq_card P, hfilt, Finset.card_product,
    Finset.card_univ, Fintype.card_prod]
  push_cast
  field_simp

open Classical in
/-- Splitting a dependent function type at one coordinate. -/
def piEquivProd {ι : Type} [DecidableEq ι] (β : ι → Type) (i : ι) :
    (∀ j, β j) ≃ β i × ((j : {j : ι // j ≠ i}) → β j) where
  toFun f := (f i, fun j => f j.1)
  invFun p := fun j => if h : j = i then h.symm ▸ p.1 else p.2 ⟨j, h⟩
  left_inv f := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  right_inv p := by
    obtain ⟨b, g⟩ := p
    ext j
    · simp
    · simp [j.2]

open Classical in
set_option maxHeartbeats 1000000 in
/-- The marginal of the uniform law on a product of finitely many finite types. -/
lemma prU_pi_marginal {ι : Type} [Fintype ι] [DecidableEq ι]
    {β : ι → Type} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (i : ι) (P : β i → Prop) :
    prU (fun f : (∀ j, β j) => P (f i)) = prU P := by
  haveI : Nonempty ((j : {j : ι // j ≠ i}) → β j) := ⟨fun j => Classical.choice inferInstance⟩
  have he : ∀ f : (∀ j, β j), ((piEquivProd β i) f).1 = f i := fun f => rfl
  rw [show (fun f : (∀ j, β j) => P (f i))
      = (fun f => P (((piEquivProd β i) f).1)) from funext (fun f => by rw [he f])]
  have h2 := prU_equiv (piEquivProd β i)
    (fun p : β i × ((j : {j : ι // j ≠ i}) → β j) => P p.1)
  rw [h2]
  exact prU_prod_fst P

/-! ## Generic union bounds on products and on dependent function spaces -/

open Classical in
/-- A bound on a product, obtained fiberwise over the first coordinate. -/
lemma prU_prod_le {α β : Type} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (R : α → β → Prop) (B : ℝ) (h : ∀ a, prU (R a) ≤ B) :
    prU (fun p : α × β => R p.1 p.2) ≤ B := by
  rw [prU_prod_eq (fun p : α × β => R p.1 p.2)]
  have h2 : ∑ a : α, prU (fun b : β => R a b) ≤ ∑ _a : α, B :=
    Finset.sum_le_sum (fun a _ => h a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos (α := α))]
  calc ∑ a : α, prU (fun b : β => R a b) ≤ (Fintype.card α : ℝ) * B := h2
    _ = B * (Fintype.card α : ℝ) := by ring

open Classical in
/-- The arithmetic of the union bound at a recursive node. -/
lemma prU_arith_bound {ι : Type} [Fintype ι] (δ : ℝ) (c : ι → ℕ) :
    δ + ∑ i, (δ + δ + (c i : ℝ) * δ)
      = ((2 * Fintype.card ι + 1 + ∑ i, c i : ℕ) : ℝ) * δ := by
  have h1 : ∀ i : ι, δ + δ + (c i : ℝ) * δ = (2 + (c i : ℝ)) * δ := fun i => by ring
  simp only [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ i : ι, (2 + (c i : ℝ)) = 2 * (Fintype.card ι : ℝ) + ((∑ i, c i : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, ← Nat.cast_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [h2]
  push_cast
  ring

open Classical in
/-- The union bound at a recursive node, in abstract form.  The single-node bounds depend only on
the local seed `α`, the child bounds only on the corresponding coordinate of the children's seeds;
the child bound is applied under the additional assumption that the two `U`, `V` bounds of the
parent hold, which is what makes the child input valid. -/
lemma prU_prod_union_bound {α : Type} [Fintype α] [Nonempty α]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {β : ι → Type} [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)]
    (Pz : α → Prop) (Pu Pv : ι → α → Prop) (Pc : ι → α → (∀ i, β i) → Prop)
    (δ : ℝ) (c : ι → ℕ)
    (hZ : prU Pz ≤ δ) (hU : ∀ i, prU (Pu i) ≤ δ) (hV : ∀ i, prU (Pv i) ≤ δ)
    (hC : ∀ i a, ¬ (Pu i a ∨ Pv i a) → prU (fun g : ∀ j, β j => Pc i a g) ≤ (c i : ℝ) * δ)
    (hδ : 0 ≤ δ) :
    prU (fun p : α × (∀ i, β i) =>
        Pz p.1 ∨ ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)) ≤
      ((2 * Fintype.card ι + 1 + ∑ i, c i : ℕ) : ℝ) * δ := by
  have hstep : ∀ i : ι, prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)
      ≤ δ + δ + (c i : ℝ) * δ := by
    intro i
    have h1 : prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)
        ≤ prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1)
          + prU (fun p : α × (∀ j, β j) => ¬ (Pu i p.1 ∨ Pv i p.1) ∧ Pc i p.1 p.2) := by
      have hpe : (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)
          = (fun p : α × (∀ j, β j) =>
              (Pu i p.1 ∨ Pv i p.1) ∨ (¬ (Pu i p.1 ∨ Pv i p.1) ∧ Pc i p.1 p.2)) := by
        funext p
        apply propext
        tauto
      rw [hpe]
      exact prU_or_le _ _
    have h2 : prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1)
        ≤ prU (fun p : α × (∀ j, β j) => Pu i p.1)
          + prU (fun p : α × (∀ j, β j) => Pv i p.1) := prU_or_le _ _
    have h3 : prU (fun p : α × (∀ j, β j) => Pu i p.1) ≤ δ := by
      rw [prU_prod_fst]
      exact hU i
    have h4 : prU (fun p : α × (∀ j, β j) => Pv i p.1) ≤ δ := by
      rw [prU_prod_fst]
      exact hV i
    have h5 : prU (fun p : α × (∀ j, β j) => ¬ (Pu i p.1 ∨ Pv i p.1) ∧ Pc i p.1 p.2)
        ≤ (c i : ℝ) * δ := by
      refine prU_prod_le (R := fun a g => ¬ (Pu i a ∨ Pv i a) ∧ Pc i a g)
        ((c i : ℝ) * δ) ?_
      intro a
      by_cases ha : Pu i a ∨ Pv i a
      · have hpe : (fun g : ∀ j, β j => ¬ (Pu i a ∨ Pv i a) ∧ Pc i a g)
            = (fun _ => False) := by
          funext g
          exact propext ⟨fun h => h.1 ha, fun h => False.elim h⟩
        rw [hpe, prU_false]
        exact mul_nonneg (Nat.cast_nonneg _) hδ
      · have hpe : (fun g : ∀ j, β j => ¬ (Pu i a ∨ Pv i a) ∧ Pc i a g)
            = (fun g => Pc i a g) := by
          funext g
          exact propext ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
        rw [hpe]
        exact hC i a ha
    linarith
  have hZsum : prU (fun p : α × (∀ j, β j) =>
        Pz p.1 ∨ ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2))
      ≤ prU (fun p : α × (∀ j, β j) => Pz p.1)
        + prU (fun p : α × (∀ j, β j) => ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)) :=
    prU_or_le _ _
  have hZ2 : prU (fun p : α × (∀ j, β j) => Pz p.1) ≤ δ := by
    rw [prU_prod_fst]
    exact hZ
  have hsum : prU (fun p : α × (∀ j, β j) => ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2))
      ≤ ∑ i, prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2) :=
    prU_le_sum _ _ _ (by
      intro a ha
      obtain ⟨i, hi⟩ := ha
      exact ⟨i, Finset.mem_univ i, hi⟩)
  calc prU (fun p : α × (∀ j, β j) =>
        Pz p.1 ∨ ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2))
      ≤ prU (fun p : α × (∀ j, β j) => Pz p.1)
        + prU (fun p : α × (∀ j, β j) => ∃ i, (Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2)) := hZsum
    _ ≤ δ + ∑ i, prU (fun p : α × (∀ j, β j) => Pu i p.1 ∨ Pv i p.1 ∨ Pc i p.1 p.2) :=
        add_le_add hZ2 hsum
    _ ≤ δ + ∑ i, (δ + δ + (c i : ℝ) * δ) :=
        add_le_add (le_refl δ) (Finset.sum_le_sum (fun i _ => hstep i))
    _ = ((2 * Fintype.card ι + 1 + ∑ i, c i : ℕ) : ℝ) * δ := prU_arith_bound δ c

/-! ## Part (ii) of Theorem 4.9 -/

set_option maxHeartbeats 4000000 in
/-- Part (ii) of Theorem 4.9: the probability that some capacity bound fails is at most
`boundCount · δ`. -/
theorem allBounds_prob : ∀ (T : Node) (X Y : ℕ) (δ : ℝ), T.WF X Y → T.BoundsProb δ X Y →
    ∀ x J : Finset ℕ, Node.Valid T.N X Y x J →
      prU (fun r : T.Seed => ¬ T.AllBounds r x J) ≤ (T.boundCount : ℝ) * δ := by
  intro T
  induction T with
  | store N =>
      intro X Y δ hWF hBP x J hvalid
      have hp : (fun r : Node.Seed (Node.store N) => ¬ Node.AllBounds (Node.store N) r x J)
          = (fun _ : Node.Seed (Node.store N) => False) := by
        funext r
        exact propext ⟨fun h => h trivial, fun h _ => h⟩
      rw [hp, prU_false]
      have h0 : Node.boundCount (Node.store N) = 0 := rfl
      rw [h0]
      simp
  | cr N t =>
      intro X Y δ hWF hBP x J hvalid
      have hp : (fun r : Node.Seed (Node.cr N t) => ¬ Node.AllBounds (Node.cr N t) r x J)
          = (fun _ : Node.Seed (Node.cr N t) => False) := by
        funext r
        exact propext ⟨fun h => h trivial, fun h _ => h⟩
      rw [hp, prU_false]
      have h0 : Node.boundCount (Node.cr N t) = 0 := rfl
      rw [h0]
      simp
  | direct sch t =>
      intro X Y δ hWF hBP x J hvalid
      have hp : (fun r : Node.Seed (Node.direct sch t) => ¬ Node.AllBounds (Node.direct sch t) r x J)
          = (fun r : sch.LocalSeed => t < sch.Z r x J) := by
        funext r
        exact propext not_le
      rw [hp]
      have h1 : Node.boundCount (Node.direct sch t) = 1 := rfl
      rw [h1, Nat.cast_one, one_mul]
      exact hBP x J hvalid
  | recursive sch t Xs Ys child ih =>
      intro X Y δ hWF hBP x J hvalid
      obtain ⟨hWFt, hWFchild⟩ := hWF
      have hvalid0 : Node.Valid sch.N X Y (∅ : Finset ℕ) (∅ : Finset ℕ) :=
        ⟨Finset.empty_subset _, Finset.empty_subset _, by simp, by simp⟩
      have hδ : 0 ≤ δ :=
        le_trans (prU_nonneg (fun lr : sch.LocalSeed =>
            t < sch.Z lr (∅ : Finset ℕ) (∅ : Finset ℕ)))
          (hBP.1 (∅ : Finset ℕ) (∅ : Finset ℕ) hvalid0).1
      have hbc : Node.boundCount (Node.recursive sch t Xs Ys child)
          = 2 * sch.ℓ + 1 + ∑ s : Fin sch.ℓ, Node.boundCount (child s) := rfl
      have hAlliff : ∀ p : sch.LocalSeed × (∀ s, (child s).Seed),
          (Node.AllBounds (Node.recursive sch t Xs Ys child) p x J) ↔
            (sch.Z p.1 x J ≤ t ∧ ∀ s : Fin sch.ℓ,
              sch.U p.1 x J s ≤ Xs s ∧ sch.V p.1 x J s ≤ Ys s ∧
                Node.AllBounds (child s) (p.2 s) (sch.exactChildInput p.1 x J s)
                  (sch.exactHint p.1 x J s)) := fun _ => Iff.rfl
      have hpred : (fun p : sch.LocalSeed × (∀ s, (child s).Seed) =>
            ¬ Node.AllBounds (Node.recursive sch t Xs Ys child) p x J)
          = (fun p : sch.LocalSeed × (∀ s, (child s).Seed) =>
              t < sch.Z p.1 x J ∨ ∃ s : Fin sch.ℓ,
                (Xs s < sch.U p.1 x J s ∨ Ys s < sch.V p.1 x J s ∨
                  ¬ Node.AllBounds (child s) (p.2 s) (sch.exactChildInput p.1 x J s)
                    (sch.exactHint p.1 x J s))) := by
        funext p
        rw [hAlliff p]
        apply propext
        constructor
        · intro h
          by_cases hZ : sch.Z p.1 x J ≤ t
          · have hforall : ¬ ∀ s : Fin sch.ℓ,
                (sch.U p.1 x J s ≤ Xs s ∧ sch.V p.1 x J s ≤ Ys s ∧
                  Node.AllBounds (child s) (p.2 s) (sch.exactChildInput p.1 x J s)
                    (sch.exactHint p.1 x J s)) := fun hh => h ⟨hZ, hh⟩
            obtain ⟨s, hs⟩ := Classical.not_forall.mp hforall
            refine Or.inr ⟨s, ?_⟩
            by_cases h1 : Xs s < sch.U p.1 x J s
            · exact Or.inl h1
            · by_cases h2 : Ys s < sch.V p.1 x J s
              · exact Or.inr (Or.inl h2)
              · exact Or.inr (Or.inr (fun hc => hs ⟨by omega, by omega, hc⟩))
          · exact Or.inl (by omega)
        · intro h
          rintro ⟨hZle, hall⟩
          rcases h with hZ | ⟨s, h1 | h2 | hc⟩
          · omega
          · exact absurd (hall s).1 (by omega)
          · exact absurd (hall s).2.1 (by omega)
          · exact absurd (hall s).2.2 hc
      have hchildValid : ∀ (lr : sch.LocalSeed) (s : Fin sch.ℓ),
          ¬ (Xs s < sch.U lr x J s ∨ Ys s < sch.V lr x J s) →
          Node.Valid (child s).N (Xs s) (Ys s) (sch.exactChildInput lr x J s)
            (sch.exactHint lr x J s) := by
        intro lr s ha
        have hNm : (child s).N = sch.m := (hWFchild s).1
        have hUle : sch.U lr x J s ≤ Xs s := by
          by_contra h
          exact ha (Or.inl (Nat.lt_of_not_le h))
        have hVle : sch.V lr x J s ≤ Ys s := by
          by_contra h
          exact ha (Or.inr (Nat.lt_of_not_le h))
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hNm]
          exact exactChildInput_subset_range sch lr x J s
        · rw [hNm]
          exact exactHint_subset_range sch lr x J s
        · rw [exactHint_card]
          exact hUle
        · exact le_trans (exactChildInput_sdiff_hint_card sch lr x J s) hVle
      show prU (fun p : sch.LocalSeed × (∀ s, (child s).Seed) =>
              ¬ Node.AllBounds (Node.recursive sch t Xs Ys child) p x J)
            ≤ ((Node.boundCount (Node.recursive sch t Xs Ys child) : ℕ) : ℝ) * δ
      rw [hpred, hbc]
      have hkey := prU_prod_union_bound (α := sch.LocalSeed) (ι := Fin sch.ℓ)
        (β := fun s => (child s).Seed)
        (Pz := fun lr => t < sch.Z lr x J)
        (Pu := fun s lr => Xs s < sch.U lr x J s)
        (Pv := fun s lr => Ys s < sch.V lr x J s)
        (Pc := fun s lr rc => ¬ Node.AllBounds (child s) (rc s)
          (sch.exactChildInput lr x J s) (sch.exactHint lr x J s))
        (δ := δ) (c := fun s => Node.boundCount (child s))
        (by exact (hBP.1 x J hvalid).1)
        (fun s => ((hBP.1 x J hvalid).2 s).1)
        (fun s => ((hBP.1 x J hvalid).2 s).2)
        (fun s lr ha => by
          refine le_trans (le_of_eq ?_) (ih s (Xs s) (Ys s) δ ((hWFchild s).2) (hBP.2 s)
            (sch.exactChildInput lr x J s) (sch.exactHint lr x J s) (hchildValid lr s ha))
          exact prU_pi_marginal (β := fun s => (child s).Seed) s
            (P := fun rc => ¬ Node.AllBounds (child s) rc (sch.exactChildInput lr x J s)
              (sch.exactHint lr x J s)))
        hδ
      rw [Fintype.card_fin] at hkey
      exact hkey

/-- Theorem 4.9 (PDF p.21): both parts. -/
theorem theorem_4_9 (CR : CRFamily) (hCR : CR.Recovers) (T : Node) (X Y : ℕ) (hT : T.WF X Y)
    (x J : Finset ℕ) (hvalid : Node.Valid T.N X Y x J) :
    (∀ r : T.Seed, T.AllBounds r x J → T.decode CR r (T.sketch CR r x) J = some x) ∧
    (∀ δ : ℝ, T.BoundsProb δ X Y →
      prU (fun r : T.Seed => T.decode CR r (T.sketch CR r x) J ≠ some x) ≤
        (T.boundCount : ℝ) * δ) := by
  refine ⟨fun r hAll => decode_eq_of_allBounds CR hCR T X Y r x J hT hvalid hAll, ?_⟩
  intro δ hBP
  refine le_trans (prU_mono ?_) (allBounds_prob T X Y δ hT hBP x J hvalid)
  intro r hr hAll
  exact hr (decode_eq_of_allBounds CR hCR T X Y r x J hT hvalid hAll)

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Theorem 4.9 — submission wrapper matching the target statement. -/
theorem solution (CR : CRFamily) (hCR : CR.Recovers) (T : Node) (X Y : ℕ) (hT : T.WF X Y)
    (x J : Finset ℕ) (hvalid : Node.Valid T.N X Y x J) :
    (∀ r : T.Seed, T.AllBounds r x J → T.decode CR r (T.sketch CR r x) J = some x) ∧
    (∀ δ : ℝ, T.BoundsProb δ X Y →
      prU (fun r : T.Seed => T.decode CR r (T.sketch CR r x) J ≠ some x) ≤
        (T.boundCount : ℝ) * δ) :=
  LinearSetReconciliation327.Main.theorem_4_9 CR hCR T X Y hT x J hvalid
