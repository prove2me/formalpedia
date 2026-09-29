-- Prove2me | solution 1 for MasekPaterson.FourRussians.possibleSteps_finite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:50:44.664421+00:00
-- url     : https://prove2.me/submissions/9cece429-0b50-4e83-87c4-96a4e4aa2627

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Shared_steps
open MasekPaterson.Shared


namespace MasekPaterson.FourRussians

section EdCore
variable {α : Type*}
noncomputable def mpdp (γ : EditOp α → ℝ) : List α → List α → ℝ
  | [], [] => 0
  | x :: xs, [] => delCost γ x + mpdp γ xs []
  | [], y :: ys => insCost γ y + mpdp γ [] ys
  | x :: xs, y :: ys => min (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys))

variable (γ : EditOp α → ℝ)

lemma mpdp_nn : mpdp γ [] [] = 0 := by rw [mpdp]
lemma mpdp_cn (x : α) xs : mpdp γ (x :: xs) [] = delCost γ x + mpdp γ xs [] := by rw [mpdp]
lemma mpdp_nc (y : α) ys : mpdp γ [] (y :: ys) = insCost γ y + mpdp γ [] ys := by rw [mpdp]
lemma mpdp_cc (x y : α) xs ys : mpdp γ (x :: xs) (y :: ys) =
    min (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys)) := by rw [mpdp]

lemma mpdp_cc_cases (x y : α) xs ys :
    mpdp γ (x :: xs) (y :: ys) = delCost γ x + mpdp γ xs (y :: ys) ∨
    mpdp γ (x :: xs) (y :: ys) = insCost γ y + mpdp γ (x :: xs) ys ∨
    mpdp γ (x :: xs) (y :: ys) = replCost γ x y + mpdp γ xs ys := by
  rw [mpdp_cc]
  rcases min_choice (delCost γ x + mpdp γ xs (y :: ys))
      (min (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys)) with h | h
  · left; rw [h]
  · rw [h]
    rcases min_choice (insCost γ y + mpdp γ (x :: xs) ys) (replCost γ x y + mpdp γ xs ys) with h' | h'
    · right; left; rw [h']
    · right; right; rw [h']

lemma mpdp_le_del (x : α) xs ys : mpdp γ (x :: xs) ys ≤ delCost γ x + mpdp γ xs ys := by
  cases ys with
  | nil => rw [mpdp_cn]
  | cons y ys => rw [mpdp_cc]; exact min_le_left _ _

lemma mpdp_le_ins xs (y : α) ys : mpdp γ xs (y :: ys) ≤ insCost γ y + mpdp γ xs ys := by
  cases xs with
  | nil => rw [mpdp_nc]
  | cons x xs => rw [mpdp_cc]; exact le_trans (min_le_right _ _) (min_le_left _ _)

lemma mpdp_le_rep (x : α) xs y ys : mpdp γ (x :: xs) (y :: ys) ≤ replCost γ x y + mpdp γ xs ys := by
  rw [mpdp_cc]; exact le_trans (min_le_right _ _) (min_le_right _ _)

def MPTri : Prop :=
  (∀ o, 0 ≤ γ o) ∧ (∀ x y b : α, replCost γ x b ≤ replCost γ x y + replCost γ y b) ∧
  (∀ x y : α, delCost γ x ≤ replCost γ x y + delCost γ y) ∧
  (∀ y b : α, insCost γ b ≤ insCost γ y + replCost γ y b) ∧ (∀ x : α, replCost γ x x ≤ 0)

variable {γ}

lemma mp_rep_base (h : MPTri γ) (x y : α) τ : ∀ B, mpdp γ (x :: τ) B ≤ replCost γ x y + mpdp γ (y :: τ) B := by
  intro B
  induction B with
  | nil => rw [mpdp_cn, mpdp_cn]; linarith [h.2.2.1 x y]
  | cons b B ih =>
    rcases mpdp_cc_cases γ y b τ B with h1 | h1 | h1 <;> rw [h1]
    · linarith [mpdp_le_del γ x τ (b :: B), h.2.2.1 x y]
    · linarith [mpdp_le_ins γ (x :: τ) b B]
    · linarith [mpdp_le_rep γ x τ b B, h.2.1 x y b]

lemma mp_ins_base (h : MPTri γ) (y : α) τ : ∀ B, mpdp γ τ B ≤ insCost γ y + mpdp γ (y :: τ) B := by
  have h0 : 0 ≤ insCost γ y + delCost γ y := add_nonneg (h.1 _) (h.1 _)
  intro B
  induction B with
  | nil => rw [mpdp_cn]; linarith
  | cons b B ih =>
    rcases mpdp_cc_cases γ y b τ B with h1 | h1 | h1 <;> rw [h1]
    · linarith
    · linarith [mpdp_le_ins γ τ b B]
    · linarith [mpdp_le_ins γ τ b B, h.2.2.2.1 y b]

lemma mp_edit_one (h : MPTri γ) (o : EditOp α) (τ : List α) :
    ∀ σ B, mpdp γ (σ ++ o.src.toList ++ τ) B ≤ γ o + mpdp γ (σ ++ o.tgt.toList ++ τ) B := by
  intro σ
  induction σ with
  | nil =>
    intro B
    rcases o with ⟨_ | x, _ | y, hn⟩
    · exact absurd ⟨rfl, rfl⟩ hn
    · exact mp_ins_base h y τ B
    · exact mpdp_le_del γ x τ B
    · exact mp_rep_base h x y τ B
  | cons x σ ih =>
    intro B
    simp only [List.cons_append]
    induction B with
    | nil => rw [mpdp_cn, mpdp_cn]; linarith [ih []]
    | cons b B ihB =>
      rcases mpdp_cc_cases γ x b (σ ++ o.tgt.toList ++ τ) B with h1 | h1 | h1 <;> rw [h1]
      · linarith [mpdp_le_del γ x (σ ++ o.src.toList ++ τ) (b :: B), ih (b :: B)]
      · linarith [mpdp_le_ins γ (x :: (σ ++ o.src.toList ++ τ)) b B]
      · linarith [mpdp_le_rep γ x (σ ++ o.src.toList ++ τ) b B, ih B]

lemma mpdp_self (h : MPTri γ) : ∀ A : List α, mpdp γ A A ≤ 0 := by
  intro A
  induction A with
  | nil => rw [mpdp_nn]
  | cons x A ih => linarith [mpdp_le_rep γ x A x A, h.2.2.2.2 x]

lemma mp_takes_lower (h : MPTri γ) {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) :
    mpdp γ A B ≤ seqCost γ S := by
  induction hS with
  | nil A => simpa [seqCost] using mpdp_self h A
  | @cons s S' A' C' B' hy _ ih =>
    obtain ⟨σ, τ, rfl, rfl⟩ := hy
    simp only [seqCost, List.map_cons, List.sum_cons] at ih ⊢
    linarith [mp_edit_one h s τ σ B']

lemma mp_yields_del (x : α) xs : Yields (delOp x) (x :: xs) xs := ⟨[], xs, by simp [delOp], by simp [delOp]⟩
lemma mp_yields_ins (y : α) xs : Yields (insOp y) xs (y :: xs) := ⟨[], xs, by simp [insOp], by simp [insOp]⟩
lemma mp_yields_rep (x y : α) xs : Yields (replOp x y) (x :: xs) (y :: xs) :=
  ⟨[], xs, by simp [replOp], by simp [replOp]⟩

lemma mp_takes_lift {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) (c : α) :
    Takes S (c :: A) (c :: B) := by
  induction hS with
  | nil A => exact Takes.nil _
  | cons hy _ ih =>
    obtain ⟨σ, τ, h1, h2⟩ := hy
    exact Takes.cons ⟨c :: σ, τ, by simp [h1], by simp [h2]⟩ ih

variable (γ)

theorem mp_realize : ∀ xs ys : List α, ∃ S, Takes S xs ys ∧ seqCost γ S ≤ mpdp γ xs ys
  | [], [] => ⟨[], Takes.nil _, by simp [seqCost, mpdp_nn]⟩
  | x :: xs, [] => by
    obtain ⟨S, hS, hc⟩ := mp_realize xs []
    refine ⟨delOp x :: S, Takes.cons (mp_yields_del x xs) hS, ?_⟩
    rw [mpdp_cn]; simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
    exact add_le_add le_rfl hc
  | [], y :: ys => by
    obtain ⟨S, hS, hc⟩ := mp_realize [] ys
    refine ⟨insOp y :: S, Takes.cons (mp_yields_ins y []) (mp_takes_lift hS y), ?_⟩
    rw [mpdp_nc]; simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
    exact add_le_add le_rfl hc
  | x :: xs, y :: ys => by
    rcases mpdp_cc_cases γ x y xs ys with h1 | h1 | h1 <;> rw [h1]
    · obtain ⟨S, hS, hc⟩ := mp_realize xs (y :: ys)
      refine ⟨delOp x :: S, Takes.cons (mp_yields_del x xs) hS, ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc
    · obtain ⟨S, hS, hc⟩ := mp_realize (x :: xs) ys
      refine ⟨insOp y :: S, Takes.cons (mp_yields_ins y _) (mp_takes_lift hS y), ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc
    · obtain ⟨S, hS, hc⟩ := mp_realize xs ys
      refine ⟨replOp x y :: S, Takes.cons (mp_yields_rep x y xs) (mp_takes_lift hS y), ?_⟩
      simp only [seqCost, List.map_cons, List.sum_cons] at hc ⊢
      exact add_le_add le_rfl hc

variable {γ}

theorem mp_editDist_eq (h : MPTri γ) (xs ys : List α) : editDist γ xs ys = mpdp γ xs ys := by
  obtain ⟨S, hS, hc⟩ := mp_realize γ xs ys
  apply le_antisymm
  · refine le_trans (csInf_le ⟨mpdp γ xs ys, ?_⟩ ⟨S, hS, rfl⟩) hc
    rintro c ⟨T, hT, rfl⟩; exact mp_takes_lower h hT
  · exact le_csInf ⟨_, S, hS, rfl⟩ (by rintro c ⟨T, hT, rfl⟩; exact mp_takes_lower h hT)

lemma mp_seqCost_nonneg (hγ : ∀ o, 0 ≤ γ o) (S : List (EditOp α)) : 0 ≤ seqCost γ S := by
  unfold seqCost
  exact List.sum_nonneg (by intro x hx; obtain ⟨o, _, rfl⟩ := List.mem_map.mp hx; exact hγ o)

lemma mp_editDist_le (hγ : ∀ o, 0 ≤ γ o) {S : List (EditOp α)} {A B : List α} (hS : Takes S A B) :
    editDist γ A B ≤ seqCost γ S :=
  csInf_le ⟨0, by rintro c ⟨T, _, rfl⟩; exact mp_seqCost_nonneg hγ T⟩ ⟨S, hS, rfl⟩

theorem mp_tri_of_norm (hγ : ∀ o, 0 ≤ γ o) (hnorm : IsNormalized γ) : MPTri γ := by
  refine ⟨hγ, ?_, ?_, ?_, ?_⟩
  · intro x y b
    have h1 := hnorm (replOp x b)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_rep x y []) (Takes.cons (mp_yields_rep y b [])
      (Takes.nil _)))
    simp only [replOp, Option.toList_some] at h1
    simp only [replCost, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h2 ⊢
    linarith
  · intro x y
    have h1 := hnorm (delOp x)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_rep x y []) (Takes.cons (mp_yields_del y [])
      (Takes.nil _)))
    simp only [delOp, Option.toList_some, Option.toList_none] at h1
    simp only [delCost, replCost, delOp, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h2 ⊢
    linarith
  · intro y b
    have h1 := hnorm (insOp b)
    have h2 := mp_editDist_le hγ (Takes.cons (mp_yields_ins y []) (Takes.cons (mp_yields_rep y b [])
      (Takes.nil _)))
    simp only [insOp, Option.toList_some, Option.toList_none] at h1
    simp only [insCost, replCost, insOp, replOp, seqCost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at h2 ⊢
    linarith
  · intro x
    have h1 := hnorm (replOp x x)
    have h2 := mp_editDist_le hγ (Takes.nil [x])
    simp only [replOp, Option.toList_some] at h1
    simp only [replCost, replOp, seqCost, List.map_nil, List.sum_nil] at h2 ⊢
    linarith

end EdCore

section Rec
variable {α : Type*}

lemma mr_toList_rev (o : Option α) : o.toList.reverse = o.toList := by cases o <;> simp

lemma mr_takes_rev {S : List (EditOp α)} {A B : List α} (h : Takes S A B) :
    Takes S A.reverse B.reverse := by
  induction h with
  | nil A => exact Takes.nil _
  | @cons s S' A' C' B' hy _ ih =>
    obtain ⟨σ, τ, h1, h2⟩ := hy
    refine Takes.cons ⟨τ.reverse, σ.reverse, ?_, ?_⟩ ih
    · rw [h1]; simp [mr_toList_rev]
    · rw [h2]; simp [mr_toList_rev]

lemma mr_ed_rev (γ : EditOp α → ℝ) (A B : List α) :
    editDist γ A.reverse B.reverse = editDist γ A B := by
  unfold editDist
  congr 1
  ext c
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, by simpa using mr_takes_rev hS, rfl⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨S, mr_takes_rev hS, rfl⟩

lemma mr_take_succ (l : List α) (n : ℕ) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

variable {γ : EditOp α → ℝ}

lemma mr_e (h : MPTri γ) (U V : List α) : mpdp γ U.reverse V.reverse = editDist γ U V := by
  rw [← mp_editDist_eq h, mr_ed_rev]

lemma mr_snoc_snoc (h : MPTri γ) (X Y : List α) (a b : α) :
    editDist γ (X ++ [a]) (Y ++ [b]) =
      min (min (editDist γ X Y + replCost γ a b) (editDist γ X (Y ++ [b]) + delCost γ a))
        (editDist γ (X ++ [a]) Y + insCost γ b) := by
  have e1 := mr_e h (X ++ [a]) (Y ++ [b])
  have e2 := mr_e h X (Y ++ [b])
  have e3 := mr_e h (X ++ [a]) Y
  have e4 := mr_e h X Y
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at e1 e2 e3
  rw [mpdp_cc] at e1
  rw [← e1, ← e2, ← e3, ← e4]
  simp only [min_def]; split_ifs <;> linarith

lemma mr_snoc_nil (h : MPTri γ) (X : List α) (a : α) :
    editDist γ (X ++ [a]) [] = editDist γ X [] + delCost γ a := by
  have e1 := mr_e h (X ++ [a]) []
  have e2 := mr_e h X []
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at e1 e2
  rw [mpdp_cn] at e1
  rw [← e1, ← e2]; ring

lemma mr_nil_snoc (h : MPTri γ) (Y : List α) (b : α) :
    editDist γ [] (Y ++ [b]) = editDist γ [] Y + insCost γ b := by
  have e1 := mr_e h [] (Y ++ [b])
  have e2 := mr_e h [] Y
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at e1 e2
  rw [mpdp_nc] at e1
  rw [← e1, ← e2]; ring

lemma mr_nil_nil (h : MPTri γ) : editDist γ ([] : List α) [] = 0 := by
  have e1 := mr_e h ([] : List α) []
  simp only [List.reverse_nil] at e1
  rw [← e1, mpdp_nn]

/-- dmat-form recurrence -/
lemma mr_dmat_rec (h : MPTri γ) (A B : List α) (i j : ℕ) (hi : i < A.length) (hj : j < B.length) :
    dmat γ A B (i + 1) (j + 1) =
      min (min (dmat γ A B i j + replCost γ A[i] B[j]) (dmat γ A B i (j + 1) + delCost γ A[i]))
        (dmat γ A B (i + 1) j + insCost γ B[j]) := by
  unfold dmat
  rw [mr_take_succ A i hi, mr_take_succ B j hj, mr_snoc_snoc h]

lemma mr_dmat_col0 (h : MPTri γ) (A B : List α) (i : ℕ) (hi : i < A.length) :
    dmat γ A B (i + 1) 0 = dmat γ A B i 0 + delCost γ A[i] := by
  unfold dmat
  rw [mr_take_succ A i hi, List.take_zero, mr_snoc_nil h]

lemma mr_dmat_row0 (h : MPTri γ) (A B : List α) (j : ℕ) (hj : j < B.length) :
    dmat γ A B 0 (j + 1) = dmat γ A B 0 j + insCost γ B[j] := by
  unfold dmat
  rw [mr_take_succ B j hj, List.take_zero, mr_nil_snoc h]

lemma mr_dmat_00 (h : MPTri γ) (A B : List α) : dmat γ A B 0 0 = 0 := by
  unfold dmat; simp only [List.take_zero]; exact mr_nil_nil h

/-! non-normalized bounds -/

lemma mr_takes_snoc {S : List (EditOp α)} {X Y Z : List α} (h : Takes S X Y) {o : EditOp α}
    (hy : Yields o Y Z) : Takes (S ++ [o]) X Z := by
  induction h with
  | nil A => exact Takes.cons hy (Takes.nil _)
  | cons hy' _ ih => exact Takes.cons hy' (ih hy)

lemma mr_ed_pre (hγ : ∀ o, 0 ≤ γ o) {o : EditOp α} {X X' : List α} (hy : Yields o X X')
    (Y : List α) : editDist γ X Y ≤ γ o + editDist γ X' Y := by
  obtain ⟨S0, hS0, _⟩ := mp_realize γ X' Y
  have : editDist γ X Y - γ o ≤ editDist γ X' Y := by
    refine le_csInf ⟨_, S0, hS0, rfl⟩ ?_
    rintro c ⟨S, hS, rfl⟩
    have := mp_editDist_le hγ (Takes.cons hy hS)
    simp only [seqCost, List.map_cons, List.sum_cons] at this ⊢
    linarith
  linarith

lemma mr_ed_post (hγ : ∀ o, 0 ≤ γ o) {o : EditOp α} {Y Y' : List α} (hy : Yields o Y' Y)
    (X : List α) : editDist γ X Y ≤ editDist γ X Y' + γ o := by
  obtain ⟨S0, hS0, _⟩ := mp_realize γ X Y'
  have : editDist γ X Y - γ o ≤ editDist γ X Y' := by
    refine le_csInf ⟨_, S0, hS0, rfl⟩ ?_
    rintro c ⟨S, hS, rfl⟩
    have := mp_editDist_le hγ (mr_takes_snoc hS hy)
    simp only [seqCost, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil] at this ⊢
    linarith
  linarith

lemma mr_y_del (X : List α) (a : α) : Yields (delOp a) (X ++ [a]) X :=
  ⟨X, [], by simp [delOp], by simp [delOp]⟩
lemma mr_y_ins (X : List α) (a : α) : Yields (insOp a) X (X ++ [a]) :=
  ⟨X, [], by simp [insOp], by simp [insOp]⟩

lemma mr_vstep (hγ : ∀ o, 0 ≤ γ o) (A B : List α) (i j : ℕ) (hi : i < A.length) :
    -insCost γ A[i] ≤ dmat γ A B (i + 1) j - dmat γ A B i j ∧
      dmat γ A B (i + 1) j - dmat γ A B i j ≤ delCost γ A[i] := by
  unfold dmat
  rw [mr_take_succ A i hi]
  have h1 := mr_ed_pre hγ (mr_y_del (A.take i) A[i]) (B.take j)
  have h2 := mr_ed_pre hγ (mr_y_ins (A.take i) A[i]) (B.take j)
  unfold delCost insCost
  constructor <;> linarith

lemma mr_hstep (hγ : ∀ o, 0 ≤ γ o) (A B : List α) (i j : ℕ) (hj : j < B.length) :
    -delCost γ B[j] ≤ dmat γ A B i (j + 1) - dmat γ A B i j ∧
      dmat γ A B i (j + 1) - dmat γ A B i j ≤ insCost γ B[j] := by
  unfold dmat
  rw [mr_take_succ B j hj]
  have h1 := mr_ed_post hγ (mr_y_del (B.take j) B[j]) (A.take i)
  have h2 := mr_ed_post hγ (mr_y_ins (B.take j) B[j]) (A.take i)
  unfold delCost insCost
  constructor <;> linarith

end Rec

theorem initial_vectors_core {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) :
    dmat γ A B 0 0 = 0 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ A.length → dmat γ A B i 0 = ((A.take i).map (delCost γ)).sum) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ B.length → dmat γ A B 0 j = ((B.take j).map (insCost γ)).sum) := by
  have h := mp_tri_of_norm hγ hN
  refine ⟨mr_dmat_00 h A B, ?_, ?_⟩
  · intro i _ hi
    clear ‹1 ≤ i›
    induction i with
    | zero => simp [mr_dmat_00 h]
    | succ i ih =>
      rw [mr_dmat_col0 h A B i (by omega), ih (by omega)]
      simp only [mr_take_succ A i (by omega), List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  · intro j _ hj
    clear ‹1 ≤ j›
    induction j with
    | zero => simp [mr_dmat_00 h]
    | succ j ih =>
      rw [mr_dmat_row0 h A B j (by omega), ih (by omega)]
      simp only [mr_take_succ B j (by omega), List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]

theorem wagner_fischer_recurrence_core {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j =
      min (min (dmat γ A B (i - 1) (j - 1) + replCost γ A[i - 1] B[j - 1])
               (dmat γ A B (i - 1) j + delCost γ A[i - 1]))
          (dmat γ A B i (j - 1) + insCost γ B[j - 1]) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact mr_dmat_rec (mp_tri_of_norm hγ hN) A B i j (by omega) (by omega)

theorem step_recurrence_core {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j - dmat γ A B (i - 1) j =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1]))
          (insCost γ B[j - 1] + (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))) ∧
    dmat γ A B i j - dmat γ A B i (j - 1) =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1] + (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))))
          (insCost γ B[j - 1]) := by
  rw [wagner_fischer_recurrence_core γ hγ hN A B i j hi hiA hj hjB]
  constructor <;> (simp only [min_def]; split_ifs <;> linarith)

theorem step_bounds_core {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (I D : ℝ) (hI : ∀ a : α, insCost γ a ≤ I) (hD : ∀ a : α, delCost γ a ≤ D)
    (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    (-I ≤ dmat γ A B i j - dmat γ A B (i - 1) j ∧ dmat γ A B i j - dmat γ A B (i - 1) j ≤ D) ∧
    (-D ≤ dmat γ A B i j - dmat γ A B i (j - 1) ∧ dmat γ A B i j - dmat γ A B i (j - 1) ≤ I) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := mr_vstep hγ A B i (j + 1) (by omega)
  have h2 := mr_hstep hγ A B (i + 1) j (by omega)
  have := hI A[i]; have := hD A[i]; have := hI B[j]; have := hD B[j]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

section Fin
variable {α : Type*} {γ : EditOp α → ℝ}

lemma mr_cost_mult (hγ : ∀ o, 0 ≤ γ o) (r : ℝ) (hr : 0 < r)
    (hΩ : ∀ ω ∈ costSet γ, ∃ z : ℤ, ω = z * r) :
    ∀ S : List (EditOp α), ∃ n : ℕ, seqCost γ S = n * r := by
  intro S
  induction S with
  | nil => exact ⟨0, by simp [seqCost]⟩
  | cons o S ih =>
    obtain ⟨n, hn⟩ := ih
    have ho : γ o ∈ costSet γ := by
      simp only [costSet, Set.mem_union, Set.mem_setOf_eq]
      rcases o with ⟨_ | x, _ | y, h⟩
      · exact absurd ⟨rfl, rfl⟩ h
      · exact Or.inl (Or.inr ⟨y, rfl⟩)
      · exact Or.inl (Or.inl ⟨x, rfl⟩)
      · exact Or.inr ⟨x, y, rfl⟩
    obtain ⟨z, hz⟩ := hΩ _ ho
    have hz0 : 0 ≤ z := by
      have h1 : (0:ℝ) ≤ z * r := hz ▸ hγ o
      have : (0:ℝ) ≤ z := by
        by_contra hc; push_neg at hc; nlinarith
      exact_mod_cast this
    refine ⟨z.toNat + n, ?_⟩
    simp only [seqCost, List.map_cons, List.sum_cons] at hn ⊢
    rw [hn, hz]
    have : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hz0
    push_cast; rw [this]; ring

lemma mr_ed_mult (hγ : ∀ o, 0 ≤ γ o) (r : ℝ) (hr : 0 < r)
    (hΩ : ∀ ω ∈ costSet γ, ∃ z : ℤ, ω = z * r) (X Y : List α) :
    ∃ n : ℕ, editDist γ X Y = n * r := by
  classical
  obtain ⟨S0, hS0, _⟩ := mp_realize γ X Y
  obtain ⟨n0, hn0⟩ := mr_cost_mult hγ r hr hΩ S0
  have hne : {n : ℕ | ∃ S, Takes S X Y ∧ seqCost γ S = n * r}.Nonempty := ⟨n0, S0, hS0, hn0⟩
  refine ⟨sInf {n : ℕ | ∃ S, Takes S X Y ∧ seqCost γ S = n * r}, le_antisymm ?_ ?_⟩
  · obtain ⟨S, hS, hc⟩ := Nat.sInf_mem hne
    rw [← hc]; exact mp_editDist_le hγ hS
  · unfold editDist
    refine le_csInf ⟨_, S0, hS0, rfl⟩ ?_
    rintro c ⟨S, hS, rfl⟩
    obtain ⟨n, hn⟩ := mr_cost_mult hγ r hr hΩ S
    rw [hn]
    have : sInf {n : ℕ | ∃ S, Takes S X Y ∧ seqCost γ S = n * r} ≤ n := Nat.sInf_le ⟨S, hS, hn⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hr.le

lemma mr_bound (r M : ℝ) (hr : 0 < r) (z : ℤ) (h1 : -M ≤ z * r) (h2 : z * r ≤ M) :
    z ∈ Set.Icc (-⌈M / r⌉) ⌈M / r⌉ := by
  constructor
  · have : ((-z : ℤ) : ℝ) ≤ M / r := by
      rw [le_div_iff₀ hr]; push_cast; linarith
    have := le_trans this (Int.le_ceil _)
    have : -z ≤ ⌈M / r⌉ := by exact_mod_cast this
    omega
  · have : (z : ℝ) ≤ M / r := by rw [le_div_iff₀ hr]; linarith
    exact_mod_cast le_trans this (Int.le_ceil _)

end Fin

theorem possibleSteps_finite_core {α : Type*} [Fintype α] (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hΩ : IsDiscrete γ) :
    (possibleSteps γ).Finite := by
  classical
  obtain ⟨r, hr, hΩ⟩ := hΩ
  have hI0 : 0 ≤ ∑ a, insCost γ a := Finset.sum_nonneg (fun a _ => hγ _)
  have hD0 : 0 ≤ ∑ a, delCost γ a := Finset.sum_nonneg (fun a _ => hγ _)
  have hIa : ∀ a, insCost γ a ≤ ∑ a, insCost γ a + ∑ a, delCost γ a := fun a => by
    have := Finset.single_le_sum (f := fun a => insCost γ a) (fun a _ => hγ _) (Finset.mem_univ a)
    linarith
  have hDa : ∀ a, delCost γ a ≤ ∑ a, insCost γ a + ∑ a, delCost γ a := fun a => by
    have := Finset.single_le_sum (f := fun a => delCost γ a) (fun a _ => hγ _) (Finset.mem_univ a)
    linarith
  set M := ∑ a, insCost γ a + ∑ a, delCost γ a with hM
  apply ((Set.finite_Icc (-⌈M / r⌉) ⌈M / r⌉).image (fun z : ℤ => (z : ℝ) * r)).subset
  rintro s ⟨A, B, i, j, h | h⟩
  · obtain ⟨hi, hiA, hjB, rfl⟩ := h
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hb := mr_vstep hγ A B i j (by omega)
    obtain ⟨n1, h1⟩ := mr_ed_mult hγ r hr hΩ (A.take (i + 1)) (B.take j)
    obtain ⟨n2, h2⟩ := mr_ed_mult hγ r hr hΩ (A.take i) (B.take j)
    have e : dmat γ A B (i + 1) j - dmat γ A B i j = (((n1 : ℤ) - n2 : ℤ) : ℝ) * r := by
      unfold dmat; rw [h1, h2]; push_cast; ring
    refine ⟨(n1 : ℤ) - n2, mr_bound r M hr _ ?_ ?_, e.symm⟩
    · rw [← e]; linarith [hIa A[i]]
    · rw [← e]; linarith [hDa A[i]]
  · obtain ⟨hiA, hj, hjB, rfl⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hb := mr_hstep hγ A B i j (by omega)
    obtain ⟨n1, h1⟩ := mr_ed_mult hγ r hr hΩ (A.take i) (B.take (j + 1))
    obtain ⟨n2, h2⟩ := mr_ed_mult hγ r hr hΩ (A.take i) (B.take j)
    have e : dmat γ A B i (j + 1) - dmat γ A B i j = (((n1 : ℤ) - n2 : ℤ) : ℝ) * r := by
      unfold dmat; rw [h1, h2]; push_cast; ring
    refine ⟨(n1 : ℤ) - n2, mr_bound r M hr _ ?_ ?_, e.symm⟩
    · rw [← e]; linarith [hDa B[j]]
    · rw [← e]; linarith [hIa B[j]]

end MasekPaterson.FourRussians

open MasekPaterson.FourRussians


theorem solution {α : Type*} [Fintype α] (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hΩ : IsDiscrete γ) :
    (possibleSteps γ).Finite := by
  exact possibleSteps_finite_core γ hγ hΩ
