-- Prove2me | solution 1 for NishtAbel2024.theorem2_size_soundness
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:32:06.49441+00:00
-- url     : https://prove2.me/submissions/2305d998-c822-4f40-87ba-415517c1783d

import Definitions.Def_NishtAbel2024_Syntax
import Definitions.Def_NishtAbel2024_Semantics

namespace NishtAbel2024

theorem size_shift_monotone (α β : SizeOrd) (n : Nat) (h : SizeOrd.le α β) :
    SizeOrd.le (α.shift n) (β.shift n) := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  simp_all [SizeOrd.le, SizeOrd.shift]

theorem size_min_monotone (a a' b b' : SizeOrd)
    (ha : SizeOrd.le a a') (hb : SizeOrd.le b b') :
    SizeOrd.le (SizeOrd.min a b) (SizeOrd.min a' b') := by
  rcases a with ⟨atier, ao⟩
  rcases a' with ⟨a't, a'o⟩
  rcases b with ⟨bt, bo⟩
  rcases b' with ⟨b't, b'o⟩
  simp only [SizeOrd.min]
  split <;> split <;> simp_all [SizeOrd.le] <;> omega

theorem size_le_chain (a b c : SizeOrd) (hab : SizeOrd.le a b) (hbc : SizeOrd.le b c) :
    SizeOrd.le a c := by
  simp_all only [SizeOrd.le]
  omega

theorem size_min_le_left (α β : SizeOrd) : SizeOrd.le (SizeOrd.min α β) α := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  unfold SizeOrd.min
  split
  · simp [SizeOrd.le]
  · simp_all [SizeOrd.le]
    omega

theorem size_min_le_right (α β : SizeOrd) : SizeOrd.le (SizeOrd.min α β) β := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  unfold SizeOrd.min
  split <;> simp_all [SizeOrd.le]

/-- Variables admitted by the size well-formedness judgment vary covariantly. -/
theorem size_var_monotone (Ψ : SizeCtx) (ρ ρ' : SizeVal) (i : SizeVar) (a : SizeExp)
    (hval : SizeValLe Ψ ρ ρ') (hbound : SizeVarBound Ψ i a) :
    SizeOrd.le (ρ i) (ρ' i) := by
  obtain ⟨π, hmem, hpol⟩ := hbound
  have hv := hval.2.2 ⟨i, π, a⟩ hmem
  cases π <;> simp_all [Polarity.le, SizeOrd.le]

theorem size_var_bound_valid (Ψ : SizeCtx) (ρ : SizeVal) (i : SizeVar) (a : SizeExp)
    (hval : ValidSizeVal Ψ ρ) (hbound : SizeVarBound Ψ i a) :
    SizeOrd.lt (ρ i) (evalSizeExp ρ a) := by
  obtain ⟨π, hmem, _⟩ := hbound
  exact hval ⟨i, π, a⟩ hmem

theorem size_lt_shift (α β : SizeOrd) (n : Nat) (h : SizeOrd.lt α β) :
    SizeOrd.lt (α.shift n) (β.shift n) := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  simp_all [SizeOrd.lt, SizeOrd.shift]

theorem size_lt_succ_to_le (α β : SizeOrd) (h : SizeOrd.lt α (β.shift 1)) :
    SizeOrd.le α β := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  simp_all [SizeOrd.lt, SizeOrd.le, SizeOrd.shift]

theorem size_min_shift (α β : SizeOrd) (n : Nat) :
    (SizeOrd.min α β).shift n = SizeOrd.min (α.shift n) (β.shift n) := by
  rcases α with ⟨a, b⟩
  rcases β with ⟨c, d⟩
  by_cases h : a < c ∨ a = c ∧ b ≤ d
  · simp [SizeOrd.min, SizeOrd.shift, SizeOrd.le, h]
  · simp [SizeOrd.min, SizeOrd.shift, SizeOrd.le, h]

theorem size_shift_shift (α : SizeOrd) (m n : Nat) :
    (α.shift m).shift n = α.shift (m + n) := by
  rcases α with ⟨a, b⟩
  simp [SizeOrd.shift, Nat.add_assoc]

theorem size_fold_shift (ρ : SizeVal) (xs : List ShiftedSizeVar) (a : SizeOrd) (n : Nat) :
    (xs.foldl (fun acc sv => SizeOrd.min acc ((ρ sv.var).shift sv.shift)) a).shift n =
    xs.foldl (fun acc sv => SizeOrd.min acc ((ρ sv.var).shift (sv.shift + n))) (a.shift n) := by
  induction xs generalizing a with
  | nil => rfl
  | cons sv xs ih =>
    simp only [List.foldl_cons]
    rw [ih, size_min_shift, size_shift_shift]

theorem evalSizeMin_shift (ρ : SizeVal) (m : SizeMin) (n : Nat) :
    evalSizeMin ρ (m.shift n) = (evalSizeMin ρ m).shift n := by
  rcases m with ⟨head, tail⟩
  simpa [SizeMin.shift, evalSizeMin, List.foldl_map, size_shift_shift] using
    (size_fold_shift ρ tail ((ρ head.var).shift head.shift) n).symm

theorem evalSizeExp_shift (ρ : SizeVal) (a : SizeExp) (n : Nat) :
    evalSizeExp ρ (a.shift n) = (evalSizeExp ρ a).shift n := by
  cases a with
  | inf k => simp [SizeExp.shift, evalSizeExp, SizeOrd.infAdd, SizeOrd.shift]
  | meet m => simp [SizeExp.shift, evalSizeExp, evalSizeMin_shift]

theorem size_var_expr_monotone (Ψ : SizeCtx) (ρ ρ' : SizeVal) (i n : Nat) (a : SizeExp)
    (hval : SizeValLe Ψ ρ ρ') (hbound : SizeVarBound Ψ i a) :
    SizeOrd.le (evalSizeExp ρ (.var i n)) (evalSizeExp ρ' (.var i n)) := by
  simpa [SizeExp.var, SizeMin.single, evalSizeExp, evalSizeMin] using
    size_shift_monotone (ρ i) (ρ' i) n (size_var_monotone Ψ ρ ρ' i a hval hbound)

theorem size_fold_monotone (ρ ρ' : SizeVal) (xs : List ShiftedSizeVar)
    (hx : ∀ sv ∈ xs, SizeOrd.le ((ρ sv.var).shift sv.shift) ((ρ' sv.var).shift sv.shift))
    (a b : SizeOrd) (hab : SizeOrd.le a b) :
    SizeOrd.le (xs.foldl (fun acc sv => SizeOrd.min acc ((ρ sv.var).shift sv.shift)) a)
      (xs.foldl (fun acc sv => SizeOrd.min acc ((ρ' sv.var).shift sv.shift)) b) := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons sv xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro v hv
      exact hx v (List.mem_cons_of_mem sv hv)
    · exact size_min_monotone a b _ _ hab (hx sv (by simp))

theorem size_lt_fold (ρ : SizeVal) (xs : List ShiftedSizeVar) (a acc : SizeOrd)
    (hacc : SizeOrd.lt a acc)
    (hvars : ∀ sv ∈ xs, SizeOrd.lt a ((ρ sv.var).shift sv.shift)) :
    SizeOrd.lt a (xs.foldl (fun v sv => SizeOrd.min v ((ρ sv.var).shift sv.shift)) acc) := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons sv xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · unfold SizeOrd.min
      split
      · exact hacc
      · exact hvars sv (by simp)
    · intro v hv
      exact hvars v (List.mem_cons_of_mem sv hv)

theorem size_lt_min_of_all (ρ : SizeVal) (m : SizeMin) (a : SizeOrd)
    (hvars : ∀ sv ∈ m.toList, SizeOrd.lt a ((ρ sv.var).shift sv.shift)) :
    SizeOrd.lt a (evalSizeMin ρ m) := by
  unfold evalSizeMin
  apply size_lt_fold
  · exact hvars m.head (by simp [SizeMin.toList])
  · intro sv hs
    exact hvars sv (by simp [SizeMin.toList, hs])

theorem size_fold_le_initial (ρ : SizeVal) (xs : List ShiftedSizeVar) (acc : SizeOrd) :
    SizeOrd.le (xs.foldl (fun v sv => SizeOrd.min v ((ρ sv.var).shift sv.shift)) acc) acc := by
  induction xs generalizing acc with
  | nil => simp [SizeOrd.le]
  | cons sv xs ih =>
    simp only [List.foldl_cons]
    exact size_le_chain _ _ _ (ih _) (size_min_le_left _ _)

theorem size_fold_le_mem (ρ : SizeVal) (xs : List ShiftedSizeVar) (acc : SizeOrd)
    (sv : ShiftedSizeVar) (hmem : sv ∈ xs) :
    SizeOrd.le (xs.foldl (fun v s => SizeOrd.min v ((ρ s.var).shift s.shift)) acc)
      ((ρ sv.var).shift sv.shift) := by
  induction xs generalizing acc with
  | nil => simp at hmem
  | cons v xs ih =>
    simp only [List.mem_cons] at hmem
    simp only [List.foldl_cons]
    rcases hmem with rfl | hmem
    · exact size_le_chain _ _ _ (size_fold_le_initial ρ xs _) (size_min_le_right _ _)
    · exact ih _ hmem

theorem size_min_le_member (ρ : SizeVal) (m : SizeMin) (sv : ShiftedSizeVar)
    (hmem : sv ∈ m.toList) :
    SizeOrd.le (evalSizeMin ρ m) ((ρ sv.var).shift sv.shift) := by
  simp only [SizeMin.toList, List.mem_cons] at hmem
  unfold evalSizeMin
  rcases hmem with rfl | hmem
  · exact size_fold_le_initial ρ m.tail _
  · exact size_fold_le_mem ρ m.tail _ sv hmem

theorem size_wf_monotone (Ψ : SizeCtx) (ρ ρ' : SizeVal)
    (hval : SizeValLe Ψ ρ ρ') (a : SizeExp) (ha : SizeWf Ψ a) :
    SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a) := by
  cases a with
  | inf n => simp [evalSizeExp, SizeOrd.infAdd, SizeOrd.le]
  | meet m =>
    have hvars : ∀ sv ∈ m.toList,
        SizeOrd.le ((ρ sv.var).shift sv.shift) ((ρ' sv.var).shift sv.shift) := by
      intro sv hs
      obtain ⟨bound, hb⟩ := ha sv hs
      exact size_shift_monotone _ _ sv.shift (size_var_monotone Ψ ρ ρ' sv.var bound hval hb)
    change SizeOrd.le (evalSizeMin ρ m) (evalSizeMin ρ' m)
    unfold evalSizeMin
    apply size_fold_monotone
    · intro sv hs
      exact hvars sv (by simp [SizeMin.toList, hs])
    · exact hvars m.head (by simp [SizeMin.toList])

private theorem size_le_lt_trans (a b c : SizeOrd) :
    SizeOrd.le a b → SizeOrd.lt b c → SizeOrd.lt a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  simp only [SizeOrd.le, SizeOrd.lt]
  omega

private theorem size_lt_le_trans (a b c : SizeOrd) :
    SizeOrd.lt a b → SizeOrd.le b c → SizeOrd.lt a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  simp only [SizeOrd.le, SizeOrd.lt]
  omega

/-- Structural soundness of strict comparisons, conditional on the usual
semantic laws for shifts and finite minima. -/
theorem size_lt_sound_of_min_shift (Ψ : SizeCtx) (ρ ρ' : SizeVal)
    (hval : SizeValLe Ψ ρ ρ')
    (evalShift : ∀ (v : SizeVal) (a : SizeExp) (n : Nat),
      evalSizeExp v (a.shift n) = (evalSizeExp v a).shift n)
    (minLe : ∀ (v : SizeVal) (m : SizeMin) (sv : ShiftedSizeVar),
      sv ∈ m.toList → SizeOrd.le (evalSizeMin v m) ((v sv.var).shift sv.shift))
    (ltMin : ∀ (v : SizeVal) (m : SizeMin) (α : SizeOrd),
      (∀ sv ∈ m.toList, SizeOrd.lt α ((v sv.var).shift sv.shift)) →
      SizeOrd.lt α (evalSizeMin v m))
    {a b : SizeExp} (h : SizeLt Ψ a b) :
    SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b) := by
  induction h with
  | @inf_lt_inf n m hnm =>
    simpa [evalSizeExp, SizeOrd.infAdd, SizeOrd.lt] using hnm
  | @var_lt_var i n m bound hnm hbound =>
    have hv := size_var_monotone Ψ ρ ρ' i bound hval hbound
    simp only [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin, List.foldl_nil]
    cases hρ : ρ i with
    | mk a b =>
      cases hρ' : ρ' i with
      | mk c d =>
        simp_all [SizeOrd.le, SizeOrd.lt, SizeOrd.shift]
        omega
  | @var_lt_inf i n m hbound =>
    have hv := size_var_bound_valid Ψ ρ i .infty hval.1 hbound
    simp only [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin, List.foldl_nil, SizeOrd.infAdd]
    cases hρ : ρ i with
    | mk a b =>
      simp_all [SizeOrd.lt, SizeOrd.infAdd, SizeOrd.shift, SizeExp.infty, evalSizeExp]
  | @var_lt_inf_add i n m hbound =>
    have hv := size_var_bound_valid Ψ ρ i (.inf m) hval.1 hbound
    simp only [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin, List.foldl_nil, SizeOrd.infAdd]
    cases hρ : ρ i with
    | mk a b =>
      simp_all [SizeOrd.lt, SizeOrd.infAdd, SizeOrd.shift, evalSizeExp]
  | @var_bound_step i n a b hbound hlt ih =>
    have hb := size_var_bound_valid Ψ ρ i a hval.1 hbound
    have hb' := size_lt_shift _ _ n hb
    have hi := size_lt_succ_to_le _ _ (by simpa only [evalShift] using ih)
    apply size_lt_le_trans _ _ _ ?_ hi
    simpa [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin] using hb'
  | @meet_lt_left m sv b hwf hmem hlt ih =>
    apply size_le_lt_trans _ _ _ (minLe ρ m sv hmem) ?_
    simpa [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin] using ih
  | @lt_meet_right a m hlt ih =>
    apply ltMin ρ' m (evalSizeExp ρ a)
    intro sv hmem
    simpa [evalSizeExp, SizeExp.var, SizeMin.single, evalSizeMin] using ih sv hmem

theorem size_lt_sound_of_min_le (Ψ : SizeCtx) (ρ ρ' : SizeVal)
    (hval : SizeValLe Ψ ρ ρ')
    (minLe : ∀ (v : SizeVal) (m : SizeMin) (sv : ShiftedSizeVar),
      sv ∈ m.toList → SizeOrd.le (evalSizeMin v m) ((v sv.var).shift sv.shift))
    {a b : SizeExp} (h : SizeLt Ψ a b) :
    SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b) :=
  size_lt_sound_of_min_shift Ψ ρ ρ' hval evalSizeExp_shift minLe size_lt_min_of_all h

theorem size_le_sound_of_min_le (Ψ : SizeCtx) (ρ ρ' : SizeVal)
    (hval : SizeValLe Ψ ρ ρ')
    (minLe : ∀ (v : SizeVal) (m : SizeMin) (sv : ShiftedSizeVar),
      sv ∈ m.toList → SizeOrd.le (evalSizeMin v m) ((v sv.var).shift sv.shift))
    {a b : SizeExp} (h : SizeLe Ψ a b) :
    SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b) := by
  apply size_lt_succ_to_le
  simpa only [← evalSizeExp_shift] using size_lt_sound_of_min_le Ψ ρ ρ' hval minLe h

end NishtAbel2024

open NishtAbel2024

/-- The exact size-soundness conjunct of the existing Theorems 2–3 statement.
This result concerns the current `SizeOrd` and size-judgment definitions. -/
theorem solution :
    ∀ (Ψ : SizeCtx) (ρ ρ' : SizeVal),
      SizeCtxWf Ψ →
      SizeValLe Ψ ρ ρ' →
      (∀ a : SizeExp, SizeWf Ψ a → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' a)) ∧
      (∀ a b : SizeExp, SizeLe Ψ a b → SizeOrd.le (evalSizeExp ρ a) (evalSizeExp ρ' b)) ∧
      (∀ a b : SizeExp, SizeLt Ψ a b → SizeOrd.lt (evalSizeExp ρ a) (evalSizeExp ρ' b)) := by
  exact fun Ψ ρ ρ' _ hval => ⟨size_wf_monotone Ψ ρ ρ' hval,
    fun _ _ h => size_le_sound_of_min_le Ψ ρ ρ' hval size_min_le_member h,
    fun _ _ h => size_lt_sound_of_min_le Ψ ρ ρ' hval size_min_le_member h⟩
