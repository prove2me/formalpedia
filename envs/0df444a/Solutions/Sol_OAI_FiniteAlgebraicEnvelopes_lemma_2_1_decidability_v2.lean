-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_2_1_decidability_v2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-12T23:11:36.097703+00:00
-- url     : https://prove2.me/submissions/6e67683a-f23f-4ab7-ba1a-4221f511f2a2

import Mathlib
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_BooneHigman
import Definitions.Def_lemma_2_1_data

open OAI.FiniteAlgebraicEnvelopes

universe u

namespace OAI.FiniteAlgebraicEnvelopes

variable {H : Type u} [Group H] {m : ℕ} (g : Fin m → H)

theorem evalWord_append (w1 w2 : Word m) :
    evalWord g (w1 ++ w2) = evalWord g w1 * evalWord g w2 := by
  simp [evalWord, List.map_append, List.prod_append]

def invertWord (w : Word m) : Word m := (w.map (fun l => (l.1, !l.2))).reverse

theorem evalWord_invertWord (w : Word m) :
    evalWord g (invertWord w) = (evalWord g w)⁻¹ := by
  induction w with
  | nil => simp [invertWord, evalWord]
  | cons hd tl ih =>
    have : invertWord (hd :: tl) = invertWord tl ++ [(hd.1, !hd.2)] := by
      simp [invertWord]
    rw [this, evalWord_append, ih]
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    cases hd.2 <;> simp [mul_inv_rev]

/-- A pair of `H`-words, representing an element of `H × H` (first coordinate from the first
word, second from the second). -/
abbrev WordPair (m : ℕ) := Word m × Word m

def pairEval (wp : WordPair m) : H × H := (evalWord g wp.1, evalWord g wp.2)

def mulPair (a b : WordPair m) : WordPair m := (a.1 ++ b.1, a.2 ++ b.2)

theorem pairEval_mulPair (a b : WordPair m) :
    pairEval g (mulPair a b) = pairEval g a * pairEval g b := by
  simp [pairEval, mulPair, evalWord_append, Prod.mul_def]

/-- A reduced form for a word in the HNN extension: a `head` block of `H × H`-generator
letters, followed by a list of `(stable-letter-sign, block)` pairs. `true` encodes `t`
(exponent `1`), `false` encodes `t⁻¹` (exponent `-1`). -/
abbrev HNNForm (m : ℕ) := WordPair m × List (Bool × WordPair m)

def emptyPair : WordPair m := ([], [])

def prependGen (i : Fin m) (sign copy : Bool) (w : HNNForm m) : HNNForm m :=
  if copy then (((i, sign) :: w.1.1, w.1.2), w.2)
  else ((w.1.1, (i, sign) :: w.1.2), w.2)

variable (decH : Word m → Bool)

def inDiagonal (wp : WordPair m) : Bool := decH (wp.1 ++ invertWord wp.2)
def inSecondFactor (wp : WordPair m) : Bool := decH wp.1

def phiFwd (wp : WordPair m) : WordPair m := ([], wp.2)
def phiBwd (wp : WordPair m) : WordPair m := (wp.2, wp.2)

def canCancel (sign sign2 : Bool) (head : WordPair m) : Bool :=
  (sign != sign2) && (if sign then inDiagonal decH head else inSecondFactor decH head)

def prependStable (sign : Bool) (w : HNNForm m) : HNNForm m :=
  match w.2 with
  | [] => (emptyPair, [(sign, w.1)])
  | (sign2, wp2) :: rest =>
    if canCancel decH sign sign2 w.1 then
      (mulPair (if sign then phiFwd w.1 else phiBwd w.1) wp2, rest)
    else
      (emptyPair, (sign, w.1) :: w.2)

/-- Apply one letter of the `2m+1`-generator word (first `m`: first-copy generators, next
`m`: second-copy generators, last: the stable letter) to a reduced form, on the left. -/
def applyLetter (letter : Fin (2 * m + 1) × Bool) (w : HNNForm m) : HNNForm m :=
  let i := letter.1.val
  if h : i < m then prependGen ⟨i, h⟩ letter.2 true w
  else if h2 : i < 2 * m then prependGen ⟨i - m, by omega⟩ letter.2 false w
  else prependStable decH letter.2 w

def decideWord (word : Word (2 * m + 1)) : Bool :=
  let w := word.foldr (applyLetter decH) (emptyPair, [])
  w.2.isEmpty && decH w.1.1 && decH w.1.2

def combinedGen (i : Fin (2 * m + 1)) :
    HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
      (diagonalEquivSecondFactor H) :=
  if h : i.val < m then HNNExtension.of (g ⟨i.val, h⟩, (1 : H))
  else if h2 : i.val < 2 * m then HNNExtension.of ((1 : H), g ⟨i.val - m, by omega⟩)
  else HNNExtension.t

def evalHNNForm (w : HNNForm m) :
    HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
      (diagonalEquivSecondFactor H) :=
  HNNExtension.of (pairEval g w.1) *
    (w.2.map (fun p => (if p.1 then HNNExtension.t else HNNExtension.t⁻¹) *
      HNNExtension.of (pairEval g p.2))).prod

theorem evalHNNForm_empty :
    evalHNNForm g ((emptyPair : WordPair m), ([] : List (Bool × WordPair m))) = 1 := by
  simp only [evalHNNForm, emptyPair, pairEval, evalWord, List.map_nil, List.prod_nil, mul_one]
  rw [show ((1 : H), (1 : H)) = (1 : H × H) from rfl, map_one]

theorem evalHNNForm_prependGen (i : Fin m) (sign copy : Bool) (w : HNNForm m) :
    evalHNNForm g (prependGen i sign copy w) =
      (if copy then HNNExtension.of ((if sign then g i else (g i)⁻¹), (1 : H))
       else HNNExtension.of ((1 : H), (if sign then g i else (g i)⁻¹))) *
        evalHNNForm g w := by
  rcases w with ⟨⟨w1, w2⟩, l⟩
  cases copy <;>
    · unfold evalHNNForm pairEval prependGen
      simp only [Bool.false_eq_true, if_false, if_true]
      rw [← mul_assoc, ← map_mul]
      congr 2
      cases sign <;> simp [evalWord, Prod.mul_def]

variable {decH}

theorem eq_of_inDiagonal (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    {wp : WordPair m} (h : inDiagonal decH wp = true) :
    evalWord g wp.1 = evalWord g wp.2 := by
  have h1 := (hdecH _).mp h
  rw [evalWord_append, evalWord_invertWord] at h1
  exact (mul_inv_eq_one.mp h1)

theorem eq_one_of_inSecondFactor (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    {wp : WordPair m} (h : inSecondFactor decH wp = true) :
    evalWord g wp.1 = 1 := (hdecH _).mp h

theorem pairEval_phiFwd (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (wp : WordPair m) (h : inDiagonal decH wp = true) :
    pairEval g (phiFwd wp) =
      (diagonalEquivSecondFactor H ⟨pairEval g wp, eq_of_inDiagonal g hdecH h⟩ : H × H) := by
  have heq := eq_of_inDiagonal g hdecH h
  have hsub : (⟨pairEval g wp, eq_of_inDiagonal g hdecH h⟩ : diagonalSubgroup H) =
      ⟨(evalWord g wp.2, evalWord g wp.2), rfl⟩ := by
    apply Subtype.ext; simp [pairEval, heq]
  rw [hsub, diagonalEquivSecondFactor_apply]
  simp [phiFwd, pairEval, evalWord]

theorem pairEval_phiBwd (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (wp : WordPair m) (h : inSecondFactor decH wp = true) :
    pairEval g (phiBwd wp) =
      ((diagonalEquivSecondFactor H).symm
        ⟨pairEval g wp, eq_one_of_inSecondFactor g hdecH h⟩ : H × H) := by
  have heq := eq_one_of_inSecondFactor g hdecH h
  have hsub : (⟨pairEval g wp, eq_one_of_inSecondFactor g hdecH h⟩ : secondFactorSubgroup H) =
      ⟨(1, evalWord g wp.2), rfl⟩ := by
    apply Subtype.ext; simp [pairEval, heq]
  have hcong : ((diagonalEquivSecondFactor H).symm
        ⟨pairEval g wp, eq_one_of_inSecondFactor g hdecH h⟩ : H × H) =
      ((diagonalEquivSecondFactor H).symm ⟨(1, evalWord g wp.2), rfl⟩ : H × H) :=
    congrArg (fun x => ((diagonalEquivSecondFactor H).symm x : H × H)) hsub
  have hforward : (diagonalEquivSecondFactor H) ⟨(evalWord g wp.2, evalWord g wp.2), rfl⟩ =
      (⟨(1, evalWord g wp.2), rfl⟩ : secondFactorSubgroup H) :=
    Subtype.ext (diagonalEquivSecondFactor_apply H (evalWord g wp.2))
  have hbackward := congrArg (diagonalEquivSecondFactor H).symm hforward
  rw [MulEquiv.symm_apply_apply] at hbackward
  have hval := congrArg Subtype.val hbackward
  calc pairEval g (phiBwd wp)
      = ((evalWord g wp.2, evalWord g wp.2) : H × H) := by simp [phiBwd, pairEval]
    _ = ((diagonalEquivSecondFactor H).symm ⟨(1, evalWord g wp.2), rfl⟩ : H × H) := hval
    _ = ((diagonalEquivSecondFactor H).symm
          ⟨pairEval g wp, eq_one_of_inSecondFactor g hdecH h⟩ : H × H) := hcong.symm

theorem evalHNNForm_noCancel (sign : Bool) (w : HNNForm m) :
    evalHNNForm g (emptyPair, (sign, w.1) :: w.2) =
      (if sign then HNNExtension.t else HNNExtension.t⁻¹) * evalHNNForm g w := by
  rcases w with ⟨head, l⟩
  simp only [evalHNNForm, List.map_cons, List.prod_cons]
  have h1 : (HNNExtension.of (pairEval g (emptyPair : WordPair m)) :
      HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
        (diagonalEquivSecondFactor H)) = 1 := by
    simp only [emptyPair, pairEval, evalWord, List.map_nil, List.prod_nil]
    rw [show ((1 : H), (1 : H)) = (1 : H × H) from rfl, map_one]
  rw [h1, one_mul, mul_assoc]

theorem evalHNNForm_cancel_fwd (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (head wp2 : WordPair m) (rest : List (Bool × WordPair m))
    (hmem : inDiagonal decH head = true) :
    evalHNNForm g (mulPair (phiFwd head) wp2, rest) =
      HNNExtension.t * evalHNNForm g (head, (false, wp2) :: rest) := by
  have hpe := pairEval_phiFwd g hdecH head hmem
  have hce := HNNExtension.equiv_eq_conj (A := diagonalSubgroup H)
    (B := secondFactorSubgroup H) (φ := diagonalEquivSecondFactor H)
    ⟨pairEval g head, eq_of_inDiagonal g hdecH hmem⟩
  simp only [evalHNNForm, List.map_cons, List.prod_cons]
  rw [pairEval_mulPair, map_mul, hpe, hce]
  simp only [mul_assoc, Bool.false_eq_true, if_false]

theorem evalHNNForm_cancel_bwd (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (head wp2 : WordPair m) (rest : List (Bool × WordPair m))
    (hmem : inSecondFactor decH head = true) :
    evalHNNForm g (mulPair (phiBwd head) wp2, rest) =
      HNNExtension.t⁻¹ * evalHNNForm g (head, (true, wp2) :: rest) := by
  have hpe := pairEval_phiBwd g hdecH head hmem
  have hce := HNNExtension.equiv_symm_eq_conj (A := diagonalSubgroup H)
    (B := secondFactorSubgroup H) (φ := diagonalEquivSecondFactor H)
    ⟨pairEval g head, eq_one_of_inSecondFactor g hdecH hmem⟩
  simp only [evalHNNForm, List.map_cons, List.prod_cons]
  rw [pairEval_mulPair, map_mul, hpe, hce]
  simp [mul_assoc]

theorem evalHNNForm_prependStable (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (sign : Bool) (w : HNNForm m) :
    evalHNNForm g (prependStable decH sign w) =
      (if sign then HNNExtension.t else HNNExtension.t⁻¹) * evalHNNForm g w := by
  rcases w with ⟨head, l⟩
  rcases l with _ | ⟨⟨sign2, wp2⟩, rest⟩
  · simp only [prependStable]
    exact evalHNNForm_noCancel g sign (head, [])
  · by_cases hcc : canCancel decH sign sign2 head = true
    · have hcc' := hcc
      simp only [canCancel, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcc'
      obtain ⟨hsign, hmem⟩ := hcc'
      rcases sign with _ | _
      · -- sign = false (t⁻¹), head ∈ B, sign2 = true
        have hsign2 : sign2 = true := by cases sign2 <;> simp_all
        subst hsign2
        have hps : prependStable decH false (head, (true, wp2) :: rest) =
            (mulPair (phiBwd head) wp2, rest) := by simp [prependStable, hcc]
        rw [hps]
        exact evalHNNForm_cancel_bwd g hdecH head wp2 rest hmem
      · -- sign = true (t), head ∈ A, sign2 = false
        have hsign2 : sign2 = false := by cases sign2 <;> simp_all
        subst hsign2
        have hps : prependStable decH true (head, (false, wp2) :: rest) =
            (mulPair (phiFwd head) wp2, rest) := by simp [prependStable, hcc]
        rw [hps]
        exact evalHNNForm_cancel_fwd g hdecH head wp2 rest hmem
    · simp only [prependStable, hcc]
      exact evalHNNForm_noCancel g sign (head, (sign2, wp2) :: rest)

theorem of_inv_fst (A : Subgroup (H × H)) (B : Subgroup (H × H)) (φ : A ≃* B) (x : H) :
    (HNNExtension.of ((x⁻¹, (1 : H))) : HNNExtension (H × H) A B φ) =
      (HNNExtension.of (x, (1 : H)))⁻¹ := by
  rw [← map_inv]; congr 1; simp

theorem of_inv_snd (A : Subgroup (H × H)) (B : Subgroup (H × H)) (φ : A ≃* B) (x : H) :
    (HNNExtension.of (((1 : H), x⁻¹)) : HNNExtension (H × H) A B φ) =
      (HNNExtension.of ((1 : H), x))⁻¹ := by
  rw [← map_inv]; congr 1; simp

theorem evalHNNForm_applyLetter (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (letter : Fin (2 * m + 1) × Bool) (w : HNNForm m) :
    evalHNNForm g (applyLetter decH letter w) =
      (if letter.2 then combinedGen g letter.1 else (combinedGen g letter.1)⁻¹) *
        evalHNNForm g w := by
  rcases letter with ⟨i, sign⟩
  simp only [applyLetter]
  by_cases h1 : i.val < m
  · rw [dif_pos h1, evalHNNForm_prependGen]
    congr 1
    simp only [combinedGen, dif_pos h1]
    cases sign <;> first | rfl | exact of_inv_fst _ _ _ _
  · rw [dif_neg h1]
    by_cases h2 : i.val < 2 * m
    · rw [dif_pos h2, evalHNNForm_prependGen]
      congr 1
      simp only [combinedGen, dif_neg h1, dif_pos h2]
      cases sign <;> first | rfl | exact of_inv_snd _ _ _ _
    · rw [dif_neg h2, evalHNNForm_prependStable g hdecH]
      congr 1
      simp only [combinedGen, dif_neg h1, dif_neg h2]

theorem evalHNNForm_foldr (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (word : Word (2 * m + 1)) (init : HNNForm m) :
    evalHNNForm g (word.foldr (applyLetter decH) init) =
      evalWord (combinedGen g) word * evalHNNForm g init := by
  induction word with
  | nil => simp [evalWord]
  | cons hd tl ih =>
    simp only [List.foldr_cons, evalHNNForm_applyLetter g hdecH, ih, evalWord, List.map_cons,
      List.prod_cons, mul_assoc]

def signToUnit (b : Bool) : ℤˣ := if b then 1 else -1

def IsReducedList (l : List (Bool × WordPair m)) : Prop :=
  (l.map (fun p => (signToUnit p.1, pairEval g p.2))).IsChain
    (fun a b => a.2 ∈ HNNExtension.toSubgroup (diagonalSubgroup H) (secondFactorSubgroup H) a.1 →
      a.1 = b.1)

theorem inDiagonal_iff (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (wp : WordPair m) : inDiagonal decH wp = true ↔ pairEval g wp ∈ diagonalSubgroup H := by
  rw [mem_diagonalSubgroup]
  constructor
  · exact eq_of_inDiagonal g hdecH
  · intro h
    rw [inDiagonal, hdecH, evalWord_append, evalWord_invertWord]
    exact mul_inv_eq_one.mpr h

theorem inSecondFactor_iff (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (wp : WordPair m) : inSecondFactor decH wp = true ↔ pairEval g wp ∈ secondFactorSubgroup H := by
  rw [mem_secondFactorSubgroup]
  exact hdecH wp.1

theorem IsReducedList.tail {l : List (Bool × WordPair m)} (h : IsReducedList g l) :
    IsReducedList g l.tail := by
  unfold IsReducedList at *
  rcases l with _ | ⟨hd, tl⟩
  · exact h
  · simpa using h.tail

theorem IsReducedList_prependStable (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (sign : Bool) (w : HNNForm m) (hw : IsReducedList g w.2) :
    IsReducedList g (prependStable decH sign w).2 := by
  rcases w with ⟨head, l⟩
  rcases l with _ | ⟨⟨sign2, wp2⟩, rest⟩
  · simp only [prependStable]
    exact List.isChain_singleton _
  · by_cases hcc : canCancel decH sign sign2 head = true
    · have hcc' := hcc
      simp only [canCancel, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcc'
      rcases sign with _ | _
      · have hsign2 : sign2 = true := by cases sign2 <;> simp_all
        subst hsign2
        have hps : prependStable decH false (head, (true, wp2) :: rest) =
            (mulPair (phiBwd head) wp2, rest) := by simp [prependStable, hcc]
        rw [hps]
        exact hw.tail
      · have hsign2 : sign2 = false := by cases sign2 <;> simp_all
        subst hsign2
        have hps : prependStable decH true (head, (false, wp2) :: rest) =
            (mulPair (phiFwd head) wp2, rest) := by simp [prependStable, hcc]
        rw [hps]
        exact hw.tail
    · simp only [prependStable, hcc, Bool.false_eq_true, if_false]
      simp only [IsReducedList, List.map_cons]
      rw [List.isChain_cons]
      refine ⟨?_, hw⟩
      intro y hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      intro hmemA
      simp only [signToUnit] at hmemA ⊢
      by_contra hne
      apply hcc
      simp only [canCancel, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rcases sign with _ | _ <;> rcases sign2 with _ | _ <;> simp_all
      · rcases sign with _ | _
        · simp only [Bool.false_eq_true, if_false] at hmemA ⊢
          rw [HNNExtension.toSubgroup_neg_one] at hmemA
          rw [inSecondFactor_iff g hdecH]
          exact hmemA
        · simp only [if_true] at hmemA ⊢
          rw [HNNExtension.toSubgroup_one] at hmemA
          rw [inDiagonal_iff g hdecH]
          exact hmemA

theorem IsReducedList_applyLetter (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (letter : Fin (2 * m + 1) × Bool) (w : HNNForm m) (hw : IsReducedList g w.2) :
    IsReducedList g (applyLetter decH letter w).2 := by
  rcases letter with ⟨i, sign⟩
  simp only [applyLetter]
  by_cases h1 : i.val < m
  · rw [dif_pos h1]; exact hw
  · rw [dif_neg h1]
    by_cases h2 : i.val < 2 * m
    · rw [dif_pos h2]; exact hw
    · rw [dif_neg h2]; exact IsReducedList_prependStable g hdecH sign w hw

theorem IsReducedList_foldr (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (word : Word (2 * m + 1)) (init : HNNForm m) (hinit : IsReducedList g init.2) :
    IsReducedList g (word.foldr (applyLetter decH) init).2 := by
  induction word with
  | nil => exact hinit
  | cons hd tl ih => exact IsReducedList_applyLetter g hdecH hd _ ih

def toReducedWord (w : HNNForm m) (h : IsReducedList g w.2) :
    HNNExtension.NormalWord.ReducedWord (H × H) (diagonalSubgroup H) (secondFactorSubgroup H) where
  head := pairEval g w.1
  toList := w.2.map (fun p => (signToUnit p.1, pairEval g p.2))
  chain := by unfold IsReducedList at h; exact h

theorem toReducedWord_prod (w : HNNForm m) (h : IsReducedList g w.2) :
    (toReducedWord g w h).prod (diagonalEquivSecondFactor H) = evalHNNForm g w := by
  rcases w with ⟨head, l⟩
  simp only [toReducedWord, HNNExtension.NormalWord.ReducedWord.prod, evalHNNForm]
  congr 1
  clear h
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    congr 1
    cases hd.1 <;> simp [signToUnit]

theorem decideWord_correct (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1)
    (word : Word (2 * m + 1)) :
    decideWord decH word = true ↔ evalWord (combinedGen g) word = 1 := by
  have hval : evalHNNForm g (word.foldr (applyLetter decH) (emptyPair, [])) =
      evalWord (combinedGen g) word := by
    rw [evalHNNForm_foldr g hdecH, evalHNNForm_empty, mul_one]
  have hred : IsReducedList g (word.foldr (applyLetter decH) (emptyPair, [])).2 :=
    IsReducedList_foldr g hdecH word (emptyPair, []) List.isChain_nil
  set w := word.foldr (applyLetter decH) (emptyPair, []) with hw_def
  unfold decideWord
  rw [← hw_def]
  rcases hl : w.2 with _ | ⟨hd, tl⟩
  · simp only [hl, List.isEmpty_nil, Bool.true_and]
    rw [Bool.and_eq_true, hdecH, hdecH, ← hval, evalHNNForm, hl]
    simp only [List.map_nil, List.prod_nil, mul_one]
    constructor
    · rintro ⟨h1, h2⟩
      have hpair : pairEval g w.1 = (1, 1) := Prod.ext h1 h2
      rw [hpair, show ((1 : H), (1 : H)) = (1 : H × H) from rfl, map_one]
    · intro h
      have h1 : (HNNExtension.of (pairEval g w.1) :
          HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
            (diagonalEquivSecondFactor H)) =
          HNNExtension.of ((1, 1) : H × H) := by
        rw [h, show ((1 : H), (1 : H)) = (1 : H × H) from rfl, map_one]
      have heqpair := HNNExtension.of_injective (A := diagonalSubgroup H)
        (B := secondFactorSubgroup H) (φ := diagonalEquivSecondFactor H) h1
      exact ⟨congrArg Prod.fst heqpair, congrArg Prod.snd heqpair⟩
  · simp only [hl, List.isEmpty_cons, Bool.false_and]
    constructor
    · intro h; exact absurd h (by simp)
    · intro heq
      exfalso
      rw [← hval] at heq
      have hred' : IsReducedList g (hd :: tl) := hl ▸ hred
      have hmem : evalHNNForm g w ∈
          (HNNExtension.of (A := diagonalSubgroup H) (B := secondFactorSubgroup H)
            (φ := diagonalEquivSecondFactor H)).range := by
        rw [heq]; exact ⟨1, map_one _⟩
      rw [← toReducedWord_prod g w hred] at hmem
      have := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        (diagonalEquivSecondFactor H) _ hmem
      simp only [toReducedWord, hl] at this
      simp at this

section Computability

theorem primrec_invertWord : Primrec (invertWord (m := m)) := by
  unfold invertWord
  exact Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.not.comp (Primrec.snd.comp Primrec.snd))))

end Computability

theorem primrec_mulPair : Primrec₂ (mulPair (m := m)) := by
  unfold mulPair
  exact (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem primrec_prependGenList (copy : Bool) :
    Primrec₂ (fun (p : (Fin m × Bool)) (w : WordPair m) =>
      if copy then (p :: w.1, w.2) else (w.1, p :: w.2)) := by
  cases copy
  · exact (Primrec.fst.comp Primrec.snd).pair
      (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  · exact (Primrec.list_cons.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)

variable (decH : Word m → Bool) (hCompDecH : Computable decH)

theorem computable_inDiagonal (hCompDecH : Computable decH) :
    Computable (inDiagonal decH : WordPair m → Bool) := by
  unfold inDiagonal
  exact hCompDecH.comp
    ((Primrec.list_append.comp Primrec.fst (primrec_invertWord.comp Primrec.snd)).to_comp)

theorem computable_inSecondFactor (hCompDecH : Computable decH) :
    Computable (inSecondFactor decH : WordPair m → Bool) := by
  unfold inSecondFactor
  exact hCompDecH.comp Primrec.fst.to_comp

theorem computable_canCancel (hCompDecH : Computable decH) :
    Computable (fun p : Bool × Bool × WordPair m => canCancel decH p.1 p.2.1 p.2.2) := by
  unfold canCancel
  have hbne : Computable (fun p : Bool × Bool × WordPair m => p.1 != p.2.1) :=
    (Primrec.cond Primrec.fst (Primrec.not.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)).to_comp.of_eq fun p => by
        cases p.1 <;> simp [bne]
  have hite : Computable (fun p : Bool × Bool × WordPair m =>
      if p.1 then inDiagonal decH p.2.2 else inSecondFactor decH p.2.2) :=
    (Computable.cond Primrec.fst.to_comp
      ((computable_inDiagonal decH hCompDecH).comp (Primrec.snd.comp Primrec.snd).to_comp)
      ((computable_inSecondFactor decH hCompDecH).comp
        (Primrec.snd.comp Primrec.snd).to_comp)).of_eq fun p => by cases p.1 <;> rfl
  exact ((Primrec.and.to_comp).comp hbne hite).of_eq fun p => by simp

theorem prependStable_eq_option (sign : Bool) (w : HNNForm m) :
    prependStable decH sign w =
      Option.casesOn (motive := fun _ => HNNForm m) w.2.head? (emptyPair, [(sign, w.1)])
        (fun hd => if canCancel decH sign hd.1 w.1 then
            (mulPair (if sign then phiFwd w.1 else phiBwd w.1) hd.2, w.2.tail)
          else (emptyPair, (sign, w.1) :: w.2)) := by
  rcases w with ⟨head, l⟩
  cases l with
  | nil => simp [prependStable]
  | cons hd tl => simp [prependStable]

theorem primrec_phiFwd : Primrec (phiFwd (m := m)) := by
  unfold phiFwd
  exact (Primrec.const []).pair Primrec.snd

theorem primrec_phiBwd : Primrec (phiBwd (m := m)) := by
  unfold phiBwd
  exact Primrec.snd.pair Primrec.snd

theorem computable_hcc (hCompDecH : Computable decH) :
    Computable (fun p : (Bool × HNNForm m) × (Bool × WordPair m) =>
      canCancel decH p.1.1 p.2.1 p.1.2.1) :=
  ((computable_canCancel decH hCompDecH).comp
    (((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      )).to_comp)).of_eq fun p => rfl

set_option maxHeartbeats 0 in
theorem computable_prependStable (hCompDecH : Computable decH) :
    Computable₂ (prependStable decH : Bool → HNNForm m → HNNForm m) := by
  have ho : Computable (fun p : Bool × HNNForm m => p.2.2.head?) :=
    (Primrec.list_head?.comp (Primrec.snd.comp Primrec.snd)).to_comp
  have hf : Computable (fun p : Bool × HNNForm m => ((emptyPair : WordPair m), [(p.1, p.2.1)])) :=
    ((Primrec.const (emptyPair : WordPair m)).pair
      (Primrec.list_cons.comp
        (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
        (Primrec.const ([] : List (Bool × WordPair m))))).to_comp
  have hcc := computable_hcc decH hCompDecH
  have hphi : Computable (fun p : (Bool × HNNForm m) × (Bool × WordPair m) =>
      if p.1.1 then phiFwd p.1.2.1 else phiBwd p.1.2.1) :=
    (Computable.cond (Primrec.fst.comp Primrec.fst).to_comp
      (primrec_phiFwd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to_comp
      (primrec_phiBwd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).to_comp).of_eq
      fun p => by cases p.1.1 <;> rfl
  have htrue : Computable (fun p : (Bool × HNNForm m) × (Bool × WordPair m) =>
      (mulPair (if p.1.1 then phiFwd p.1.2.1 else phiBwd p.1.2.1) p.2.2,
        p.1.2.2.tail)) :=
    (primrec_mulPair.to_comp.comp hphi
      (Primrec.snd.comp Primrec.snd).to_comp).pair
      (Primrec.list_tail.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to_comp
  have hfalse : Computable (fun p : (Bool × HNNForm m) × (Bool × WordPair m) =>
      ((emptyPair : WordPair m),
        (p.1.1, p.1.2.1) :: p.1.2.2)) :=
    ((Primrec.const (emptyPair : WordPair m)).pair
      (Primrec.list_cons.comp
        ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to_comp
  have hg : Computable₂ (fun (a : Bool × HNNForm m) (hd : Bool × WordPair m) =>
      if canCancel decH a.1 hd.1 a.2.1 then
          (mulPair (if a.1 then phiFwd a.2.1 else phiBwd a.2.1) hd.2, a.2.2.tail)
        else (emptyPair, (a.1, a.2.1) :: a.2.2)) :=
    (Computable.cond hcc htrue hfalse).of_eq fun p => by
      cases h : canCancel decH p.1.1 p.2.1 p.1.2.1 <;> simp [h]
  have key : Computable (fun p : Bool × HNNForm m =>
      Option.casesOn (motive := fun _ => HNNForm m) p.2.2.head? (emptyPair, [(p.1, p.2.1)])
        (fun hd => if canCancel decH p.1 hd.1 p.2.1 then
            (mulPair (if p.1 then phiFwd p.2.1 else phiBwd p.2.1) hd.2, p.2.2.tail)
          else (emptyPair, (p.1, p.2.1) :: p.2.2))) :=
    Computable.option_casesOn ho hf hg
  exact key.of_eq fun p => (prependStable_eq_option decH p.1 p.2).symm

theorem primrec_prependGen (copy : Bool) :
    Primrec (fun (q : (Fin m × Bool) × HNNForm m) => prependGen q.1.1 q.1.2 copy q.2) := by
  unfold prependGen
  have hp1 : Primrec (fun q : (Fin m × Bool) × HNNForm m => q.1) := Primrec.fst
  have hp211 : Primrec (fun q : (Fin m × Bool) × HNNForm m => q.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hp212 : Primrec (fun q : (Fin m × Bool) × HNNForm m => q.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hp22 : Primrec (fun q : (Fin m × Bool) × HNNForm m => q.2.2) :=
    Primrec.snd.comp Primrec.snd
  cases copy
  · exact (hp211.pair (Primrec.list_cons.comp hp1 hp212)).pair hp22
  · exact ((Primrec.list_cons.comp hp1 hp211).pair hp212).pair hp22

set_option maxHeartbeats 0 in
theorem computable_applyLetter (hm : 0 < m) (hCompDecH : Computable decH) :
    Computable₂ (applyLetter decH : (Fin (2 * m + 1) × Bool) → HNNForm m → HNNForm m) := by
  have hidxFst : Primrec (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      (⟨q.1.1.val % m, Nat.mod_lt _ hm⟩ : Fin m)) :=
    Primrec.fin_val_iff.mp
      (Primrec.nat_mod.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const m))
  have hidxSnd : Primrec (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      (⟨(q.1.1.val - m) % m, Nat.mod_lt _ hm⟩ : Fin m)) :=
    Primrec.fin_val_iff.mp
      (Primrec.nat_mod.comp
        (Primrec.nat_sub.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.const m))
        (Primrec.const m))
  have hFin1 : Computable (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      prependGen ⟨q.1.1.val % m, Nat.mod_lt _ hm⟩ q.1.2 true q.2) :=
    ((primrec_prependGen true).comp
      ((hidxFst.pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp
  have hFin2 : Computable (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      prependGen ⟨(q.1.1.val - m) % m, Nat.mod_lt _ hm⟩ q.1.2 false q.2) :=
    ((primrec_prependGen false).comp
      ((hidxSnd.pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp
  have hStable : Computable (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      prependStable decH q.1.2 q.2) :=
    (computable_prependStable decH hCompDecH).comp
      ((Primrec.snd.comp Primrec.fst).to_comp) Computable.snd
  have hCondInner : Computable (fun q : (Fin (2 * m + 1) × Bool) × HNNForm m =>
      if q.1.1.val < 2 * m then
        prependGen ⟨(q.1.1.val - m) % m, Nat.mod_lt _ hm⟩ q.1.2 false q.2
      else prependStable decH q.1.2 q.2) :=
    (Computable.cond
      (Primrec.nat_lt.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const (2 * m))).decide.to_comp
      hFin2 hStable).of_eq fun q => by
        by_cases h : q.1.1.val < 2 * m <;> simp [h]
  exact (Computable.cond
    (Primrec.nat_lt.comp (Primrec.fin_val.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.const m)).decide.to_comp
    hFin1 hCondInner).of_eq fun q => by
      simp only [Bool.cond_decide]
      unfold applyLetter
      by_cases h1 : q.1.1.val < m
      · rw [if_pos h1, dif_pos h1]
        have hidx : (⟨q.1.1.val % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨q.1.1.val, h1⟩ :=
          Fin.ext (Nat.mod_eq_of_lt h1)
        rw [hidx]
      · rw [if_neg h1, dif_neg h1]
        by_cases h2 : q.1.1.val < 2 * m
        · rw [if_pos h2, dif_pos h2]
          have hidx : (⟨(q.1.1.val - m) % m, Nat.mod_lt _ hm⟩ : Fin m) = ⟨q.1.1.val - m, by omega⟩ :=
            Fin.ext (Nat.mod_eq_of_lt (by omega))
          rw [hidx]
        · rw [if_neg h2, dif_neg h2]

theorem natRec_ext {β : Type*} (init : β) (step1 step2 : ℕ → β → β) (n : ℕ)
    (h : ∀ k < n, step1 k = step2 k) :
    Nat.rec (motive := fun _ => β) init step1 n = Nat.rec (motive := fun _ => β) init step2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show step1 n (Nat.rec init step1 n) = step2 n (Nat.rec init step2 n)
    rw [ih fun k hk => h k (by omega), h n (by omega)]

theorem foldr_eq_natRec (decH : Word m → Bool) (word : Word (2 * m + 1)) :
    word.foldr (applyLetter decH) (emptyPair, []) =
      Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
        (fun k IH => applyLetter decH
          (word.reverse.getD k (⟨0, by omega⟩, false)) IH)
        word.length := by
  induction word with
  | nil => rfl
  | cons hd tl ih =>
    have hstep : Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
        (fun k IH => applyLetter decH ((hd :: tl).reverse.getD k (⟨0, by omega⟩, false)) IH)
        (tl.length + 1) =
      applyLetter decH ((hd :: tl).reverse.getD tl.length (⟨0, by omega⟩, false))
        (Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
          (fun k IH => applyLetter decH ((hd :: tl).reverse.getD k (⟨0, by omega⟩, false)) IH)
          tl.length) := rfl
    have hlen : (hd :: tl).length = tl.length + 1 := rfl
    show applyLetter decH hd (tl.foldr (applyLetter decH) (emptyPair, [])) = _
    rw [ih, hlen, hstep]
    have hmatch : Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
        (fun k IH => applyLetter decH (tl.reverse.getD k (⟨0, by omega⟩, false)) IH) tl.length =
      Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
        (fun k IH => applyLetter decH ((hd :: tl).reverse.getD k (⟨0, by omega⟩, false)) IH)
        tl.length := by
      apply natRec_ext
      intro k hk
      funext IH
      rw [show tl.reverse.getD k ((⟨0, by omega⟩ : Fin (2 * m + 1)), false) =
          (hd :: tl).reverse.getD k ((⟨0, by omega⟩ : Fin (2 * m + 1)), false) from by
        rw [List.reverse_cons,
          List.getD_append tl.reverse [hd] (⟨0, by omega⟩, false) k (by simpa using hk)]]
    rw [← hmatch]
    congr 1
    rw [List.reverse_cons]
    rw [List.getD_append_right tl.reverse [hd] (⟨0, by omega⟩, false) tl.length
      (by simp)]
    simp

set_option maxHeartbeats 0 in
theorem computable_decideWord (hm : 0 < m) (hCompDecH : Computable decH) :
    Computable (decideWord decH : Word (2 * m + 1) → Bool) := by
  have hCompLetter := computable_applyLetter decH hm hCompDecH
  have hfoldStep : Computable₂ (fun (word : Word (2 * m + 1)) (p : ℕ × HNNForm m) =>
      applyLetter decH (word.reverse.getD p.1 (⟨0, by omega⟩, false)) p.2) :=
    hCompLetter.comp
      ((Primrec.list_getElem?.comp (Primrec.list_reverse.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd)).to_comp.option_getD
          (Computable.const (((⟨0, by omega⟩ : Fin (2 * m + 1)), false) :
            Fin (2 * m + 1) × Bool)))
      (Computable.snd.comp Computable.snd)
  have hfold : Computable (fun word : Word (2 * m + 1) =>
      Nat.rec (motive := fun _ => HNNForm m) (emptyPair, [])
        (fun k IH => applyLetter decH
          (word.reverse.getD k (⟨0, by omega⟩, false)) IH)
        word.length) :=
    Computable.nat_rec Primrec.list_length.to_comp (Computable.const (emptyPair, [])) hfoldStep
  have hfold2 : Computable (fun word : Word (2 * m + 1) =>
      word.foldr (applyLetter decH) (emptyPair, [])) :=
    hfold.of_eq fun word => (foldr_eq_natRec decH word).symm
  unfold decideWord
  have h1 : Computable (fun word : Word (2 * m + 1) =>
      (word.foldr (applyLetter decH) (emptyPair, [])).2.isEmpty &&
      decH (word.foldr (applyLetter decH) (emptyPair, [])).1.1 &&
      decH (word.foldr (applyLetter decH) (emptyPair, [])).1.2) := by
    have hisEmpty : Primrec (fun l : List (Bool × WordPair m) => l.isEmpty) :=
      (Primrec.list_casesOn Primrec.id (Primrec.const true)
        (Primrec.const false).to₂).of_eq fun l => by cases l <;> rfl
    have hA : Computable (fun word : Word (2 * m + 1) =>
        (word.foldr (applyLetter decH) (emptyPair, [])).2.isEmpty) :=
      (hisEmpty.comp (Primrec.snd.comp (Primrec.id (α := HNNForm m)))).to_comp.comp hfold2
    have hB : Computable (fun word : Word (2 * m + 1) =>
        decH (word.foldr (applyLetter decH) (emptyPair, [])).1.1) :=
      hCompDecH.comp (Computable.fst.comp (Computable.fst.comp hfold2))
    have hC : Computable (fun word : Word (2 * m + 1) =>
        decH (word.foldr (applyLetter decH) (emptyPair, [])).1.2) :=
      hCompDecH.comp (Computable.snd.comp (Computable.fst.comp hfold2))
    exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp hA hB) hC)
  exact h1

theorem decideWord_computablePred (hm : 0 < m) (hCompDecH : Computable decH)
    (hdecH : ∀ w : Word m, decH w = true ↔ evalWord g w = 1) :
    ComputablePred (fun word : Word (2 * m + 1) => evalWord (combinedGen g) word = 1) := by
  have hdec : DecidablePred (fun word : Word (2 * m + 1) => evalWord (combinedGen g) word = 1) :=
    fun word => decidable_of_iff (decideWord decH word = true) (decideWord_correct g hdecH word)
  refine ⟨hdec, ?_⟩
  have hcomp := computable_decideWord decH hm hCompDecH
  refine hcomp.of_eq fun word => ?_
  rcases Decidable.em (evalWord (combinedGen g) word = 1) with hp | hp
  · rw [(decideWord_correct g hdecH word).mpr hp, decide_eq_true_eq.mpr hp]
  · cases hb : decideWord decH word
    · exact (decide_eq_false_iff_not.mpr hp).symm
    · exact absurd ((decideWord_correct g hdecH word).mp hb) hp


theorem pad_generators {H : Type u} [Group H] (hH : HasDecidableWordProblem H) :
    ∃ (m : ℕ) (g : Fin (m + 1) → H), Subgroup.closure (Set.range g) = ⊤ ∧
      ComputablePred (fun w : Word (m + 1) => evalWord g w = 1) := by
  obtain ⟨m0, g0, hclosure0, hcomp0⟩ := hH
  match m0, g0, hclosure0, hcomp0 with
  | 0, g0, hclosure0, _ =>
    have hbot : (⊥ : Subgroup H) = ⊤ := by
      rw [← hclosure0]
      rw [show Set.range g0 = (∅ : Set H) from by simp]
      exact (Subgroup.closure_empty).symm
    refine ⟨0, fun _ => (1 : H), ?_, ?_⟩
    · rw [show Set.range (fun _ : Fin 1 => (1 : H)) = {1} from by simp]
      rw [Subgroup.closure_singleton_one]
      exact hbot
    · have htrivial : ∀ w : Word 1, evalWord (fun _ : Fin 1 => (1 : H)) w = 1 := by
        intro w
        induction w with
        | nil => rfl
        | cons hd tl ih =>
          simp only [evalWord, List.map_cons, List.prod_cons] at ih ⊢
          rw [ih]
          cases hd.2 <;> simp
      exact ⟨fun w => isTrue (htrivial w), (Computable.const true).of_eq fun w => by
        simp [htrivial w]⟩
  | (m0 + 1), g0, hclosure0, hcomp0 =>
    exact ⟨m0, g0, hclosure0, hcomp0⟩



open Monoid Coprod Multiplicative Subgroup Function in
theorem hnn_gens_top {H : Type u} [Group H] (A B : Subgroup H) (φ : A ≃* B) :
    Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
      {HNNExtension.t (A := A) (B := B) (φ := φ)}) = ⊤ := by
  have hsurj : Function.Surjective (HNNExtension.con H A B φ).mk' := Con.mk'_surjective
  have h1 : Subgroup.closure (Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ)) ∪
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))) = ⊤ :=
    Coprod.closure_range_inl_union_inr
  have h2 : Subgroup.closure (((HNNExtension.con H A B φ).mk' :
      Coprod H (Multiplicative ℤ) →* HNNExtension H A B φ) ''
      (Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ)) ∪
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ)))) = ⊤ := by
    rw [← MonoidHom.map_closure, h1, Subgroup.map_top_of_surjective _ hsurj]
  rw [Set.image_union] at h2
  have heq1 : ((HNNExtension.con H A B φ).mk' ''
      Set.range (Coprod.inl : H →* Coprod H (Multiplicative ℤ))) =
      Set.range (HNNExtension.of : H →* HNNExtension H A B φ) := by
    rw [← Set.range_comp]; congr 1
  have hsub2 : ((HNNExtension.con H A B φ).mk' ''
      Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))) ⊆
      (Subgroup.zpowers (HNNExtension.t (A := A) (B := B) (φ := φ)) : Set (HNNExtension H A B φ)) := by
    rintro x ⟨y, ⟨n, rfl⟩, rfl⟩
    set k := Multiplicative.toAdd n with hk
    refine ⟨k, ?_⟩
    have hn : n = Multiplicative.ofAdd (1 : ℤ) ^ k := by
      rw [hk, ← Int.ofAdd_mul, one_mul]; rfl
    show (HNNExtension.t (A := A) (B := B) (φ := φ)) ^ k =
        (HNNExtension.con H A B φ).mk' (Coprod.inr n)
    rw [hn, map_zpow, map_zpow]
    rfl
  rw [heq1] at h2
  have hle : Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
      ((HNNExtension.con H A B φ).mk' ''
        Set.range (Coprod.inr : Multiplicative ℤ →* Coprod H (Multiplicative ℤ))))
      ≤ Subgroup.closure (Set.range (HNNExtension.of : H →* HNNExtension H A B φ) ∪
          {HNNExtension.t (A := A) (B := B) (φ := φ)}) := by
    rw [Subgroup.closure_le]
    apply Set.union_subset
    · exact Set.subset_union_left.trans Subgroup.subset_closure
    · refine hsub2.trans ?_
      rw [Subgroup.zpowers_eq_closure]
      exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono Set.subset_union_right)
  exact le_antisymm le_top (h2 ▸ hle)

theorem combinedGen_generates {H : Type u} [Group H] {m : ℕ} (g : Fin m → H)
    (hclosure : Subgroup.closure (Set.range g) = ⊤) :
    Subgroup.closure (Set.range (combinedGen g (m := m))) = ⊤ := by
  classical
  set A := diagonalSubgroup H
  set B := secondFactorSubgroup H
  set φ := diagonalEquivSecondFactor H
  set S : Set (H × H) := (MonoidHom.inl H H '' Set.range g) ∪ (MonoidHom.inr H H '' Set.range g)
    with hS_def
  have hSclosure : Subgroup.closure S = ⊤ := by
    apply le_antisymm le_top
    rw [hS_def, Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
      hclosure, ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map]
    intro x _
    obtain ⟨a, b⟩ := x
    have hab : ((a, b) : H × H) = (a, (1:H)) * ((1:H), b) := by simp [Prod.mul_def]
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩)
  have hofS : Subgroup.closure ((HNNExtension.of (A := A) (B := B) (φ := φ)) '' S) =
      (HNNExtension.of (A := A) (B := B) (φ := φ)).range := by
    rw [← MonoidHom.map_closure, hSclosure, MonoidHom.range_eq_map]
  have hofS' : (↑(Subgroup.closure ((HNNExtension.of (A := A) (B := B) (φ := φ)) '' S)) :
        Set (HNNExtension (H × H) A B φ)) =
      Set.range (HNNExtension.of (A := A) (B := B) (φ := φ)) := by
    rw [hofS, MonoidHom.coe_range]
  have hSrange : (HNNExtension.of (A := A) (B := B) (φ := φ)) '' S ⊆
      Set.range (combinedGen g (m := m)) := by
    rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨_, ⟨i, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩
    · refine ⟨⟨i.val, by omega⟩, ?_⟩
      unfold combinedGen
      rw [dif_pos (show i.val < m from i.isLt)]
      have hidx : (⟨i.val, show i.val < m from i.isLt⟩ : Fin m) = i := Fin.ext rfl
      rw [hidx]; rfl
    · refine ⟨⟨m + i.val, by omega⟩, ?_⟩
      unfold combinedGen
      rw [dif_neg (show ¬ (m + i.val < m) by omega),
        dif_pos (show m + i.val < 2 * m by omega)]
      have hidx : (⟨m + i.val - m, show m + i.val - m < m by omega⟩ : Fin m) = i :=
        Fin.ext (show m + i.val - m = i.val by omega)
      rw [hidx]; rfl
  have h1 := hnn_gens_top A B φ
  apply le_antisymm le_top
  rw [← h1, Subgroup.closure_le]
  apply Set.union_subset
  · rw [← hofS']
    exact SetLike.coe_subset_coe.mpr (Subgroup.closure_mono hSrange)
  · intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    have : (HNNExtension.t (A := A) (B := B) (φ := φ)) ∈ Set.range (combinedGen g (m := m)) := by
      refine ⟨⟨2 * m, by omega⟩, ?_⟩
      unfold combinedGen
      rw [dif_neg (show ¬ (2 * m < m) by omega),
        dif_neg (show ¬ (2 * m < 2 * m) by omega)]
    exact Subgroup.subset_closure this

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes in
theorem solution {H : Type u} [Group H] [Group.FG H]
    (hH : HasDecidableWordProblem H) :
    HasDecidableWordProblem (HNNExtension (H × H) (diagonalSubgroup H) (secondFactorSubgroup H)
      (diagonalEquivSecondFactor H)) := by
  obtain ⟨m, g, hclosure, hcomp⟩ := pad_generators hH
  obtain ⟨hdec, hCompDecide⟩ := hcomp
  have hCompDecH : Computable (fun w : Word (m + 1) => decide (evalWord g w = 1)) := hCompDecide
  refine ⟨2 * (m + 1) + 1, combinedGen g, combinedGen_generates g hclosure, ?_⟩
  exact decideWord_computablePred g (fun w => decide (evalWord g w = 1)) (by omega) hCompDecH
    (fun w => by simp)
