-- Prove2me | solution 1 for KarpPapadimitriou.Facial.notMem_DLang_iff_lt_on_hull
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:35:49.620512+00:00
-- url     : https://prove2.me/submissions/4fc2fdcf-f893-445a-9fd8-107febfce4d1

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

open KarpPapadimitriou.Facial ProjSchedTW.Complexity

private def digit (b : Bool) : BSym := if b then BSym.one else BSym.zero

private lemma digit_inj : Function.Injective digit := by
  intro a b h; cases a <;> cases b <;> simp_all [digit]

private lemma no_sep (xs : List Bool) : BSym.sep ∉ xs.map digit := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _; cases b <;> simp [digit]

private lemma no_minus (xs : List Bool) : BSym.minus ∉ xs.map digit := by
  simp only [List.mem_map, not_exists, not_and]
  intro b _; cases b <;> simp [digit]

private lemma peel (u v r s : List BSym) (hu : BSym.sep ∉ u) (hv : BSym.sep ∉ v)
    (h : u ++ BSym.sep :: r = v ++ BSym.sep :: s) : u = v ∧ r = s := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => simpa using h
    | cons b v =>
      have hb : b ≠ BSym.sep := fun he => hv (by simp [he])
      have he : BSym.sep = b := (List.cons.inj h).1
      exact (hb he.symm).elim
  | cons a u ih =>
    cases v with
    | nil =>
      have ha : a ≠ BSym.sep := fun he => hu (by simp [he])
      exact (ha (List.cons.inj h).1).elim
    | cons b v =>
      obtain ⟨hab, htail⟩ := List.cons.inj h
      obtain ⟨huv, hrs⟩ := ih v (fun hh => hu (List.mem_cons_of_mem a hh))
        (fun hh => hv (List.mem_cons_of_mem b hh)) htail
      exact ⟨by simp [hab, huv], hrs⟩

private lemma decode_bits (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih => simp [Nat.bits_append_bit n b hn, ih]

private lemma natword_inj {a b : ℕ} (h : a.bits.map digit = b.bits.map digit) : a = b := by
  have he := digit_inj.list_map h
  have hh := congrArg (fun l => l.foldr Nat.bit 0) he
  simpa [decode_bits] using hh

private def intword (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++ z.natAbs.bits.map digit

private lemma intword_no_sep (z : ℤ) : BSym.sep ∉ intword z := by
  simp [intword, no_sep]

private lemma intword_inj {a b : ℤ} (h : intword a = intword b) : a = b := by
  have hsign : (a < 0) ↔ (b < 0) := by
    have he := congrArg (fun l => BSym.minus ∈ l) h
    simpa [intword, no_minus] using he
  by_cases ha : a < 0
  · have hb := hsign.mp ha
    have hw : a.natAbs.bits.map digit = b.natAbs.bits.map digit := by
      simpa [intword, ha, hb] using h
    exact Int.natAbs_inj_of_nonpos_of_nonpos ha.le hb.le |>.mp (natword_inj hw)
  · have hb : ¬ b < 0 := fun hb => ha (hsign.mpr hb)
    have hw : a.natAbs.bits.map digit = b.natAbs.bits.map digit := by
      simpa [intword, ha, hb] using h
    exact Int.natAbs_inj_of_nonneg_of_nonneg (le_of_not_gt ha) (le_of_not_gt hb) |>.mp (natword_inj hw)

private lemma int_code (a : ℤ) : encInt a = intword a ++ [BSym.sep] := by
  simp [encInt, encNat, intword, digit, List.append_assoc]

private lemma ints_inj_suffix (xs ys : List ℤ) (r s : List BSym)
    (hl : xs.length = ys.length) (h : encInts xs ++ r = encInts ys ++ s) : xs=ys ∧ r=s := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys=[] := List.length_eq_zero_iff.mp hl.symm
    subst ys; simpa [encInts] using h
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have he : intword x ++ BSym.sep :: (encInts xs ++ r) =
          intword y ++ BSym.sep :: (encInts ys ++ s) := by
        simpa [encInts, int_code, List.append_assoc] using h
      obtain ⟨hw, ht⟩ := peel _ _ _ _ (intword_no_sep x) (intword_no_sep y) he
      obtain ⟨hxy, hrs⟩ := ih ys (by simpa using hl) ht
      exact ⟨by simp [intword_inj hw, hxy], hrs⟩

private lemma triple_inj (C : COP) (z z' : List Bool) (c : Fin (C.n z) → ℤ)
    (c' : Fin (C.n z') → ℤ) (k k' : ℤ) (h : encTriple z c k = encTriple z' c' k') :
    z=z' ∧ k=k' ∧ HEq c c' := by
  have he : z.map digit ++ BSym.sep :: (encVec c ++ encInt k) =
      z'.map digit ++ BSym.sep :: (encVec c' ++ encInt k') := by
    unfold digit
    simpa [encTriple, encBits, List.append_assoc] using h
  obtain ⟨hz, ht⟩ := peel _ _ _ _ (no_sep z) (no_sep z') he
  have hzz : z=z' := digit_inj.list_map hz
  subst z'
  have ht' : encInts (List.ofFn c) ++ encInt k = encInts (List.ofFn c') ++ encInt k' := by
    apply List.append_right_injective (encNat (C.n z))
    simpa [encVec, List.append_assoc] using ht
  obtain ⟨hc, hk⟩ := ints_inj_suffix _ _ _ _ (by simp) ht'
  have hkk : k=k' := by
    have he' : intword k ++ BSym.sep :: [] = intword k' ++ BSym.sep :: [] := by
      simpa [int_code] using hk
    exact intword_inj (peel _ _ _ _ (intword_no_sep k) (intword_no_sep k') he').1
  have hcc : c=c' := List.ofFn_injective hc
  exact ⟨rfl, hkk, hcc.heq⟩

theorem solution (C : COP) (z : List Bool) (hz : z ∈ C.L)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    encTriple z c k ∉ DLang C ↔
      ∀ x ∈ hull C z, (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ) := by
  classical
  have hm : encTriple z c k ∈ DLang C ↔ ∃ x ∈ C.S z, k ≤ c ⬝ᵥ x := by
    constructor
    · rintro ⟨z', hz', c', k', hx, he⟩
      obtain ⟨hzz, hkk, hcc⟩ := triple_inj C z z' c c' k k' he
      subst z'; subst k'; cases hcc
      exact hx
    · intro hx; exact ⟨z, hz, c, k, hx, rfl⟩
  rw [hm]
  constructor
  · intro h
    have hs : ((fun x : Fin (C.n z) → ℤ => fun j => (x j : ℚ)) '' C.S z) ⊆
        {x | (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)} := by
      rintro x ⟨y, hy, rfl⟩
      have hl : c ⬝ᵥ y < k := lt_of_not_ge (fun hk => h ⟨y, hy, hk⟩)
      change (fun j => (c j : ℚ)) ⬝ᵥ (fun j => (y j : ℚ)) < (k : ℚ)
      simp only [dotProduct] at hl ⊢
      exact_mod_cast hl
    have hc : Convex ℚ {x : Fin (C.n z) → ℚ | (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ)} := by
      apply convex_halfSpace_lt
      exact ⟨by intros; simp [dotProduct_add], by intros; simp [dotProduct_smul]⟩
    exact convexHull_min hs hc
  · intro h ⟨x, hx, hk⟩
    have hh := h (fun j => (x j : ℚ)) (subset_convexHull ℚ _ ⟨x, hx, rfl⟩)
    have hcast : (k : ℚ) ≤ (fun j => (c j : ℚ)) ⬝ᵥ (fun j => (x j : ℚ)) := by
      simp only [dotProduct] at hk ⊢
      exact_mod_cast hk
    exact (not_lt_of_ge hcast) hh

#print axioms solution
