-- Prove2me | solution 1 for MagicSquares.sm3_params_card
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-17T05:00:31.565794+00:00
-- url     : https://prove2.me/submissions/55dc6de9-3064-40d5-8da4-52019a1aeeac

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresSemiMagic3

set_option autoImplicit false

open scoped BigOperators

namespace MagicSquares

open MagicSquares

/- Split the normalized parameter set according to the first zero among
   the odd multiplicities (x,y,z) = (p 3, p 4, p 5). -/
def sm3Params1 (t : ℕ) : Finset (Fin 6 → Fin (t + 1)) :=
  (sm3Params t).filter fun p => (p 3 : ℕ) = 0

def sm3Params2 (t : ℕ) : Finset (Fin 6 → Fin (t + 1)) :=
  (sm3Params t).filter fun p => (p 3 : ℕ) > 0 ∧ (p 4 : ℕ) = 0

def sm3Params3 (t : ℕ) : Finset (Fin 6 → Fin (t + 1)) :=
  (sm3Params t).filter fun p => (p 3 : ℕ) > 0 ∧ (p 4 : ℕ) > 0 ∧ (p 5 : ℕ) = 0

/- The composition predicate, inlined: the platform preamble for this
   theorem does not import `Definitions.Def_MagicSquaresCompositions`. -/
private def compsLocal (N k n : ℕ) : Finset (Fin k → Fin (N + 1)) :=
  by
    classical
    exact Finset.univ.filter fun q => (∑ i : Fin k, (q i : ℕ)) = n

private lemma mem_sm3Params {t : ℕ} {p : Fin 6 → Fin (t + 1)} :
    p ∈ sm3Params t ↔
      (∑ i : Fin 6, (p i : ℕ)) = t ∧
        min ((p 3 : ℕ)) (min ((p 4 : ℕ)) ((p 5 : ℕ))) = 0 := by
  simp [sm3Params]

private lemma mem_comps {N k n : ℕ} {q : Fin k → Fin (N + 1)} :
    q ∈ compsLocal N k n ↔ (∑ i : Fin k, (q i : ℕ)) = n := by
  simp [compsLocal]

private lemma sum_fin5_explicit (f : Fin 5 → ℕ) :
    ∑ i : Fin 5, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

private lemma sum_fin6_explicit (f : Fin 6 → ℕ) :
    ∑ i : Fin 6, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]

private lemma coord_le_sum5 (q : Fin 5 → ℕ) (i : Fin 5) :
    q i ≤ ∑ j : Fin 5, q j := by
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 5 => q j)
    (by intro j hj; exact Nat.zero_le _) (Finset.mem_univ i)

/-! ## Stars and bars (inlined)

The count of each piece below is a composition count.  The stars-and-bars
theorem `comps_card` is already proved on the platform; we inline the proof
here (renamed) so this file is self-contained. -/

private theorem hockey (m n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ((j + m).choose j)) = (n + m + 1).choose n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hp := Nat.choose_succ_succ (n + m + 1) n
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp.symm

private theorem comps_succ_card (N k n : ℕ) (hn : n ≤ N) :
    (compsLocal N (k + 1) n).card =
      ((Finset.range (n + 1)).sigma (fun i => compsLocal N k (n - i))).card := by
  classical
  refine Finset.card_bij
    (fun F _hF => (⟨(F 0 : ℕ), Fin.tail F⟩ : (i : ℕ) × (Fin k → Fin (N + 1)))) ?mem ?inj ?surj
  · intro F hF
    have hsum : (∑ i : Fin (k + 1), (F i : ℕ)) = n := by
      simpa [compsLocal] using hF
    have hle0 : (F 0 : ℕ) ≤ n := by
      have hle : (F (0 : Fin (k + 1)) : ℕ) ≤ ∑ i : Fin (k + 1), (F i : ℕ) := by
        simpa using (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := fun i : Fin (k + 1) => (F i : ℕ))
          (by intro i hi; exact Nat.zero_le _)
          (Finset.mem_univ (0 : Fin (k + 1))))
      omega
    have htail : (∑ j : Fin k, ((Fin.tail F) j : ℕ)) = n - (F 0 : ℕ) := by
      have hsum' : (F 0 : ℕ) + ∑ j : Fin k, ((Fin.tail F) j : ℕ) = n := by
        simpa [Fin.tail, Fin.sum_univ_succ] using hsum
      omega
    simp only [Finset.mem_sigma, Finset.mem_range, compsLocal, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Nat.lt_succ_of_le hle0, htail⟩
  · intro F hF G hG h
    have h0 : (F 0 : ℕ) = (G 0 : ℕ) := congrArg Sigma.fst h
    have ht : Fin.tail F = Fin.tail G :=
      congrArg (fun x : (i : ℕ) × (Fin k → Fin (N + 1)) => x.2) h
    have h0fin : F 0 = G 0 := Fin.ext h0
    calc
      F = Fin.cons (F 0) (Fin.tail F) := (Fin.cons_self_tail F).symm
      _ = Fin.cons (G 0) (Fin.tail G) := by rw [h0fin, ht]
      _ = G := Fin.cons_self_tail G
  · intro x hx
    rcases x with ⟨i, q⟩
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hi_le_n : i ≤ n := Nat.lt_succ_iff.mp hx.1
    have hi_lt : i < N + 1 := by omega
    have hq : (∑ j : Fin k, (q j : ℕ)) = n - i := by
      simpa [compsLocal] using hx.2
    let Fnew : Fin (k + 1) → Fin (N + 1) :=
      Fin.cons (n := k) (α := fun _ => Fin (N + 1)) (⟨i, hi_lt⟩ : Fin (N + 1)) q
    refine ⟨Fnew, ?_, ?_⟩
    · have hsum : (∑ j : Fin (k + 1), (Fnew j : ℕ)) = n := by
        rw [Fin.sum_univ_succ]
        change i + (∑ j : Fin k, (q j : ℕ)) = n
        omega
      simpa [compsLocal] using hsum
    · simp [Fnew, Fin.cons_zero, Fin.tail_cons]

private theorem comps_card_local (N k n : ℕ) (hn : n ≤ N) :
    (compsLocal N (k + 1) n).card = (n + k).choose n := by
  induction k generalizing n with
  | zero =>
      let e : Fin 1 → Fin (N + 1) := fun _ => ⟨n, Nat.lt_succ_of_le hn⟩
      have hset : compsLocal N 1 n = {e} := by
        ext q
        constructor
        · intro hq
          have hq0 : (q (0 : Fin 1) : ℕ) = n := by
            simpa [compsLocal] using hq
          apply Finset.mem_singleton.mpr
          funext i
          fin_cases i
          exact Fin.ext hq0
        · intro hq
          rw [Finset.mem_singleton.mp hq]
          simp [compsLocal, e]
      rw [hset]
      simp
  | succ k ih =>
      rw [comps_succ_card N (k + 1) n hn, Finset.card_sigma]
      calc
        (∑ i ∈ Finset.range (n + 1), (compsLocal N (k + 1) (n - i)).card)
            = ∑ i ∈ Finset.range (n + 1), ((n - i) + k).choose (n - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ih (n - i) (by omega)
        _ = ∑ j ∈ Finset.range (n + 1), (j + k).choose j := by
              simpa using (Finset.sum_range_reflect (fun j => (j + k).choose j) (n + 1))
        _ = (n + k + 1).choose n := hockey k n

/-! ## Section 1: x = 0.

The remaining five coordinates u,v,w,y,z sum to t, so this piece is in
bijection with `compsLocal t 5 t`.  No subtraction is involved, so this is valid
for every t, including t = 0. -/

private def toComp1 (t : ℕ) (p : Fin 6 → Fin (t + 1)) : Fin 5 → Fin (t + 1) :=
  fun i =>
    if h : (i : ℕ) < 3 then p ⟨i, by omega⟩
    else p ⟨(i : ℕ) + 1, by omega⟩

private def fromComp1 (t : ℕ) (q : Fin 5 → Fin (t + 1)) : Fin 6 → Fin (t + 1) :=
  fun j =>
    if h : (j : ℕ) = 3 then ⟨0, by omega⟩
    else
      if h' : (j : ℕ) < 3 then q ⟨j, by omega⟩
      else q ⟨(j : ℕ) - 1, by omega⟩

private lemma sum_toComp1 (t : ℕ) (p : Fin 6 → Fin (t + 1)) :
    (∑ i : Fin 5, (toComp1 t p i : ℕ)) =
      (p 0 : ℕ) + (p 1 : ℕ) + (p 2 : ℕ) + (p 4 : ℕ) + (p 5 : ℕ) := by
  have h0 : (toComp1 t p 0 : ℕ) = (p 0 : ℕ) := by simp [toComp1]
  have h1 : (toComp1 t p 1 : ℕ) = (p 1 : ℕ) := by simp [toComp1]
  have h2 : (toComp1 t p 2 : ℕ) = (p 2 : ℕ) := by simp [toComp1]
  have h3 : (toComp1 t p 3 : ℕ) = (p 4 : ℕ) := by simp [toComp1]
  have h4 : (toComp1 t p 4 : ℕ) = (p 5 : ℕ) := by simp [toComp1]
  rw [sum_fin5_explicit]
  rw [h0, h1, h2, h3, h4]

private lemma sum_fromComp1 (t : ℕ) (q : Fin 5 → Fin (t + 1)) :
    (∑ i : Fin 6, (fromComp1 t q i : ℕ)) =
      (q 0 : ℕ) + (q 1 : ℕ) + (q 2 : ℕ) + (q 3 : ℕ) + (q 4 : ℕ) := by
  have h0 : (fromComp1 t q 0 : ℕ) = (q 0 : ℕ) := by simp [fromComp1]
  have h1 : (fromComp1 t q 1 : ℕ) = (q 1 : ℕ) := by simp [fromComp1]
  have h2 : (fromComp1 t q 2 : ℕ) = (q 2 : ℕ) := by simp [fromComp1]
  have h3 : (fromComp1 t q 3 : ℕ) = 0 := by simp [fromComp1]
  have h4 : (fromComp1 t q 4 : ℕ) = (q 3 : ℕ) := by simp [fromComp1]
  have h5 : (fromComp1 t q 5 : ℕ) = (q 4 : ℕ) := by simp [fromComp1]
  rw [sum_fin6_explicit]
  rw [h0, h1, h2, h3, h4, h5]
  ring

private lemma comp1_bij (t : ℕ) :
    (sm3Params1 t).card = (compsLocal t 5 t).card := by
  refine Finset.card_bij' (fun p _ => toComp1 t p) (fun q _ => fromComp1 t q) ?_ ?_ ?_ ?_
  · -- toComp1 lands in compsLocal t 5 t
    intro p hp
    rw [mem_comps]
    have h1 : p ∈ sm3Params t := (Finset.mem_filter.mp hp).1
    have hx : (p 3 : ℕ) = 0 := (Finset.mem_filter.mp hp).2
    have hsum : (∑ i : Fin 6, (p i : ℕ)) = t := (mem_sm3Params.mp h1).1
    rw [sum_toComp1 t p]
    rw [sum_fin6_explicit] at hsum
    simp [hx] at hsum
    omega
  · -- fromComp1 lands in sm3Params1 t
    intro q hq
    rw [mem_comps] at hq
    simp [sm3Params1, mem_sm3Params]
    constructor
    · constructor
      · rw [sum_fromComp1 t q]
        rw [sum_fin5_explicit] at hq
        omega
      · simp [fromComp1]
    · simp [fromComp1]
  · -- left inverse
    intro p hp
    funext j
    have hx : (p 3 : ℕ) = 0 := (Finset.mem_filter.mp hp).2
    have hp3 : p 3 = ⟨0, by omega⟩ := Fin.ext hx
    simp [toComp1, fromComp1]
    fin_cases j <;> simp [hp3]
  · -- right inverse
    intro q hq
    funext i
    simp [toComp1, fromComp1]
    fin_cases i <;> rfl

/-! ## Section 2: x > 0, y = 0.

Subtracting 1 from x leaves five coordinates u,v,w,x-1,z summing to t - 1.
This is only meaningful for t ≥ 1; for t = 0 the piece is empty. -/

private def toComp2 (t : ℕ) (p : Fin 6 → Fin (t + 1)) : Fin 5 → Fin (t + 1) :=
  fun i =>
    if h : (i : ℕ) < 3 then p ⟨i, by omega⟩
    else if h' : (i : ℕ) = 3 then ⟨(p 3 : ℕ) - 1, by omega⟩
    else p 5

private def fromComp2 (t : ℕ) (ht : t ≥ 1) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 1)) : Fin 6 → Fin (t + 1) :=
  fun j =>
    if h : (j : ℕ) = 4 then ⟨0, by omega⟩
    else
      if h' : (j : ℕ) < 3 then q ⟨j, by omega⟩
      else
        if h'' : (j : ℕ) = 3 then
          ⟨(q 3 : ℕ) + 1, by
            have hs : (∑ i : Fin 5, (q i : ℕ)) = t - 1 := (mem_comps.mp hq)
            have hle := coord_le_sum5 (fun i : Fin 5 => (q i : ℕ)) 3
            omega⟩
        else q 4

private lemma sum_toComp2 (t : ℕ) (p : Fin 6 → Fin (t + 1)) (hx : (p 3 : ℕ) > 0) :
    (∑ i : Fin 5, (toComp2 t p i : ℕ)) =
      (p 0 : ℕ) + (p 1 : ℕ) + (p 2 : ℕ) + ((p 3 : ℕ) - 1) + (p 5 : ℕ) := by
  have h0 : (toComp2 t p 0 : ℕ) = (p 0 : ℕ) := by simp [toComp2]
  have h1 : (toComp2 t p 1 : ℕ) = (p 1 : ℕ) := by simp [toComp2]
  have h2 : (toComp2 t p 2 : ℕ) = (p 2 : ℕ) := by simp [toComp2]
  have h3 : (toComp2 t p 3 : ℕ) = (p 3 : ℕ) - 1 := by simp [toComp2]
  have h4 : (toComp2 t p 4 : ℕ) = (p 5 : ℕ) := by simp [toComp2]
  rw [sum_fin5_explicit]
  rw [h0, h1, h2, h3, h4]

private lemma sum_fromComp2 (t : ℕ) (ht : t ≥ 1) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 1)) :
    (∑ i : Fin 6, (fromComp2 t ht q hq i : ℕ)) =
      1 + (∑ i : Fin 5, (q i : ℕ)) := by
  have h0 : (fromComp2 t ht q hq 0 : ℕ) = (q 0 : ℕ) := by simp [fromComp2]
  have h1 : (fromComp2 t ht q hq 1 : ℕ) = (q 1 : ℕ) := by simp [fromComp2]
  have h2 : (fromComp2 t ht q hq 2 : ℕ) = (q 2 : ℕ) := by simp [fromComp2]
  have h3 : (fromComp2 t ht q hq 3 : ℕ) = (q 3 : ℕ) + 1 := by simp [fromComp2]
  have h4 : (fromComp2 t ht q hq 4 : ℕ) = 0 := by simp [fromComp2]
  have h5 : (fromComp2 t ht q hq 5 : ℕ) = (q 4 : ℕ) := by simp [fromComp2]
  rw [sum_fin6_explicit]
  rw [h0, h1, h2, h3, h4, h5]
  rw [sum_fin5_explicit]
  ring

private lemma fromComp2_three (t : ℕ) (ht : t ≥ 1) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 1)) :
    (fromComp2 t ht q hq 3 : ℕ) = (q 3 : ℕ) + 1 := by
  simp [fromComp2]

private lemma fromComp2_four (t : ℕ) (ht : t ≥ 1) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 1)) :
    (fromComp2 t ht q hq 4 : ℕ) = 0 := by
  simp [fromComp2]

private lemma sm3Params2_empty_zero : sm3Params2 0 = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨p, hp⟩
  have h1 : p ∈ sm3Params 0 := (Finset.mem_filter.mp hp).1
  have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
  have hsum : (∑ i : Fin 6, (p i : ℕ)) = 0 := (mem_sm3Params.mp h1).1
  rw [sum_fin6_explicit] at hsum
  omega

private lemma comp2_bij (t : ℕ) (ht : t ≥ 1) :
    (sm3Params2 t).card = (compsLocal t 5 (t - 1)).card := by
  refine Finset.card_bij' (fun p _ => toComp2 t p) (fun q hq => fromComp2 t ht q hq) ?_ ?_ ?_ ?_
  · -- toComp2 lands in compsLocal t 5 (t - 1)
    intro p hp
    rw [mem_comps]
    have h1 : p ∈ sm3Params t := (Finset.mem_filter.mp hp).1
    have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
    have hy : (p 4 : ℕ) = 0 := (Finset.mem_filter.mp hp).2.2
    have hsum : (∑ i : Fin 6, (p i : ℕ)) = t := (mem_sm3Params.mp h1).1
    rw [sum_toComp2 t p hx]
    rw [sum_fin6_explicit] at hsum
    omega
  · -- fromComp2 lands in sm3Params2 t
    intro q hq
    simp [sm3Params2, mem_sm3Params]
    constructor
    · constructor
      · rw [sum_fromComp2 t ht q hq]
        have hs : (∑ i : Fin 5, (q i : ℕ)) = t - 1 := (mem_comps.mp hq)
        omega
      · simp [fromComp2]
    · have hxpos : (fromComp2 t ht q hq 3 : ℕ) > 0 := by
        rw [fromComp2_three t ht q hq]
        omega
      have hy0 : (fromComp2 t ht q hq 4 : ℕ) = 0 := by
        rw [fromComp2_four t ht q hq]
      exact ⟨hxpos, Fin.ext hy0⟩
  · -- left inverse
    intro p hp
    funext j
    have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
    have hy : (p 4 : ℕ) = 0 := (Finset.mem_filter.mp hp).2.2
    fin_cases j <;> apply Fin.ext <;> simp [toComp2, fromComp2] <;> omega
  · -- right inverse
    intro q hq
    funext i
    fin_cases i <;> apply Fin.ext <;> simp [toComp2, fromComp2] <;> omega

/-! ## Section 3: x > 0, y > 0, z = 0.

Subtracting 1 from each of x and y leaves five coordinates summing to t - 2.
This is only meaningful for t ≥ 2. -/

private def toComp3 (t : ℕ) (p : Fin 6 → Fin (t + 1)) : Fin 5 → Fin (t + 1) :=
  fun i =>
    if h : (i : ℕ) < 3 then p ⟨i, by omega⟩
    else if h' : (i : ℕ) = 3 then ⟨(p 3 : ℕ) - 1, by omega⟩
    else ⟨(p 4 : ℕ) - 1, by omega⟩

private def fromComp3 (t : ℕ) (ht : t ≥ 2) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 2)) : Fin 6 → Fin (t + 1) :=
  fun j =>
    if h : (j : ℕ) = 5 then ⟨0, by omega⟩
    else
      if h' : (j : ℕ) < 3 then q ⟨j, by omega⟩
      else
        if h'' : (j : ℕ) = 3 then
          ⟨(q 3 : ℕ) + 1, by
            have hs : (∑ i : Fin 5, (q i : ℕ)) = t - 2 := (mem_comps.mp hq)
            have hle := coord_le_sum5 (fun i : Fin 5 => (q i : ℕ)) 3
            omega⟩
        else
          ⟨(q 4 : ℕ) + 1, by
            have hs : (∑ i : Fin 5, (q i : ℕ)) = t - 2 := (mem_comps.mp hq)
            have hle := coord_le_sum5 (fun i : Fin 5 => (q i : ℕ)) 4
            omega⟩

private lemma sum_toComp3 (t : ℕ) (p : Fin 6 → Fin (t + 1))
    (hx : (p 3 : ℕ) > 0) (hy : (p 4 : ℕ) > 0) :
    (∑ i : Fin 5, (toComp3 t p i : ℕ)) =
      (p 0 : ℕ) + (p 1 : ℕ) + (p 2 : ℕ) + ((p 3 : ℕ) - 1) + ((p 4 : ℕ) - 1) := by
  have h0 : (toComp3 t p 0 : ℕ) = (p 0 : ℕ) := by simp [toComp3]
  have h1 : (toComp3 t p 1 : ℕ) = (p 1 : ℕ) := by simp [toComp3]
  have h2 : (toComp3 t p 2 : ℕ) = (p 2 : ℕ) := by simp [toComp3]
  have h3 : (toComp3 t p 3 : ℕ) = (p 3 : ℕ) - 1 := by simp [toComp3]
  have h4 : (toComp3 t p 4 : ℕ) = (p 4 : ℕ) - 1 := by simp [toComp3]
  rw [sum_fin5_explicit]
  rw [h0, h1, h2, h3, h4]

private lemma sum_fromComp3 (t : ℕ) (ht : t ≥ 2) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 2)) :
    (∑ i : Fin 6, (fromComp3 t ht q hq i : ℕ)) =
      2 + (∑ i : Fin 5, (q i : ℕ)) := by
  have h0 : (fromComp3 t ht q hq 0 : ℕ) = (q 0 : ℕ) := by simp [fromComp3]
  have h1 : (fromComp3 t ht q hq 1 : ℕ) = (q 1 : ℕ) := by simp [fromComp3]
  have h2 : (fromComp3 t ht q hq 2 : ℕ) = (q 2 : ℕ) := by simp [fromComp3]
  have h3 : (fromComp3 t ht q hq 3 : ℕ) = (q 3 : ℕ) + 1 := by simp [fromComp3]
  have h4 : (fromComp3 t ht q hq 4 : ℕ) = (q 4 : ℕ) + 1 := by simp [fromComp3]
  have h5 : (fromComp3 t ht q hq 5 : ℕ) = 0 := by simp [fromComp3]
  rw [sum_fin6_explicit]
  rw [h0, h1, h2, h3, h4, h5]
  rw [sum_fin5_explicit]
  ring

private lemma fromComp3_three (t : ℕ) (ht : t ≥ 2) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 2)) :
    (fromComp3 t ht q hq 3 : ℕ) = (q 3 : ℕ) + 1 := by
  simp [fromComp3]

private lemma fromComp3_four (t : ℕ) (ht : t ≥ 2) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 2)) :
    (fromComp3 t ht q hq 4 : ℕ) = (q 4 : ℕ) + 1 := by
  simp [fromComp3]

private lemma fromComp3_five (t : ℕ) (ht : t ≥ 2) (q : Fin 5 → Fin (t + 1))
    (hq : q ∈ compsLocal t 5 (t - 2)) :
    (fromComp3 t ht q hq 5 : ℕ) = 0 := by
  simp [fromComp3]

private lemma sm3Params3_empty_small {t : ℕ} (ht : t ≤ 1) : sm3Params3 t = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨p, hp⟩
  have h1 : p ∈ sm3Params t := (Finset.mem_filter.mp hp).1
  have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
  have hy : (p 4 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.2.1
  have hsum : (∑ i : Fin 6, (p i : ℕ)) = t := (mem_sm3Params.mp h1).1
  rw [sum_fin6_explicit] at hsum
  omega

private lemma comp3_bij (t : ℕ) (ht : t ≥ 2) :
    (sm3Params3 t).card = (compsLocal t 5 (t - 2)).card := by
  refine Finset.card_bij' (fun p _ => toComp3 t p) (fun q hq => fromComp3 t ht q hq) ?_ ?_ ?_ ?_
  · -- toComp3 lands in compsLocal t 5 (t - 2)
    intro p hp
    rw [mem_comps]
    have h1 : p ∈ sm3Params t := (Finset.mem_filter.mp hp).1
    have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
    have hy : (p 4 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.2.1
    have hz : (p 5 : ℕ) = 0 := (Finset.mem_filter.mp hp).2.2.2
    have hsum : (∑ i : Fin 6, (p i : ℕ)) = t := (mem_sm3Params.mp h1).1
    rw [sum_toComp3 t p hx hy]
    rw [sum_fin6_explicit] at hsum
    omega
  · -- fromComp3 lands in sm3Params3 t
    intro q hq
    simp [sm3Params3, mem_sm3Params]
    constructor
    · constructor
      · rw [sum_fromComp3 t ht q hq]
        have hs : (∑ i : Fin 5, (q i : ℕ)) = t - 2 := (mem_comps.mp hq)
        omega
      · simp [fromComp3]
    · have hxpos : (fromComp3 t ht q hq 3 : ℕ) > 0 := by
        rw [fromComp3_three t ht q hq]
        omega
      have hypos : (fromComp3 t ht q hq 4 : ℕ) > 0 := by
        rw [fromComp3_four t ht q hq]
        omega
      have hz0 : (fromComp3 t ht q hq 5 : ℕ) = 0 := by
        rw [fromComp3_five t ht q hq]
      exact ⟨hxpos, hypos, Fin.ext hz0⟩
  · -- left inverse
    intro p hp
    funext j
    have hx : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.1
    have hy : (p 4 : ℕ) > 0 := (Finset.mem_filter.mp hp).2.2.1
    have hz : (p 5 : ℕ) = 0 := (Finset.mem_filter.mp hp).2.2.2
    fin_cases j <;> apply Fin.ext <;> simp [toComp3, fromComp3] <;> omega
  · -- right inverse
    intro q hq
    funext i
    fin_cases i <;> apply Fin.ext <;> simp [toComp3, fromComp3] <;> omega

/-! ## Assembling the three pieces -/

private lemma union_split (t : ℕ) :
    sm3Params t = sm3Params1 t ∪ sm3Params2 t ∪ sm3Params3 t := by
  ext p
  simp only [sm3Params1, sm3Params2, sm3Params3, Finset.mem_union, Finset.mem_filter,
    mem_sm3Params]
  constructor
  · rintro ⟨hsum, hmin⟩
    by_cases hx : (p 3 : ℕ) = 0
    · left; left
      exact ⟨⟨hsum, by simp [hx]⟩, hx⟩
    · have hxpos : (p 3 : ℕ) > 0 := by omega
      by_cases hy : (p 4 : ℕ) = 0
      · left; right
        exact ⟨⟨hsum, by simp [hy]⟩, hxpos, hy⟩
      · have hypos : (p 4 : ℕ) > 0 := by omega
        right
        have hz : (p 5 : ℕ) = 0 := by
          by_contra hz'
          have hzpos : (p 5 : ℕ) > 0 := by omega
          have hminpos : 0 < min ((p 3 : ℕ)) (min ((p 4 : ℕ)) ((p 5 : ℕ))) :=
            lt_min (by omega) (lt_min (by omega) (by omega))
          omega
        exact ⟨⟨hsum, by simp [hz]⟩, hxpos, hypos, hz⟩
  · rintro ((⟨⟨hsum, hmin⟩, hx⟩ | ⟨⟨hsum, hmin⟩, hx, hy⟩) | ⟨⟨hsum, hmin⟩, hx, hy, hz⟩)
    · exact ⟨hsum, by simp [hx]⟩
    · exact ⟨hsum, by simp [hy]⟩
    · exact ⟨hsum, by simp [hz]⟩

private lemma disjoint12 (t : ℕ) : Disjoint (sm3Params1 t) (sm3Params2 t) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have hx0 : (p 3 : ℕ) = 0 := (Finset.mem_filter.mp hp1).2
  have hxpos : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp2).2.1
  omega

private lemma disjoint13 (t : ℕ) : Disjoint (sm3Params1 t) (sm3Params3 t) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp3
  have hx0 : (p 3 : ℕ) = 0 := (Finset.mem_filter.mp hp1).2
  have hxpos : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp3).2.1
  omega

private lemma disjoint23 (t : ℕ) : Disjoint (sm3Params2 t) (sm3Params3 t) := by
  rw [Finset.disjoint_left]
  intro p hp2 hp3
  have hy0 : (p 4 : ℕ) = 0 := (Finset.mem_filter.mp hp2).2.2
  have hypos : (p 4 : ℕ) > 0 := (Finset.mem_filter.mp hp3).2.2.1
  omega

private lemma card_split (t : ℕ) :
    (sm3Params t).card =
      (sm3Params1 t).card + (sm3Params2 t).card + (sm3Params3 t).card := by
  rw [union_split t]
  have hdisj : Disjoint (sm3Params1 t ∪ sm3Params2 t) (sm3Params3 t) := by
    rw [Finset.disjoint_left]
    intro p hp hp3
    rw [Finset.mem_union] at hp
    rcases hp with hp1 | hp2
    · have hx0 : (p 3 : ℕ) = 0 := (Finset.mem_filter.mp hp1).2
      have hxpos : (p 3 : ℕ) > 0 := (Finset.mem_filter.mp hp3).2.1
      omega
    · have hy0 : (p 4 : ℕ) = 0 := (Finset.mem_filter.mp hp2).2.2
      have hypos : (p 4 : ℕ) > 0 := (Finset.mem_filter.mp hp3).2.2.1
      omega
  rw [Finset.card_union_of_disjoint hdisj]
  rw [Finset.card_union_of_disjoint (disjoint12 t)]

private lemma sm3Params_zero : sm3Params 0 = (Finset.univ : Finset (Fin 6 → Fin 1)) := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_univ p
  · intro _
    rw [mem_sm3Params]
    constructor
    · have hz : ∀ i : Fin 6, (p i : ℕ) = 0 := by
        intro i
        have hlt : (p i).val < 1 := by
          simpa using (p i).isLt
        omega
      rw [sum_fin6_explicit]
      simp [hz]
    · simp

end MagicSquares

open MagicSquares

theorem solution (t : ℕ) :
    sm3Count t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by
  rw [sm3Count]
  by_cases ht0 : t = 0
  · -- t = 0: only the all-zero parameter vector
    subst t
    rw [sm3Params_zero]
    norm_num
  · by_cases ht1 : t = 1
    · -- t = 1: the first piece has 5 elements, the second 1, the third none
      rw [ht1]
      have hs1 : (sm3Params1 1).card = 5 := by
        rw [comp1_bij 1]
        rw [show 5 = 4 + 1 by rfl]
        rw [comps_card_local 1 4 1 (by omega)]
        norm_num
      have hs2 : (sm3Params2 1).card = 1 := by
        rw [comp2_bij 1 (by omega)]
        rw [show 5 = 4 + 1 by rfl]
        rw [comps_card_local 1 4 0 (by omega)]
        norm_num
      have hs3 : (sm3Params3 1).card = 0 := by
        rw [sm3Params3_empty_small (by omega)]
        simp
      rw [card_split 1, hs1, hs2, hs3]
      norm_num
    · -- t ≥ 2
      have ht2 : t ≥ 2 := by omega
      rw [card_split t]
      rw [comp1_bij t, comp2_bij t (by omega), comp3_bij t ht2]
      have h1 : (compsLocal t 5 t).card = (t + 4).choose 4 := by
        rw [show 5 = 4 + 1 by rfl]
        rw [comps_card_local t 4 t (by omega)]
        simpa [show t + 4 - 4 = t by omega] using
          (Nat.choose_symm (n := t + 4) (k := 4) (by omega : 4 ≤ t + 4))
      have h2 : (compsLocal t 5 (t - 1)).card = (t + 3).choose 4 := by
        rw [show 5 = 4 + 1 by rfl]
        rw [comps_card_local t 4 (t - 1) (by omega)]
        rw [show t - 1 + 4 = t + 3 by omega]
        simpa [show t + 3 - 4 = t - 1 by omega] using
          (Nat.choose_symm (n := t + 3) (k := 4) (by omega : 4 ≤ t + 3))
      have h3 : (compsLocal t 5 (t - 2)).card = (t + 2).choose 4 := by
        rw [show 5 = 4 + 1 by rfl]
        rw [comps_card_local t 4 (t - 2) (by omega)]
        rw [show t - 2 + 4 = t + 2 by omega]
        simpa [show t + 2 - 4 = t - 2 by omega] using
          (Nat.choose_symm (n := t + 2) (k := 4) (by omega : 4 ≤ t + 2))
      rw [h1, h2, h3]
      have h4 : (t + 4).choose 4 = (t + 3).choose 4 + (t + 3).choose 3 := by
        rw [Nat.choose_succ_succ (t + 3) 3]
        ring
      have h5 : (t + 3).choose 4 = (t + 2).choose 4 + (t + 2).choose 3 := by
        rw [Nat.choose_succ_succ (t + 2) 3]
        ring
      have h6 : (t + 3).choose 3 = (t + 2).choose 3 + (t + 2).choose 2 := by
        rw [Nat.choose_succ_succ (t + 2) 2]
        ring
      calc
        (t + 4).choose 4 + (t + 3).choose 4 + (t + 2).choose 4
            = ((t + 3).choose 4 + (t + 3).choose 3) + (t + 3).choose 4 + (t + 2).choose 4 := by
                rw [h4]
        _ = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by
                rw [h5, h6]
                ring
