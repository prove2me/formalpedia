-- Prove2me | solution 1 for KadatchJenkins.crc32_zero_bytes_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-21T22:40:13.374377+00:00
-- url     : https://prove2.me/submissions/40be596b-503a-4c75-b5dc-2b5825a7fc43

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins.Readings

/-- The polynomial `∑_{i ∈ l} X ^ i` over `GF(2)` of a list of exponents (repetitions allowed). -/
noncomputable def B (l : List ℕ) : (ZMod 2)[X] := (l.map fun i => (X : (ZMod 2)[X]) ^ i).sum

@[simp] theorem B_nil : B [] = 0 := rfl
@[simp] theorem B_cons (i : ℕ) (l : List ℕ) : B (i :: l) = X ^ i + B l := by simp [B]
theorem B_append (l₁ l₂ : List ℕ) : B (l₁ ++ l₂) = B l₁ + B l₂ := by simp [B]
theorem B_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) : B l₁ = B l₂ := (h.map _).sum_eq

/-- Add `X ^ x` to the reduced form `l`: cancel it in characteristic 2 or insert it. -/
def toggle (x : ℕ) (l : List ℕ) : List ℕ := if x ∈ l then l.erase x else x :: l

theorem B_toggle (x : ℕ) (l : List ℕ) : B (toggle x l) = X ^ x + B l := by
  unfold toggle
  split_ifs with h
  · rw [B_perm (List.perm_cons_erase h), B_cons, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · rfl

/-- The reduced, sorted list of exponents of `B l`. -/
def norm (l : List ℕ) : List ℕ := (l.foldr toggle []).insertionSort (· ≤ ·)

theorem B_norm (l : List ℕ) : B (norm l) = B l := by
  unfold norm
  rw [B_perm (List.perm_insertionSort _ _)]
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldr_cons, B_toggle, ih, B_cons]

theorem B_shift (l : List ℕ) : B (l.map (· + 1)) = X * B l := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, B_cons, ih, pow_succ]; ring

theorem B_double (l : List ℕ) : B (l.map (2 * ·)) = B l ^ 2 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, B_cons, B_cons, ih, add_pow_char, ← pow_mul, mul_comm x 2]

/-- The exponents of `P(x) - x^32` for CRC-32. -/
def lowP : List ℕ := [26, 23, 22, 16, 12, 11, 10, 8, 7, 5, 4, 2, 1, 0]

/-- The CRC-32 polynomial. -/
noncomputable abbrev P32 : (ZMod 2)[X] :=
  X ^ 32 + X ^ 26 + X ^ 23 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 +
    X ^ 5 + X ^ 4 + X ^ 2 + X + 1

theorem P32_eq : P32 = X ^ 32 + B lowP := by simp [lowP, B]; ring

/-- Replace `x^32` by `P(x) - x^32`. -/
def red (l : List ℕ) : List ℕ := l.flatMap fun i => if i = 32 then lowP else [i]

theorem red_dvd (l : List ℕ) : P32 ∣ B (red l) - B l := by
  induction l with
  | nil => simp [red]
  | cons x l ih =>
    have e : B (red (x :: l)) - B (x :: l) =
        (B (if x = 32 then lowP else [x]) - X ^ x) + (B (red l) - B l) := by
      simp only [red, List.flatMap_cons, B_append, B_cons]; ring
    rw [e]
    refine dvd_add ?_ ih
    split_ifs with h
    · subst h
      rw [CharTwo.sub_eq_add, add_comm, ← P32_eq]
    · simp

/-- Multiply by `x` and reduce modulo `P`. -/
def mulXRed (l : List ℕ) : List ℕ := norm (red (l.map (· + 1)))

theorem mulXRed_dvd (l : List ℕ) : P32 ∣ B (mulXRed l) - X * B l := by
  unfold mulXRed
  rw [B_norm, ← B_shift]
  exact red_dvd _

/-- `x^j mod P` for `j ≤ 62`. -/
def tbl : List (List ℕ) :=
  [[0],
  [1],
  [2],
  [3],
  [4],
  [5],
  [6],
  [7],
  [8],
  [9],
  [10],
  [11],
  [12],
  [13],
  [14],
  [15],
  [16],
  [17],
  [18],
  [19],
  [20],
  [21],
  [22],
  [23],
  [24],
  [25],
  [26],
  [27],
  [28],
  [29],
  [30],
  [31],
  [0, 1, 2, 4, 5, 7, 8, 10, 11, 12, 16, 22, 23, 26],
  [1, 2, 3, 5, 6, 8, 9, 11, 12, 13, 17, 23, 24, 27],
  [2, 3, 4, 6, 7, 9, 10, 12, 13, 14, 18, 24, 25, 28],
  [3, 4, 5, 7, 8, 10, 11, 13, 14, 15, 19, 25, 26, 29],
  [4, 5, 6, 8, 9, 11, 12, 14, 15, 16, 20, 26, 27, 30],
  [5, 6, 7, 9, 10, 12, 13, 15, 16, 17, 21, 27, 28, 31],
  [0, 1, 2, 4, 5, 6, 12, 13, 14, 17, 18, 23, 26, 28, 29],
  [1, 2, 3, 5, 6, 7, 13, 14, 15, 18, 19, 24, 27, 29, 30],
  [2, 3, 4, 6, 7, 8, 14, 15, 16, 19, 20, 25, 28, 30, 31],
  [0, 1, 2, 3, 9, 10, 11, 12, 15, 17, 20, 21, 22, 23, 29, 31],
  [0, 3, 5, 7, 8, 13, 18, 21, 24, 26, 30],
  [1, 4, 6, 8, 9, 14, 19, 22, 25, 27, 31],
  [0, 1, 4, 8, 9, 11, 12, 15, 16, 20, 22, 28],
  [1, 2, 5, 9, 10, 12, 13, 16, 17, 21, 23, 29],
  [2, 3, 6, 10, 11, 13, 14, 17, 18, 22, 24, 30],
  [3, 4, 7, 11, 12, 14, 15, 18, 19, 23, 25, 31],
  [0, 1, 2, 7, 10, 11, 13, 15, 19, 20, 22, 23, 24],
  [1, 2, 3, 8, 11, 12, 14, 16, 20, 21, 23, 24, 25],
  [2, 3, 4, 9, 12, 13, 15, 17, 21, 22, 24, 25, 26],
  [3, 4, 5, 10, 13, 14, 16, 18, 22, 23, 25, 26, 27],
  [4, 5, 6, 11, 14, 15, 17, 19, 23, 24, 26, 27, 28],
  [5, 6, 7, 12, 15, 16, 18, 20, 24, 25, 27, 28, 29],
  [6, 7, 8, 13, 16, 17, 19, 21, 25, 26, 28, 29, 30],
  [7, 8, 9, 14, 17, 18, 20, 22, 26, 27, 29, 30, 31],
  [0, 1, 2, 4, 5, 7, 9, 11, 12, 15, 16, 18, 19, 21, 22, 26, 27, 28, 30, 31],
  [0, 3, 4, 6, 7, 11, 13, 17, 19, 20, 26, 27, 28, 29, 31],
  [0, 2, 10, 11, 14, 16, 18, 20, 21, 22, 23, 26, 27, 28, 29, 30],
  [1, 3, 11, 12, 15, 17, 19, 21, 22, 23, 24, 27, 28, 29, 30, 31],
  [0, 1, 5, 7, 8, 10, 11, 13, 18, 20, 24, 25, 26, 28, 29, 30, 31],
  [0, 4, 5, 6, 7, 9, 10, 14, 16, 19, 21, 22, 23, 25, 27, 29, 30, 31],
  [0, 2, 4, 6, 12, 15, 16, 17, 20, 24, 28, 30, 31]]

set_option maxRecDepth 100000

theorem tbl_zero : tbl.getD 0 [] = [0] := by decide +kernel

theorem tbl_succ : ∀ j < 62, tbl.getD (j + 1) [] = mulXRed (tbl.getD j []) := by decide +kernel

theorem tbl_dvd (j : ℕ) (hj : j < 63) : P32 ∣ B (tbl.getD j []) - X ^ j := by
  induction j with
  | zero => rw [tbl_zero]; simp
  | succ j ih =>
    rw [tbl_succ j (by omega)]
    have e : B (mulXRed (tbl.getD j [])) - X ^ (j + 1) =
        (B (mulXRed (tbl.getD j [])) - X * B (tbl.getD j [])) + X * (B (tbl.getD j []) - X ^ j) := by
      ring
    rw [e]
    exact dvd_add (mulXRed_dvd _) (dvd_mul_of_dvd_right (ih (by omega)) _)

/-- `x^j mod P` from the table, or `x^j` itself beyond it. -/
def tab (j : ℕ) : List ℕ := if j < 63 then tbl.getD j [] else [j]

theorem flatMap_tab_dvd (l : List ℕ) : P32 ∣ B (l.flatMap tab) - B l := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have e : B ((x :: l).flatMap tab) - B (x :: l) = (B (tab x) - X ^ x) + (B (l.flatMap tab) - B l) := by
      simp only [List.flatMap_cons, B_append, B_cons]; ring
    rw [e]
    refine dvd_add ?_ ih
    unfold tab
    split_ifs with h
    · exact tbl_dvd x h
    · simp

/-- Square modulo `P` (Frobenius, then reduce). -/
def sqRed (l : List ℕ) : List ℕ := norm ((l.map (2 * ·)).flatMap tab)

/-- `x^(2^k) mod P` for `k ≤ 32`. -/
def pows : List (List ℕ) :=
  [[1],
  [2],
  [4],
  [8],
  [16],
  [0, 1, 2, 4, 5, 7, 8, 10, 11, 12, 16, 22, 23, 26],
  [0, 2, 3, 7, 8, 9, 10, 13, 14, 16, 18, 19, 24, 27, 30],
  [0, 2, 9, 10, 12, 14, 18, 21, 23, 27, 29, 30, 31],
  [0, 1, 2, 4, 5, 7, 9, 10, 14, 17, 18, 19, 20, 21, 23, 24, 26, 28, 29, 30],
  [0, 4, 8, 9, 11, 15, 17, 21, 25, 26, 29, 30, 31],
  [0, 1, 3, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 28, 30],
  [0, 1, 2, 4, 5, 9, 13, 17, 18, 19, 20, 21, 22, 23, 27, 31],
  [0, 4, 5, 6, 9, 10, 11, 12, 13, 14, 16, 18, 23, 25, 26, 27],
  [1, 2, 5, 10, 13, 14, 15, 16, 28, 29, 30],
  [1, 4, 5, 7, 9, 13, 14, 15, 16, 18, 19, 20, 22, 24, 25, 26],
  [4, 7, 8, 9, 10, 11, 12, 13, 14, 17, 19, 21, 24, 28, 29, 30, 31],
  [0, 6, 7, 8, 13, 15, 18, 20, 21, 23, 28, 29, 30, 31],
  [2, 3, 10, 11, 13, 14, 18, 20, 21, 22, 23, 27, 28, 30],
  [1, 2, 3, 4, 6, 7, 9, 11, 12, 14, 16, 19, 20, 21, 24, 25, 30, 31],
  [2, 3, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 23, 25, 26, 28, 31],
  [0, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 22, 26, 28, 30],
  [1, 2, 4, 5, 8, 12, 13, 15, 16, 17, 18, 20, 21, 23, 24, 25, 29],
  [3, 5, 7, 8, 9, 11, 13, 14, 16, 21, 22, 23, 25, 28, 29, 31],
  [1, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 17, 18, 19, 20, 22, 25, 28, 29, 30],
  [0, 2, 3, 4, 6, 8, 9, 11, 12, 15, 20, 21, 22, 26, 27, 29, 30, 31],
  [2, 4, 5, 6, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30, 31],
  [1, 4, 5, 6, 8, 10, 12, 14, 15, 16, 18, 22, 27, 29],
  [0, 2, 4, 8, 10, 13, 17, 18, 19, 22, 24, 25],
  [1, 6, 8, 11, 12, 14, 16, 19, 21, 22, 24, 27, 28, 29, 30],
  [3, 5, 8, 12, 13, 15, 18, 19, 26, 28, 30],
  [0, 1, 5, 12, 14, 15, 16, 18, 21, 22, 24, 25, 27],
  [0, 1, 5, 8, 9, 10, 14, 18, 20, 21, 26, 27, 28, 29],
  [1]]

theorem pows_zero : pows.getD 0 [] = [1] := by decide +kernel

theorem pows_succ : ∀ k < 32, pows.getD (k + 1) [] = sqRed (pows.getD k []) := by decide +kernel

theorem pows_32 : pows.getD 32 [] = [1] := by decide +kernel

theorem pows_dvd (k : ℕ) (hk : k ≤ 32) : P32 ∣ B (pows.getD k []) - X ^ (2 ^ k) := by
  induction k with
  | zero => rw [pows_zero]; simp
  | succ k ih =>
    rw [pows_succ k (by omega)]
    set R := pows.getD k []
    have e : B (sqRed R) - X ^ (2 ^ (k + 1)) =
        (B ((R.map (2 * ·)).flatMap tab) - B (R.map (2 * ·))) +
          (B R - X ^ (2 ^ k)) * (B R + X ^ (2 ^ k)) := by
      rw [sqRed, B_norm, B_double, pow_succ, pow_mul]; ring
    rw [e]
    exact dvd_add (flatMap_tab_dvd _) (dvd_mul_of_dvd_left (ih (by omega)) _)

theorem pows_32_eq : B (pows.getD 32 []) = X := by rw [pows_32]; simp

theorem dvd_X_pow_sub_X_of {n : ℕ} (h : P32 ∣ B (pows.getD 32 []) - X ^ n) : P32 ∣ X ^ n - X := by
  rw [pows_32_eq] at h
  exact dvd_sub_comm.mp h

/-- `x^(2^32) ≡ x (mod P)`. -/
theorem P32_dvd_X_pow_two_pow_32_sub_X : P32 ∣ X ^ (2 ^ 32) - X :=
  dvd_X_pow_sub_X_of (pows_dvd 32 le_rfl)

theorem X_isCoprime_P32 : IsCoprime (X : (ZMod 2)[X]) P32 :=
  ⟨-(X ^ 31 + X ^ 25 + X ^ 22 + X ^ 21 + X ^ 15 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 6 +
      X ^ 4 + X ^ 3 + X + 1), 1, by ring⟩

theorem P32_dvd_X_pow_sub_one_of {n : ℕ} (h : P32 ∣ X ^ n - X) (hn : 1 ≤ n) :
    P32 ∣ X ^ (n - 1) - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel]
  have e : (X : (ZMod 2)[X]) ^ (m + 1) - X = X * (X ^ m - 1) := by ring
  rw [e] at h
  exact X_isCoprime_P32.symm.dvd_of_dvd_mul_left h

/-- `x` has order dividing `2^32 - 1` modulo `P`. -/
theorem P32_dvd_X_pow_sub_one : P32 ∣ X ^ (2 ^ 32 - 1) - 1 :=
  P32_dvd_X_pow_sub_one_of P32_dvd_X_pow_two_pow_32_sub_X Nat.one_le_two_pow

theorem length_ofBytes (bs : List (BitVec 8)) : (Message.ofBytes bs).length = bs.length * 8 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [Message.ofBytes, List.flatMap_cons, List.length_append, List.length_ofFn] at ih ⊢
    rw [ih, List.length_cons]; ring

theorem poly_eq_zero_of_forall {M : Message} (h : ∀ b ∈ M, b = 0) : M.poly = 0 := by
  unfold Message.poly
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [h _ (List.get_mem M k), map_zero, zero_mul]

theorem ofBytes_replicate_zero (n : ℕ) : ∀ b ∈ Message.ofBytes (List.replicate n 0#8), b = 0 := by
  intro b hb
  simp only [Message.ofBytes, List.mem_flatMap, List.mem_replicate, List.mem_ofFn] at hb
  obtain ⟨a, ⟨_, rfl⟩, i, rfl⟩ := hb
  simp

theorem crc_zero_init_of_dvd (P u : (ZMod 2)[X]) (M : Message) (hM : ∀ b ∈ M, b = 0)
    (h : P ∣ X ^ M.length - 1) : crc P u M 0 = 0 := by
  unfold crc
  rw [poly_eq_zero_of_forall hM]
  have e : (0 - u) * X ^ M.length + 0 * X ^ P.natDegree + u = -(u * (X ^ M.length - 1)) := by ring
  rw [e]
  exact EuclideanDomain.mod_eq_zero.mpr (dvd_neg.mpr (dvd_mul_of_dvd_right h u))

theorem dvd_pow_mul_eight {n L : ℕ} (h : P32 ∣ X ^ n - 1) (hL : L = n * 8) : P32 ∣ X ^ L - 1 := by
  subst hL
  exact h.trans (pow_one_sub_dvd_pow_mul_sub_one X n 8)

end KadatchJenkins.Readings

namespace KadatchJenkins

open Readings in
theorem crc32_zero_bytes_eq_zero_dev :
    crc (X ^ 32 + X ^ 26 + X ^ 23 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 +
          X ^ 5 + X ^ 4 + X ^ 2 + X + 1) (stdU 32)
        (Message.ofBytes (List.replicate (2 ^ 32 - 1) 0#8)) 0 = 0 := by
  refine crc_zero_init_of_dvd _ _ _ (ofBytes_replicate_zero _) ?_
  exact dvd_pow_mul_eight P32_dvd_X_pow_sub_one (by rw [length_ofBytes, List.length_replicate])

end KadatchJenkins

theorem solution : type_of% @KadatchJenkins.crc32_zero_bytes_eq_zero_dev :=
  @KadatchJenkins.crc32_zero_bytes_eq_zero_dev
