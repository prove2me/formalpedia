-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/de28aeb0-66be-5a0d-8289-ad9aa88eed21

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le

set_option autoImplicit false

open MvPolynomial

namespace CompactPictureLowering

abbrev P3 := MvPolynomial (Fin 3) ℂ

noncomputable def Xi (ν : Fin 3 → ℂ) (p : P3) : Matrix (Fin 3) (Fin 3) P3 :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

noncomputable def lowerTwo (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

noncomputable def lowerOne (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

theorem coeff_pderiv {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    coeff m (pderiv i f) = (m i + 1) * coeff (m + Finsupp.single i 1) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m + Finsupp.single i 1
    · subst h
      simp [mul_comm]
    · rw [if_neg h]
      split_ifs with h'
      · have hs : s i = 0 := by
          by_contra hne
          apply h
          rw [← h']
          ext j
          simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply,
            Finsupp.single_apply]
          split_ifs with hj
          · subst hj; omega
          · omega
        simp [hs]
      · simp
  | add f g hf hg => simp [hf, hg, mul_add]

theorem pderiv_comm {σ : Type*} [DecidableEq σ] (i j : σ) (f : MvPolynomial σ ℂ) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  ext m
  simp only [coeff_pderiv]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [add_right_comm]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg hij,
      if_neg (Ne.symm hij), add_zero]
    ring

@[scoped simp] lemma max01 : max (0 : Fin 3) 1 = 1 := by decide
@[scoped simp] lemma max02 : max (0 : Fin 3) 2 = 2 := by decide
@[scoped simp] lemma max12 : max (1 : Fin 3) 2 = 2 := by decide
@[scoped simp] lemma max10 : max (1 : Fin 3) 0 = 1 := by decide
@[scoped simp] lemma max20 : max (2 : Fin 3) 0 = 2 := by decide
@[scoped simp] lemma max21 : max (2 : Fin 3) 1 = 2 := by decide
@[scoped simp] lemma min01 : min (0 : Fin 3) 1 = 0 := by decide
@[scoped simp] lemma min02 : min (0 : Fin 3) 2 = 0 := by decide
@[scoped simp] lemma min12 : min (1 : Fin 3) 2 = 1 := by decide
@[scoped simp] lemma min10 : min (1 : Fin 3) 0 = 0 := by decide
@[scoped simp] lemma min20 : min (2 : Fin 3) 0 = 0 := by decide
@[scoped simp] lemma min21 : min (2 : Fin 3) 1 = 1 := by decide

lemma pdX (i j : Fin 3) : pderiv i (X j : P3) = if j = i then 1 else 0 := by
  classical
  rw [pderiv_X]; simp [Pi.single_apply]

lemma c10 (f : P3) : pderiv 1 (pderiv 0 f) = pderiv 0 (pderiv 1 f) := pderiv_comm _ _ _
lemma c20 (f : P3) : pderiv 2 (pderiv 0 f) = pderiv 0 (pderiv 2 f) := pderiv_comm _ _ _
lemma c21 (f : P3) : pderiv 2 (pderiv 1 f) = pderiv 1 (pderiv 2 f) := pderiv_comm _ _ _

theorem lowerTwo_Xi (ν : Fin 3 → ℂ) (p : P3) :
    lowerTwo (Xi ν p) = C 2 * ((C (ν 0) - 1) * pderiv 0 (pderiv 0 p) + C (ν 1) * pderiv 1 (pderiv 1 p)
      + (C (ν 2) + 1) * pderiv 2 (pderiv 2 p)
      + X 0 * pderiv 0 (pderiv 1 (pderiv 1 p)) + X 0 * pderiv 0 (pderiv 2 (pderiv 2 p))
      - X 1 * pderiv 1 (pderiv 0 (pderiv 0 p)) + X 1 * pderiv 1 (pderiv 2 (pderiv 2 p))
      - X 2 * pderiv 2 (pderiv 0 (pderiv 0 p)) - X 2 * pderiv 2 (pderiv 1 (pderiv 1 p))) := by
  simp only [lowerTwo, Xi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue, Fin.reduceEq, if_true, if_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem lowerOne_eq (M : Matrix (Fin 3) (Fin 3) P3) :
    lowerOne M =
      (X 1 * pderiv 0 (pderiv 2 (M 0 0)) + X 1 * pderiv 1 (pderiv 2 (M 0 1)) + X 1 * pderiv 2 (pderiv 2 (M 0 2)))
      - (X 2 * pderiv 0 (pderiv 1 (M 0 0)) + X 2 * pderiv 1 (pderiv 1 (M 0 1)) + X 2 * pderiv 1 (pderiv 2 (M 0 2)))
      + (X 2 * pderiv 0 (pderiv 0 (M 1 0)) + X 2 * pderiv 0 (pderiv 1 (M 1 1)) + X 2 * pderiv 0 (pderiv 2 (M 1 2)))
      - (X 0 * pderiv 0 (pderiv 2 (M 1 0)) + X 0 * pderiv 1 (pderiv 2 (M 1 1)) + X 0 * pderiv 2 (pderiv 2 (M 1 2)))
      + (X 0 * pderiv 0 (pderiv 1 (M 2 0)) + X 0 * pderiv 1 (pderiv 1 (M 2 1)) + X 0 * pderiv 1 (pderiv 2 (M 2 2)))
      - (X 1 * pderiv 0 (pderiv 0 (M 2 0)) + X 1 * pderiv 0 (pderiv 1 (M 2 1)) + X 1 * pderiv 0 (pderiv 2 (M 2 2))) := by
  simp only [lowerOne, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, c10, c20, c21]
  norm_num
  ring

theorem lowerOne_Xi (ν : Fin 3 → ℂ) (p : P3) :
    lowerOne (Xi ν p) = C 2 * (C (ν 1 - ν 0 + 1) * (X 2 * pderiv 0 (pderiv 1 p))
      + C (ν 0 - ν 2 - 1) * (X 1 * pderiv 0 (pderiv 2 p))
      + C (ν 2 - ν 1 + 1) * (X 0 * pderiv 1 (pderiv 2 p))
      + X 2 * (X 1 * pderiv 1 (pderiv 0 (pderiv 1 p)))
      - X 1 * (X 1 * pderiv 1 (pderiv 0 (pderiv 2 p)))
      - X 0 * (X 2 * pderiv 1 (pderiv 1 (pderiv 1 p)))
      + X 0 * (X 1 * pderiv 1 (pderiv 1 (pderiv 2 p)))) := by
  rw [lowerOne_eq]
  simp only [Xi, Matrix.of_apply, Fin.isValue, Fin.reduceEq, if_true, if_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

noncomputable def fs (a b k : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 k

@[scoped simp] lemma fs_apply_zero (a b k : ℕ) : fs a b k 0 = a := by simp [fs]
@[scoped simp] lemma fs_apply_one (a b k : ℕ) : fs a b k 1 = b := by simp [fs]
@[scoped simp] lemma fs_apply_two (a b k : ℕ) : fs a b k 2 = k := by simp [fs]

lemma eq_fs (m : Fin 3 →₀ ℕ) : m = fs (m 0) (m 1) (m 2) := by
  ext i; fin_cases i <;> simp

lemma fs_degree (a b k : ℕ) : (fs a b k).degree = a + b + k := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]; simp

lemma fs_add_single_zero (a b k : ℕ) : fs a b k + Finsupp.single 0 1 = fs (a + 1) b k := by
  ext i; fin_cases i <;> simp
lemma fs_add_single_one (a b k : ℕ) : fs a b k + Finsupp.single 1 1 = fs a (b + 1) k := by
  ext i; fin_cases i <;> simp
lemma fs_add_single_two (a b k : ℕ) : fs a b k + Finsupp.single 2 1 = fs a b (k + 1) := by
  ext i; fin_cases i <;> simp
lemma fs_sub_single_zero (a b k : ℕ) : fs (a + 1) b k - Finsupp.single 0 1 = fs a b k := by
  ext i; fin_cases i <;> simp
lemma fs_sub_single_one (a b k : ℕ) : fs a (b + 1) k - Finsupp.single 1 1 = fs a b k := by
  ext i; fin_cases i <;> simp
lemma fs_sub_single_two (a b k : ℕ) : fs a b (k + 1) - Finsupp.single 2 1 = fs a b k := by
  ext i; fin_cases i <;> simp

lemma coeff_pderiv_zero (a b k : ℕ) (f : P3) :
    coeff (fs a b k) (pderiv 0 f) = ((a : ℂ) + 1) * coeff (fs (a + 1) b k) f := by
  rw [coeff_pderiv, fs_add_single_zero, fs_apply_zero]
lemma coeff_pderiv_one (a b k : ℕ) (f : P3) :
    coeff (fs a b k) (pderiv 1 f) = ((b : ℂ) + 1) * coeff (fs a (b + 1) k) f := by
  rw [coeff_pderiv, fs_add_single_one, fs_apply_one]
lemma coeff_pderiv_two (a b k : ℕ) (f : P3) :
    coeff (fs a b k) (pderiv 2 f) = ((k : ℂ) + 1) * coeff (fs a b (k + 1)) f := by
  rw [coeff_pderiv, fs_add_single_two, fs_apply_two]

lemma coeff_X_mul_pderiv_self {σ : Type*} [DecidableEq σ] (i : σ) (m : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    coeff m (X i * pderiv i f) = (m i : ℂ) * coeff m f := by
  rw [coeff_X_mul']
  split_ifs with h
  · rw [coeff_pderiv]
    have hi : m i ≠ 0 := Finsupp.mem_support_iff.1 h
    have : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
      ext j
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hij
      · subst hij; omega
      · omega
    rw [this]
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hi)]
    push_cast; ring
  · have hi : m i = 0 := by simpa [Finsupp.mem_support_iff] using h
    simp [hi]

lemma coeff_X_zero_mul_succ (a b k : ℕ) (f : P3) : coeff (fs (a + 1) b k) (X 0 * f) = coeff (fs a b k) f := by
  rw [coeff_X_mul', if_pos (by simp [Finsupp.mem_support_iff]), fs_sub_single_zero]
lemma coeff_X_one_mul_succ (a b k : ℕ) (f : P3) : coeff (fs a (b + 1) k) (X 1 * f) = coeff (fs a b k) f := by
  rw [coeff_X_mul', if_pos (by simp [Finsupp.mem_support_iff]), fs_sub_single_one]
lemma coeff_X_two_mul_succ (a b k : ℕ) (f : P3) : coeff (fs a b (k + 1)) (X 2 * f) = coeff (fs a b k) f := by
  rw [coeff_X_mul', if_pos (by simp [Finsupp.mem_support_iff]), fs_sub_single_two]
lemma coeff_X_zero_mul_zero (b k : ℕ) (f : P3) : coeff (fs 0 b k) (X 0 * f) = 0 := by
  rw [coeff_X_mul', if_neg (by simp [Finsupp.mem_support_iff])]
lemma coeff_X_one_mul_zero (a k : ℕ) (f : P3) : coeff (fs a 0 k) (X 1 * f) = 0 := by
  rw [coeff_X_mul', if_neg (by simp [Finsupp.mem_support_iff])]
lemma coeff_X_two_mul_zero (a b : ℕ) (f : P3) : coeff (fs a b 0) (X 2 * f) = 0 := by
  rw [coeff_X_mul', if_neg (by simp [Finsupp.mem_support_iff])]

section Equations

variable {ν : Fin 3 → ℂ} {p : P3}

lemma harm_cf (hΔ : (∑ i : Fin 3, pderiv i (pderiv i p)) = 0) (a b k : ℕ) :
    ((a : ℂ) + 2) * ((a : ℂ) + 1) * coeff (fs (a + 2) b k) p
      + ((b : ℂ) + 2) * ((b : ℂ) + 1) * coeff (fs a (b + 2) k) p
      + ((k : ℂ) + 2) * ((k : ℂ) + 1) * coeff (fs a b (k + 2)) p = 0 := by
  have h := congrArg (coeff (fs a b k)) hΔ
  simp only [Fin.sum_univ_three, Fin.isValue, coeff_add, coeff_zero, coeff_pderiv_zero, coeff_pderiv_one,
    coeff_pderiv_two] at h
  push_cast at h
  linear_combination h

lemma lowerTwo_cf (h2 : lowerTwo (Xi ν p) = 0) (a b k : ℕ) :
    (ν 0 - 1 - b - k) * (((a : ℂ) + 2) * ((a : ℂ) + 1)) * coeff (fs (a + 2) b k) p
      + (ν 1 + a - k) * (((b : ℂ) + 2) * ((b : ℂ) + 1)) * coeff (fs a (b + 2) k) p
      + (ν 2 + 1 + a + b) * (((k : ℂ) + 2) * ((k : ℂ) + 1)) * coeff (fs a b (k + 2)) p = 0 := by
  rw [lowerTwo_Xi] at h2
  have h := congrArg (coeff (fs a b k)) h2
  simp only [Fin.isValue, sub_mul, add_mul, one_mul, coeff_add, coeff_sub, coeff_zero, coeff_pderiv_zero,
    coeff_pderiv_one, coeff_pderiv_two, coeff_X_mul_pderiv_self, fs_apply_zero, fs_apply_one, fs_apply_two,
    coeff_C_mul, add_assoc, Nat.reduceAdd] at h
  push_cast at h
  linear_combination h / 2

lemma layer_cf (hΔ : (∑ i : Fin 3, pderiv i (pderiv i p)) = 0) (h2 : lowerTwo (Xi ν p) = 0) (a b k : ℕ) :
    ((a : ℂ) + 2) * ((a : ℂ) + 1) * (ν 0 - ν 2 - 2 - a - 2 * b - k) * coeff (fs (a + 2) b k) p
      + ((b : ℂ) + 2) * ((b : ℂ) + 1) * (ν 1 - ν 2 - 1 - b - k) * coeff (fs a (b + 2) k) p = 0 := by
  linear_combination lowerTwo_cf h2 a b k - (ν 2 + 1 + a + b) * harm_cf hΔ a b k

lemma lowerOne_cf (h1 : lowerOne (Xi ν p) = 0) (n : ℕ) :
    ((ν 0 - ν 2 - n - 2) * coeff (fs 1 (n + 1) 1) p = 0)
    ∧ (2 * (ν 0 - ν 2 - 1 - n) * coeff (fs 2 n 1) p
        + ((n : ℂ) + 2) * (ν 2 - ν 1 + n + 2) * coeff (fs 0 (n + 2) 1) p = 0)
    ∧ (((n : ℂ) + 2) * (ν 1 - ν 0 + n + 2) * coeff (fs 1 (n + 2) 0) p
        + 2 * (ν 0 - ν 2 - 1 - n) * coeff (fs 1 n 2) p = 0)
    ∧ (2 * (ν 1 - ν 0 + 1) * coeff (fs 2 1 0) p + 2 * (ν 2 - ν 1 + 1) * coeff (fs 0 1 2) p
        - 6 * coeff (fs 0 3 0) p = 0)
    ∧ (2 * ((n : ℂ) + 2) * (ν 1 - ν 0 + n + 2) * coeff (fs 2 (n + 2) 0) p
        + 4 * (ν 0 - ν 2 - 1 - n) * coeff (fs 2 n 2) p
        + 2 * ((n : ℂ) + 2) * (ν 2 - ν 1 + n + 2) * coeff (fs 0 (n + 2) 2) p
        - ((n : ℂ) + 2) * ((n : ℂ) + 3) * ((n : ℂ) + 4) * coeff (fs 0 (n + 4) 0) p = 0) := by
  rw [lowerOne_Xi] at h1
  have q0 := congrArg (coeff (fs 0 (n + 2) 0)) h1
  have q1 := congrArg (coeff (fs 1 (n + 1) 0)) h1
  have r0 := congrArg (coeff (fs 0 (n + 1) 1)) h1
  have r1z := congrArg (coeff (fs 1 0 1)) h1
  have r1s := congrArg (coeff (fs 1 (n + 1) 1)) h1
  simp only [Fin.isValue, mul_add, mul_sub, coeff_add, coeff_sub, coeff_zero, coeff_pderiv_zero,
    coeff_pderiv_one, coeff_pderiv_two, coeff_X_mul_pderiv_self, fs_apply_one,
    coeff_C_mul, coeff_X_zero_mul_succ, coeff_X_one_mul_succ, coeff_X_two_mul_succ, coeff_X_zero_mul_zero,
    coeff_X_one_mul_zero, coeff_X_two_mul_zero, add_assoc, Nat.reduceAdd, mul_zero, add_zero,
    zero_add, sub_zero] at q0 q1 r0 r1z r1s
  push_cast at q0 q1 r0 r1z r1s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination q0 / 2
  · linear_combination q1 / 2
  · linear_combination r0 / 2
  · linear_combination r1z / 2
  · linear_combination r1s / 2

end Equations

theorem eq_zero_of_lowering_eq_zero (ν : Fin 3 → ℂ) (ℓ : ℕ) (hℓ : 3 ≤ ℓ)
    (h01 : ν 0 - ν 1 - (ℓ - 1 : ℂ) ≠ 0) (h02 : ν 0 - ν 2 - (ℓ - 1 : ℂ) ≠ 0)
    (h12 : ν 1 - ν 2 - (ℓ - 1 : ℂ) ≠ 0) (hprop : ∀ j : ℕ, ν 0 - ν 2 - 2 - j ≠ 0)
    (p : P3) (hp : p.IsHomogeneous ℓ) (hΔ : (∑ i : Fin 3, pderiv i (pderiv i p)) = 0)
    (h2 : lowerTwo (Xi ν p) = 0) (h1 : lowerOne (Xi ν p) = 0) : p = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 3 := ⟨ℓ - 3, by omega⟩

  have hH := harm_cf hΔ
  have hT := layer_cf hΔ h2

  have h02' : ν 0 - ν 2 - n - 2 ≠ 0 := fun h => h02 (by push_cast; linear_combination h)
  have h01' : ν 0 - ν 1 - n - 2 ≠ 0 := fun h => h01 (by push_cast; linear_combination h)
  have h12' : ν 1 - ν 2 - n - 2 ≠ 0 := fun h => h12 (by push_cast; linear_combination h)
  have hn2 : ((n : ℂ) + 2) ≠ 0 := by norm_cast

  have propag : ∀ a b k : ℕ, coeff (fs a (b + 2) k) p = 0 → coeff (fs (a + 2) b k) p = 0 := by
    intro a b k h
    have e := hT a b k
    rw [h, mul_zero, add_zero] at e
    have hne : ν 0 - ν 2 - 2 - a - 2 * b - k ≠ 0 := fun h' => hprop (a + 2 * b + k) (by
      push_cast; linear_combination h')
    have ha2 : ((a : ℂ) + 2) ≠ 0 := by norm_cast
    have ha1 : ((a : ℂ) + 1) ≠ 0 := by norm_cast
    exact (mul_eq_zero.1 e).resolve_left (mul_ne_zero (mul_ne_zero ha2 ha1) hne)
  have layer : ∀ k : ℕ, (∀ b, 0 + b + k = n + 3 → coeff (fs 0 b k) p = 0) →
      (∀ b, 1 + b + k = n + 3 → coeff (fs 1 b k) p = 0) →
      ∀ a b, a + b + k = n + 3 → coeff (fs a b k) p = 0 := by
    intro k h0 h1'
    refine Nat.twoStepInduction h0 h1' ?_
    intro a iha _ b hab

    exact propag a b k (iha (b + 2) (by omega))

  obtain ⟨hq0, hq1, hr0, hr1z, -⟩ := lowerOne_cf h1 n
  have v1 : coeff (fs 1 (n + 1) 1) p = 0 := (mul_eq_zero.1 hq0).resolve_left h02'
  have v0 : coeff (fs 0 (n + 2) 1) p = 0 := by
    have e1 := hT 0 n 1
    simp only [Nat.cast_zero, Nat.cast_one, zero_add] at e1
    have key : coeff (fs 0 (n + 2) 1) p
        * (((n : ℂ) + 2) ^ 2 * (ν 0 - ν 2 - n - 2) * (ν 1 - ν 2 - n - 2)) = 0 := by
      linear_combination (-1 : ℂ) * ((-2 * (n : ℂ) + ν 0 - ν 2 - 3) * hq1
        + ((n : ℂ) - ν 0 + ν 2 + 1) * e1)
    exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn2) h02') h12')

  have u1 : coeff (fs 1 (n + 2) 0) p = 0 := by
    have e1 := hH 1 n 0
    have e2 := hT 1 n 0
    simp only [Nat.cast_zero, Nat.cast_one, add_assoc, Nat.reduceAdd, zero_add] at e1 e2
    have key : coeff (fs 1 (n + 2) 0) p
        * (((n : ℂ) + 2) ^ 2 * (ν 0 - ν 1 - n - 2) * (ν 0 - ν 2 - n - 2)) = 0 := by
      linear_combination (-1 : ℂ) * ((-2 * (n : ℂ) + ν 0 - ν 2 - 3) * hr0
        + (-((n : ℂ) - ν 0 + ν 2 + 1) * (2 * (n : ℂ) - ν 0 + ν 2 + 3)) * e1
        + (-(n : ℂ) + ν 0 - ν 2 - 1) * e2)
    exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn2) h01') h02')
  have u0 : coeff (fs 0 (n + 3) 0) p = 0 := by
    cases n with
    | zero =>
      have e1 := hH 0 1 0
      have e2 := hT 0 1 0
      simp only [Nat.cast_zero, Nat.cast_one, add_assoc, Nat.reduceAdd, zero_add] at e1 e2
      have key : coeff (fs 0 3 0) p * (12 * (ν 0 - ν 1 - 2) * (ν 1 - ν 2 - 2)) = 0 := by
        linear_combination (ν 0 - ν 2 - 4) * hr1z + ((ν 0 - ν 2 - 4) * (ν 1 - ν 2 - 1)) * e1
          + (ν 0 - 2 * ν 1 + ν 2) * e2
      refine (mul_eq_zero.1 key).resolve_right (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_)
      · exact fun h => h01' (by push_cast; linear_combination h)
      · exact fun h => h12' (by push_cast; linear_combination h)
    | succ m =>
      obtain ⟨-, -, -, -, hr1s⟩ := lowerOne_cf h1 m
      have e1 := hH 2 m 0
      have e2 := hH 0 (m + 2) 0
      have e3 := hT 2 m 0
      have e4 := hT 0 (m + 2) 0
      simp only [Nat.cast_zero, Nat.cast_ofNat, add_assoc, Nat.reduceAdd, zero_add] at e1 e2 e3 e4
      push_cast at e1 e2 e3 e4
      have key : coeff (fs 0 (m + 4) 0) p * (2 * ((m : ℂ) + 2) * ((m : ℂ) + 3) ^ 2 * ((m : ℂ) + 4)
          * (ν 0 - ν 1 - m - 3) * (ν 0 - ν 2 - m - 3) * (ν 1 - ν 2 - m - 3)) = 0 := by
        linear_combination (2 * (2 * (m : ℂ) - ν 0 + ν 2 + 4) * (2 * (m : ℂ) - ν 0 + ν 2 + 6)) * hr1s
          + (4 * ((m : ℂ) - ν 0 + ν 2 + 1) * (2 * (m : ℂ) - ν 0 + ν 2 + 4) * (2 * (m : ℂ) - ν 0 + ν 2 + 6))
            * e1
          + (-2 * ((m : ℂ) + 2) * ((m : ℂ) - ν 1 + ν 2 + 2) * (2 * (m : ℂ) - ν 0 + ν 2 + 4)
            * (2 * (m : ℂ) - ν 0 + ν 2 + 6)) * e2
          + (4 * ((m : ℂ) - ν 0 + ν 2 + 1) * (2 * (m : ℂ) - ν 0 + ν 2 + 6)) * e3
          + (2 * ((m : ℂ) + 2) * ((m : ℂ) ^ 3 - 2 * (m : ℂ) ^ 2 * ν 0 + (m : ℂ) ^ 2 * ν 1
            + (m : ℂ) ^ 2 * ν 2 + 5 * (m : ℂ) ^ 2 + (m : ℂ) * ν 0 ^ 2 - (m : ℂ) * ν 0 * ν 1
            - (m : ℂ) * ν 0 * ν 2 - 8 * (m : ℂ) * ν 0 + (m : ℂ) * ν 1 * ν 2 + 6 * (m : ℂ) * ν 1
            + 2 * (m : ℂ) * ν 2 + 7 * (m : ℂ) + 2 * ν 0 ^ 2 - 3 * ν 0 * ν 1 - ν 0 * ν 2 - 8 * ν 0
            + 3 * ν 1 * ν 2 + 9 * ν 1 - ν 2 ^ 2 - ν 2 + 3)) * e4
      have hm2 : ((m : ℂ) + 2) ≠ 0 := by norm_cast
      have hm3 : ((m : ℂ) + 3) ≠ 0 := by norm_cast
      have hm4 : ((m : ℂ) + 4) ≠ 0 := by norm_cast
      have g01 : ν 0 - ν 1 - m - 3 ≠ 0 := fun h => h01' (by push_cast; linear_combination h)
      have g02 : ν 0 - ν 2 - m - 3 ≠ 0 := fun h => h02' (by push_cast; linear_combination h)
      have g12 : ν 1 - ν 2 - m - 3 ≠ 0 := fun h => h12' (by push_cast; linear_combination h)
      refine (mul_eq_zero.1 key).resolve_right ?_
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hm2)
        (pow_ne_zero _ hm3)) hm4) g01) g02) g12

  have L0 : ∀ a b, a + b + 0 = n + 3 → coeff (fs a b 0) p = 0 := by
    refine layer 0 ?_ ?_
    · intro b hb; obtain rfl : b = n + 3 := (by omega); exact u0
    · intro b hb; obtain rfl : b = n + 2 := (by omega); exact u1
  have L1 : ∀ a b, a + b + 1 = n + 3 → coeff (fs a b 1) p = 0 := by
    refine layer 1 ?_ ?_
    · intro b hb; obtain rfl : b = n + 2 := (by omega); exact v0
    · intro b hb; obtain rfl : b = n + 1 := (by omega); exact v1

  have all : ∀ k a b, a + b + k = n + 3 → coeff (fs a b k) p = 0 := by
    refine Nat.twoStepInduction L0 L1 ?_
    intro k ihk _ a b habk
    have e := hH a b k
    rw [ihk (a + 2) b (by omega), ihk a (b + 2) (by omega), mul_zero, mul_zero, zero_add, zero_add] at e
    have hk2 : ((k : ℂ) + 2) ≠ 0 := by norm_cast
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by norm_cast
    exact (mul_eq_zero.1 e).resolve_left (mul_ne_zero hk2 hk1)

  ext m
  rw [coeff_zero]
  by_cases hd : m.degree = n + 3
  · rw [eq_fs m] at hd ⊢
    rw [fs_degree] at hd
    exact all _ _ _ (by omega)
  · exact hp.coeff_eq_zero hd

lemma ne_zero_of_re_ne_zero {z : ℂ} (h : z.re ≠ 0) : z ≠ 0 := fun hz => h (by simp [hz])

end CompactPictureLowering
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le.CompactPictureLowering"

open CompactPictureLowering in
theorem solution
    (τ τ₃ : ℝ) (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    let ν₁₂ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]
    let ν₁₃ : Fin 3 → ℂ := ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]
    ∀ p : MvPolynomial (Fin 3) ℂ, p.IsHomogeneous ℓ →
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0 →
      (lower₂ (Ξ ν₁₂ p) = 0 → lower₁ (Ξ ν₁₂ p) = 0 → p = 0) ∧
      (lower₂ (Ξ ν₁₃ p) = 0 → lower₁ (Ξ ν₁₃ p) = 0 → p = 0) := by
  intro Ξ lower₂ lower₁ _ ν₁₂ ν₁₃ p hp hΔ
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  refine ⟨fun h2 h1 => eq_zero_of_lowering_eq_zero ν₁₂ ℓ hℓ ?_ ?_ ?_ ?_ p hp hΔ h2 h1,
    fun h2 h1 => eq_zero_of_lowering_eq_zero ν₁₃ ℓ hℓ ?_ ?_ ?_ ?_ p hp hΔ h2 h1⟩
  · apply ne_zero_of_re_ne_zero; simp [ν₁₂]; intro h; linarith
  · apply ne_zero_of_re_ne_zero; simp [ν₁₂]; intro h; linarith
  · apply ne_zero_of_re_ne_zero; simp [ν₁₂]; intro h; linarith
  · intro j; apply ne_zero_of_re_ne_zero; simp [ν₁₂]; intro h; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · apply ne_zero_of_re_ne_zero; simp [ν₁₃]; intro h; linarith
  · apply ne_zero_of_re_ne_zero; simp [ν₁₃]; intro h; linarith
  · apply ne_zero_of_re_ne_zero; simp [ν₁₃]; intro h; linarith
  · intro j; apply ne_zero_of_re_ne_zero; simp [ν₁₃]; intro h; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

end S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_eq_zero_of_lowering_eq_zero_of_three_le (solution)
