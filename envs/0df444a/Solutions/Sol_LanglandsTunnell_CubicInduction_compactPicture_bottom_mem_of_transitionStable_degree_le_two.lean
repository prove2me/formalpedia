-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.compactPicture_bottom_mem_of_transitionStable_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d5b6a24c-825a-574d-9212-7e53f213a46a

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Span.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open MvPolynomial

namespace CompactPictureBottom

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

noncomputable def qsum (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)

noncomputable def sameTwo (M : Matrix (Fin 3) (Fin 3) P3) : P3 :=
  MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
    (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))

theorem sameTwo_eq (M : Matrix (Fin 3) (Fin 3) P3) :
    sameTwo M = C 6 * qsum M - (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) *
      (pderiv 0 (pderiv 0 (qsum M)) + pderiv 1 (pderiv 1 (qsum M)) + pderiv 2 (pderiv 2 (qsum M))) := by
  simp only [sameTwo, qsum, Fin.sum_univ_three]

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

lemma pdXsq (i j : Fin 3) : pderiv i (X j ^ 2 : P3) = if j = i then C 2 * X j else 0 := by
  rw [sq, pderiv_mul, pdX]
  split_ifs
  · simp only [map_ofNat]; ring
  · ring

lemma pd_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n) : P3) = 0 := by
  rw [← map_ofNat (C : ℂ →+* P3) n]; exact pderiv_C

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

theorem qsum_Xi (ν : Fin 3 → ℂ) (p : P3) :
    qsum (Xi ν p) = C 2 * (C (ν 0) * (X 0 * pderiv 0 p) + C (ν 1) * (X 1 * pderiv 1 p)
      + C (ν 2) * (X 2 * pderiv 2 p))
      + X 0 ^ 2 * (pderiv 1 (pderiv 1 p) + pderiv 2 (pderiv 2 p))
      + X 1 ^ 2 * (pderiv 2 (pderiv 2 p) - pderiv 0 (pderiv 0 p))
      - X 2 ^ 2 * (pderiv 0 (pderiv 0 p) + pderiv 1 (pderiv 1 p)) := by
  simp only [qsum, Xi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue, Fin.reduceEq, if_true, if_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul, add_zero,
    zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem lowerTwo_Xi_dq (ν : Fin 3 → ℂ) (α β : ℂ) :
    lowerTwo (Xi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (4 * (α * (ν 0 - ν 2 - 2) + β * (ν 1 - ν 2 - 1))) := by
  rw [lowerTwo_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdXsq, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, if_true, if_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem sameTwo_Xi_dq (ν : Fin 3 → ℂ) (α β : ℂ) :
    sameTwo (Xi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (16 * α * ν 0 + 8 * α * ν 2 + 4 * α - 8 * β * ν 1 + 8 * β * ν 2 + 8 * β) * (X 0 ^ 2 - X 2 ^ 2)
      + C (-8 * α * ν 0 + 8 * α * ν 2 - 8 * α + 16 * β * ν 1 + 8 * β * ν 2 - 4 * β) * (X 1 ^ 2 - X 2 ^ 2) := by
  rw [sameTwo_eq, qsum_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdXsq, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, if_true, if_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem lowerOne_Xi_X01 (ν : Fin 3 → ℂ) (z : ℂ) :
    lowerOne (Xi ν (C z * (X 0 * X 1))) = C (-2 * z * (ν 0 - ν 1 - 1)) * X 2 := by
  rw [lowerOne_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, if_true, if_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

theorem lowerOne_Xi_X02 (ν : Fin 3 → ℂ) (z : ℂ) :
    lowerOne (Xi ν (C z * (X 0 * X 2))) = C (2 * z * (ν 0 - ν 2 - 1)) * X 1 := by
  rw [lowerOne_Xi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C, pd_ofNat, pdX,
    pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true, if_true, if_false, mul_zero, zero_mul,
    add_zero, zero_add, sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

lemma mem_of_C_mul_mem (S : Submodule ℂ P3) (v : P3) (L : ℂ) (hL : L ≠ 0) (h : C L * v ∈ S) : v ∈ S := by
  have := S.smul_mem L⁻¹ h
  rwa [smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hL, map_one, one_mul] at this

theorem one_mem_of_stable (ν : Fin 3 → ℂ)
    (h01 : ν 0 - ν 1 - 1 ≠ 0) (h02 : ν 0 - ν 2 - 1 ≠ 0) (h12 : ν 1 - ν 2 - 1 ≠ 0)
    (S₀ S₂ : Submodule ℂ P3)
    (hS₀ : S₀ ≤ Submodule.span ℂ {(1 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 ^ 2 - X 2 ^ 2 : P3), X 1 ^ 2 - X 2 ^ 2})
    (hst : ∀ p ∈ S₂, lowerTwo (Xi ν p) ∈ S₀ ∧ sameTwo (Xi ν p) ∈ S₂)
    (hne : S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) : (1 : P3) ∈ S₀ := by

  have key : ∀ L : ℂ, C L ∈ S₀ → L = 0 ∨ (1 : P3) ∈ S₀ := by
    intro L hmem
    rcases eq_or_ne L 0 with hL | hL
    · exact Or.inl hL
    · exact Or.inr (mem_of_C_mul_mem S₀ 1 L hL (by rwa [mul_one]))
  rcases hne with h0 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₀ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul, mul_one] at hs
    exact (key z hs).resolve_left hz
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 (hS₂ hp)
    rw [smul_eq_C_mul, smul_eq_C_mul] at hp hp0
    obtain ⟨hL1, hS⟩ := hst _ hp
    obtain ⟨hL2, -⟩ := hst _ hS
    rw [lowerTwo_Xi_dq] at hL1
    rw [sameTwo_Xi_dq, lowerTwo_Xi_dq] at hL2
    rcases key _ hL1 with hz1 | h
    swap; · exact h
    rcases key _ hL2 with hz2 | h
    swap; · exact h
    exfalso
    apply hp0
    have hdet : (ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h01 h02) h12
    have hα : α = 0 := by
      have e : α * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          (-(-2 * ν 0 * ν 1 + 2 * ν 0 * ν 2 + 2 * ν 0 + 4 * ν 1 ^ 2 - ν 1 - 4 * ν 2 ^ 2 - 7 * ν 2 - 3) / 24) * hz1
          + ((ν 1 - ν 2 - 1) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    have hβ : β = 0 := by
      have e : β * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          ((4 * ν 0 ^ 2 - 2 * ν 0 * ν 1 - 5 * ν 0 + 2 * ν 1 * ν 2 - 2 * ν 1 - 4 * ν 2 ^ 2 - 5 * ν 2) / 24) * hz1
          + (-(ν 0 - ν 2 - 2) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    simp [hα, hβ]

theorem X_two_mem_of_stable (ν : Fin 3 → ℂ) (h01 : ν 0 - ν 1 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ P3)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 2 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 1 : P3)})
    (hst : ∀ p ∈ S₂, lowerOne (Xi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 2 : P3) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [lowerOne_Xi_X01] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h01

theorem X_one_mem_of_stable (ν : Fin 3 → ℂ) (h02 : ν 0 - ν 2 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ P3)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 1 : P3)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 2 : P3)})
    (hst : ∀ p ∈ S₂, lowerOne (Xi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 1 : P3) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [lowerOne_Xi_X02] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h02

lemma ne_zero_of_re_ne_zero {z : ℂ} (h : z.re ≠ 0) : z ≠ 0 := fun hz => h (by simp [hz])

end CompactPictureBottom
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two.CompactPictureBottom"

open CompactPictureBottom in
theorem solution
    (τ τ₃ : ℝ) :
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
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₂ p) ∈ S₀ ∧ same₂ (Ξ ν₁₂ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₂ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ S₁) ∧
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, lower₂ (Ξ ν₁₃ p) ∈ S₀ ∧ same₂ (Ξ ν₁₃ p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, lower₁ (Ξ ν₁₃ p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ S₁) := by
  intro Ξ lower₂ lower₁ same₂ ν₁₂ ν₁₃

  have A01 : ν₁₂ 0 - ν₁₂ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have A02 : ν₁₂ 0 - ν₁₂ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have A12 : ν₁₂ 1 - ν₁₂ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₂]; norm_num
  have B01 : ν₁₃ 0 - ν₁₃ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  have B02 : ν₁₃ 0 - ν₁₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  have B12 : ν₁₃ 1 - ν₁₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [ν₁₃]; norm_num
  refine ⟨fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_,
    fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_⟩
  · exact one_mem_of_stable ν₁₂ A01 A02 A12 S₀ S₂ h0 h2 hst hne
  · exact X_two_mem_of_stable ν₁₂ A01 S₁ S₂ h1 h2 hst hne
  · exact one_mem_of_stable ν₁₃ B01 B02 B12 S₀ S₂ h0 h2 hst hne
  · exact X_one_mem_of_stable ν₁₃ B02 S₁ S₂ h1 h2 hst hne

end S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_transitionStable_degree_le_two (solution)
