-- Prove2me | solution 1 for MinimaxATE.Learnability.lemma_5_5
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T09:18:46.028906+00:00
-- url     : https://prove2.me/submissions/e879334f-fd01-4e3f-a0e3-007ac8f4c54f

import Mathlib

open scoped BigOperators
open Matrix

private noncomputable def vandM {L : ℕ} (v : Fin L → ℝ) : Matrix (Fin L) (Fin L) ℝ :=
  (Matrix.vandermonde v)ᵀ * Matrix.diagonal v

private lemma vandM_apply {L : ℕ} (v : Fin L → ℝ) (i j : Fin L) :
    vandM v i j = v j ^ ((i : ℕ) + 1) := by
  rw [vandM, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply]
  exact (pow_succ (v j) (i : ℕ)).symm

theorem solution (u : ℝ) (hu : 0 < u) (L : ℕ) (hL : 2 ≤ L) :
    ∃ (q w : Fin L → ℝ) (A : ℝ), A ≠ 0 ∧ A < 4 ∧
      (∀ j, q j ∈ Set.Icc u ((L : ℝ) ^ 2 * u)) ∧
      ∑ j, |w j| ≤ 1 ∧
      ∑ j, q j * |w j| = u ∧
      ∑ j, q j * w j = u / A ∧
      ∀ h : ℕ, 2 ≤ h → h ≤ L → ∑ j, q j ^ h * w j = 0 := by
  classical
  haveI : NeZero L := ⟨by omega⟩
  set v : Fin L → ℝ := fun i => (i : ℝ) + 1 with hv
  set b : Fin L → ℝ := -Pi.single (0 : Fin L) 1 with hb
  set M : Matrix (Fin L) (Fin L) ℝ := vandM v with hM
  set w₀ : Fin L → ℝ := M⁻¹ *ᵥ b with hw₀
  set S : ℝ := ∑ j, v j * |w₀ j| with hS
  have hv_pos : ∀ j : Fin L, 0 < v j := by
    intro j
    simp only [hv]
    positivity
  have hv_ge1 : ∀ j : Fin L, (1 : ℝ) ≤ v j := by
    intro j
    simp only [hv]
    have := Nat.cast_nonneg (α := ℝ) (j : ℕ)
    linarith
  have hv_le : ∀ j : Fin L, v j ≤ (L : ℝ) := by
    intro j
    have h1 : (j : ℕ) + 1 ≤ L := by have := j.isLt; omega
    have h2 : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    simpa [hv, Nat.cast_add, Nat.cast_one] using h2
  have hinj : Function.Injective v := by
    intro i j hij
    simp only [hv] at hij
    have h2 : (i : ℝ) = (j : ℝ) := by linarith
    exact Fin.ext (Nat.cast_injective h2)
  have hdetV : (Matrix.vandermonde v).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hdetM : M.det ≠ 0 := by
    rw [hM, vandM, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
    exact mul_ne_zero hdetV (ne_of_gt (Finset.prod_pos (fun j _ => hv_pos j)))
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdetM
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hunit
  have hMw : M *ᵥ w₀ = b := by
    rw [hw₀, Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have hMapply : ∀ i j : Fin L, M i j = v j ^ ((i : ℕ) + 1) := by
    intro i j
    rw [hM]
    exact vandM_apply v i j
  have hentry : ∀ i : Fin L, ∑ j, v j ^ ((i : ℕ) + 1) * w₀ j = b i := by
    intro i
    have h := congrFun hMw i
    rw [Matrix.mulVec_apply, Matrix.row, dotProduct] at h
    simpa only [hMapply] using h
  have hmoment : ∀ h : ℕ, 1 ≤ h → h ≤ L →
      ∑ j, v j ^ h * w₀ j = -(if h = 1 then 1 else 0) := by
    intro h h1 h2
    have hlt : h - 1 < L := by omega
    have hcast : ((⟨h - 1, hlt⟩ : Fin L) : ℕ) = h - 1 := rfl
    have hsucc : h - 1 + 1 = h := by omega
    have hkey := hentry ⟨h - 1, hlt⟩
    rw [hcast, hsucc] at hkey
    have hbval : b ⟨h - 1, hlt⟩ = -(if h = 1 then 1 else 0) := by
      by_cases hh1 : h = 1
      · subst hh1
        simp [hb]
      · have hne : (⟨h - 1, hlt⟩ : Fin L) ≠ 0 := by
          intro hc
          have h0 : ((⟨h - 1, hlt⟩ : Fin L) : ℕ) = 0 := by rw [hc]; rfl
          omega
        simp [hb, hh1, hne]
    rw [hbval] at hkey
    exact hkey
  have h0 : ∑ j, v j * w₀ j = -1 := by
    have h := hmoment 1 le_rfl (by omega)
    simpa using h
  have hS1 : 1 ≤ S := by
    have htri : |∑ j : Fin L, v j * w₀ j| ≤ ∑ j : Fin L, |v j * w₀ j| :=
      Finset.abs_sum_le_sum_abs _ _
    rw [h0, abs_neg, abs_one] at htri
    have hcongr : ∑ j : Fin L, |v j * w₀ j| = ∑ j : Fin L, v j * |w₀ j| := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [abs_mul, abs_of_pos (hv_pos j)]
    rw [hcongr] at htri
    rw [hS]
    exact htri
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hSne : S ≠ 0 := hSpos.ne'
  refine ⟨fun j => u * v j, fun j => S⁻¹ * w₀ j, -S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact neg_ne_zero.mpr hSne
  · linarith
  · intro j
    refine ⟨?_, ?_⟩
    · have h1 : (1 : ℝ) ≤ v j := hv_ge1 j
      nlinarith [hu]
    · have h1 : v j ≤ (L : ℝ) := hv_le j
      have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
      have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
      nlinarith [hu, h1, hL1, hL2]
  · have hinv : 0 ≤ S⁻¹ := inv_nonneg.mpr hSpos.le
    have hsum : ∑ j, |S⁻¹ * w₀ j| = S⁻¹ * ∑ j, |w₀ j| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg hinv]
    rw [hsum]
    have h2 : ∑ j, |w₀ j| ≤ ∑ j, v j * |w₀ j| := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h3 : (1 : ℝ) ≤ v j := hv_ge1 j
      have h4 : (0 : ℝ) ≤ |w₀ j| := abs_nonneg _
      nlinarith
    have h3 : S⁻¹ * ∑ j, |w₀ j| ≤ S⁻¹ * S := mul_le_mul_of_nonneg_left h2 hinv
    rwa [inv_mul_cancel₀ hSne] at h3
  · have hterm : ∀ j, (u * v j) * |S⁻¹ * w₀ j| = (u * S⁻¹) * (v j * |w₀ j|) := by
      intro j
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hSpos.le)]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, hS,
      mul_assoc, inv_mul_cancel₀ hSne, mul_one]
  · have hterm : ∀ j, (u * v j) * (S⁻¹ * w₀ j) = (u * S⁻¹) * (v j * w₀ j) := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, h0]
    rw [div_eq_mul_inv, inv_neg]
    ring
  · intro h h2 h3
    have hz : ∑ j, v j ^ h * w₀ j = 0 := by
      have hh := hmoment h (by omega) h3
      rw [if_neg (by omega)] at hh
      simpa using hh
    have hterm : ∀ j, (u * v j) ^ h * (S⁻¹ * w₀ j) = (u ^ h * S⁻¹) * (v j ^ h * w₀ j) := by
      intro j
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, hz, mul_zero]
