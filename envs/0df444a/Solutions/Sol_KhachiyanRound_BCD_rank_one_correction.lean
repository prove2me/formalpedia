-- Prove2me | solution 1 for KhachiyanRound.BCD.rank_one_correction
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:18:13.304072+00:00
-- url     : https://prove2.me/submissions/ac93f98d-06d5-47b3-a142-6696af77b798

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

open KhachiyanRound.BCD Matrix

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (hn : 2 ≤ n) (p : ι → ℝ) (hp : p ∈ SF a)
    (r : ι) (hr : ∀ j, w a p j ≤ w a p r)
    (ε τ : ℝ) (hε : ε = epsOf a p) (hτ : τ = ε / (w a p r - 1))
    (b : Fin n → ℝ) (hb : b = (momentMatrix a p)⁻¹.mulVec (a r)) :
    (momentMatrix a ((1 - τ) • p + τ • Pi.single r 1))⁻¹ =
      (1 + ε / (((n : ℝ) - 1) * (1 + ε))) • (momentMatrix a p)⁻¹ -
        (ε / (((n : ℝ) - 1) * (1 + ε) ^ 2)) • Matrix.vecMulVec b b := by
  classical
  let A := momentMatrix a p
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hp.2)
  have hinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  have hinv' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdet
  have hsym : Aᵀ = A := by
    ext i j
    simp only [A, momentMatrix, Matrix.transpose_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hisym : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  have hb' : b = A⁻¹ *ᵥ a r := hb
  have hab : A *ᵥ b = a r := by
    rw [hb', Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hav : a r ᵥ* A⁻¹ = b := by
    rw [← hisym, Matrix.vecMul_transpose, ← hb']
  have hsum : ∑ j, p j * w a p j = (n : ℝ) := by
    have ht := congrArg Matrix.trace hinv'
    simp only [A, momentMatrix, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Matrix.mul_vecMulVec,
      Matrix.trace_vecMulVec, Matrix.trace_one, Fintype.card_fin] at ht
    simpa only [w, momentMatrix, dotProduct_comm] using ht
  have hwr : (n : ℝ) ≤ w a p r := by
    calc
      (n : ℝ) = ∑ j, p j * w a p j := hsum.symm
      _ ≤ ∑ j, p j * w a p r := Finset.sum_le_sum
        (fun j _ => mul_le_mul_of_nonneg_left (hr j) (hp.1.1 j))
      _ = w a p r := by rw [← Finset.sum_mul, hp.1.2, one_mul]
  letI : Nonempty ι := ⟨r⟩
  have hmax : (⨆ j, w a p j) = w a p r := by
    apply le_antisymm (ciSup_le hr)
    exact le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) r
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have heps : ε = w a p r / (n : ℝ) - 1 := by rw [hε, epsOf, hmax]
  have hwe : w a p r = (1+ε)*(n : ℝ) := by
    rw [heps]
    field_simp
    ring
  have hepos : 0 < 1+ε := by
    have : 0 < w a p r := by linarith
    nlinarith
  have hn1 : (n : ℝ)-1 ≠ 0 := by linarith
  have hwr1 : w a p r - 1 ≠ 0 := by linarith
  let α : ℝ := 1 + ε / (((n : ℝ)-1)*(1+ε))
  let β : ℝ := ε / (((n : ℝ)-1)*(1+ε)^2)
  have hz : (1+ε)*(n : ℝ)-1 ≠ 0 := by rw [← hwe]; exact hwr1
  have coeff1 : (1-τ)*α = 1 := by
    dsimp [α]
    rw [hτ, hwe]
    field_simp [hz, hn1, ne_of_gt hepos]
    <;> ring
  have coeff2 : τ*α - (1-τ)*β - τ*β*w a p r = 0 := by
    dsimp [α, β]
    rw [hτ, hwe]
    field_simp [hz, hn1, ne_of_gt hepos]
    <;> ring
  have hnew : momentMatrix a ((1-τ) • p + τ • Pi.single r 1) =
      (1-τ) • A + τ • Matrix.vecMulVec (a r) (a r) := by
    ext i j
    simp only [momentMatrix, A, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.add_apply, Pi.add_apply, Pi.smul_apply,
      Matrix.vecMulVec_apply]
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    simp [Pi.single_apply]
  rw [hnew]
  apply Matrix.inv_eq_right_inv
  change ((1-τ) • A + τ • Matrix.vecMulVec (a r) (a r)) *
    (α • A⁻¹ - β • Matrix.vecMulVec b b) = 1
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hinv, Matrix.mul_vecMulVec, hab, Matrix.vecMulVec_mul, hav,
    Matrix.vecMulVec_mul_vecMulVec]
  simp only [Matrix.vecMulVec_smul, smul_smul]
  have hdot : a r ⬝ᵥ b = w a p r := by rw [hb']; rfl
  rw [hdot]
  ext i j
  have hc1 := congrArg (fun x : ℝ => x * (1 : Matrix (Fin n) (Fin n) ℝ) i j) coeff1
  have hc2 := congrArg (fun x : ℝ => x * Matrix.vecMulVec (a r) b i j) coeff2
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at *
  nlinarith



#print axioms solution
