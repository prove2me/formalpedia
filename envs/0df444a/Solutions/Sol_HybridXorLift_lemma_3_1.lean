-- Prove2me | solution 1 for HybridXorLift.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T15:04:19.956085+00:00
-- url     : https://prove2.me/submissions/3d0afd52-8479-4bfb-aca9-28d342c1f043

import Mathlib
import Definitions.Def_HybridXorLift_kernelL
import Definitions.Def_HybridXorLift_signZ
namespace HybridXorLift

theorem kernel_eigenvectors (q : ℕ) :
    (kernelL q).mulVec (fun _ => 1) = Real.exp (-(1 / (2 * (q : ℝ)))) • (fun _ => 1) ∧
    (kernelL q).mulVec (fun b => if b then -1 else 1) =
      Real.exp (1 / (2 * (q : ℝ))) • (fun b => if b then -1 else 1) := by
  constructor <;> funext b <;> cases b <;>
    simp [kernelL, Matrix.mulVec, dotProduct]
  all_goals
    have h1 := Real.cosh_add_sinh (1 / (2 * (q : ℝ)))
    have h2 := Real.cosh_sub_sinh (1 / (2 * (q : ℝ)))
    simp only [one_div, mul_inv_rev] at h1 h2
    linarith

theorem kernel_sign_psd (q : ℕ) (hq : 1 ≤ q) :
    (signZ + kernelL q).PosSemidef ∧ (kernelL q - signZ).PosSemidef := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let t : ℝ := 1 / (2 * q)
  have ht : 0 < t := by dsimp [t]; positivity
  have hc : 1 < Real.cosh t := Real.one_lt_cosh.mpr (ne_of_gt ht)
  have hs := Real.cosh_sq_sub_sinh_sq t
  have hinv : (Real.cosh t + 1) * (Real.cosh t - 1) = (Real.sinh t)^2 := by nlinarith
  constructor <;> apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr <;> constructor
  all_goals try
    (ext i j; cases i <;> cases j <;>
      simp [Matrix.IsHermitian, Matrix.conjTranspose, signZ, kernelL, t])
  all_goals
    intro x
    have hpos : 0 < Real.cosh t + 1 := by linarith
    have hmul := congrArg (fun z : ℝ => z * (x true)^2) hinv
    have hsq := sq_nonneg ((Real.cosh t + 1) * x false - Real.sinh t * x true)
    have hmul2 := congrArg (fun z : ℝ => z * (x false)^2) hinv
    have hsq2 := sq_nonneg ((Real.cosh t + 1) * x true - Real.sinh t * x false)
    simp [dotProduct, Matrix.mulVec, signZ, kernelL] 
    dsimp [t] at *
    simp only [one_div, mul_inv_rev] at *
    apply (mul_nonneg_iff_of_pos_left hpos).mp
    nlinarith [hmul, hsq, hmul2, hsq2]

theorem kernel_conjugation_psd (q : ℕ) (hq : 1 ≤ q) :
    (Real.exp (2 * (1 / (2 * (q : ℝ)))) • kernelL q - signZ * kernelL q * signZ).PosSemidef := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  let t : ℝ := 1 / (2 * q)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hc : 0 < Real.cosh t := Real.cosh_pos _
  have hp := Real.cosh_add_sinh t
  have hm := Real.cosh_sub_sinh t
  have hprod : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hfactor : (Real.exp t ^ 2 - 1) * Real.cosh t =
      (Real.exp t ^ 2 + 1) * Real.sinh t := by
    have hA : Real.exp t * (Real.cosh t - Real.sinh t) = 1 := by rw [hm]; exact hprod
    have hB := congrArg (fun z : ℝ => z * Real.exp t) hp
    have hC := congrArg (fun z : ℝ => z * (Real.cosh t + Real.sinh t)) hA
    nlinarith [hB, hC]
  have hcoef : 0 ≤ (Real.exp t ^ 2 - 1) * Real.cosh t := by
    apply mul_nonneg _ hc.le
    nlinarith [sq_nonneg (Real.exp t - 1)]
  have hdouble : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [show 2 * t = t + t by ring, Real.exp_add]
    ring
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    cases i <;> cases j <;> simp [Matrix.conjTranspose, signZ, kernelL, Matrix.mul_apply]
  · intro x
    have hsq := mul_nonneg hcoef (sq_nonneg (x false - x true))
    have hcross := congrArg (fun z : ℝ => z * x false * x true) hfactor
    simp [dotProduct, Matrix.mulVec, Matrix.mul_apply, signZ, kernelL]
    dsimp [t] at *
    simp only [one_div, mul_inv_rev] at *
    rw [hdouble]
    nlinarith

theorem kernel_sign_involution (q : ℕ) :
    kernelL q * signZ * kernelL q = signZ := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.mul_apply, signZ, kernelL]
  all_goals
    have h := Real.cosh_sq_sub_sinh_sq (1 / (2 * (q : ℝ)))
    simp only [one_div, mul_inv_rev] at h
    nlinarith

theorem square_root_sign (q : ℕ) (hq : 1 ≤ q) (S : Matrix Bool Bool ℝ)
    (hS : S.PosSemidef) (hSq : S * S = kernelL q) :
    S⁻¹ * signZ * S⁻¹ = signZ := by
  have hsym : S false true = S true false := by
    have h := hS.1
    have ht := congrFun (congrFun h false) true
    simpa [Matrix.conjTranspose] using ht.symm
  have ha : 0 ≤ S false false := hS.diag_nonneg
  have hc : 0 ≤ S true true := hS.diag_nonneg
  have h00 := congrFun (congrFun hSq false) false
  have h11 := congrFun (congrFun hSq true) true
  have h01 := congrFun (congrFun hSq false) true
  simp [Matrix.mul_apply, kernelL, ← hsym] at h00 h11 h01
  have heq : S false false = S true true := by nlinarith
  have hv := hS.dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  have hw := hS.dotProduct_mulVec_nonneg (fun b => if b then (-1 : ℝ) else 1)
  simp [dotProduct, Matrix.mulVec, ← hsym, ← heq] at hv hw
  have hab : 0 ≤ (S false false)^2 - (S false true)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ S false false + S false true by linarith)
      (show 0 ≤ S false false - S false true by linarith)]
  have hh := Real.cosh_sq_sub_sinh_sq (1 / (2 * (q : ℝ)))
  simp only [one_div, mul_inv_rev] at hh
  have hSin : Real.sinh ((q : ℝ)⁻¹ * 2⁻¹) =
      -(S false true * S true true + S false false * S false true) := by linarith
  rw [← h00, hSin, ← heq] at hh
  have hsquares : ((S false false)^2 - (S false true)^2)^2 = 1 := by nlinarith [hh]
  have hdet : (S false false)^2 - (S false true)^2 = 1 := by nlinarith

  have hszs : S * signZ * S = signZ := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.mul_apply, signZ, ← hsym, ← heq] <;> nlinarith
  have hz : signZ * signZ = (1 : Matrix Bool Bool ℝ) := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.mul_apply, signZ]
  have hright : S * (signZ * S * signZ) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hszs, hz]
  have hunit : IsUnit S := IsUnit.of_mul_eq_one (signZ * S * signZ) hright
  have hdetunit : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hunit
  have hleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdetunit
  have hright' : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdetunit
  calc
    _ = S⁻¹ * (S * signZ * S) * S⁻¹ := by rw [hszs]
    _ = signZ := by
      simp only [Matrix.mul_assoc, hright', Matrix.mul_one]
      rw [← Matrix.mul_assoc, hleft, Matrix.one_mul]

end HybridXorLift
open HybridXorLift

theorem solution (q : ℕ) (hq : 1 ≤ q) :
    (kernelL q).mulVec (fun _ => 1) = Real.exp (-(1 / (2 * (q : ℝ)))) • (fun _ => 1) ∧
    (kernelL q).mulVec (fun b => if b then -1 else 1) =
      Real.exp (1 / (2 * (q : ℝ))) • (fun b => if b then -1 else 1) ∧
    (Real.exp (2 * (1 / (2 * (q : ℝ)))) • kernelL q - signZ * kernelL q * signZ).PosSemidef ∧
    (∀ S : Matrix Bool Bool ℝ, S.PosSemidef → S * S = kernelL q → S⁻¹ * signZ * S⁻¹ = signZ) ∧
    (signZ + kernelL q).PosSemidef ∧ (kernelL q - signZ).PosSemidef := by
  obtain ⟨h1, h2⟩ := kernel_eigenvectors q
  obtain ⟨h3, h4⟩ := kernel_sign_psd q hq
  exact ⟨h1, h2, kernel_conjugation_psd q hq, square_root_sign q hq, h3, h4⟩

#print axioms solution
