-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_integral_cexp_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:18.932389+00:00
-- url     : https://prove2.me/submissions/ac7a961c-539c-44b3-ba4f-a2965a459d67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_exists_eq_transpose_mul_diagonal_mul
import Theorems.Thm_GlobalTheory_ofReal_mulVec_eq
import Theorems.Thm_GlobalTheory_isUnit_det_map_ofReal
import Theorems.Thm_GlobalTheory_inv_diagonal_of_ne_zero
import Theorems.Thm_GlobalTheory_integral_comp_mulVec_of_det_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ s : ℂ, s ^ 2 * (-I • σ).det = 1 ∧ ∀ w : ι → ℂ,
      ∫ x : ι → ℝ, cexp (2 * π * I * (((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))) / 2 +
        (fun i => (x i : ℂ)) ⬝ᵥ w)) = s * cexp (-(π * I) * (w ⬝ᵥ (σ⁻¹ *ᵥ w))) := by
  obtain ⟨P, hP, t, ht, rfl⟩ := h.exists_eq_transpose_mul_diagonal_mul
  have ht0 (i : ι) : t i ≠ 0 := fun h0 => by simpa [h0] using ht i
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu := isUnit_det_map_ofReal hP
  refine ⟨(|P.det⁻¹| : ℝ) * ∏ i, (π / (-(π * I * t i))) ^ (1 / 2 : ℂ), ?_, fun w => ?_⟩
  · have e : (P.map ofReal).det = (P.det : ℂ) := (ofRealHom.map_det P).symm
    have e2 (i : ι) : ((π / (-(π * I * t i))) ^ (1 / 2 : ℂ)) ^ 2 * (-I * t i) = 1 := by
      rw [one_div, cpow_ofNat_inv_pow]
      field_simp [ht0 i]
    have e3 : (P.det : ℂ) ≠ 0 := by exact_mod_cast hP
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← diagonal_smul, det_mul, det_mul, det_transpose,
      det_diagonal, e, mul_pow, ← ofReal_pow, sq_abs, ← Finset.prod_pow]
    have e4 := Finset.prod_congr (s₁ := Finset.univ) rfl fun i _ => e2 i
    rw [Finset.prod_mul_distrib, Finset.prod_const_one] at e4
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    have e5 : (P.det : ℂ)⁻¹ ^ 2 * P.det * P.det = 1 := by field_simp
    linear_combination ((P.det : ℂ)⁻¹ ^ 2 * P.det * P.det) * e4 + e5
  set v := ((P.map ofReal)ᵀ)⁻¹ *ᵥ w with hv
  have hw : w = (P.map ofReal)ᵀ *ᵥ v := by
    rw [hv, mulVec_mulVec, mul_nonsing_inv _ (isUnit_det_transpose _ hu), one_mulVec]
  have hb (i : ι) : 0 < (-(π * I * t i)).re := by simpa using mul_pos Real.pi_pos (ht i)
  have key := GaussianFourier.integral_cexp_neg_sum_mul_add hb fun i => 2 * π * I * v i
  have hc := integral_comp_mulVec_of_det_ne_zero hP (f := fun y : ι → ℝ =>
    cexp (-∑ i, -(π * I * t i) * (y i : ℂ) ^ 2 + ∑ i, 2 * π * I * v i * y i)) (by fun_prop)
  rw [key, Finset.prod_mul_distrib, ← Complex.exp_sum, ← mul_assoc] at hc
  convert hc using 3 with x
  · congr 1
    have e := ofReal_mulVec_eq P x
    rw [hw, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec _ _ v,
      vecMul_transpose, ← e]
    simp only [dotProduct, mulVec_diagonal, Finset.sum_div, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_diagonal_of_ne_zero ht0, ← mulVec_mulVec,
      ← mulVec_mulVec, ← hv, dotProduct_mulVec, ← mulVec_transpose, transpose_nonsing_inv, ← hv]
    simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp [ht0 i]
    ring
end IsSiegel
end GlobalTheory
