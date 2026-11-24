-- Prove2me | solution 1 for GlobalTheory.TriangularIsometryBoundedPowers.diag_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:54.442611+00:00
-- url     : https://prove2.me/submissions/c777c16d-7c24-4b24-939a-f2eb77c1701f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularIsometryBoundedPowers
open Matrix
namespace GlobalTheory.TriangularIsometryBoundedPowers
theorem _root_.solution {n : ℕ} (d : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ)
    (hd : d.BlockTriangular id) (hμ : ∀ i, μ i ≠ 0)
    (h : dᴴ * diagonal μ * d = diagonal μ) :
    ∃ l : Fin n → ℂ, d = diagonal l ∧ ∀ i, ‖l i‖ = 1 := by
  have hμd : (diagonal μ).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hμ i
  have hdet : (dᴴ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at this
    exact hμd this.symm
  have hu : IsUnit (dᴴ).det := isUnit_iff_ne_zero.mpr hdet
  have hlow : (dᴴ).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have : d j i = 0 := hd (show i < j from hij)
    rw [Matrix.conjTranspose_apply, this, star_zero]
  haveI := Matrix.invertibleOfIsUnitDet _ hu
  have hlow' := Matrix.blockTriangular_inv_of_blockTriangular hlow
  have h2 : diagonal μ * d = (dᴴ)⁻¹ * diagonal μ := by
    conv_rhs => rw [← h]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hdiag : d = diagonal fun i => d i i := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · have h3 := congrFun (congrFun h2 i) j
      have h4 : (dᴴ)⁻¹ i j = 0 := hlow' (show OrderDual.toDual j < OrderDual.toDual i from hij)
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, h4, zero_mul] at h3
      rw [Matrix.diagonal_apply_ne _ hij.ne]
      exact (mul_eq_zero.mp h3).resolve_left (hμ i)
    · subst hij; rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij.ne']
      exact hd hij
  refine ⟨_, hdiag, fun i => ?_⟩
  rw [hdiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal] at h
  have h5 := congrFun (congrFun h i) i
  simp only [Matrix.diagonal_apply_eq, Pi.star_apply] at h5
  have h6 := congrArg norm h5
  rw [norm_mul, norm_mul, norm_star] at h6
  have h7 : ‖μ i‖ ≠ 0 := norm_ne_zero_iff.mpr (hμ i)
  have h8 : ‖d i i‖ * ‖d i i‖ = 1 := by
    apply mul_right_cancel₀ h7
    linarith
  have h9 := norm_nonneg (d i i)
  nlinarith
end GlobalTheory.TriangularIsometryBoundedPowers
