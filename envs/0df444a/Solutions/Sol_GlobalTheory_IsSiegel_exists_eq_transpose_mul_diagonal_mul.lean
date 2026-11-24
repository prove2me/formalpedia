-- Prove2me | solution 1 for GlobalTheory.IsSiegel.exists_eq_transpose_mul_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:41.124173+00:00
-- url     : https://prove2.me/submissions/c782e383-5209-4d7c-8374-67175aaa1e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul

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
open scoped MatrixOrder
namespace GlobalTheory
namespace IsSiegel
theorem _root_.solution {σ : Matrix ι ι ℂ} (h : IsSiegel σ) :
    ∃ P : Matrix ι ι ℝ, P.det ≠ 0 ∧ ∃ t : ι → ℂ, (∀ i, 0 < (t i).im) ∧
      σ = (P.map ofReal)ᵀ * diagonal t * P.map ofReal := by
  obtain ⟨B, hB, hY⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    h.posDef.isStrictlyPositive
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hY
  have hB' : IsUnit B.det := (isUnit_iff_isUnit_det B).1 hB
  have hX : (σ.map Complex.re).IsHermitian := by
    ext i j
    simp [conjTranspose_apply, h.isSymm.apply]
  have hX' : (B⁻¹ᴴ * σ.map Complex.re * B⁻¹).IsHermitian := isHermitian_conjTranspose_mul_mul _ hX
  obtain ⟨U, l, hUU, hs⟩ : ∃ (U : Matrix ι ι ℝ) (l : ι → ℝ), U * Uᵀ = 1 ∧
      B⁻¹ᵀ * σ.map Complex.re * B⁻¹ = U * diagonal l * Uᵀ :=
    ⟨hX'.eigenvectorUnitary.1, hX'.eigenvalues, Unitary.coe_mul_star_self hX'.eigenvectorUnitary,
      hX'.spectral_theorem⟩
  refine ⟨Uᵀ * B, ?_, fun i => l i + I, fun i => by simp, ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (isUnit_det_of_right_inverse hUU).ne_zero hB'.ne_zero
  have e1 : σ.map Complex.re = (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) := by
    have : (Uᵀ * B)ᵀ * diagonal l * (Uᵀ * B) =
        Bᵀ * (U * diagonal l * Uᵀ) * B := by
      simp [Matrix.mul_assoc]
    rw [this, ← hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul,
      nonsing_inv_mul _ hB', transpose_one, Matrix.one_mul, Matrix.mul_assoc,
      nonsing_inv_mul _ hB', Matrix.mul_one]
  have e2 : σ.map Complex.im = (Uᵀ * B)ᵀ * (Uᵀ * B) := by
    rw [hY, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU,
      Matrix.one_mul]
  generalize Uᵀ * B = P at e1 e2
  ext i j
  have e1' := congrFun (congrFun e1 i) j
  have e2' := congrFun (congrFun e2 i) j
  simp only [mul_apply, map_apply, transpose_apply, diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at e1' e2' ⊢
  apply Complex.ext <;> simp [e1', e2']
end IsSiegel
end GlobalTheory
