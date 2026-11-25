-- Prove2me | solution 1 for GlobalTheory.HolTheta.pull_eq_imInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:55:15.138807+00:00
-- url     : https://prove2.me/submissions/ef7badf3-857c-477f-b109-5d097a01b711

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaHolomorphic
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTheta
open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel
variable {g : ℕ}
namespace GlobalTheory.HolTheta
theorem _root_.solution (M τ : Matrix (Fin g) (Fin g) ℂ) (hM : ∀ j k, (M j k).im = 0)
    (hN : ∀ j k, ((M * τ.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    M = imInv τ := by
  have hRY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext j k
    have := hN j k
    simp only [Matrix.mul_apply, Complex.im_sum, map_apply, Complex.mul_im, hM, Complex.conj_im, zero_mul, add_zero,
      mul_neg, Finset.sum_neg_distrib, neg_inj] at this
    rw [← this]
    simp [Matrix.mul_apply]
  rw [imInv, inv_eq_left_inv hRY]
  ext j k
  apply Complex.ext
  · simp
  · simp [hM]
end GlobalTheory.HolTheta
