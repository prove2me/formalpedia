-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.Normal.isQuadOf_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:40.188313+00:00
-- url     : https://prove2.me/submissions/8ffff91c-a647-4e04-9789-69f62446cc17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal
import Theorems.Thm_GlobalTheory_Mem_Lift_Normal_im_add_I_re
import Theorems.Thm_GlobalTheory_Mem_Lift_Normal_im_sub_I_re
import Theorems.Thm_GlobalTheory_Mem_Lift_Normal_sum_lin
import Theorems.Thm_GlobalTheory_Mem_Lift_Normal_sum_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Mem.Lift.Normal
theorem _root_.solution {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0) :
    IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) (nC X) nP (nQ H) := by
  intro l v
  beta_reduce
  have hinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hd)

  have hkj : ∀ k j, (∑ b1 : Bool, ∑ b2 : Bool, nC X (k, j, b1, b2) *
      (((star v ⬝ᵥ H *ᵥ nQ H (k, j, b1, b2)).im : ℂ) * l (nP (k, j, b1, b2)) +
        ((star v ⬝ᵥ H *ᵥ nP (k, j, b1, b2)).im : ℂ) * l (nQ H (k, j, b1, b2)))) =
      X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
        (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    intro k j
    have ha : ((star v ⬝ᵥ H *ᵥ (H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) +
        I * ((star v ⬝ᵥ H *ᵥ (I • H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) = I * v j := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_add_I_re, Matrix.mulVec_mulVec, hinv,
        Matrix.one_mulVec, dotProduct_single, mul_one, Pi.star_apply, starRingEnd_apply, star_star]
    have hp : ((star v ⬝ᵥ H *ᵥ Pi.single k 1).im : ℂ) -
        I * ((star v ⬝ᵥ H *ᵥ (I • Pi.single k 1)).im : ℂ) = -I * (star v ⬝ᵥ H *ᵥ Pi.single k 1) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_sub_I_re]
    simp only [Fintype.sum_bool, nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    linear_combination (X k j * (-(1 / (4 * π))) * (l (Pi.single k 1) - I * l (I • Pi.single k 1))) * ha +
      (X k j * (-(1 / (4 * π))) * (l (H⁻¹ *ᵥ Pi.single j 1) + I * l (I • H⁻¹ *ᵥ Pi.single j 1))) * hp
  have hsum : ∀ F : ι × ι × Bool × Bool → ℂ, ∑ i, F i = ∑ k, ∑ j, ∑ b1, ∑ b2, F (k, j, b1, b2) :=
    fun F => by simp only [Fintype.sum_prod_type]
  rw [hsum, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hkj k j]
  have hsplit : (∑ k, ∑ j, X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
      (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1)))) =
      (-(1 / (4 * π)) * I : ℂ) * ((∑ k, ∑ j, X k j * (v j * linPart l (Pi.single k 1))) -
        ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hLA : linPart l (X *ᵥ v) + antiPart l (X *ᵥ v) = 2 * l (X *ᵥ v) := by
    simp only [linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfin : ∀ z : ℂ, 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = z := by
    intro z
    rw [show 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = -(I * I) * ((π : ℂ) * (π : ℂ)⁻¹) * z by ring,
      I_mul_I, mul_inv_cancel₀ hπ]
    ring
  rw [hsplit, sum_lin, sum_anti hH hd hX, sub_neg_eq_add, hLA]
  exact hfin _
end GlobalTheory.Mem.Lift.Normal
