-- Prove2me | solution 1 for GlobalTheory.IsSiegel.riemannTheta_char_eq_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:07:15.325292+00:00
-- url     : https://prove2.me/submissions/be8b6d58-533d-45d9-a5c1-f8cb7a098405

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_eq_neg_inv

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
theorem _root_.solution {τ : Matrix ι ι ℂ} (h : IsSiegel τ) (a b : ι → ℝ)
    (z : ι → ℂ) :
    riemannTheta b (-a) τ z = siegelGaussIntegral τ * cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) -
      2 * π * I * ((fun i => (a i : ℂ)) ⬝ᵥ fun i => (b i : ℂ))) *
      riemannTheta a b (-τ⁻¹) (τ⁻¹ *ᵥ z) := by
  have hsi : τ⁻¹.IsSymm := by rw [Matrix.IsSymm, transpose_nonsing_inv, h.isSymm.eq]
  have e1 := riemannTheta_add_ofReal b 0 (-a) τ z
  have e2 : (z + fun i => ((-a) i : ℂ)) = z - fun i => (a i : ℂ) := by
    ext i
    simp [sub_eq_add_neg]
  have e3 : τ⁻¹ *ᵥ (z - fun i => (a i : ℂ)) = τ⁻¹ *ᵥ z + -τ⁻¹ *ᵥ fun i => (a i : ℂ) := by
    rw [mulVec_sub, neg_mulVec, sub_eq_add_neg]
  have e4 : (fun i => (τ⁻¹ *ᵥ z) i + (b i : ℂ)) = τ⁻¹ *ᵥ z + fun i => (b i : ℂ) := rfl
  rw [zero_add, e2] at e1
  rw [← e1, h.riemannTheta_eq_neg_inv, e3, riemannTheta_add_mulVec_ofReal hsi.neg, zero_add,
    ← mul_assoc, mul_assoc (siegelGaussIntegral τ), ← Complex.exp_add, e4]
  congr 3
  simp only [dotProduct_add, sub_dotProduct, neg_mulVec, dotProduct_neg,
    dotProduct_mulVec_comm_of_isSymm hsi z fun i => (a i : ℂ)]
  ring
end IsSiegel
end GlobalTheory
