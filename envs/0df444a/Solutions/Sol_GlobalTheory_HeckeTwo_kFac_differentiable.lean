-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.kFac_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:28:57.260587+00:00
-- url     : https://prove2.me/submissions/e8e4a7e3-bbec-447c-aefb-58d79deb6202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwo
theorem _root_.solution : Differentiable ℂ (kFac F) := by
  intro σ
  unfold kFac
  rw [show (fun σ : ℂ => ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))) =
      fun σ => ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ)) ^ Fintype.card (Emb F) from
    funext fun σ => Finset.prod_const _]
  refine DifferentiableAt.pow (DifferentiableAt.const_mul ?_ _) _
  refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
  exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'
end GlobalTheory.HeckeTwo
