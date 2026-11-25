-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.thetaSummable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:09:04.197365+00:00
-- url     : https://prove2.me/submissions/7e14d1bf-f7c4-4426-a672-ccf6c9fcea51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution : ReciprocityTheory.PTheta.ThetaSummableStatement := by
  intro ι _ a b z τ hτ
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le hτ
  have hY' (x : ι → ℝ) : c / 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x) := by
    have := hY x
    rw [add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_comm x (x ᵥ* _),
      ← dotProduct_mulVec] at this
    linarith
  exact (summable_riemannThetaBound a (half_pos hc) ‖z‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_riemannThetaTerm_le a b hY' (abs_im_apply_le_norm z))
end GlobalTheory.RiemannThetaModel
