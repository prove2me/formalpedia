-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.inner_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:52:46.217365+00:00
-- url     : https://prove2.me/submissions/d0dc1d1f-0574-4899-b56a-6d6238b2b79a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_norm_sq_eq_dot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.GaussPairing
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]
namespace GlobalTheory.RealWeil.GaussPairing
theorem _root_.solution (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (x y : V) :
    ((⟪x, y⟫ : ℝ) : ℂ) = (1 / 2 : ℂ) * (star (e x) ⬝ᵥ e y + star (e y) ⬝ᵥ e x) := by
  have h : ((‖x + y‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_add_sq_real]
  push_cast at h
  rw [norm_sq_eq_dot e he (x + y), norm_sq_eq_dot e he x, norm_sq_eq_dot e he y, map_add, star_add,
    add_dotProduct, dotProduct_add, dotProduct_add] at h
  linear_combination (-1 / 2 : ℂ) * h
end GlobalTheory.RealWeil.GaussPairing
