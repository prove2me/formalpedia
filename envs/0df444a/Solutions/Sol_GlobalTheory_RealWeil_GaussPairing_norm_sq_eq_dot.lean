-- Prove2me | solution 1 for GlobalTheory.RealWeil.GaussPairing.norm_sq_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:48.517963+00:00
-- url     : https://prove2.me/submissions/bcf705ca-fc66-46f4-ac0a-7982ab37ea72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HalfAddSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingOfNormSqEqSumComplexCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree

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
theorem _root_.solution (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (v : V) :
    (‖v‖ : ℂ) ^ 2 = star (e v) ⬝ᵥ e v := by
  have h : ((‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖e v i‖ ^ 2 : ℝ) : ℂ) := by rw [he v]
  push_cast at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Complex.conj_mul' _).symm
end GlobalTheory.RealWeil.GaussPairing
