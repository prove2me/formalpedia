-- Prove2me | solution 1 for GlobalTheory.RealWeil.omJ_skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:50.91991+00:00
-- url     : https://prove2.me/submissions/8270940a-638f-492f-8832-228415435489

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
variable {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}
variable {J : V ≃ₗᵢ[ℝ] V}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.RealWeil
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (x y : V) : omJ J y x = -omJ J x y := by
  unfold omJ
  rw [← J.inner_map_map, hJ, inner_neg_right, real_inner_comm]
end GlobalTheory.RealWeil
