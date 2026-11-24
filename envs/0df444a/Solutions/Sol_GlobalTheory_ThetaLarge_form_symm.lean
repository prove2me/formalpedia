-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.form_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:18.964494+00:00
-- url     : https://prove2.me/submissions/c90ecfe4-1352-4118-88e5-4a9f7bc26f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {g : ℕ}
namespace GlobalTheory.ThetaLarge
theorem _root_.solution {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ M.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ M.mulVec (star y)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hM.apply j i
  simp only [RCLike.star_def] at this ⊢
  rw [← this, Complex.conj_conj]
  ring
end GlobalTheory.ThetaLarge
