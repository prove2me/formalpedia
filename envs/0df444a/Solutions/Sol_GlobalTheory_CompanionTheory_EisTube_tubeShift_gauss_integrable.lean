-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:16.881803+00:00
-- url     : https://prove2.me/submissions/913ed4e3-ccd0-4d94-bc78-27ac97ac8840

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution (ι : Type) [Fintype ι] :
    Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 4)) := by
  have h : Integrable (fun y : ι → ℝ => ∏ i, Real.exp (-(1 / 4 : ℝ) * y i ^ 2)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq (by norm_num))
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only []
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]
  ring
end GlobalTheory.CompanionTheory.EisTube
