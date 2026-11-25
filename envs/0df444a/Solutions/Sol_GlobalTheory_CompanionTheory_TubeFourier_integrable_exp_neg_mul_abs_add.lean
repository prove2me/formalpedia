-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_mul_abs_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:24:47.872216+00:00
-- url     : https://prove2.me/submissions/d177c26a-ebcc-4573-a072-253b9288567e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussTubeOfTubeGood
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FInt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InverseTransformContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_TubeFourier_integrable_exp_neg_mul_abs_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TubeFourier
namespace GlobalTheory.CompanionTheory.TubeFourier
theorem _root_.solution {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun t : ℝ × ℝ => M * Real.exp (-c * (|t.1| + |t.2|))) := by
  have h := (integrable_exp_neg_mul_abs_alt hc).mul_prod (integrable_exp_neg_mul_abs_alt hc)
  refine (h.const_mul M).congr (Eventually.of_forall fun t => ?_)
  simp only [mul_add, Real.exp_add]
end GlobalTheory.CompanionTheory.TubeFourier
