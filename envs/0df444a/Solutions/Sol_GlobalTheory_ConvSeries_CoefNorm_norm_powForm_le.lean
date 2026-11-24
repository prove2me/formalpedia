-- Prove2me | solution 1 for GlobalTheory.ConvSeries.CoefNorm.norm_powForm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:08.3756+00:00
-- url     : https://prove2.me/submissions/16cbe4a1-2c62-43e2-b3b3-2db98f426173

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr
import Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_innerC_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ConvSeries
open GlobalTheory.ConvSeries.CoefNorm
namespace GlobalTheory.ConvSeries.CoefNorm
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ) (a : E) :
    ‖powForm k a‖ ≤ ‖a‖ ^ k := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  simp only [powForm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  rw [norm_prod]
  calc ∏ i, ‖innerC a (m i)‖ ≤ ∏ i, (‖a‖ * ‖m i‖) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_innerC_apply_le a (m i)
    _ = ‖a‖ ^ k * ∏ i, ‖m i‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end GlobalTheory.ConvSeries.CoefNorm
