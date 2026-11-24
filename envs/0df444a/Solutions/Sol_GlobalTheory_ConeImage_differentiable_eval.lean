-- Prove2me | solution 1 for GlobalTheory.ConeImage.differentiable_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:41.021192+00:00
-- url     : https://prove2.me/submissions/0d378c30-4db6-438b-984a-fa7e0b0a7ffd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {f : W → ι → ℂ} (hf : ∀ c, Differentiable ℂ fun w => f w c) (F : MvPolynomial ι ℂ) :
    Differentiable ℂ fun w => MvPolynomial.eval (f w) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hf i)
end GlobalTheory.ConeImage
