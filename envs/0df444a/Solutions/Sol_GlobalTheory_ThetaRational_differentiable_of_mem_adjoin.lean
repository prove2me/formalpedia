-- Prove2me | solution 1 for GlobalTheory.ThetaRational.differentiable_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:01.502307+00:00
-- url     : https://prove2.me/submissions/9098c15f-ad59-4d27-9ccf-cd7095b86068

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
omit [FiniteDimensional ℂ E] [Fintype ι]
namespace GlobalTheory.ThetaRational
theorem _root_.solution {u : ι → E → ℂ} (hu : ∀ c, Differentiable ℂ (u c))
    {b : E → ℂ} (hb : b ∈ Algebra.adjoin ℂ (Set.range u)) : Differentiable ℂ b := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨c, rfl⟩ := hx; exact hu c
  | algebraMap r => exact differentiable_const r
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy
end GlobalTheory.ThetaRational
