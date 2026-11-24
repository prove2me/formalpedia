-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.tendsto_inv_ofReal_add_I_atTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:23:19.238332+00:00
-- url     : https://prove2.me/submissions/a48caab2-496e-4e01-bfd1-60b1b170e43a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)⁻¹) Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun t : ℝ => ((t : ℂ) + I)) Filter.atTop (Bornology.cobounded ℂ) := by
    rw [← tendsto_norm_atTop_iff_cobounded]
    refine Filter.tendsto_atTop_mono (fun t => ?_) Filter.tendsto_abs_atTop_atTop
    have := Complex.abs_re_le_norm ((t : ℂ) + I)
    simpa using this
  exact Filter.Tendsto.comp Filter.tendsto_inv₀_cobounded hb
end GlobalTheory.HeckeTwo
