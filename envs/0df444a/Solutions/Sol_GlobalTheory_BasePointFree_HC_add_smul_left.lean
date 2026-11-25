-- Prove2me | solution 1 for GlobalTheory.BasePointFree.HC_add_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:45.100836+00:00
-- url     : https://prove2.me/submissions/84189bd4-075e-4111-a355-e1fbf22cbc48

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.BasePointFree
namespace GlobalTheory.BasePointFree
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (w c γ : Fin n → EuclideanSpace ℂ ι)
    (a : ℂ) : HC (w + a • c) γ = HC w γ + a * HC c γ := by
  simp only [HC, Hf, Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end GlobalTheory.BasePointFree
