-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.norm_prod_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:56.815028+00:00
-- url     : https://prove2.me/submissions/4ce1ea9a-477c-40fb-acc2-e8d62a1d0e81

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

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
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ) (n : ℕ) (hB : 1 ≤ B)
    (hs : s.card ≤ n) (h : ∀ i ∈ s, ‖f i‖ ≤ B) : ‖∏ i ∈ s, f i‖ ≤ B ^ n := by
  rw [norm_prod]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _) h).trans ?_
  rw [Finset.prod_const]
  exact pow_le_pow_right₀ hB hs
end GlobalTheory.FiniteCoverGrowth
