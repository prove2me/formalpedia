-- Prove2me | solution 1 for GlobalTheory.WeilM.isLocallyConstant_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:16:42.302608+00:00
-- url     : https://prove2.me/submissions/43998d6a-f2be-42a6-b766-71af692c27c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
namespace GlobalTheory.WeilM
theorem _root_.solution {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (om : G →* Module.End ℂ V) {v : V} (h : ∀ᶠ g in 𝓝 (1 : G), om g v = v) :
    IsLocallyConstant fun g => om g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g₀ => ?_
  have : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := Continuous.tendsto' (by fun_prop) _ _ (inv_mul_cancel _)
  filter_upwards [this.eventually h] with g hg
  conv_rhs => rw [← hg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
end GlobalTheory.WeilM
