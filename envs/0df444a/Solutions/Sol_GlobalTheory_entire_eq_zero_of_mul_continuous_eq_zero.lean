-- Prove2me | solution 1 for GlobalTheory.entire_eq_zero_of_mul_continuous_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:19.291691+00:00
-- url     : https://prove2.me/submissions/073e0cda-385f-4f67-b0c4-67db2578033f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open Complex Matrix NumberField Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f t : E → ℂ} (hf : Differentiable ℂ f) (ht : Continuous t) (ht0 : t ≠ 0)
    (h : ∀ z, f z * t z = 0) (z : E) : f z = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, t w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact ht0 (funext hne)
  have hU : ∀ᶠ y in 𝓝 w, f y = 0 := by
    filter_upwards [ht.continuousAt.eventually_ne hw] with y hy
    exact (mul_eq_zero.mp (h y)).resolve_right hy
  have hc : Continuous fun s : ℂ => w + s • (z - w) := by fun_prop
  have hlim : Tendsto (fun s : ℂ => w + s • (z - w)) (𝓝 0) (𝓝 w) := by
    simpa using hc.tendsto 0
  have hd : Differentiable ℂ fun s : ℂ => f (w + s • (z - w)) :=
    hf.comp ((differentiable_const _).add (differentiable_id.smul_const _))
  have h0 : (fun s : ℂ => f (w + s • (z - w))) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hlim.eventually hU] with s hs
    simpa using hs
  have han : AnalyticOnNhd ℂ (fun s : ℂ => f (w + s • (z - w))) Set.univ :=
    fun s _ => hd.analyticAt s
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) h0 (Set.mem_univ 1)
  simpa using this
end _root_.GlobalTheory
end GlobalTheory
