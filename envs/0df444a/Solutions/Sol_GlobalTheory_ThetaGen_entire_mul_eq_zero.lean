-- Prove2me | solution 1 for GlobalTheory.ThetaGen.entire_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:03.170801+00:00
-- url     : https://prove2.me/submissions/d9d9afc4-b115-4216-94a6-8955a4f4cfbc

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

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
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaGen
theorem _root_.solution {f h : E → ℂ} (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hfh : f * h = 0) : f = 0 ∨ h = 0 := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hne.1
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne.2
  have hl : Differentiable ℂ (fun t : ℂ => x + t • (y - x)) := by fun_prop
  have h1 : AnalyticOnNhd ℂ (fun t : ℂ => f (x + t • (y - x))) Set.univ :=
    fun t _ => (hf.comp hl).analyticAt t
  have h2 : AnalyticOnNhd ℂ (fun t : ℂ => h (x + t • (y - x))) Set.univ :=
    fun t _ => (hh.comp hl).analyticAt t
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero h1 h2
    (fun t _ => congrFun hfh _) isPreconnected_univ with h3 | h3
  · exact hx (by simpa using h3 0 trivial)
  · exact hy (by simpa using h3 1 trivial)
end GlobalTheory.ThetaGen
