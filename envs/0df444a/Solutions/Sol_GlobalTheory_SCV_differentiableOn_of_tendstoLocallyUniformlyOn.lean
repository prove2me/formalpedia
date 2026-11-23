-- Prove2me | solution 1 for GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.870744+00:00
-- url     : https://prove2.me/submissions/abca2fac-f6af-4eee-9b4a-4b8bc2c0b421

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_tendstoUniformlyOn_fderiv_ball
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Metric Set Filter
open scoped Topology ContDiff Nat
namespace GlobalTheory.SCV
section Estimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
end Estimates
section FiniteDimensional
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
section Limits
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
private theorem exists_ball_limit [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U)
    {c : E} (hc : c ∈ U) : ∃ r > 0, DifferentiableOn ℂ f (ball c r) ∧
      TendstoUniformlyOn (fun n => fderiv ℂ (F n)) (fderiv ℂ f) l (ball c r) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  have hsub : closedBall c (2 * (R / 4)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  have h1 := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hlim _ hsub
    (isCompact_closedBall _ _)
  exact ⟨R / 4, by positivity, tendstoUniformlyOn_fderiv_ball (h1.mono ball_subset_closedBall)
    (hF.mono fun n hn => hn.mono (ball_subset_closedBall.trans hsub))⟩
end Limits
end FiniteDimensional
end GlobalTheory.SCV
end

set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {ι : Type*} {l : Filter ι} {F : ι → E → V} {f : E → V} {U : Set E}
namespace GlobalTheory.SCV
theorem _root_.solution [l.NeBot] (hU : IsOpen U)
    (hlim : TendstoLocallyUniformlyOn F f l U) (hF : ∀ᶠ n in l, DifferentiableOn ℂ (F n) U) :
    DifferentiableOn ℂ f U := by
  intro c hc
  obtain ⟨r, hr, h, -⟩ := exists_ball_limit hU hlim hF hc
  exact (h.differentiableAt (ball_mem_nhds c hr)).differentiableWithinAt
end GlobalTheory.SCV
