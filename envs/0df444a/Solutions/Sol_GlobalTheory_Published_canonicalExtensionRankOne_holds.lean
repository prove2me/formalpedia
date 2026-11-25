-- Prove2me | solution 1 for GlobalTheory.Published.canonicalExtensionRankOne_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:10:04.288963+00:00
-- url     : https://prove2.me/submissions/fc01b97d-8e1f-47c2-9975-1d3f0bfb4b2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ExistsHorizontalGeneratorOfCharts_f0ad16e2bc421ec8
import Theorems.Thm_GlobalTheory_Published_LogLine_offDivisor_mono
import Theorems.Thm_GlobalTheory_Published_LogLine_isOpen_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_subset_closure_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_eqOn_of_eqOn_offDivisor
import Theorems.Thm_GlobalTheory_Published_LogLine_exists_ball_div
import Theorems.Thm_GlobalTheory_Published_LogLine_exists_local_extension
import Theorems.Thm_GlobalTheory_Published_LogLine_continuousOn_logPartial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open GlobalTheory GlobalTheory.Published
open LogLine
namespace GlobalTheory.Published
theorem _root_.solution : CanonicalExtensionRankOne := by
  intro n U S a f hU ha h0 hf hne
  set V := offDivisor U S with hV
  have hVo : IsOpen V := isOpen_offDivisor hU S
  have hloc : ∀ c ∈ U, ∃ G : (Fin n → ℂ) → ℂ, DifferentiableAt ℂ G c ∧ G c ≠ 0 ∧
      extendFrom V f =ᶠ[𝓝 c] G ∧ (c ∈ V → G c = f c) := by
    intro c hc
    obtain ⟨r, hr, hsub, b, hb, hab⟩ := exists_ball_div hU S ha h0 hc
    have hm := offDivisor_mono hsub S
    obtain ⟨G, hG, hGf, hG0⟩ := exists_local_extension hr S hb (hf.1.mono hm)
      (fun z hz => hne z (hm hz)) fun z hz i => by
        have h1 := hf.2 z (hm hz) i
        have h2 : (if i ∈ S then z i else 1) ≠ 0 := by
          split_ifs with hi
          · exact hz.2 i hi
          · exact one_ne_zero
        rw [logPartial, hab i z hz.1] at h1
        apply mul_left_cancel₀ h2
        linear_combination h1
    refine ⟨G, hG.differentiableAt (ball_mem_nhds c hr), hG0 c (mem_ball_self hr), ?_,
      fun hcV => hGf ⟨mem_ball_self hr, hcV.2⟩⟩
    filter_upwards [ball_mem_nhds c hr] with z hz
    refine extendFrom_eq (subset_closure_offDivisor hU S (hsub hz)) ?_
    have hn := isOpen_ball.mem_nhds hz
    refine ((hG.differentiableAt hn).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hn, self_mem_nhdsWithin] with w hw hwV
    exact hGf ⟨hw, hwV.2⟩
  have hFd : DifferentiableOn ℂ (extendFrom V f) U := fun c hc => by
    obtain ⟨G, hG, -, he, -⟩ := hloc c hc
    exact (hG.congr_of_eventuallyEq he).differentiableWithinAt
  have hFf : EqOn (extendFrom V f) f V := fun c hc => by
    obtain ⟨G, -, -, he, h⟩ := hloc c hc.1
    rw [he.eq_of_nhds, h hc]
  refine ⟨extendFrom V f, hFf, ⟨hFd, fun z hz i => ?_⟩, fun c hc => ?_, fun G hG hGf =>
    eqOn_of_eqOn_offDivisor hU S hG hFd.continuousOn (hGf.trans hFf.symm)⟩
  · refine eqOn_of_eqOn_offDivisor (G := fun _ => 0) hU S
      (F := fun z => logPartial S i (extendFrom V f) z + a i z * extendFrom V f z)
      ((continuousOn_logPartial hU S i hFd).add ((ha i).continuousOn.mul hFd.continuousOn))
      continuousOn_const (fun w hw => ?_) hz
    have he : extendFrom V f =ᶠ[𝓝 w] f := hFf.eventuallyEq_of_mem (hVo.mem_nhds hw)
    have := hf.2 w hw i
    simp only [logPartial] at this ⊢
    rw [he.fderiv_eq, hFf hw, this]
  · obtain ⟨G, -, hG0, he, -⟩ := hloc c hc
    rwa [he.eq_of_nhds]
end GlobalTheory.Published
