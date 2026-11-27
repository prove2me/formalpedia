-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_eq_algebraMap_of_germDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:46:25.634826+00:00
-- url     : https://prove2.me/submissions/2119dde8-9dae-45d4-bba8-51c62e9c8f93

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
import Theorems.Thm_GroundTheory_Global_Elliptic_nonempty_of_mem_codiscrete
import Theorems.Thm_GroundTheory_Global_Elliptic_germ_eq_zero_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_germDeriv_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {u : MeroField} (hu : germDeriv u = 0) :
    ∃ c : ℂ, u = algebraMap ℂ MeroField c := by
  obtain ⟨f, hf, rfl⟩ := germ_surjective u
  rw [germDeriv_germ hf, germ_eq_zero_iff hf.deriv] at hu
  obtain ⟨x₀, hx₀⟩ := nonempty_of_mem_codiscrete (eventually_analyticAt hf)
  have hd : deriv f =ᶠ[𝓝 x₀] 0 := by
    have hne : ∀ᶠ z in 𝓝[≠] x₀, deriv f z = 0 := eventuallyEq_zero_codiscrete_iff.1 hu x₀
    have hcont : ContinuousAt (deriv f) x₀ := hx₀.deriv.continuousAt
    have h0 : deriv f x₀ = 0 := by
      have ht : Tendsto (deriv f) (𝓝[≠] x₀) (𝓝 (deriv f x₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
      have hne' : deriv f =ᶠ[𝓝[≠] x₀] fun _ ↦ 0 := hne
      exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' hne'.symm)
    rw [← nhdsNE_sup_pure x₀]
    exact ⟨hne, h0⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hx₀.eventually_analyticAt).and hd)
  have hconst : ∀ y ∈ Metric.ball x₀ ε, f x₀ = f y := fun y hy ↦
    (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball x₀ ε).isPreconnected
      (fun z hz ↦ (hball z hz).1.differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hball z hz).2) (Metric.mem_ball_self hε) hy
  refine ⟨f x₀, ?_⟩
  rw [← germ_const, germ_eq_germ_iff hf (Meromorphic.const _), Filter.eventuallyEq_iff_sub]
  apply eventuallyEq_zero_codiscrete_of_nhdsNE (hf.sub (Meromorphic.const _)) (x := x₀)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hε)] with z hz
  simp only [Pi.sub_apply]
  rw [← hconst z hz, sub_self]
end GroundTheory.Global.Elliptic
