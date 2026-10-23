-- Prove2me | solution 1 for JHolomorphic.eventuallyEq_zero_of_forall_norm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T14:35:48.601092+00:00
-- url     : https://prove2.me/submissions/3917026d-572e-42c6-9e7e-784a6065756d

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros



namespace JHolomorphic

open Metric Filter Topology

/-- A holomorphic map on a disc around `0` with `‖f z‖ ≤ C ‖z‖ ^ N` near `0` for every `N`
vanishes on a neighbourhood of `0`. -/
theorem eventuallyEq_zero_of_forall_norm_le_pow_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (r : ℝ) (hr : 0 < r) (f : ℂ → F)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hb : ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖f z‖ ≤ C * ‖z‖ ^ N) :
    f =ᶠ[𝓝 0] 0 := by
  have ha : AnalyticAt ℂ f 0 := hf.analyticAt (ball_mem_nhds 0 hr)
  by_contra hne
  have hne' : ¬∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := hne
  obtain ⟨k, g, hg, hg0, hfg⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hne'
  obtain ⟨C, δ, hδ, hC⟩ := hb (k + 1)
  -- `‖g z‖ ≤ C ‖z‖` for `z ≠ 0` near `0`
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖g z‖ ≤ C * ‖z‖ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) δ := ball_mem_nhds 0 hδ
    filter_upwards [nhdsWithin_le_nhds (h1.and hfg), self_mem_nhdsWithin] with z ⟨hz, hz'⟩ hz0
    have hz0' : z ≠ 0 := hz0
    have hpos : 0 < ‖z‖ ^ k := pow_pos (norm_pos_iff.2 hz0') k
    have := hC z hz
    rw [hz', sub_zero, norm_smul, norm_pow] at this
    have h2 : ‖z‖ ^ k * ‖g z‖ ≤ ‖z‖ ^ k * (C * ‖z‖) := by
      calc _ ≤ C * ‖z‖ ^ (k + 1) := this
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2 hpos
  have hlim : Tendsto (fun z => ‖g z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖g 0‖) :=
    (hg.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun z : ℂ => C * ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => C * ‖z‖) (𝓝 (0 : ℂ)) (𝓝 (C * ‖(0 : ℂ)‖)) :=
      (continuous_const.mul continuous_norm).tendsto _
    simpa using this.mono_left nhdsWithin_le_nhds
  have hle : ‖g 0‖ ≤ 0 := le_of_tendsto_of_tendsto hlim hlim2 hev
  exact hg0 (norm_le_zero_iff.1 hle)

end JHolomorphic

open JHolomorphic

open Metric Filter Topology

theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] (r : ℝ) (hr : 0 < r) (f : ℂ → F)
    (hf : DifferentiableOn ℂ f (ball 0 r))
    (hb : ∀ N : ℕ, ∃ C δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (0 : ℂ) δ, ‖f z‖ ≤ C * ‖z‖ ^ N) :
    f =ᶠ[𝓝 0] 0 :=
  eventuallyEq_zero_of_forall_norm_le_pow_aux r hr f hf hb
