-- Prove2me | solution 1 for GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:34.815099+00:00
-- url     : https://prove2.me/submissions/61499b53-64c8-42e6-807f-3fc49a236290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MemLpAndTendstoIntegralInnerOfEventuallyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by
  intro X _ μ E _ _ a u h hh hm hb he

  obtain ⟨s, hs⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (hm.and hb))
  have hs' : Tendsto (fun n => s (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hs.comp (tendsto_add_atTop_nat N)
  have hev : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a (s (n + N)) x = u x := by
    filter_upwards [he] with x hx
    exact hs'.eventually hx
  have hu : AEStronglyMeasurable u μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => a (s (n + N)))
      (fun n => (hN (n + N) (Nat.le_add_left _ _)).1) ?_
    filter_upwards [hev] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => hn.symm)
  have hub : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ h x := by
    have h1 : ∀ᵐ x ∂μ, ∀ n, ‖a (s (n + N)) x‖ ^ 2 ≤ h x :=
      ae_all_iff.2 fun n => (hN (n + N) (Nat.le_add_left _ _)).2
    filter_upwards [hev, h1] with x hx h1x
    obtain ⟨n, hn⟩ := hx.exists
    rw [← hn]; exact h1x n
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hu]
    refine hh.mono' (hu.norm.pow 2) ?_
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  · have key : (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ)) = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [key]
    refine tendsto_integral_filter_of_dominated_convergence h ?_ ?_ hh ?_
    · filter_upwards [hm] with ε hε
      exact hε.inner hu
    · filter_upwards [hb] with ε hε
      filter_upwards [hε, hub] with x h1 h2
      have := norm_inner_le_norm (𝕜 := ℂ) (a ε x) (u x)
      nlinarith [sq_nonneg (‖a ε x‖ - ‖u x‖)]
    · filter_upwards [he] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun ε hε => by simp only [hε])
end GlobalTheory
