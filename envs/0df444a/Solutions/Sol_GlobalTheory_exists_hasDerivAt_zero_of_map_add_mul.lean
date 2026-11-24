-- Prove2me | solution 1 for GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:32.951001+00:00
-- url     : https://prove2.me/submissions/567b2587-6da4-4454-9dd6-34e78da7d654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHasDerivAtZeroOfMapAddMul
import Theorems.Thm_GlobalTheory_continuous_of_map_add_mul_of_continuousAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 →
      ∃ a : ℂ, HasDerivAt ν a 0 := by
  intro ν h0 hm hc0
  have hc := continuous_of_map_add_mul_of_continuousAt_zero ν hm hc0
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, ν x with hF
  have hd : ∀ u, HasDerivAt F (ν u) u := fun u => (hc.deriv_integral ν 0 u ▸
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt.hasDerivAt)
  have hex : ∃ δ, F δ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hz : F = fun _ => 0 := funext hne
    have h1 := hd 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  obtain ⟨δ, hδ⟩ := hex
  have key : ∀ t, ν t = (F (t + δ) - F t) / F δ := by
    intro t
    rw [eq_div_iff hδ]
    have e1 : F (t + δ) - F t = ∫ x in t..(t + δ), ν x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have e2 : ∫ x in t..(t + δ), ν x = ∫ x in (0:ℝ)..δ, ν (t + x) := by
      rw [intervalIntegral.integral_comp_add_left ν t, add_zero]
    rw [e1, e2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  have h1 : HasDerivAt (fun t => F (t + δ)) (ν (0 + δ)) 0 := (hd (0 + δ)).comp_add_const 0 δ
  refine ⟨(ν (0 + δ) - ν 0) / F δ, ?_⟩
  have h2 := (h1.sub (hd 0)).div_const (F δ)
  have h3 : ν = fun t => (F (t + δ) - F t) / F δ := funext key
  conv => arg 1; rw [h3]
  exact h2
end GlobalTheory
