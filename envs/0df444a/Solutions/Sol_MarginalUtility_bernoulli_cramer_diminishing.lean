-- Prove2me | solution 1 for MarginalUtility.bernoulli_cramer_diminishing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:04:10.486337+00:00
-- url     : https://prove2.me/submissions/39a9b528-61ec-4768-b0d7-4a7074935453

import Mathlib
import Definitions.Def_MarginalUtility_Model

open Set

theorem solution :
    MarginalUtility.HasDiminishingMarginalUtility Real.log (Ioi 0) ∧
      MarginalUtility.HasDiminishingMarginalUtility Real.sqrt (Ioi 0) := by
  have hsqd : ∀ x ∈ Ioi (0:ℝ), deriv Real.sqrt =ᶠ[nhds x] fun y => (2 * Real.sqrt y)⁻¹ := by
    intro x hx
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [(Real.hasDerivAt_sqrt (ne_of_gt hy)).deriv, one_div]
  have hg : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => (2 * Real.sqrt y)⁻¹)
      (-(2 * (1 / (2 * Real.sqrt x))) / (2 * Real.sqrt x) ^ 2) x := by
    intro x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    exact ((Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul 2).inv (by positivity)
  refine ⟨⟨Real.differentiableOn_log.mono (fun x hx => ne_of_gt hx), ?_, ?_⟩,
    ⟨fun x hx => (Real.hasDerivAt_sqrt (ne_of_gt hx)).differentiableAt.differentiableWithinAt,
      fun x hx => ?_, fun x hx => ?_⟩⟩
  · rw [Real.deriv_log']
    exact differentiableOn_inv.mono (fun x hx => ne_of_gt hx)
  · intro x hx
    rw [Real.deriv_log', deriv_inv]
    have : 0 < x := hx
    have : 0 < x ^ 2 := by positivity
    linarith [neg_neg_of_pos (inv_pos.2 this)]
  · exact ((hg x hx).differentiableAt.congr_of_eventuallyEq (hsqd x hx)).differentiableWithinAt
  · rw [(hsqd x hx).deriv_eq, (hg x hx).deriv]
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    rw [neg_div]
    exact neg_neg_of_pos (by positivity)
