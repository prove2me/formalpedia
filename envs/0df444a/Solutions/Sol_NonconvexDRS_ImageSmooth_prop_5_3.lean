-- Prove2me | solution 1 for NonconvexDRS.ImageSmooth.prop_5_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:21:29.550991+00:00
-- url     : https://prove2.me/submissions/a24b5b7b-88da-4171-ab3f-c2dd2d148c13

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

open NonconvexDRS.ImageSmooth in
theorem solution {n p : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, h x ≠ ⊥)
    (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (sbar : EuclideanSpace ℝ (Fin p)) (hs : ∃ x, C x = sbar ∧ h x ≠ ⊤)
    (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : C xbar = sbar ∧ ∀ x, C x = sbar → h xbar ≤ h x)
    (v : EuclideanSpace ℝ (Fin p)) (hv : IsRegularSubgrad (imageFn C h) sbar v) :
    IsRegularSubgrad h xbar (ContinuousLinearMap.adjoint C v) := by
  have hg : imageFn C h sbar = h xbar := by
    unfold imageFn
    apply le_antisymm
    · exact iInf_le_of_le xbar (iInf_le_of_le hxbar.1 le_rfl)
    · exact le_iInf₂ (fun x hx => hxbar.2 x hx)
  have hgle : ∀ z, imageFn C h (C z) ≤ h z := by
    intro z
    unfold imageFn
    exact iInf_le_of_le z (iInf_le_of_le rfl le_rfl)
  obtain ⟨hvtop, hv2⟩ := hv
  refine ⟨by rw [← hg]; exact hvtop, ?_⟩
  intro ε hε
  set ε' := ε / (‖C‖ + 1) with hε'
  have hCpos : 0 < ‖C‖ + 1 := by positivity
  have hε'pos : 0 < ε' := div_pos hε hCpos
  have hev := hv2 ε' hε'pos
  have hcont : Filter.Tendsto C (nhds xbar) (nhds sbar) := by
    rw [← hxbar.1]; exact C.continuous.tendsto xbar
  filter_upwards [hcont.eventually hev] with z hz
  rw [hg] at hz
  refine le_trans ?_ (hz.trans (hgle z))
  refine add_le_add le_rfl ?_
  apply EReal.coe_le_coe_iff.mpr
  have hinner : ⟪ContinuousLinearMap.adjoint C v, z - xbar⟫_ℝ = ⟪v, C z - sbar⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_left, map_sub, hxbar.1]
  have hnorm : ‖C z - sbar‖ ≤ ‖C‖ * ‖z - xbar‖ := by
    rw [← hxbar.1, ← map_sub]; exact C.le_opNorm _
  have hkey : ε' * ‖C z - sbar‖ ≤ ε * ‖z - xbar‖ := by
    have h1 : ε' * ‖C z - sbar‖ ≤ ε' * (‖C‖ * ‖z - xbar‖) :=
      mul_le_mul_of_nonneg_left hnorm hε'pos.le
    have h2 : ε' * (‖C‖ * ‖z - xbar‖) ≤ ε * ‖z - xbar‖ := by
      rw [hε', div_mul_eq_mul_div, div_le_iff₀ hCpos]
      nlinarith [norm_nonneg (z - xbar), norm_nonneg C, mul_nonneg hε.le (norm_nonneg (z - xbar))]
    linarith
  rw [hinner]
  linarith
