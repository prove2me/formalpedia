-- Prove2me | solution 1 for GlobalTheory.ZetaHalfPlane.zeta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:50:06.715018+00:00
-- url     : https://prove2.me/submissions/0124ab56-c5f1-456d-8c0e-07885b7032b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_differentiableAt_fractInt
import Theorems.Thm_GlobalTheory_ZetaHalfPlane_zeta_eq_of_one_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Set Filter Topology
open GlobalTheory GlobalTheory.ZetaHalfPlane
namespace GlobalTheory.ZetaHalfPlane
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * fractInt s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hf : AnalyticOnNhd ℂ riemannZeta₀ {z : ℂ | 0 < z.re} :=
    differentiable_riemannZeta₀.differentiableOn.analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z => 1 - z * fractInt z) {z : ℂ | 0 < z.re} :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_const _).sub
        (differentiableAt_id.mul (differentiableAt_fractInt hz))).differentiableWithinAt) hU
  have key : ∀ z : ℂ, z ≠ 1 → z / (z - 1) = (z - 1)⁻¹ + 1 := by
    intro z hz
    have := sub_ne_zero.2 hz
    field_simp
    ring
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      have hz1 : z ≠ 1 := by
        rintro rfl
        simp at hz
      have h1 := zeta_eq_of_one_lt hz
      rw [riemannZeta_eq_inv_sub_add hz1, key z hz1] at h1
      linear_combination h1)
  have h2 : riemannZeta₀ s = 1 - s * fractInt s := heq hs
  rw [riemannZeta_eq_inv_sub_add hs1, key s hs1, h2]
  ring
end GlobalTheory.ZetaHalfPlane
