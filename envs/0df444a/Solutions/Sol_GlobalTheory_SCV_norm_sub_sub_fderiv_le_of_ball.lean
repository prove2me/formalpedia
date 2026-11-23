-- Prove2me | solution 1 for GlobalTheory.SCV.norm_sub_sub_fderiv_le_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:45.249937+00:00
-- url     : https://prove2.me/submissions/3ea5739d-a1ea-4ab4-8305-eadac6144a1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_fderiv_le_of_ball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {c z : E} {r M : ℝ}
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M)
    (hz : z ∈ ball c r) :
    ‖f z - f c - fderiv ℂ f c (z - c)‖ ≤ 4 * M * (‖z - c‖ / r) ^ 2 := by
  have hr : 0 < r := pos_of_mem_ball hz
  have h1 := norm_fderiv_le_of_ball hr hf hM
  have hc : HasFDerivAt f (fderiv ℂ f c) c :=
    (hf.differentiableAt (ball_mem_nhds c hr)).hasFDerivAt
  set g : E → V := fun w => f w - fderiv ℂ f c (w - c) with hg
  have hgc : g c = f c := by simp [hg]
  have hgw : ∀ w, g w - g c = f w - f c - fderiv ℂ f c (w - c) := by
    intro w; rw [hgc, hg]; simp only; abel
  have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (f := g) (c := c) (z := z)
    (R₁ := r) (R₂ := 4 * M) (n := 1) ?_ ?_ ?_ hz
  · rwa [dist_eq_norm, dist_eq_norm, hgw] at key
  · exact hf.sub (by fun_prop)
  · intro w hw
    rw [mem_closedBall_iff_norm, hgw]
    have h2 : ‖fderiv ℂ f c (w - c)‖ ≤ 2 * M := by
      refine ((fderiv ℂ f c).le_opNorm _).trans ?_
      calc _ ≤ (2 * M / r) * r :=
            mul_le_mul h1 (mem_ball_iff_norm.mp hw).le (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = 2 * M := by field_simp
    have := norm_sub_le (f w - f c) (fderiv ℂ f c (w - c))
    have := norm_sub_le (f w) (f c)
    linarith [hM w hw, hM c (mem_ball_self hr)]
  · simp only [hgw, pow_one]
    exact hc.isLittleO.norm_right
end GlobalTheory.SCV
