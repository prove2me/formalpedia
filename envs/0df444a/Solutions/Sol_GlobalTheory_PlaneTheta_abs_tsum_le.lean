-- Prove2me | solution 1 for GlobalTheory.PlaneTheta.abs_tsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:11.710384+00:00
-- url     : https://prove2.me/submissions/0477edae-39b2-4fa2-a59c-b37000d2fe9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptotics

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open scoped RealInnerProductSpace
open GlobalTheory GlobalTheory.PlaneTheta
namespace GlobalTheory.PlaneTheta
theorem _root_.solution {ι : Type*} {q f : ι → ℝ} {δ s : ℝ} (hs : 1 ≤ s)
    (h : Summable fun i => Real.exp (-q i)) (hf : ∀ i, |f i| ≤ Real.exp (-(s * q i)))
    (hδ : ∀ i, f i ≠ 0 → δ ≤ q i) :
    |∑' i, f i| ≤ (Real.exp δ * ∑' i, Real.exp (-q i)) * Real.exp (-δ * s) := by
  have hb : ∀ i, ‖f i‖ ≤ Real.exp δ * Real.exp (-q i) * Real.exp (-δ * s) := by
    intro i
    by_cases h0 : f i = 0
    · rw [h0, norm_zero]; positivity
    · refine (hf i).trans ?_
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [hδ i h0]
  have := tsum_of_norm_bounded ((h.hasSum.mul_left (Real.exp δ)).mul_right (Real.exp (-δ * s))) hb
  exact this
end GlobalTheory.PlaneTheta
