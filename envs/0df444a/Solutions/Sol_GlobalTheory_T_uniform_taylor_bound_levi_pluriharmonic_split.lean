-- Prove2me | solution 1 for GlobalTheory.T.uniform_taylor_bound_levi_pluriharmonic_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:26:00.410422+00:00
-- url     : https://prove2.me/submissions/95bd789f-852d-4006-a536-6ec4ebda949e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplit
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformTaylorBoundLeviPluriharmonicSplitStatement
import Theorems.Thm_GlobalTheory_PluriTaylor_taylor_levi_unif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (U K : Set (V n)) (φ : V n → ℝ) (η : ℝ), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 2 φ U → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ K, closedBall z δ ⊆ U ∧ ∃ h : V n → ℂ, Differentiable ℂ h ∧ h 0 = 0 ∧ ∀ w ∈ closedBall (0 : V n) δ, φ (z + w) ≤ φ z + 2 * (h w).re + (leviV n (fun v => (φ v : ℂ)) z fun j => w j).re + η * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.PluriTaylor.taylor_levi_unif | exact GlobalTheory.PluriTaylor.taylor_levi_unif | (intros; apply GlobalTheory.PluriTaylor.taylor_levi_unif <;> assumption)
end _root_.GlobalTheory.T
