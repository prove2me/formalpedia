-- Prove2me | solution 1 for GlobalTheory.leviForm_log_normSq_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:03.565418+00:00
-- url     : https://prove2.me/submissions/a0acbcf5-fd22-42b4-9dd5-1f7c64f186da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_leviForm_log_normSq_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ComplexConjugate
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H]
variable {φ : E → H} {z : E}
namespace GlobalTheory
theorem _root_.solution {f : E → ℂ} (hf : ContDiffAt ℂ 2 f z) (hz : f z ≠ 0) :
    leviForm (fun x => Real.log (‖f x‖ ^ 2)) z = 0 := by
  ext v w
  rw [leviForm_log_normSq_comp hf hz, ← conj_mul', show (‖f z‖ : ℂ) ^ 4 = (conj (f z) * f z) ^ 2 by
    rw [conj_mul']; ring]
  have : conj (f z) ≠ 0 := by simpa using hz
  simp only [inner, ContinuousLinearMap.zero_apply, star_def]
  field_simp
  ring
end GlobalTheory
