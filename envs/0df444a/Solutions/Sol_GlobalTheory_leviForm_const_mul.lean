-- Prove2me | solution 1 for GlobalTheory.leviForm_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:53.954424+00:00
-- url     : https://prove2.me/submissions/1d20b54e-0958-4901-895d-b30b485ec49a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Theorems.Thm_GlobalTheory_ddbar_const_smul

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
variable {u u' : E → ℝ} {z : E}
namespace GlobalTheory
theorem _root_.solution (c : ℝ) (hu : ContDiffAt ℝ 2 u z) :
    leviForm (fun x => c * u x) z = (c : ℂ) • leviForm u z := by
  simp only [leviForm, ofReal_mul]
  exact ddbar_const_smul (c : ℂ) (contDiffAt_ofReal_comp hu)
end GlobalTheory
