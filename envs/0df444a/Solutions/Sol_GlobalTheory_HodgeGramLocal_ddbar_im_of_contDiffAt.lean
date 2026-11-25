-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.ddbar_im_of_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:28.989324+00:00
-- url     : https://prove2.me/submissions/095cb4ee-8ea0-4f46-b461-fee368df9e83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_leviForm_re_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HodgeGramLocal
theorem _root_.solution {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by
  have h := leviForm_re_eq_zero (f := fun x => -I * F x) (contDiffAt_const.mul hF)
  have e : (fun x => ((F x).im : ℂ)) = fun x => (((-I * F x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e]; exact h
end GlobalTheory.HodgeGramLocal
