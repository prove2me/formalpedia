-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.del_im_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:29.75527+00:00
-- url     : https://prove2.me/submissions/ff0dc2c0-4142-41da-897c-3e4597cfa235

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_del_sub
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
theorem _root_.solution {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by
  have hR : DifferentiableAt ℝ F z := hF.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun x => conj (F x)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hR
  have e : (fun x => ((F x).im : ℂ)) = fun x => (1 / (2 * I)) • (F x - conj (F x)) := by
    funext x; rw [im_eq_sub_conj, smul_eq_mul]; ring
  rw [e, del_const_smul _ (hR.fun_sub hc), ContinuousLinearMap.smul_apply, del_sub hR hc,
    ContinuousLinearMap.sub_apply, del_conj, dbar_eq_zero hF, del_eq_fderiv hF]
  simp
end GlobalTheory.HodgeGramLocal
