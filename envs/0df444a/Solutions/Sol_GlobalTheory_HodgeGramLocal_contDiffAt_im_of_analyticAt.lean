-- Prove2me | solution 1 for GlobalTheory.HodgeGramLocal.contDiffAt_im_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:28.218222+00:00
-- url     : https://prove2.me/submissions/5d8983bb-813a-4178-af9b-7557fc0694f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
namespace GlobalTheory.HodgeGramLocal
theorem _root_.solution {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z :=
  (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp z (hF.contDiffAt.restrict_scalars ℝ)
end GlobalTheory.HodgeGramLocal
