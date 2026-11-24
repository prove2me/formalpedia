-- Prove2me | solution 1 for GlobalTheory.updCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:24.400019+00:00
-- url     : https://prove2.me/submissions/e3182feb-0b1a-44d3-bfd9-32bbf15a8fb3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtCoordinateCauchyIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (k : Fin n) (p : (Fin n → ℂ) × ℂ) :
    updCLM n k p = Function.update p.1 k p.2 := by
  funext i
  simp only [updCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split_ifs <;> simp
end GlobalTheory
