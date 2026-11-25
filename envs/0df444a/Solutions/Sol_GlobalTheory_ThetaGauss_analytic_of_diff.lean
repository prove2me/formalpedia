-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.analytic_of_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:09.720416+00:00
-- url     : https://prove2.me/submissions/f601f464-b8c5-4f86-a2c4-e8a7a1034588

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f Set.univ :=
  ReciprocityTheory.AnForm.Osgood.osgood g _ f isOpen_univ hf.differentiableOn
end GlobalTheory.ThetaGauss
