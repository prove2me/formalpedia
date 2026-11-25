-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.differentiable_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:54.795988+00:00
-- url     : https://prove2.me/submissions/f3095741-847e-4dcf-b2d1-49921281403d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_analytic_of_diff

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
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (v : Fin g → ℂ) : Differentiable ℂ fun z => fderiv ℂ θ z v :=
  (differentiableOn_univ.1 (analytic_of_diff hθ).fderiv.differentiableOn).clm_apply
    (differentiable_const v)
end GlobalTheory.ThetaGauss
