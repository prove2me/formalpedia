-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.frequently_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:22.945239+00:00
-- url     : https://prove2.me/submissions/073e55fa-ee77-4afb-988d-2c346ef29259

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_analytic_of_diff
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (z) :
    (𝓝[{x | θ x ≠ 0}] z).NeBot := by
  refine frequently_mem_iff_neBot.1 fun h => ?_
  refine h0 (funext fun x => (analytic_of_diff hθ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) (h.mono fun y hy => ?_) (Set.mem_univ x))
  simpa using hy
end GlobalTheory.ThetaGauss
