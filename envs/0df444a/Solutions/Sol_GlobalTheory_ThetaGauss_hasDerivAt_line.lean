-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:50.52287+00:00
-- url     : https://prove2.me/submissions/71cd3614-a5c6-4fbb-bdb3-193b4d12b06a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
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
theorem _root_.solution {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) (x v : Fin g → ℂ) (t : ℂ) :
    HasDerivAt (fun t : ℂ => f (x + t • v)) (fderiv ℂ f (x + t • v) v) t := by
  have h : HasDerivAt (fun t : ℂ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hf _).hasFDerivAt.comp_hasDerivAt t h
end GlobalTheory.ThetaGauss
