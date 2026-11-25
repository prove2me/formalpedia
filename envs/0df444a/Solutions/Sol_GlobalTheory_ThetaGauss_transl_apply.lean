-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.transl_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:52.025585+00:00
-- url     : https://prove2.me/submissions/bd3ded8a-f4e5-44b1-a398-db0b2c4668ae

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply

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
theorem _root_.solution {K : Type} [TopologicalSpace K] {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) (z : Fin g → ℂ) (k : K) :
    transl hf γ z k = f (z + γ k) := rfl
end GlobalTheory.ThetaGauss
