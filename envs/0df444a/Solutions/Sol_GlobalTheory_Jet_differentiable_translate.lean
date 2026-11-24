-- Prove2me | solution 1 for GlobalTheory.Jet.differentiable_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:54.101013+00:00
-- url     : https://prove2.me/submissions/6b4b8c4c-cc40-411d-b00a-868cefee7fa4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_GlobalTheory_Jet_Hf_eq_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.Jet
variable {σ W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup W'] [NormedSpace ℂ W']
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.Jet
theorem _root_.solution (q : ℕ) (y : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : Differentiable ℂ F) :
    Differentiable ℂ fun v =>
      cexp (q * Real.pi * Hf v y - q * Real.pi * Hf y y / 2) * F (v - y) := by
  have h1 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => Hf v y := by
    simp only [Hf_eq_inner]
    exact (innerSL ℂ y).differentiable
  have h2 : Differentiable ℂ fun v : EuclideanSpace ℂ ι => F (v - y) :=
    hF.comp (differentiable_id.sub_const y)
  exact (((h1.const_mul _).sub_const _).cexp).mul h2
end GlobalTheory.Jet
