-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_sum_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:38.464388+00:00
-- url     : https://prove2.me/submissions/14039dab-4fd9-4188-a155-ff6def0f80e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable_fd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_sum


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
namespace GlobalTheory.Jet
theorem _root_.solution [FiniteDimensional ℂ W] {κ : Type*} (P : MvPolynomial σ ℂ) (u : σ → W)
    (s : Finset κ) (c : κ → ℂ) (F : κ → W → ℂ) (hF : ∀ i ∈ s, Differentiable ℂ (F i)) (x : W) :
    polyDeriv P u (fun w => ∑ i ∈ s, c i * F i w) x = ∑ i ∈ s, c i * polyDeriv P u (F i) x :=
  ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_sum P u s c F
    (fun i hi k => contDiff_of_differentiable_fd (hF i hi) k) x
end GlobalTheory.Jet
