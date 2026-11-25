-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_add_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:59:13.574728+00:00
-- url     : https://prove2.me/submissions/f4e7d4f0-2feb-429c-a75a-0a7cf2d994b0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable_fd


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
theorem _root_.solution [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F G : W → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) (x : W) :
    polyDeriv P u (F + G) x = polyDeriv P u F x + polyDeriv P u G x := by
  unfold polyDeriv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hF _).contDiffAt
    (contDiff_of_differentiable_fd hG _).contDiffAt]
  simp only [ContinuousMultilinearMap.add_apply]
  ring
end GlobalTheory.Jet
