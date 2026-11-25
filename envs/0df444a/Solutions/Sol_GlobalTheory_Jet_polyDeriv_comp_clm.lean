-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_comp_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:51.454513+00:00
-- url     : https://prove2.me/submissions/455aaab3-a615-47e2-890d-dc2d5dc12ecd

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
theorem _root_.solution [FiniteDimensional ℂ W'] (P : MvPolynomial σ ℂ) (u : σ → W)
    {F : W' → ℂ} (hF : Differentiable ℂ F) (φ : W →L[ℂ] W') (x : W) :
    polyDeriv P u (F ∘ φ) x = polyDeriv P (φ ∘ u) F (φ x) := by
  unfold polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [φ.iteratedFDeriv_comp_right (contDiff_of_differentiable_fd hF _) x le_rfl]
  rfl
end GlobalTheory.Jet
