-- Prove2me | solution 1 for GlobalTheory.Jet.polyDeriv_eq_sum_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:11.868795+00:00
-- url     : https://prove2.me/submissions/0df97111-f42c-46fc-9446-ca9344310bd2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_polyDeriv_monomial_one


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
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) :
    polyDeriv P u F x =
      ∑ m ∈ P.support, P.coeff m * polyDeriv (MvPolynomial.monomial m (1 : ℂ)) u F x := by
  simp only [polyDeriv_monomial_one]
  rfl
end GlobalTheory.Jet
