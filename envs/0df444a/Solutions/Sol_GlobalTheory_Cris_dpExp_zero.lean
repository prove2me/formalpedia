-- Prove2me | solution 1 for GlobalTheory.Cris.dpExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:24:33.533018+00:00
-- url     : https://prove2.me/submissions/a81d9b38-c86c-44bd-888f-094758e8dd1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
namespace GlobalTheory.Cris
theorem _root_.solution (δ : DividedPowers J) : dpExp δ 0 = 1 := by
  rw [dpExp, finsum_eq_single (fun n ↦ δ.dpow n 0) 0 fun n hn ↦ δ.dpow_eval_zero hn,
    δ.dpow_zero J.zero_mem]
end GlobalTheory.Cris
