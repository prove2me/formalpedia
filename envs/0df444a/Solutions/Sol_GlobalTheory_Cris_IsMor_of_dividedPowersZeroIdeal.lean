-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.of_dividedPowersZeroIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:24:25.798818+00:00
-- url     : https://prove2.me/submissions/6f9badeb-40ea-4da3-aa4b-ca30b0890c19

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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
namespace GlobalTheory.Cris
namespace IsMor
theorem _root_.solution {s : X ⟶ Sp R} (γ' : DividedPowers I') {s' : X' ⟶ Sp R'} {σ : R →+* R'}
    {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) : IsMor (dp0 R) s γ' s' σ φ := ⟨isDPMorphism_of_eq_bot _ rfl _ _, h⟩
end IsMor
end GlobalTheory.Cris
