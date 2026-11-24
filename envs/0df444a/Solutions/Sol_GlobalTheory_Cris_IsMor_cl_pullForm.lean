-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.cl_pullForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:56.932378+00:00
-- url     : https://prove2.me/submissions/71229580-7db3-4127-98bf-fddec66fdd7c

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
variable {s : X ⟶ Sp R}
namespace GlobalTheory.Cris
namespace IsMor
theorem _root_.solution {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) (f : Form s) :
    Form.cl s' (h.pullForm f) = h.pull1 (Form.cl s f) := rfl
end IsMor
end GlobalTheory.Cris
