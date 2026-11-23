-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.val_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:11:59.101013+00:00
-- url     : https://prove2.me/submissions/b365889e-482e-42c0-9683-c7ea3599b9de

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
attribute [instance] SqExt.ringC SqExt.ringB SqExt.algC SqExt.algB
open GlobalTheory.Cris.SqExt
variable {s : X ⟶ Sp R} (E E' : SqExt R)
namespace GlobalTheory.Cris.SqExt
theorem _root_.solution (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Z1 (O (dp0 R) s)) :
    E.val y hy f = ev f (E.secHom (E.red_w hy) E.i E.π_i) - ev f (E.idHom hy) := rfl
end GlobalTheory.Cris.SqExt
