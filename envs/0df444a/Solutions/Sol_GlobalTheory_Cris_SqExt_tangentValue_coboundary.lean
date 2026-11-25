-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.tangentValue_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:54.00602+00:00
-- url     : https://prove2.me/submissions/b844779d-e2b4-4c0b-9c7d-bec435dc1060

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_mp_O
import Theorems.Thm_GlobalTheory_Cris_SqExt_val_apply

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
theorem _root_.solution (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (g : C0 (O (dp0 R) s)) :
    E.val y hy ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ =
      (g (Thick.triv E.C y hy) : E.C) - E.i (g (Thick.triv E.B _ (E.red_w hy))) := by
  rw [val_apply]
  change d0 _ g _ _ (E.secHom (E.red_w hy) E.i E.π_i) - d0 _ g _ _ (E.idHom hy) = _
  rw [amitsur_d0_apply, amitsur_d0_apply, mp_O, mp_O]
  exact sub_sub_sub_cancel_left _ _ _
end GlobalTheory.Cris.SqExt
