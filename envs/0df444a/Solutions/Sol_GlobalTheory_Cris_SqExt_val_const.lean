-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.val_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:29.058467+00:00
-- url     : https://prove2.me/submissions/687cb7aa-421c-4d02-815b-e601d1a106ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_ev_comp
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
theorem _root_.solution (x : Sp E.B ⟶ X) (hx : x ≫ s = spMap (algebraMap R E.B)) (y : Sp E.C ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R E.C)) (e : spMap (E.i : E.B →+* E.C) ≫ x = y) (f : Form s) :
    E.val y hy f.1 = 0 := by
  subst e
  have hpi : (E.π : E.C →+* E.B).comp (E.i : E.B →+* E.C) = RingHom.id E.B := RingHom.ext E.π_i
  let lam : Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ spMap (E.i : E.B →+* E.C) ≫ x)
      (E.red_w hy) ⟶ Thick.triv E.C (spMap (E.i : E.B →+* E.C) ≫ x) hy :=
    Thick.trivHom E.i (by
      change spMap ((RingHom.id E.C).comp (E.i : E.B →+* E.C)) ≫ spMap (E.π : E.C →+* E.B) ≫
          spMap (E.i : E.B →+* E.C) ≫ x = spMap (E.i : E.B →+* E.C) ≫ x
      rw [RingHom.id_comp, ← Category.assoc (spMap (E.π : E.C →+* E.B)), ← spMap_comp, hpi,
        spMap_id, Category.id_comp])
  have k : E.secHom (E.red_w hy) E.i E.π_i = lam ≫ E.idHom hy := Thick.hom_ext fun _ ↦ rfl
  rw [val_apply, k, ev_comp, show ev f.1 lam = 0 from f.2 lam rfl rfl, map_zero, zero_add,
    sub_self]
end GlobalTheory.Cris.SqExt
