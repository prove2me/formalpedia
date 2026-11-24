-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.val_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:29.89529+00:00
-- url     : https://prove2.me/submissions/59588adc-b8a2-48d0-a3c5-9a15e8d8e53a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_ev_sq
import Theorems.Thm_GlobalTheory_Cris_Form_ev_sq
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
theorem _root_.solution (φ : E.C →ₐ[R] E'.C) (φ₀ : E.B →ₐ[R] E'.B) (hπ : ∀ c, φ₀ (E.π c) = E'.π (φ c))
    (hi : ∀ b, φ (E.i b) = E'.i (φ₀ b)) (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C))
    (y' : Sp E'.C ⟶ X) (hy' : y' ≫ s = spMap (algebraMap R E'.C))
    (e : spMap (φ : E.C →+* E'.C) ≫ y = y') (f : Form s) :
    E'.val y' hy' f.1 = φ (E.val y hy f.1) := by
  have hc : (φ₀ : E.B →+* E'.B).comp (E.π : E.C →+* E.B) =
      (E'.π : E'.C →+* E'.B).comp (φ : E.C →+* E'.C) := RingHom.ext hπ
  have ex : spMap (φ₀ : E.B →+* E'.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
      spMap (E'.π : E'.C →+* E'.B) ≫ y' := by
    rw [← Category.assoc, ← spMap_comp, hc, spMap_comp, Category.assoc, e]
  have s1 := Form.ev_sq f
    (Thick.trivHom (x := spMap (E.π : E.C →+* E.B) ≫ y) (hx := E.red_w hy)
      (T := Thick.triv E'.B _ (E'.red_w hy')) φ₀ (by rw [RingHom.id_comp]; exact ex))
    (E'.secHom (E'.red_w hy') E'.i E'.π_i) (E.secHom (E.red_w hy) E.i E.π_i)
    (E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') ex) rfl rfl (fun c ↦ (hi c).symm)
  have s2 := Form.ev_sq f
    (Thick.trivHom (x := y) (hx := hy) (T := Thick.triv E'.C y' hy') φ
      (by rw [RingHom.id_comp]; exact e))
    (E'.idHom hy') (E.idHom hy)
    (E.thickHom E' φ φ₀ hπ (E.red_w hy) (E'.red_w hy') ex) rfl rfl (fun c ↦ rfl)
  rw [val_apply, val_apply, s1, s2, map_sub]
  exact add_sub_add_right_eq_sub _ _ _
end GlobalTheory.Cris.SqExt
