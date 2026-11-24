-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.val_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:30.648066+00:00
-- url     : https://prove2.me/submissions/13d54806-98f9-4f7b-a488-bb1299019706

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
theorem _root_.solution {s' : X' ⟶ Sp R} {φ : X' ⟶ X} (h : IsMor (dp0 R) s (dp0 R) s' (RingHom.id R) φ)
    (y : Sp E.C ⟶ X') (hy : y ≫ s' = spMap (algebraMap R E.C))
    (hy' : (y ≫ φ) ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.val y hy (h.pullForm f).1 = E.val (y ≫ φ) hy' f.1 := by
  let θ : h.functor.obj (E.thick (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy)) ⟶
      E.thick (spMap (E.π : E.C →+* E.B) ≫ y ≫ φ) (E.red_w hy') :=
    { φ := { RingHom.id E.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.B) ≫ (spMap (E.π : E.C →+* E.B) ≫ y) ≫ φ =
          spMap (E.π : E.C →+* E.B) ≫ y ≫ φ
        rw [spMap_id, Category.id_comp, Category.assoc] }
  let θB : h.functor.obj (Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy)) ⟶
      Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y ≫ φ) (E.red_w hy') :=
    { φ := { RingHom.id E.B with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.B) ≫ (spMap (E.π : E.C →+* E.B) ≫ y) ≫ φ =
          spMap (E.π : E.C →+* E.B) ≫ y ≫ φ
        rw [spMap_id, Category.id_comp, Category.assoc] }
  let θC : h.functor.obj (Thick.triv E.C y hy) ⟶ Thick.triv E.C (y ≫ φ) hy' :=
    { φ := { RingHom.id E.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := (DPMorphism.id _).isDPMorphism
      pt := by
        change spMap (RingHom.id E.C) ≫ y ≫ φ = y ≫ φ
        rw [spMap_id, Category.id_comp] }
  have s1 := Form.ev_sq f θB (E.secHom (E.red_w hy') E.i E.π_i)
    (h.functor.map (E.secHom (E.red_w hy) E.i E.π_i)) θ rfl rfl (fun _ ↦ rfl)
  have s2 := Form.ev_sq f θC (E.idHom hy') (h.functor.map (E.idHom hy)) θ rfl rfl (fun _ ↦ rfl)
  have l1 : ev (h.pullForm f).1 (E.secHom (E.red_w hy) E.i E.π_i) =
      ev f.1 (h.functor.map (E.secHom (E.red_w hy) E.i E.π_i)) := rfl
  have l2 : ev (h.pullForm f).1 (E.idHom hy) = ev f.1 (h.functor.map (E.idHom hy)) := rfl
  rw [val_apply, val_apply, l1, l2, s1, s2]
  exact (add_sub_add_right_eq_sub _ _ _).symm
end GlobalTheory.Cris.SqExt
