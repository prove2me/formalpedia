-- Prove2me | solution 1 for GlobalTheory.Cris.SqExt.val_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:38.089318+00:00
-- url     : https://prove2.me/submissions/27a3fe86-d93d-4d55-8789-5c218dc9f9d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
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
theorem _root_.solution {B : Type} [CommRing B] [Algebra R B] (y : Sp B ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R B)) (f : Form s) : (self R B).val y hy f.1 = 0 := by
  have hk : RingHom.ker ((self R B).π : B →+* B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h ↦ h
  have k1 : ev f.1 ((self R B).secHom ((self R B).red_w hy) (self R B).i (self R B).π_i) = 0 :=
    f.2 _ rfl hk
  have k2 : ev f.1 ((self R B).idHom hy) = 0 := f.2 _ rfl hk
  rw [val_apply, k1, k2, sub_zero]
end GlobalTheory.Cris.SqExt
