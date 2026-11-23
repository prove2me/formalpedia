-- Prove2me | solution 1 for GlobalTheory.CatCoh.cup_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:45.852432+00:00
-- url     : https://prove2.me/submissions/28bbc874-c9ea-4c43-8663-874c3738b1c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne

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
open CategoryTheory
open GlobalTheory GlobalTheory.CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)
namespace GlobalTheory.CatCoh
theorem _root_.solution (a b : Z1 F) : cup F (H1.mk F a) (H1.mk F b) = H2.mk F (cupZ F a b) := rfl
end GlobalTheory.CatCoh
