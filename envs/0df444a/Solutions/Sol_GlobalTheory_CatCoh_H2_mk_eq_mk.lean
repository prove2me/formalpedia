-- Prove2me | solution 1 for GlobalTheory.CatCoh.H2.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:14.768803+00:00
-- url     : https://prove2.me/submissions/b8abb71d-229e-4771-af75-daa5f9c48e92

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
namespace GlobalTheory.CatCoh
namespace H2
theorem _root_.solution {z z' : Z2 F} : H2.mk F z = H2.mk F z' ↔ ∃ f, d1 F f = z.1 - z'.1 := by
  rw [← sub_eq_zero, ← map_sub, H2.mk_eq_zero]
  exact Iff.rfl
end H2
end GlobalTheory.CatCoh
