-- Prove2me | solution 1 for GlobalTheory.CatCoh.H1.mk_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:11.153046+00:00
-- url     : https://prove2.me/submissions/44dc3903-2cf0-495e-a5f9-d57c7e58e165

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
namespace H1
theorem _root_.solution {f f' : Z1 F} : H1.mk F f = H1.mk F f' ↔ ∃ g, d0 F g = f.1 - f'.1 := by
  rw [← sub_eq_zero, ← map_sub, H1.mk_eq_zero]
  exact Iff.rfl
end H1
end GlobalTheory.CatCoh
