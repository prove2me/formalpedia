-- Prove2me | solution 1 for GlobalTheory.CatCoh.H1.mk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:10.015649+00:00
-- url     : https://prove2.me/submissions/5a07e430-ba1b-4a8d-9740-66c0481977df

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
namespace GlobalTheory.CatCoh
namespace H1
theorem _root_.solution : Function.Surjective (H1.mk F) := by
  intro c
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨f, rfl⟩
end H1
end GlobalTheory.CatCoh
