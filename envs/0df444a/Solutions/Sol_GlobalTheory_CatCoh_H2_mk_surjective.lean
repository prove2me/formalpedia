-- Prove2me | solution 1 for GlobalTheory.CatCoh.H2.mk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:00.922775+00:00
-- url     : https://prove2.me/submissions/2ee47999-c60c-4f90-a0aa-1c58afe513fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective

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
namespace H2
theorem _root_.solution : Function.Surjective (H2.mk F) := by
  intro c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨z, rfl⟩
end H2
end GlobalTheory.CatCoh
