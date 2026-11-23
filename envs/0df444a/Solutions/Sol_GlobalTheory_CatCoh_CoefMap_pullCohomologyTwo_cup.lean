-- Prove2me | solution 1 for GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_cup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:24.382011+00:00
-- url     : https://prove2.me/submissions/bfcb07a2-33f6-410a-a8dd-b542a1c4b04a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_cup_mk
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class

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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
open GlobalTheory.CatCoh.CoefMap
variable {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}
variable (m : CoefMap σ F F')
namespace GlobalTheory.CatCoh.CoefMap
theorem _root_.solution (a b : H1 F) : m.pull2 (cup F a b) = cup F' (m.pull1 a) (m.pull1 b) := by
  obtain ⟨a, rfl⟩ := H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, pullCohomologyTwo_class, pullCohomologyOne_class, pullCohomologyOne_class, cup_mk]
  congr 1
  apply Subtype.ext
  funext T T' T'' φ ψ
  simp only [pullCocycleTwo_apply, cupZ_apply, pullCocycleOne_apply, map_mul, m.naturality]
end GlobalTheory.CatCoh.CoefMap
