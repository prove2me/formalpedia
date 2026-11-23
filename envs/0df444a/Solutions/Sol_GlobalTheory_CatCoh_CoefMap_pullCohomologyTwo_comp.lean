-- Prove2me | solution 1 for GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:06.906115+00:00
-- url     : https://prove2.me/submissions/051e5f52-516d-4081-b9a7-00910f26e19d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective

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
theorem _root_.solution (n : CoefMap τ F' F'') (c : H2 F) :
    (m.comp n).pull2 c = n.pull2 (m.pull2 c) := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rfl
end GlobalTheory.CatCoh.CoefMap
