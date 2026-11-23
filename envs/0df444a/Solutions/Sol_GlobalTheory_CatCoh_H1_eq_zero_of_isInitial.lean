-- Prove2me | solution 1 for GlobalTheory.CatCoh.H1.eq_zero_of_isInitial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:03.268802+00:00
-- url     : https://prove2.me/submissions/4975176d-5777-443c-bd4d-ebe020dc7ad2

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
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)
namespace GlobalTheory.CatCoh
namespace H1
theorem _root_.solution {T₀ : C} (h : Limits.IsInitial T₀) (c : H1 F) : c = 0 := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  refine H1.mk_eq_zero.2 ⟨fun T => f.1 T₀ T (h.to T), ?_⟩
  funext T T' φ
  have e := Z1.comp f (h.to T) φ
  rw [h.hom_ext (h.to T ≫ φ) (h.to T')] at e
  simp only [amitsur_d0_apply]
  linear_combination e
end H1
end GlobalTheory.CatCoh
