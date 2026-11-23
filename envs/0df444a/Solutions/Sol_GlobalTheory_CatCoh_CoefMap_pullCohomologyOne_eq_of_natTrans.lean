-- Prove2me | solution 1 for GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:03.165126+00:00
-- url     : https://prove2.me/submissions/53e7e923-ced2-4093-bd44-03f370e5106b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class

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
theorem _root_.solution {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
    (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (c : H1 F) : m.pull1 c = m'.pull1 c := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [pullCohomologyOne_class, pullCohomologyOne_class, H1.mk_eq_mk]
  refine ⟨fun T => -(m'.α T (f.1 _ _ (θ.app T))), ?_⟩
  funext T T' φ
  have h1 := Z1.comp f (m.G.map φ) (θ.app T')
  have h2 := Z1.comp f (θ.app T) (m'.G.map φ)
  rw [θ.naturality φ] at h1
  have h3 := congrArg (m'.α T') (h1.symm.trans h2)
  rw [map_add, map_add, h, m'.naturality] at h3
  simp only [amitsur_d0_apply, map_neg, Pi.sub_apply, pullCocycleOne_apply]
  linear_combination -h3
end GlobalTheory.CatCoh.CoefMap
