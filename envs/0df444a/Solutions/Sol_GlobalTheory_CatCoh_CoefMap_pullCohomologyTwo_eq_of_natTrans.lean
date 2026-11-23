-- Prove2me | solution 1 for GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:03.520713+00:00
-- url     : https://prove2.me/submissions/442e5395-2579-4105-96a6-a7df8e2e916a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
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
theorem _root_.solution {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
    (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (c : H2 F) : m.pull2 c = m'.pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [pullCohomologyTwo_class, pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' φ => m'.α T' (z.1 _ _ _ (m.G.map φ) (θ.app T') - z.1 _ _ _ (θ.app T) (m'.G.map φ)), ?_⟩
  funext T T' T'' φ ψ
  have e1 := z.2 (m.G.map φ) (m.G.map ψ) (θ.app T'')
  have e2 := z.2 (m.G.map φ) (θ.app T') (m'.G.map ψ)
  have e3 := z.2 (θ.app T) (m'.G.map φ) (m'.G.map ψ)
  rw [θ.naturality ψ] at e1
  rw [θ.naturality φ] at e2
  have key : mp F (θ.app T'') (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)) - z.1 _ _ _ (m'.G.map φ) (m'.G.map ψ) =
      mp F (m'.G.map ψ) (z.1 _ _ _ (m.G.map φ) (θ.app T') - z.1 _ _ _ (θ.app T) (m'.G.map φ))
      - (z.1 _ _ _ (m.G.map φ ≫ m.G.map ψ) (θ.app T'') - z.1 _ _ _ (θ.app T) (m'.G.map φ ≫ m'.G.map ψ))
      + (z.1 _ _ _ (m.G.map ψ) (θ.app T'') - z.1 _ _ _ (θ.app T') (m'.G.map ψ)) := by
    rw [map_sub]
    linear_combination e1 - e2 + e3
  have e := congrArg (m'.α T'') key
  simp only [map_sub, map_add, h, m'.naturality] at e
  simp only [d1_apply, Pi.sub_apply, pullCocycleTwo_apply, Functor.map_comp, map_sub]
  linear_combination -e
end GlobalTheory.CatCoh.CoefMap
