-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp2_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:58:57.466337+00:00
-- url     : https://prove2.me/submissions/d4061199-c903-40a9-99a9-3fa0481ffe3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_coe_pullZZ2
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_mk
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CechDR_qOm_pOm_app
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_two
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
open CatCoh
universe v u v' u' v'' u''
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')
variable {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
  (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b)
include h
namespace GlobalTheory.CechDR
theorem _root_.solution (c : Hyp2 F) : pullHyp2 m c = pullHyp2 m' c := by
  obtain ⟨z, rfl⟩ := Hyp2.mk_surjective F c
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(fun T T' φ ↦ m'.α T' (z.1.1 _ _ _ (m.G.map φ) (θ.app T') -
    z.1.1 _ _ _ (θ.app T) (m'.G.map φ)), fun T ↦ -q1 m' T (z.1.2.1 _ _ (θ.app T))),
    Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e1 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (m.G.map ψ) (θ.app T''))
    have e2 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (m.G.map φ) (θ.app T') (m'.G.map ψ))
    have e3 := congrArg (m'.α T'') (cechDeRhamTotalCocyclesTwo.comp z (θ.app T) (m'.G.map φ) (m'.G.map ψ))
    rw [θ.naturality ψ] at e1
    rw [θ.naturality φ] at e2
    simp only [map_add, h, m'.naturality] at e1 e2 e3
    simp only [cechDeRhamTotalDifferentialOne_functionPart, Prod.fst_sub, Pi.sub_apply, coe_pullZZ2, cechDeRhamPullbackTotalDegreeTwo_function_part, map_sub, Functor.map_comp]
    linear_combination -e1 + e2 - e3
  · have e := congrArg (fun ξ ↦ q1 m' T' (z.1.2.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesTwo.one z, map_add, cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_naturality, cechDeRhamCoefMapOneForms_D] at e
    simp only [dTot1_a, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_a, map_sub,
      map_neg]
    linear_combination (norm := abel1) -e
  · simp only [dTot1_η, Prod.snd_sub, Pi.sub_apply, coe_pullZZ2, pullTot2_η, map_neg]
    rw [cechDeRhamTotalCocyclesTwo.two z (θ.app T), map_add, qOm_pOm_app m m' θ h, qOm_dOne]; abel
end GlobalTheory.CechDR
