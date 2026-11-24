-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp1_eq_of_natTrans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:01.649105+00:00
-- url     : https://prove2.me/submissions/a44ebef9-d7d9-4399-9dbf-e8c9154b8af8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamTotalDifferentialOneFunctionPart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CechDeRhamCoefMapOneFormsRestrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_coe_pullZZ1
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_mk
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_eq_of_natTrans
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
theorem _root_.solution (c : Hyp1 F) : pullHyp1 m c = pullHyp1 m' c := by
  obtain ⟨f, rfl⟩ := Hyp1.mk_surjective F c
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun T ↦ -m'.α T (f.1.1 _ _ (θ.app T)), Tot1.ext (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · have e := congrArg (fun ξ ↦ m'.α T' (f.1.1 _ _ ξ)) (θ.naturality φ)
    simp only [cechDeRhamTotalCocyclesOne.comp f, map_add, h, m'.naturality] at e
    simp only [dTot0_f, Prod.fst_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_f, map_neg]
    linear_combination -e
  · simp only [dTot0_ω, Prod.snd_sub, Pi.sub_apply, coe_pullZZ1, pullTot1_ω, map_neg]
    rw [cechDeRhamTotalCocyclesOne.conn f (θ.app T), map_add, cechDeRhamCoefMapOneForms_eq_of_natTrans m m' θ h, cechDeRhamCoefMapOneForms_D]; abel
end GlobalTheory.CechDR
