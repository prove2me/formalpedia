-- Prove2me | solution 1 for GlobalTheory.AbCoh.hyp2_eq_sum_cup_of_fn_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:38:11.508811+00:00
-- url     : https://prove2.me/submissions/207ba0f5-5e0e-47ce-8259-c08b0c3461a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HyperH2SumOfCupsExact
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_two
import Theorems.Thm_GlobalTheory_CechDR_cupHyp_mk
import Theorems.Thm_GlobalTheory_CechDR_dOne_smul
import Theorems.Thm_GlobalTheory_CechDR_toO_mk
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_T_globalTwoForm_eq_sumWedgeGlobalOneForms
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by
  intro R _ C _ F hfr h0 hc hs c ⟨f, hf⟩
  obtain ⟨m, ⟨fr⟩⟩ := hfr
  have hcl : ∀ (w : Glob1 F) (T : C), dOne R _ (w.1 T) = 0 := fun w T ↦
    (show w ∈ Closed1 F by rw [hc]; trivial) T
  have hclAll : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F ⟨(0, w.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _,
      fun T T' φ ↦ by simpa using w.2 φ, fun T ↦ hcl w T⟩⟩ := fun w ↦ rfl
  set c' : cechDeRhamTotalCocyclesTwo F := c - ⟨dTot1 F (f, 0), dTot1_mem F _⟩ with hc'
  have hmk : Hyp2.mk F c = Hyp2.mk F c' := by
    rw [hc', map_sub, (Hyp2.mk_eq_zero (c := ⟨dTot1 F (f, 0), dTot1_mem F _⟩)).2 ⟨(f, 0), rfl⟩, sub_zero]
  have hz : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c'.1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf, sub_self]
  set a : A1 F := c'.1.2.1 with ha
  have hacoc : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ := by
    intro T T' T'' φ ψ
    rw [ha, cechDeRhamTotalCocyclesTwo.one c' φ ψ, hz, map_zero, add_zero]
  let g : Fin m → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    simp only [hacoc φ ψ, map_add, fr.nat]⟩
  have hE : ∀ i, ∃ e : cechDeRhamTotalCocyclesOne F, e.1.1 = (g i).1 := by
    intro i
    obtain ⟨x, hx⟩ := hs (H1.mk F (g i))
    obtain ⟨e0, rfl⟩ := Hyp1.mk_surjective F x
    rw [toO_mk, H1.mk_eq_mk] at hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨e0 - ⟨dTot0 F h, dTot0_mem F h⟩, ?_⟩
    change e0.1.1 - d0 F h = (g i).1
    rw [hh]; change e0.1.1 - (e0.1.1 - (g i).1) = (g i).1; abel
  choose e he using hE
  let η' : W0 F 2 := fun T ↦ c'.1.2.2 T - ∑ i, wedge R _ ((e i).1.2 T) ((fr.w i).1 T)
  have hη' : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η' T' = pOm F 2 φ (η' T) := by
    intro T T' φ
    have hd : dOne R _ (a T T' φ) = ∑ i, wedge R _ (D R _ (fr.δ i T' (a T T' φ))) ((fr.w i).1 T') := by
      conv_lhs => rw [fr.sum T' (a T T' φ)]
      simp [map_sum, dOne_smul, hcl]
    have hw : ∀ i, (fr.w i).1 T' = p1 F φ ((fr.w i).1 T) := fun i ↦ (fr.w i).2 φ
    have he' : ∀ i, (e i).1.2 T' = p1 F φ ((e i).1.2 T) + D R _ (fr.δ i T' (a T T' φ)) := by
      intro i; rw [cechDeRhamTotalCocyclesOne.conn (e i) φ, he]
    simp only [η', map_sub, map_sum, pOm_wedge]
    rw [cechDeRhamTotalCocyclesTwo.two c' φ, ← ha, hd]
    simp only [he', map_add, LinearMap.add_apply, Finset.sum_add_distrib, ← hw]
    abel
  obtain ⟨n, u, v, huv⟩ := GlobalTheory.T.globalTwoForm_eq_sumWedgeGlobalOneForms R C F ⟨m, ⟨fr⟩⟩ h0 η' hη'
  refine ⟨m + n, Fin.append (fun i ↦ Hyp1.mk F (e i)) (fun k ↦ clAll F hc (u k)), Fin.append fr.w v, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hclAll, cupHyp_mk, ← map_sum, ← map_add, hmk]
  congr 1
  apply Subtype.ext
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) (fun T ↦ ?_)
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.fst_add, Prod.fst_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_apply, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum,
      Pi.add_apply, Finset.sum_apply, coe_cupZZ, cupTot_a, Pi.zero_apply, zero_smul, sub_zero,
      Finset.sum_const_zero, add_zero, he]
    exact fr.sum T' (a T T' φ)
  · have := congrFun huv T
    simp only [η', wsum] at this
    simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_η]
    rw [← this]; abel
end GlobalTheory.AbCoh
