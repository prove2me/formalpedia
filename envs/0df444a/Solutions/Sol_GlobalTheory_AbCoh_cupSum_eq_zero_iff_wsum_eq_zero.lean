-- Prove2me | solution 1 for GlobalTheory.AbCoh.cupSum_eq_zero_iff_wsum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:29.110229+00:00
-- url     : https://prove2.me/submissions/74275d19-8a4d-4b93-af25-8061dc32dfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CupSumClosedGlobalOneFormsEqZeroIffSumWedge
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cupHyp_mk
import Theorems.Thm_GlobalTheory_CechDR_toO_mk
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
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
theorem _root_.solution (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (hc : Closed1 F = ⊤) (hs : Function.Surjective (toO F)) (n : ℕ)
    (u v : Fin n → Glob1 F) :
    ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) = 0 ↔ wsum F u v = 0 := by
  have hcl : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F (formZZ F ⟨w, hc ▸ Submodule.mem_top⟩) :=
    fun w ↦ rfl
  have hsum : ∑ k, cupHyp F (clAll F hc (u k)) (clAll F hc (v k)) =
      Hyp2.mk F (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)) := by
    simp only [hcl, cupHyp_mk, map_sum]
  have hval : ∀ T, (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.2 T = wsum F u v T := by
    intro T
    simp only [Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_η, wsum]
    rfl
  have h1 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    simp only [Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply, coe_cupZZ, cupTot_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change mp F ψ 0 * 0 = 0
    simp
  have h2 : ∀ T T' (φ : T ⟶ T'), (∑ k, cupZZ F (formZZ F ⟨u k, hc ▸ Submodule.mem_top⟩)
        (formZZ F ⟨v k, hc ▸ Submodule.mem_top⟩)).1.2.1 T T' φ = 0 := by
    intro T T' φ
    simp only [Submodule.coe_sum, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, coe_cupZZ, cupTot_a]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    change (0 : F.obj T') • _ - (0 : F.obj T') • _ = 0
    simp
  rw [hsum, Hyp2.mk_eq_zero]
  constructor
  · rintro ⟨e, he⟩
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''), (dTot1 F e).1 T T' T'' φ ψ = 0 := fun T T' T'' φ ψ ↦ by
      rw [he]; exact h1 T T' T'' φ ψ
    have ha : ∀ T T' (φ : T ⟶ T'), e.2 T' = p1 F φ (e.2 T) + D R _ (e.1 T T' φ) := fun T T' φ ↦ by
      have := (congrArg (fun x : Tot2 F ↦ x.2.1 T T' φ) he).trans (h2 T T' φ)
      rw [dTot1_a] at this
      rw [sub_sub, sub_eq_zero] at this
      exact this
    have hη : ∀ T, dOne R _ (e.2 T) = wsum F u v T := fun T ↦ by
      have := congrArg (fun x : Tot2 F ↦ x.2.2 T) he
      rw [dTot1_η] at this
      rw [this, hval]
    have hf : e.1 ∈ Z1 F := by
      rw [commAlgFunctorCocyclesOne_eq_ker]
      funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    obtain ⟨c, hcz⟩ := hs (CatCoh.H1.mk F ⟨e.1, hf⟩)
    obtain ⟨cz, rfl⟩ := Hyp1.mk_surjective F c
    rw [toO_mk, CatCoh.H1.mk_eq_mk] at hcz
    obtain ⟨g, hg⟩ := hcz
    have hg' : ∀ T T' (φ : T ⟶ T'), g T' - mp F φ (g T) = cz.1.1 T T' φ - e.1 T T' φ := fun T T' φ ↦
      congrFun (congrFun (congrFun hg T) T') φ
    let θ : A0 F := fun T ↦ e.2 T - (cz.1.2 T - D R _ (g T))
    have hθ : θ ∈ Glob1 F := by
      intro T T' φ
      simp only [θ, map_sub, p1_D]
      have hgT : g T' = mp F φ (g T) + (cz.1.1 T T' φ - e.1 T T' φ) := by rw [← hg' T T' φ]; abel
      rw [ha T T' φ, cechDeRhamTotalCocyclesOne.conn cz φ, hgT]
      simp only [map_add, map_sub]
      abel
    have hθc : (⟨θ, hθ⟩ : Glob1 F) ∈ Closed1 F := hc ▸ Submodule.mem_top
    funext T
    have hθ0 : dOne R _ (e.2 T - (cz.1.2 T - D R _ (g T))) = 0 := hθc T
    rw [map_sub, map_sub, cechDeRhamTotalCocyclesOne.closed cz T, dOne_D, sub_zero, sub_zero] at hθ0
    rw [← hη T, hθ0]; rfl
  · intro hw
    refine ⟨0, ?_⟩
    rw [map_zero]
    refine Tot2.ext (fun T T' T'' φ ψ ↦ (h1 T T' T'' φ ψ).symm) (fun T T' φ ↦ (h2 T T' φ).symm)
      fun T ↦ ?_
    rw [hval, hw]; rfl
end GlobalTheory.AbCoh
