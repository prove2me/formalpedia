-- Prove2me | solution 1 for GlobalTheory.AbCoh.twoForm_eq_wsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:28:17.879032+00:00
-- url     : https://prove2.me/submissions/acc8110d-0880-4b5b-ac28-078a5b0e8761

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlobalTwoFormEqSumWedgeGlobalOneForms
import Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_eq_expand
import Theorems.Thm_GlobalTheory_AbCoh_TwoFormSum_coordPair_nat
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_wedge_smul_left
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
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
open TwoFormSum
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → ∀ ζ : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ζ T' = pOm F 2 φ (ζ T)) →
      ∃ (n : ℕ) (u v : Fin n → Glob1 F), ζ = wsum F u v := by
  intro R _ C _ F ⟨n, ⟨Φ⟩⟩ h0 ζ hζ
  let g : Fin n → Fin n → C0 F := fun i j T ↦ coordPair (Φ.δ i T) (Φ.δ j T) (ζ T)
  have hg : ∀ i j, d0 F (g i j) = 0 := by
    intro i j
    funext T T' φ
    rw [amitsur_d0_apply]
    simp only [g]
    rw [hζ φ, coordPair_nat, sub_self]
    rfl
  choose c hc using fun i j ↦ (h0 (g i j) (hg i j)).exists
  let e : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm
  refine ⟨n * n, fun k ↦ (if (e k).1 < (e k).2 then c (e k).1 (e k).2 else 0) • Φ.w (e k).1,
    fun k ↦ Φ.w (e k).2, ?_⟩
  funext T
  simp only [wsum]
  rw [Fintype.sum_equiv e _ (fun p ↦ wedge R (F.obj T)
      (((if p.1 < p.2 then c p.1 p.2 else 0) • Φ.w p.1 : Glob1 F).1 T) ((Φ.w p.2).1 T)) (fun k ↦ rfl),
    Fintype.sum_prod_type]
  conv_lhs => rw [eq_expand (fun i ↦ (Φ.w i).1 T) (fun i ↦ Φ.δ i T) (Φ.sum T) (ζ T)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, wedge_smul_left]
  split_ifs
  · have := hc i j T
    simp only [g] at this
    rw [this, algebraMap_smul]
  · simp
end GlobalTheory.AbCoh
