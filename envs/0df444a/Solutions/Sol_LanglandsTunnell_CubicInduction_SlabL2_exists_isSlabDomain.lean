-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_isSlabDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b85b8910-5f76-514d-b005-c3fa0e237614

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Theorems.Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_discreteTopology_range_globalPointsGL_three_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField

noncomputable section

namespace GapSlabDomainThree

open Set LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

private scoped instance secondCountableTopology_adelicGL_three : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private theorem exists_isOpen_inter_range_eq_singleton :
    ∃ V : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsOpen V ∧
      V ∩ ((globalPointsGL 3 (𝓞 ℚ) ℚ).range : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) = {1} := by
  haveI := LanglandsTunnell.CubicInduction.discreteTopology_range_globalPointsGL_three_rat
  have h1 : IsOpen ({1} : Set ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range) := isOpen_discrete _
  obtain ⟨V, hV, hpre⟩ := isOpen_induced_iff.mp h1
  refine ⟨V, hV, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxV, hxΓ⟩
    have hx : (⟨x, hxΓ⟩ : ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range) ∈ Subtype.val ⁻¹' V := hxV
    rw [hpre] at hx
    simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp hx)
  · rintro rfl
    refine ⟨?_, Subgroup.one_mem _⟩
    have h : (1 : ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range) ∈ Subtype.val ⁻¹' V := by
      rw [hpre]
      exact Set.mem_singleton _
    exact h

private theorem exists_isFundamentalDomain_slabMeasure (a b : ℝ) :
    ∃ Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), MeasurableSet Φ₀ ∧
      IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨F₀, ⟨U, C, hU, hC, rfl⟩, hexact⟩ :=
    Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology (globalPointsGL 3 (𝓞 ℚ) ℚ).range
      exists_isOpen_inter_range_eq_singleton
  have hF₀m : MeasurableSet (⋃ n, U n \ C n) :=
    MeasurableSet.iUnion fun n => (hU n).measurableSet.diff (hC n).measurableSet
  refine ⟨⋃ n, U n \ C n, hF₀m, hF₀m.nullMeasurableSet, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨γ₀, hγ₀, -⟩ := hexact x
    exact ⟨γ₀, hγ₀⟩
  · intro g₁ g₂ hne
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr fun y hy₁ hy₂ => hne ?_)
    obtain ⟨p, hp, rfl⟩ := hy₁
    obtain ⟨q, hq, hpq⟩ := hy₂
    have h₁ : ((g₁⁻¹ : ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range) : AdelicGL 3 (𝓞 ℚ) ℚ) * (g₁ • p)
        ∈ ⋃ n, U n \ C n := by
      simpa [Subgroup.smul_def] using hp
    have h₂ : ((g₂⁻¹ : ↥(globalPointsGL 3 (𝓞 ℚ) ℚ).range) : AdelicGL 3 (𝓞 ℚ) ℚ) * (g₁ • p)
        ∈ ⋃ n, U n \ C n := by
      have hpq' : g₂ • q = g₁ • p := hpq
      rw [← hpq']
      simpa [Subgroup.smul_def] using hq
    exact inv_injective ((hexact (g₁ • p)).unique h₁ h₂)

end GapSlabDomainThree
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain.GapSlabDomainThree"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain.GapSlabDomainThree"

open NumberField LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem solution (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsSlabDomain a b Φ₀ := by
  obtain ⟨Φ₀, -, hΦ₀⟩ := GapSlabDomainThree.exists_isFundamentalDomain_slabMeasure a b
  exact ⟨Φ₀, (isSlabDomain_iff a b Φ₀).mpr ⟨ha, hab, hΦ₀⟩⟩

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain (solution)
