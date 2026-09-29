-- Prove2me | solution 1 for NumberField.exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4073c277-d261-503f-9e92-502f603d5cec

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
import Theorems.Thm_NumberField_sum_ideleClassChar_eq_of_comp_idelicNorm_eq
import Theorems.Thm_NumberField_setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
import Theorems.Thm_NumberField_exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_GenuineDescent_exists_ideleChar_comp_idelicNorm_eq_of_unitsAct_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
p2m_attr_erase "instance" "FrobeniusDensity.isMaximal_ratPrimeIdeal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec IsLocalRing.principalUnits_zero ContinuousAddEquiv.preimage_mulLeft_smul ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal Pointwise

namespace R3FafM6

section NormInvariance

variable {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E] [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F]
  [Algebra E F]

theorem adelicNorm_actOf (B : M4aHerbrand.AdeleBaseChange R E S F) (g : F ≃ₐ[E] F)
    (x : AdeleRing S F) :
    B.adelicNorm ((letI := B.β.toAlgebra; M4aHerbrand.actOf R E S F B.tensorEquiv g) x) =
      B.adelicNorm x := by
  letI := B.β.toAlgebra
  exact Algebra.norm_eq_of_algEquiv
    (B.tensorEquiv.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl g).trans B.tensorEquiv)) x

theorem idelicNorm_unitsAct_toIdeleGaloisDescent (B : M4aHerbrand.AdeleBaseChange R E S F)
    (hcont : ∀ σ : F ≃ₐ[E] F,
      letI := B.β.toAlgebra; Continuous (M4aHerbrand.actOf R E S F B.tensorEquiv σ))
    (g : F ≃ₐ[E] F) (z : (AdeleRing S F)ˣ) :
    B.idelicNorm ((B.toIdeleGaloisDescent hcont).unitsAct g z) = B.idelicNorm z := by
  ext
  simp only [M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map]
  exact adelicNorm_actOf B g (z : AdeleRing S F)

end NormInvariance

theorem idelicNorm_genuineDescentDatum_unitsAct (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (g : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm
        ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct g z) =
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z :=
  idelicNorm_unitsAct_toIdeleGaloisDescent (M4aHerbrand.GenuineDescent.genuineBaseChange K L) _ g z

theorem finite_setOf_mem_and_exists_mem_of_isCompact {G A : Type*} [CommGroup G]
    [TopologicalSpace G] [ContinuousMul G] [CommGroup A] (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (ι : A →* G) (T : Set A)
    (key : ∀ t ∈ T, ∀ t' ∈ T, ι (t⁻¹ * t') ∈ U → t = t') {C : Set G} (hC : IsCompact C) :
    {t | t ∈ T ∧ ∃ u ∈ C, (ι t)⁻¹ * u ∈ U}.Finite := by
  have hDopen : ∀ x : G, IsOpen {u : G | x⁻¹ * u ∈ (U : Set G)} := fun x =>
    hU.preimage (continuous_const_mul x⁻¹)
  obtain ⟨X, hXcov⟩ := hC.elim_finite_subcover (fun x : G => {u : G | x⁻¹ * u ∈ (U : Set G)})
    hDopen (fun u _ => Set.mem_iUnion.2 ⟨u, by
      show u⁻¹ * u ∈ (U : Set G)
      rw [inv_mul_cancel]
      exact U.one_mem⟩)
  have hsub : ∀ x : G, ({t | t ∈ T ∧ (ι t)⁻¹ * x ∈ U} : Set A).Subsingleton := by
    intro x t ht t' ht'
    refine key t ht.1 t' ht'.1 ?_
    have h : ι (t⁻¹ * t') = ((ι t)⁻¹ * x) * ((ι t')⁻¹ * x)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [h]
    exact U.mul_mem ht.2 (U.inv_mem ht'.2)
  refine Set.Finite.subset (Set.Finite.biUnion X.finite_toSet fun x _ => (hsub x).finite) ?_
  rintro t ⟨htT, u, huC, hu⟩
  obtain ⟨x, hxX, hx⟩ := Set.mem_iUnion₂.1 (hXcov huC)
  refine Set.mem_iUnion₂.2 ⟨x, hxX, htT, ?_⟩
  have h : (ι t)⁻¹ * x = ((ι t)⁻¹ * u) * (x⁻¹ * u)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [h]
  exact U.mul_mem hu (U.inv_mem hx)

theorem engine {G Λ A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν]
    [MeasurableSpace Λ] (μ : Measure Λ) (Θ : Set Λ) (N : Λ → G)
    [CommGroup A] (ι : A →* G) (T : Set A)
    (U : Subgroup G) (hUopen : IsOpen (U : Set G)) (hNU : ∀ z, N z ∈ U)
    (key : ∀ t ∈ T, ∀ t' ∈ T, ι (t⁻¹ * t') ∈ U → t = t')
    (hcover : ∀ a : A, ∃ t ∈ T, ι (t⁻¹ * a) ∈ U)
    (κ : ℝ) (hκ : 0 < κ)
    (hNA : ∀ g : G → ℂ, Measurable g → ∫ z in Θ, g (N z) ∂μ = κ * ∫ u in (U : Set G), g u ∂ν)
    (χ : Λ → ℂ) (Φ : G → ℂ) (hΦc : Continuous Φ) (c : ℂ)
    (hchi1 : ∀ (a : A) (z : Λ), Φ (ι a * N z) = c * χ z)
    (hchi2 : ∀ u : G, u ∉ ι.range ⊔ U → Φ u = 0)
    (F : G → ℂ) (hFc : Continuous F) (hFs : HasCompactSupport F) :
    (T ∩ Function.support fun t => ∫ z in Θ, χ z * F (ι t * N z) ∂μ).Finite ∧
      ∫ u, Φ u * F u ∂ν =
        (c / κ) * ∑ᶠ t ∈ T, ∫ z in Θ, χ z * F (ι t * N z) ∂μ := by
  classical

  set I : A → ℂ := fun t => ∫ z in Θ, χ z * F (ι t * N z) ∂μ with hI

  let C : A → Set G := fun t => {u | (ι t)⁻¹ * u ∈ U}
  have hCopen : ∀ t, IsOpen (C t) := fun t => hUopen.preimage (continuous_const_mul (ι t)⁻¹)
  have hCmeas : ∀ t, MeasurableSet (C t) := fun t => (hCopen t).measurableSet
  have hmemC : ∀ t z, ι t * N z ∈ C t := by
    intro t z
    show (ι t)⁻¹ * (ι t * N z) ∈ U
    rw [inv_mul_cancel_left]
    exact hNU z
  have hdisj : ∀ t ∈ T, ∀ t' ∈ T, ∀ u : G, u ∈ C t → u ∈ C t' → t = t' := by
    intro t ht t' ht' u hu hu'
    refine key t ht t' ht' ?_
    have h : ι (t⁻¹ * t') = ((ι t)⁻¹ * u) * ((ι t')⁻¹ * u)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [h]
    exact U.mul_mem hu (U.inv_mem hu')

  have hS₀fin : {t | t ∈ T ∧ ∃ u ∈ tsupport F, (ι t)⁻¹ * u ∈ U}.Finite :=
    finite_setOf_mem_and_exists_mem_of_isCompact U hUopen ι T key hFs
  set s : Finset A := hS₀fin.toFinset with hs_def
  have hs : ∀ t, t ∈ s ↔ t ∈ T ∧ ∃ u ∈ tsupport F, u ∈ C t := by
    intro t
    rw [hs_def, Set.Finite.mem_toFinset]
    rfl

  have hI0 : ∀ t, (¬ ∃ u ∈ tsupport F, u ∈ C t) → I t = 0 := by
    intro t ht
    have h : (fun z => χ z * F (ι t * N z)) = fun _ => 0 := by
      funext z
      have hF : F (ι t * N z) = 0 := by
        by_contra hne
        exact ht ⟨_, subset_tsupport _ hne, hmemC t z⟩
      rw [hF, mul_zero]
    simp only [hI, h, integral_zero]

  have h1 : (T ∩ Function.support I) ⊆ {t | t ∈ T ∧ ∃ u ∈ tsupport F, (ι t)⁻¹ * u ∈ U} := by
    rintro t ⟨htT, hsupp⟩
    refine ⟨htT, ?_⟩
    by_contra hne
    exact hsupp (hI0 t hne)
  have hfin : (T ∩ Function.support I).Finite := hS₀fin.subset h1

  have hfinsum : ∑ᶠ t ∈ T, I t = ∑ t ∈ s, I t := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext t
    constructor
    · rintro ⟨htT, hsupp⟩
      exact ⟨Finset.mem_coe.2 ((hs t).2 (h1 ⟨htT, hsupp⟩)), hsupp⟩
    · rintro ⟨hts, hsupp⟩
      exact ⟨((hs t).1 (Finset.mem_coe.1 hts)).1, hsupp⟩

  have hpt : ∀ u : G, Φ u * F u = ∑ t ∈ s, (C t).indicator (fun u => Φ u * F u) u := by
    intro u
    by_cases hFu : F u = 0
    · rw [hFu, mul_zero]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hu : u ∈ C t
      · rw [Set.indicator_of_mem hu, hFu, mul_zero]
      · rw [Set.indicator_of_notMem hu]
    have hu_ts : u ∈ tsupport F := subset_tsupport _ hFu
    by_cases hH : u ∈ ι.range ⊔ U
    · obtain ⟨_, ⟨a, rfl⟩, w, hw, rfl⟩ := Subgroup.mem_sup.1 hH
      obtain ⟨t₀, ht₀T, ht₀⟩ := hcover a
      have hut₀ : ι a * w ∈ C t₀ := by
        show (ι t₀)⁻¹ * (ι a * w) ∈ U
        have h : (ι t₀)⁻¹ * (ι a * w) = ι (t₀⁻¹ * a) * w := by rw [map_mul, map_inv, mul_assoc]
        rw [h]
        exact U.mul_mem ht₀ hw
      have ht₀s : t₀ ∈ s := (hs t₀).2 ⟨ht₀T, _, hu_ts, hut₀⟩
      rw [Finset.sum_eq_single_of_mem t₀ ht₀s]
      · rw [Set.indicator_of_mem hut₀]
      · intro t hts hne
        rw [Set.indicator_of_notMem]
        intro hut
        exact hne (hdisj t ((hs t).1 hts).1 t₀ ht₀T _ hut hut₀)
    · rw [hchi2 u hH, zero_mul]
      symm
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [Set.indicator_of_notMem]
      intro hut
      apply hH
      rw [← mul_inv_cancel_left (ι t) u]
      exact Subgroup.mul_mem_sup ⟨t, rfl⟩ hut

  have hΦF_int : Integrable (fun u => Φ u * F u) ν :=
    (hΦc.mul hFc).integrable_of_hasCompactSupport hFs.mul_left
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'

  have hcoset : ∀ t : A, ∫ u, (C t).indicator (fun u => Φ u * F u) u ∂ν = (κ : ℂ)⁻¹ * (c * I t) := by
    intro t
    set gt : G → ℂ := fun v => Φ (ι t * v) * F (ι t * v) with hgt
    have hgm : Measurable gt :=
      ((hΦc.comp (continuous_const_mul (ι t))).mul (hFc.comp (continuous_const_mul (ι t)))).measurable
    have hind : ∀ u : G, (C t).indicator (fun u => Φ u * F u) u =
        (U : Set G).indicator gt ((ι t)⁻¹ * u) := by
      intro u
      by_cases hu : u ∈ C t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show (ι t)⁻¹ * u ∈ (U : Set G) from hu),
          hgt]
        simp only [mul_inv_cancel_left]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show (ι t)⁻¹ * u ∉ (U : Set G) from hu)]
    have hNAt := hNA gt hgm
    have hlhs : ∫ z in Θ, gt (N z) ∂μ = c * I t := by
      simp only [hI, hgt]
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [hchi1 t z, mul_assoc]
    calc ∫ u, (C t).indicator (fun u => Φ u * F u) u ∂ν
        = ∫ u, (U : Set G).indicator gt ((ι t)⁻¹ * u) ∂ν := by
          congr 1
          funext u
          exact hind u
      _ = ∫ v, (U : Set G).indicator gt v ∂ν :=
          integral_mul_left_eq_self (fun v => (U : Set G).indicator gt v) (ι t)⁻¹
      _ = ∫ v in (U : Set G), gt v ∂ν := integral_indicator hUopen.measurableSet
      _ = (κ : ℂ)⁻¹ * (c * I t) := by
          rw [← hlhs, hNAt, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]

  have hmain : ∫ u, Φ u * F u ∂ν = (c / κ) * ∑ t ∈ s, I t := by
    calc ∫ u, Φ u * F u ∂ν
        = ∫ u, ∑ t ∈ s, (C t).indicator (fun u => Φ u * F u) u ∂ν := by
          congr 1
          funext u
          exact hpt u
      _ = ∑ t ∈ s, ∫ u, (C t).indicator (fun u => Φ u * F u) u ∂ν :=
          integral_finsetSum s (fun t _ => hΦF_int.indicator (hCmeas t))
      _ = ∑ t ∈ s, (κ : ℂ)⁻¹ * (c * I t) := Finset.sum_congr rfl fun t _ => hcoset t
      _ = (c / κ) * ∑ t ∈ s, I t := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [div_eq_mul_inv]
          ring
  refine ⟨hfin, ?_⟩
  rw [hmain, hfinsum]

end R3FafM6

open R3FafM6 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
        (_hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
        (_hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            ξL ⟨z, Subgroup.mem_top z⟩ = 1)
        (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
        (_hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
          ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
            (∀ z : (AdeleRing (𝓞 K) K)ˣ,
              z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
                ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
            ∀ z : (AdeleRing (𝓞 L) L)ˣ,
              ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
                ξL ⟨z, Subgroup.mem_top z⟩))
        (F : (AdeleRing (𝓞 K) K)ˣ → ℂ) (_hFc : Continuous F) (_hFs : HasCompactSupport F)
        (T : Set Kˣ)
        (_hT : ∀ a : Kˣ, ∃! t : Kˣ, t ∈ T ∧ ∃ b : Lˣ, a = t * Units.map (Algebra.norm K : L →* K) b),
        (T ∩ Function.support fun t : Kˣ =>
            ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL).Finite ∧
        (∑ ξ ∈ Ξ, ∫ u : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ) * F u ∂νZK =
          ((Ξ.card : ℂ) / (κ : ℂ)) *
            ∑ᶠ t ∈ T, ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL) ∧
        (Ξ = ∅ → ∀ t : Kˣ,
          ∫ z in Θ, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              F (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) t *
                (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL = 0) := by
  classical

  obtain ⟨κ, hκ, -, hNA⟩ :=
    NumberField.exists_setLIntegral_comp_idelicNorm_eq_mul_and_setIntegral_comp_idelicNorm_eq_mul
      K L σ hgen νZL νZK Θ hΘ
  refine ⟨κ, hκ, ?_⟩
  intro ξL hξc hξt Ξ hΞ F hFc hFs T hT

  let B := M4aHerbrand.GenuineDescent.genuineBaseChange K L
  let N : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ := B.idelicNorm
  let ιK : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
    Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
  let ιL : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
    Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)
  let χL : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
  let χ : ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) → (AdeleRing (𝓞 K) K)ˣ → ℂ :=
    fun ξ u => ((ξ ⟨u, Subgroup.mem_top u⟩ : ℂˣ) : ℂ)
  let Φ : (AdeleRing (𝓞 K) K)ˣ → ℂ := fun u => ∑ ξ ∈ Ξ, χ ξ u
  haveI : IsCyclic (L ≃ₐ[K] L) := ⟨⟨σ, hgen⟩⟩

  obtain ⟨hchi1, hchi2, -⟩ := NumberField.sum_ideleClassChar_eq_of_comp_idelicNorm_eq K L ξL Ξ hΞ
  have hopen : IsOpen ((N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
    NumberField.isOpen_range_idelicNorm K L B
  have hcompat : ∀ b : Lˣ, ιK (Units.map (Algebra.norm K : L →* K) b) = N (ιL b) := by
    intro b
    ext
    simp only [ιK, ιL, N, M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map]
    exact (M4aHerbrand.GenuineDescent.adelicNorm_genuineBaseChange_algebraMap K L (b : L)).symm
  have hHasse : ∀ a : Kˣ, ιK a ∈ N.range → ∃ b : Lˣ, Units.map (Algebra.norm K : L →* K) b = a := by
    intro a ha
    obtain ⟨b, hb⟩ :=
      NumberField.exists_algebraNorm_eq_of_mem_range_idelicNorm_of_isCyclic K L a ha
    have hb0 : b ≠ 0 := by
      intro h
      apply a.ne_zero
      rw [← hb, h, Algebra.norm_zero]
    refine ⟨Units.mk0 b hb0, Units.ext ?_⟩
    simp only [Units.coe_map, Units.val_mk0]
    exact hb
  have key : ∀ t ∈ T, ∀ t' ∈ T, ιK (t⁻¹ * t') ∈ N.range → t = t' := by
    intro t ht t' ht' hmem
    obtain ⟨b, hb⟩ := hHasse _ hmem
    obtain ⟨t₀, -, huniq⟩ := hT t'
    have e1 : t' = t₀ := huniq t' ⟨ht', 1, by rw [map_one, mul_one]⟩
    have e2 : t = t₀ := huniq t ⟨ht, b, by rw [hb, mul_inv_cancel_left]⟩
    rw [e2, e1]
  have hcover : ∀ a : Kˣ, ∃ t ∈ T, ιK (t⁻¹ * a) ∈ N.range := by
    intro a
    obtain ⟨t, ⟨htT, b, hab⟩, -⟩ := hT a
    refine ⟨t, htT, ιL b, ?_⟩
    rw [← hcompat b, hab, inv_mul_cancel_left]
  have hΦc : Continuous Φ := continuous_finsetSum Ξ fun ξ hξ => ((hΞ ξ).1 hξ).1
  have hchi1' : ∀ (a : Kˣ) (z : (AdeleRing (𝓞 L) L)ˣ), Φ (ιK a * N z) = (Ξ.card : ℂ) * χL z :=
    fun a z => hchi1 a z
  have hchi2' : ∀ u : (AdeleRing (𝓞 K) K)ˣ, u ∉ ιK.range ⊔ N.range → Φ u = 0 :=
    fun u hu => hchi2 u hu
  have hNA' : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
      ∫ z in Θ, g (N z) ∂νZL = κ * ∫ u in ((N.range : Subgroup _) : Set (AdeleRing (𝓞 K) K)ˣ), g u ∂νZK :=
    fun g hg => (hNA g hg).2

  obtain ⟨h1, h2⟩ := engine νZK νZL Θ N ιK T N.range hopen (fun z => ⟨z, rfl⟩) key hcover κ hκ hNA'
    χL Φ hΦc (Ξ.card : ℂ) hchi1' hchi2' F hFc hFs

  have hint : ∀ ξ ∈ Ξ, Integrable (fun u => χ ξ u * F u) νZK := fun ξ hξ =>
    (((hΞ ξ).1 hξ).1.mul hFc).integrable_of_hasCompactSupport hFs.mul_left
  have hLHS : ∑ ξ ∈ Ξ, ∫ u, χ ξ u * F u ∂νZK = ∫ u, Φ u * F u ∂νZK := by
    rw [← integral_finsetSum Ξ hint]
    congr 1
    funext u
    exact (Finset.sum_mul Ξ (fun ξ => χ ξ u) (F u)).symm

  have h3 : Ξ = ∅ → ∀ t : Kˣ, ∫ z in Θ, χL z * F (ιK t * N z) ∂νZL = 0 := by
    intro hΞe t
    have hker : ∃ t₀ : (AdeleRing (𝓞 L) L)ˣ, N t₀ = 1 ∧ ξL ⟨t₀, Subgroup.mem_top t₀⟩ ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hinv : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξL ⟨(M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ.symm.symm z,
              Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩ := by
        intro z
        rw [AlgEquiv.symm_symm]
        set w := (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ z with hw
        have hz : N (w * z⁻¹) = 1 := by
          rw [map_mul, map_inv, hw, idelicNorm_genuineDescentDatum_unitsAct, mul_inv_cancel]
        have h := hcon _ hz
        have hmul : (⟨w * z⁻¹, Subgroup.mem_top (w * z⁻¹)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
            ⟨w, Subgroup.mem_top w⟩ * ⟨z, Subgroup.mem_top z⟩⁻¹ := rfl
        rw [hmul, map_mul, map_inv, mul_inv_eq_one] at h
        exact h
      obtain ⟨ξ, hξc', hξt', hξN⟩ :=
        M4aHerbrand.GenuineDescent.exists_ideleChar_comp_idelicNorm_eq_of_unitsAct_invariant K L
          (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ.symm
          (by rw [AlgEquiv.symm_symm]; exact hgen) ξL hξc hξt hinv
      have hmem : ξ ∈ Ξ := (hΞ ξ).2 ⟨hξc', hξt', hξN⟩
      rw [hΞe] at hmem
      exact Finset.notMem_empty _ hmem
    exact NumberField.setIntegral_ideleChar_mul_comp_idelicNorm_eq_zero_of_exists_idelicNorm_eq_one
      K L σ hgen νZL Θ hΘ ξL hξc hξt hker (fun u => F (ιK t * u))
      (hFc.comp (continuous_const_mul (ιK t))).measurable
  refine ⟨h1, ?_, h3⟩
  rw [← hLHS] at h2
  exact h2

end S_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain
end P2MW
export P2MW.S_NumberField_exists_sum_integral_mul_eq_mul_finsum_setIntegral_comp_idelicNorm_of_isFundamentalDomain (solution)
