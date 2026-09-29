-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.forall_exists_orientedCrossingChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/df45be8a-6c89-5603-8848-8ec2097f2166

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isIntegral_pullback_toBase_specMap
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_or
import Theorems.Thm_ModularCurve_DRModelPackageLevel_not_branchIdeal_le_branchIdeal_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackageLevel_residue_baseGerm_surjective_and_isClosed_crossingPt
import Theorems.Thm_ModularCurve_DRModelPackageLevel_baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk
import Theorems.Thm_ModularCurve_DRModelPackageLevel_branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_span_pair_baseGerm_eq_branchIdeal
import Theorems.Thm_ModularCurve_DRModelPackageLevel_branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm
import Theorems.Thm_ModularCurve_DRModelPackageLevel_range_comp_bcMap_eq_closure_and_isClosed
import Theorems.Thm_IsLocalRing_exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_crossingChart_of_crossingPresentation_stalk
import Theorems.Thm_MvPolynomial_CrossingQuotient_ringKrullDim_le
import Theorems.Thm_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_forall_exists_orientedCrossingChart
p2m_attr_erase "instance" "ModularCurve.eisensteinMaximalIdeal.isPrime ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFinite_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instCommRing_H ModularCurve.JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff ModularCurve.JZeroNeronPrimaryTorsionCore.instFlat_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ ModularCurve.JZeroNeronPrimaryTorsionCore.instFiniteType_H ModularCurve.JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff ModularCurve.JZeroNeronPrimaryTorsionFFModels.instFlat_Hff ModularCurve.JZeroNeronDataPrime.instFiniteΦ ModularCurve.JZeroNeronDataPrime.instAddCommGroupΦ ModularCurve.JZeroNeronDataPrime.instModuleΦ ModularCurve.JZeroNeronData.instAddCommGroupΦ ModularCurve.JZeroNeronData.instModuleΦ ModularCurve.JZeroNeronData.instFiniteΦ AlgebraicGeometry.Scheme.Fppf.instLocallyOfFinitePresentationHomDiscretePUnit AlgebraicGeometry.Scheme.Fppf.instFlatHomDiscretePUnit AlgebraicGeometry.Scheme.instAdditiveAbFunctorOppositeFppfConst AlgebraicGeometry.Scheme.instHasIsosFppfPrecoverage_definitions AlgebraicGeometry.Scheme.Fppf.instFullOverForget AlgebraicGeometry.Scheme.instAdditiveAbSheafFppfSmallFppfTopologyConstantSheaf AlgebraicGeometry.Scheme.hasSheafify_smallFppfTopology AlgebraicGeometry.Scheme.instCategoryFppf AlgebraicGeometry.Scheme.instIsCocontinuousFppfOverForgetSmallFppfTopologyOverFppfTopology AlgebraicGeometry.Scheme.instHasTerminalFppf AlgebraicGeometry.Scheme.instIsMultiplicativeLocallyOfFinitePresentation_definitions AlgebraicGeometry.Scheme.abelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.hasExt_sheaf_smallFppfTopology AlgebraicGeometry.Scheme.instLocallyCoverDenseFppfOverForgetOverFppfTopology AlgebraicGeometry.Scheme.Fppf.instFaithfulOverForget AlgebraicGeometry.Scheme.instAddCommGroupFppfCohomology AlgebraicGeometry.Scheme.instHasPullbacksFppfPrecoverage_definitions FppfCohomologyLES.fppfSheavesIsGrothendieckAbelian ModularCurve.AdmissibleInvariants.instAdd"
p2m_attr_erase "instance" "ModularCurve.AdmissibleInvariants.instZero FppfRepresentableGroupSchemeSheaf.instIsCommMonObjSchemeTensorUnit_definitions FppfRepresentableGroupSchemeSheaf.gateTrivialSheafSectionsSubsingleton ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.JZeroNeronObjectAtP.LevelData.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.mk.injEq ModularCurve.JZeroNeronObjectAtP.mk.sizeOf_spec ModularCurve.JZeroNeronObjectAtP.LevelData.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.injEq ModularCurve.JZeroNeronIdentityComponent.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionFFModels.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionCore.mk.injEq ModularCurve.JZeroNeronPrimaryTorsionSheaf.mk.sizeOf_spec ModularCurve.JZeroNeronPrimaryTorsionInvPins.mk.injEq ModularCurve.JZeroNeronDataPrime.mk.sizeOf_spec ModularCurve.JZeroNeronDataPrime.mk.injEq ModularCurve.JZeroNeronData.mk.injEq ModularCurve.JZeroNeronData.mk.sizeOf_spec ModularCurve.eisensteinEval_heckeGen ModularCurve.modSystem_apply ModularCurve.FppfKummerData.mk.injEq ModularCurve.JKummerRow.mk.injEq ModularCurve.JKummerRow.mk.sizeOf_spec ModularCurve.FppfKummerData.mk.sizeOf_spec FppfCohomologyLES.cohomologyMapAddEquiv_apply FppfCohomologyLES.biprodSESHom_τ₃ FppfCohomologyLES.cohomologyMap_apply FppfCohomologyLES.cohomologyδ_apply FppfCohomologyLES.cohomologyMapAddEquiv_symm_apply FppfCohomologyLES.biprodSESHom_τ₁ ModularCurve.AdmissibleInvariants.zero_h1 ModularCurve.AdmissibleInvariants.add_h0"
p2m_attr_erase "simp" "ModularCurve.AdmissibleInvariants.zero_δ ModularCurve.AdmissibleInvariants.zero_α ModularCurve.AdmissibleInvariants.zero_h0 ModularCurve.AdmissibleInvariants.add_α ModularCurve.AdmissibleInvariants.mk.sizeOf_spec FppfKummerSES.kummerSES_g FppfKummerSES.kummerSES_X₃ ModularCurve.AdmissibleInvariants.genericDefect_zero ModularCurve.AdmissibleInvariants.add_δ ModularCurve.AdmissibleInvariants.add_h1 FppfKummerSES.kummerSES_X₁ ModularCurve.AdmissibleInvariants.mk.injEq ModularCurve.AdmissibleInvariants.eulerDefect_zero FppfKummerSES.kummerSES_X₂ GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

noncomputable section

section Glue

private theorem ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x)
    (U : X.Opens) (hxU : x ∈ U) (s : Γ(X, U)) (hs : X.presheaf.germ U x hxU s ∈ Scheme.branchIdeal h)
    (y : X) (hy : y ∈ closure ({ξ} : Set X)) : y ∉ X.basicOpen s := by
  intro hy'
  have hξU : ξ ∈ U := h.mem_open U.isOpen hxU
  have hgerm : X.presheaf.germ U ξ hξU s ∈ IsLocalRing.maximalIdeal _ := by
    rw [Scheme.branchIdeal, Ideal.mem_comap, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at hs
    exact hs
  have hξ : ξ ∉ X.basicOpen s := fun hh =>
    (IsLocalRing.mem_maximalIdeal _ |>.mp hgerm) ((X.mem_basicOpen s ξ hξU).mp hh)
  obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy (X.basicOpen s) (X.basicOpen s).isOpen hy'
  rw [Set.mem_singleton_iff] at hz2
  subst hz2
  exact hξ hz1

private theorem ECL_Main.range_subset_closure_image_genericPoint {C X : Scheme.{u}} [IsIntegral C] (i : C ⟶ X) :
    Set.range i.base ⊆ closure {i.base (genericPoint C)} := by
  rintro _ ⟨c, rfl⟩
  have hc : c ∈ closure ({genericPoint C} : Set C) := by
    rw [genericPoint_closure]; trivial
  have := image_closure_subset_closure_image i.continuous ⟨c, hc, rfl⟩
  simpa [Set.image_singleton] using this

private theorem ECL_Main.toBase_eq_closedPoint_of_mem_asIdeal {O : Type u} [CommRing O] [IsLocalRing O] (s : O)
    (hs : s ∈ IsLocalRing.maximalIdeal O)
    {X : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of O)) (U : X.Opens)
    (f : (U : Scheme.{u}) ⟶ CrossingQuotient.crossingScheme s)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s))) = U.ι ≫ πX)
    (y : ↥(U : Scheme.{u}))
    (hy : CrossingQuotient.U s ∈ (f.base y).asIdeal ∨ CrossingQuotient.V s ∈ (f.base y).asIdeal)
    (hgen : IsLocalRing.maximalIdeal O = Ideal.span {s} ∨ ∃ (q : O) (e : ℕ), 1 ≤ e ∧ s = q ^ e ∧ IsLocalRing.maximalIdeal O = Ideal.span {q}) :
    πX.base (U.ι.base y) = IsLocalRing.closedPoint O := by

  have hsP : algebraMap O (CrossingQuotient O s) s ∈ (f.base y).asIdeal := by
    rw [← CrossingQuotient.U_mul_V]
    rcases hy with h | h
    · exact Ideal.mul_mem_right _ _ h
    · exact Ideal.mul_mem_left _ _ h
  have h1 : πX.base (U.ι.base y) =
      (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O s)))).base (f.base y) := by
    rw [← Scheme.Hom.comp_apply, ← hf, Scheme.Hom.comp_apply]
  rw [h1]
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal = IsLocalRing.maximalIdeal O
  have hprime : (Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal).IsPrime := Ideal.comap_isPrime _ _
  symm
  refine (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le hprime.ne_top ?_
  have hsO : s ∈ Ideal.comap (algebraMap O (CrossingQuotient O s)) (f.base y).asIdeal := hsP
  rcases hgen with hm | ⟨q, e, he, rfl, hm⟩
  · rw [hm, Ideal.span_singleton_le_iff_mem]; exact hsO
  · rw [hm, Ideal.span_singleton_le_iff_mem]
    exact hprime.mem_of_pow_mem e hsO

end Glue

set_option maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)

    (bc : DRLevel.fibre (N₀ := N₀) (toκ.comp ρO) ⟶
      pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hrat : ∀ x : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
          (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base x) :
    ∀ n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).Opens)
        (_ : (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((q : ℕ) : O) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((q : ℕ) : O) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) ≫ 𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ bc).base →
            CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ bc).base →
            CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) := by
  intro n

  have hbc : bc = DRLevel.bcMap (N₀ := N₀) ρO toκ := by
    apply pullback.hom_ext
    · rw [hbc₁, DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
    · rw [hbc₂, DRLevel.bcMap, pullback.map, pullback.lift_snd]
  subst hbc

  obtain ⟨hinf, hzero⟩ : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n ∧ 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n :=
    ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt N₀ q hqN 𝔛 O ρO κ toκ n
  haveI : IsIntegral (DRLevel.XO (N₀ := N₀) ρO) := ModularCurve.DRModelPackageLevel.isIntegral_pullback_toBase_specMap N₀ q hqN 𝔛 O hϖ ρO
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  have hpO : Irreducible ((q : ℕ) : O) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hϖ

  have hPQ := ModularCurve.DRModelPackageLevel.branchIdeal_xiInf_sup_branchIdeal_xiZero_eq_maximalIdeal N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  obtain ⟨hQP, hPQ'⟩ := ModularCurve.DRModelPackageLevel.not_branchIdeal_le_branchIdeal_crossingPt N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ModularCurve.DRModelPackageLevel.exists_span_pair_baseGerm_eq_branchIdeal N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  have hIU := ModularCurve.DRModelPackageLevel.branchIdeal_xiInf_inf_branchIdeal_xiZero_eq_span_baseGerm N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  obtain ⟨t, t', htt', ht, htunit⟩ := ModularCurve.DRModelPackageLevel.exists_stalk_mul_eq_baseGerm_pow_and_isUnit_stalkSpecializes_of_crossing N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  obtain ⟨hϖnz, hstalk2⟩ :=
    ModularCurve.DRModelPackageLevel.baseGerm_mem_nonZeroDivisors_and_two_le_ringKrullDim_stalk N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero
  obtain ⟨hres, hxcl⟩ :=
    ModularCurve.DRModelPackageLevel.residue_baseGerm_surjective_and_isClosed_crossingPt N₀ q hqN 𝔛 O ρO hϖ κ toκ n hinf hzero (hrat n)
  have hab : a * b ∈ Ideal.span {DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O)} := by
    rw [← hIU]
    refine ⟨?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (ha ▸ Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (hb ▸ Ideal.subset_span (by simp))

  obtain ⟨e, g₀, gi, he1, -, hrel, hg₀, hgi⟩ :
      ∃ (e : ℕ) (g₀ gi : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)), 1 ≤ e ∧ e ≤ 12 ∧
        g₀ * gi = DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O) ^ e ∧
        Ideal.span {g₀, DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O)} = Scheme.branchIdeal hzero ∧
        Ideal.span {gi, DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O)} = Scheme.branchIdeal hinf := by
    rcases htunit with hu | hu
    ·
      have htQ : t ∉ Scheme.branchIdeal hinf := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hinf t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hPQ' (by rwa [sup_comm]) hb ha
          (by rwa [mul_comm]) htQ ht htt'
      exact ⟨e, u, v, he1, he, huv, hu', hv'⟩
    ·
      have htQ : t ∉ Scheme.branchIdeal hzero := fun h =>
        (IsLocalRing.notMem_maximalIdeal.mpr hu) ((Scheme.mem_branchIdeal_iff hzero t).mp h)
      obtain ⟨e, u, v, he1, he, huv, hu', hv'⟩ :=
        IsLocalRing.exists_mul_eq_pow_and_span_pair_eq_of_sup_eq_maximalIdeal hϖnz hQP hPQ ha hb hab htQ ht htt'
      exact ⟨e, v, u, he1, he, by rw [mul_comm]; exact huv, hv', hu'⟩

  obtain ⟨hdom, hic⟩ := MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed (W := O) (((q : ℕ) : O) ^ e)
      (pow_ne_zero e hpO.ne_zero)
  haveI := hdom; haveI := hic
  haveI : LocallyOfFiniteType (DRLevel.XO.toBase (N₀ := N₀) ρO) := by
    haveI := 𝔛.isProper
    infer_instance
  haveI : IsLocallyNoetherian (DRLevel.XO (N₀ := N₀) ρO) := LocallyOfFiniteType.isLocallyNoetherian (DRLevel.XO.toBase (N₀ := N₀) ρO)
  have hmax : IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) =
      Ideal.span {DRModelPackageLevel.baseGerm ρO (𝔛.crossingPt ρO toκ n) ((q : ℕ) : O), g₀, gi} := by
    rw [← hPQ, ← hgi, ← hg₀, ← Ideal.span_union]
    congr 1
    ext z
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hdim : ringKrullDim (CrossingQuotient O (((q : ℕ) : O) ^ e)) ≤
      ringKrullDim ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) := by
    refine (MvPolynomial.CrossingQuotient.ringKrullDim_le O 1 ?_ _ (pow_ne_zero e hpO.ne_zero)).trans ?_
    · rw [IsDiscreteValuationRing.ringKrullDim_eq_one O, Nat.cast_one]
    · refine le_trans ?_ hstalk2
      norm_num
  obtain ⟨U, hxU, gU, hU, f, hgerm_g, hgerm_h, -, hover, hfib, hflat, hdictU, hdictV⟩ :=
    AlgebraicGeometry.Scheme.exists_crossingChart_of_crossingPresentation_stalk ((q : ℕ) : O) e
      (DRLevel.XO.toBase (N₀ := N₀) ρO) (𝔛.crossingPt ρO toκ n) hxcl g₀ gi hrel hmax hres hdim

  have hvan_g : ∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), 𝔛.ξzero ρO toκ ⤳ y → y ∉ (DRLevel.XO (N₀ := N₀) ρO).basicOpen gU := by
    intro y hy
    refine ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal hzero U hxU gU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_g, ← hg₀]; exact Ideal.subset_span (by simp)
  have hvan_h : ∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), 𝔛.ξinf ρO toκ ⤳ y → y ∉ (DRLevel.XO (N₀ := N₀) ρO).basicOpen hU := by
    intro y hy
    refine ECL_Main.not_mem_basicOpen_of_germ_mem_branchIdeal hinf U hxU hU ?_ y (specializes_iff_mem_closure.mp hy)
    rw [hgerm_h, ← hgi]; exact Ideal.subset_span (by simp)
  have hrange_inf : ∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base →
      𝔛.ξinf ρO toκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (ECL_Main.range_subset_closure_image_genericPoint (C := DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) (i := 𝔛.comp κ (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ) hy)
  have hrange_zero : ∀ y : ↥(DRLevel.XO (N₀ := N₀) ρO), y ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base →
      𝔛.ξzero ρO toκ ⤳ y := fun y hy => specializes_iff_mem_closure.mpr
    (ECL_Main.range_subset_closure_image_genericPoint (C := DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) (i := 𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ) hy)

  have hcover : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∨ CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) →
      𝔛.ξinf ρO toκ ⤳ U.ι.base y ∨ 𝔛.ξzero ρO toκ ⤳ U.ι.base y := by
    intro y hy
    have hbase : (DRLevel.XO.toBase (N₀ := N₀) ρO).base (U.ι.base y) = IsLocalRing.closedPoint O := by
      refine ECL_Main.toBase_eq_closedPoint_of_mem_asIdeal (((q : ℕ) : O) ^ e) ?_ (DRLevel.XO.toBase (N₀ := N₀) ρO) U f hover y hy
        (Or.inr ⟨(q : O), e, he1, rfl, hϖ⟩)
      rw [hϖ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) e he1
    refine ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_or N₀ q hqN 𝔛 O ρO hϖ κ toκ (U.ι.base y) ?_
    intro hmem
    have hmem' : (DRLevel.XO.toBase (N₀ := N₀) ρO).base (U.ι.base y) ∈
        (PrimeSpectrum.basicOpen ((q : ℕ) : O) : (Spec (CommRingCat.of O)).Opens) := hmem
    rw [hbase] at hmem'
    refine (PrimeSpectrum.mem_basicOpen _ _).mp hmem' ?_
    change ((q : ℕ) : O) ∈ IsLocalRing.maximalIdeal O
    rw [hϖ]; exact Ideal.mem_span_singleton_self _
  refine ⟨e, he1, U, hxU, f, hover, hfib, hflat, ?_, ?_, ?_, ?_⟩
  ·
    intro y hV

    have hhU : U.ι.base y ∉ (DRLevel.XO (N₀ := N₀) ρO).basicOpen hU := (hdictV y).mp hV
    rcases hcover y (Or.inr hV) with h | h
    · rw [(ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 0).1]
      exact specializes_iff_mem_closure.mp h
    · have hUy : CrossingQuotient.U (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictU y).mpr (hvan_g _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt ρO toκ n := (hfib y).mp ⟨hUy, hV⟩
      rw [hyx]
      exact ⟨(pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · intro y hUm
    rcases hcover y (Or.inl hUm) with h | h
    · have hVy : CrossingQuotient.V (((q : ℕ) : O) ^ e) ∈ (f.base y).asIdeal := (hdictV y).mpr (hvan_h _ h)
      have hyx : U.ι.base y = 𝔛.crossingPt ρO toκ n := (hfib y).mp ⟨hUm, hVy⟩
      rw [hyx]
      refine ⟨(pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition_assoc]
    · rw [(ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ 1).1]
      exact specializes_iff_mem_closure.mp h
  · intro y hy
    exact (hdictV y).mpr (hvan_h _ (hrange_inf _ hy))
  · intro y hy
    exact (hdictU y).mpr (hvan_g _ (hrange_zero _ hy))

end

end S_ModularCurve_DRModelPackageLevel_forall_exists_orientedCrossingChart
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_forall_exists_orientedCrossingChart (solution)
