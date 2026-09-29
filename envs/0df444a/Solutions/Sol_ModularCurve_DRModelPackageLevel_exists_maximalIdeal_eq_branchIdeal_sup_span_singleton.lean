-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_maximalIdeal_eq_branchIdeal_sup_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/08f38428-cc3e-5738-9f65-102581c4ace4

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevelCrossingFrame
import Definitions.Def_AlgebraicGeometry_RegularLocalRingFaithfullyFlatDescent
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_DRModelPackageLevel_finite_crossings
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed
import Theorems.Thm_ModularCurve_DRModelPackageLevel_range_comp_bcMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModelPackageLevel_preimage_closure_image_range_comp_eq_of_comp_fst_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry ModularCurve"

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

namespace RingHom.Flat

private theorem _root_.AlgebraicGeometry.RingHom.Flat.map_mem_nonZeroDivisors {A B : Type*} [CommRing A] [CommRing B] {φ : A →+* B}
    (hφ : φ.Flat) {r : A} (hr : r ∈ nonZeroDivisors A) : φ r ∈ nonZeroDivisors B := by
  letI := φ.toAlgebra
  haveI : Module.Flat A B := hφ
  have hsm : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have key : ∀ x : B, φ r * x = 0 → x = 0 := fun x hx =>
    hsm ((Algebra.smul_def r x).trans (hx.trans (smul_zero r).symm))
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x ((mul_comm _ _).trans hx)⟩

end RingHom.Flat
p2m_export "AlgebraicGeometry" "RingHom.Flat.map_mem_nonZeroDivisors"
section

variable {T S Z : Scheme.{u}} (π : T ⟶ S) [Flat π] [IsIntegral S]
  (V : S.Opens) (hV : (V : Set S).Nonempty)
  (j : Z ⟶ T) [IsOpenImmersion j] [IsReduced Z] (hj : π ⁻¹ᵁ V ≤ j.opensRange)

include hV hj in

theorem isReduced_presheaf_obj_of_flat_of_le_preimage
    (W : S.affineOpens) (Q : T.affineOpens) (hle : (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens))
    (hQ : ((Q : T.Opens) : Set T).Nonempty) :
    _root_.IsReduced Γ(T, Q) := by

  obtain ⟨t, ht⟩ := hQ
  haveI : Nonempty (W : S.Opens) := ⟨⟨π.base t, hle ht⟩⟩
  haveI : IsDomain Γ(S, W) := inferInstance

  obtain ⟨w, hwW, hwV⟩ : ((W : S.Opens) ⊓ V : S.Opens).1.Nonempty :=
    nonempty_preirreducible_inter (W : S.Opens).2 V.2 ⟨π.base t, hle ht⟩ hV
  obtain ⟨r, hrV, hwr⟩ := W.2.exists_basicOpen_le ⟨w, hwV⟩ hwW
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hwr
    exact hwr
  have hr : r ∈ nonZeroDivisors Γ(S, W) := mem_nonZeroDivisors_of_ne_zero hr0

  let φ := π.appLE W Q hle
  have hφ : φ.hom.Flat := HasRingHomProperty.appLE (P := @Flat) (f := π) inferInstance W Q hle
  set s : Γ(T, Q) := φ.hom r with hs
  have hsreg : s ∈ nonZeroDivisors Γ(T, Q) := hφ.map_mem_nonZeroDivisors hr

  haveI := Q.2.isLocalization_basicOpen s
  have hinj : Function.Injective (algebraMap Γ(T, Q) Γ(T, T.basicOpen s)) :=
    IsLocalization.injective (M := Submonoid.powers s) _ ((Submonoid.powers_le).mpr hsreg)

  have hbo : T.basicOpen s ≤ π ⁻¹ᵁ V := by
    have h1 : T.basicOpen s = (Q : T.Opens) ⊓ π ⁻¹ᵁ (S.basicOpen r) := by
      rw [hs]
      exact Scheme.basicOpen_appLE π (Q : T.Opens) (W : S.Opens) hle r
    rw [h1]
    exact inf_le_right.trans (fun x hx => hrV hx)
  have hbo' : T.basicOpen s ≤ j.opensRange := hbo.trans hj
  haveI : _root_.IsReduced Γ(T, T.basicOpen s) := by
    have e : Γ(T, T.basicOpen s) ≅ Γ(Z, j ⁻¹ᵁ (T.basicOpen s)) := by
      have h1 : j ''ᵁ (j ⁻¹ᵁ (T.basicOpen s)) = T.basicOpen s := by
        ext1
        change j.base '' (j.base ⁻¹' (T.basicOpen s : Set T)) = (T.basicOpen s : Set T)
        rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
        exact fun x hx => hbo' hx
      exact (T.presheaf.mapIso (eqToIso h1).op) ≪≫ (j.appIso (j ⁻¹ᵁ (T.basicOpen s)))
    exact isReduced_of_injective e.commRingCatIsoToRingEquiv e.commRingCatIsoToRingEquiv.injective
  exact isReduced_of_injective _ hinj

include hV hj in

theorem isReduced_of_flat_of_isReduced_preimage : IsReduced T := by
  have key : ∀ t : T, ∃ (W : S.affineOpens) (Q : T.affineOpens),
      t ∈ (Q : T.Opens) ∧ (Q : T.Opens) ≤ π ⁻¹ᵁ (W : S.Opens) := by
    intro t
    obtain ⟨W, hWB, htW, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
      (show π.base t ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨Q, hQB, htQ, hQle⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens)
      (show t ∈ π ⁻¹ᵁ W from htW)
    exact ⟨⟨W, hWB⟩, ⟨Q, hQB⟩, htQ, hQle⟩
  choose W Q htQ hQle using key
  have hcov : ⨆ t : T, (Q t : T.Opens) = ⊤ := eq_top_iff.mpr fun t _ => Opens.mem_iSup.mpr ⟨t, htQ t⟩
  haveI : ∀ t : T, IsReduced ((T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov).X t) :=
    fun t => by
      change IsReduced ((Q t : T.Opens) : Scheme.{u})
      haveI : _root_.IsReduced Γ(T, Q t) :=
        isReduced_presheaf_obj_of_flat_of_le_preimage π V hV j hj (W t) (Q t) (hQle t) ⟨t, htQ t⟩
      haveI : _root_.IsReduced Γ((Q t : T.Opens), ⊤) :=
        isReduced_of_injective (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv
          (Q t : T.Opens).topIso.commRingCatIsoToRingEquiv.injective
      exact isReduced_of_isAffine_isReduced _
  exact IsReduced.of_openCover _ (T.openCoverOfIsOpenCover (fun t : T => ((Q t : T.Opens) : T.Opens)) hcov)

end

end AlgebraicGeometry

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

section monoPullback

variable {C : Type*} [Category C] {S A B Z : C} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i]
  [HasPullback s a] [HasPullback (s ≫ i) (a ≫ i)]

noncomputable def pullbackCompMonoIso : pullback (s ≫ i) (a ≫ i) ≅ pullback s a where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _)
    ((cancel_mono i).mp (by simpa only [Category.assoc] using pullback.condition))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_hom_fst : (pullbackCompMonoIso s a i).hom ≫ pullback.fst s a = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_hom_snd : (pullbackCompMonoIso s a i).hom ≫ pullback.snd s a = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_fst : (pullbackCompMonoIso s a i).inv ≫ pullback.fst _ _ = pullback.fst s a :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc]
theorem pullbackCompMonoIso_inv_snd : (pullbackCompMonoIso s a i).inv ≫ pullback.snd _ _ = pullback.snd s a :=
  pullback.lift_snd _ _ _

end monoPullback

theorem flat_pullback_fst_comp_mono {S A B Z : Scheme.{u}} (s : S ⟶ B) (a : A ⟶ B) (i : B ⟶ Z) [Mono i] [Flat a] :
    Flat (pullback.fst (s ≫ i) (a ≫ i)) := by
  rw [← pullbackCompMonoIso_hom_fst s a i]
  infer_instance

section factor

variable {S : Scheme.{u}} {O : Type u} [CommRing O] (f : S ⟶ Spec (CommRingCat.of O)) (I : Ideal O)

noncomputable def toΓ : O →+* Γ(S, ⊤) :=
  (f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom

theorem toΓ_apply (r : O) : toΓ f r = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv r) := rfl

theorem toΓ_eq_zero_of_preimage_basicOpen_eq_bot [IsReduced S] (r : O)
    (hr : f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥) : toΓ f r = 0 := by
  rw [← basicOpen_eq_bot_iff, toΓ_apply, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hr

variable (hI : ∀ r ∈ I, f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥)

include hI in

theorem exists_lift_specQuotient [IsReduced S] :
    ∃ f' : S ⟶ Spec (CommRingCat.of (O ⧸ I)),
      f' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f := by
  have hker : ∀ r ∈ I, toΓ f r = 0 := fun r hr => toΓ_eq_zero_of_preimage_basicOpen_eq_bot f r (hI r hr)
  let φ : O ⧸ I →+* Γ(S, ⊤) := Ideal.Quotient.lift I (toΓ f) hker
  refine ⟨S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

  rw [toΓ, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality f, Category.assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

end factor

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

section basechange

variable {X S S' S'' : Scheme.{u}} (f : X ⟶ S) (g' : S' ⟶ S) (g'' : S'' ⟶ S) (i : S'' ⟶ S') (hi : i ≫ g' = g'')

theorem isPullback_map_snd_snd :
    IsPullback (pullback.map f g'' f g' (𝟙 X) i (𝟙 S) (by simp) (by rw [Category.comp_id, hi]))
      (pullback.snd f g'') (pullback.snd f g') i := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f g') (v₁₃ := f) (h₂₂ := g') ?_ ?_ (IsPullback.of_hasPullback f g')
  · rw [pullback.lift_fst, Category.comp_id, hi]
    exact IsPullback.of_hasPullback f g''
  · rw [pullback.lift_snd]

end basechange
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

section strict

variable {S Y X Xκ B Bκ R : Scheme.{u}}

theorem exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq
    (ιS : S ⟶ Y) (toDR : Y ⟶ X) (πX : X ⟶ B) (toBase : Y ⟶ B) (hbase : toDR ≫ πX = toBase)
    (b : Bκ ⟶ B) (p₁ : Xκ ⟶ X) (p₂ : Xκ ⟶ Bκ) (hP : IsPullback p₁ p₂ πX b)
    (c : R ⟶ Xκ) [IsClosedImmersion c] [IsReduced R] [IsClosedImmersion (ιS ≫ toDR)]
    (hrange : p₁.base ⁻¹' Set.range (ιS ≫ toDR).base = Set.range c.base)
    [IsReduced (pullback (ιS ≫ toBase) b)] :
    ∃ e : pullback (ιS ≫ toBase) b ⟶ R,
      IsIso e ∧ e ≫ c ≫ p₂ = pullback.snd _ _ ∧ e ≫ c ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := by

  have hw : (pullback.fst (ιS ≫ toBase) b ≫ ιS ≫ toDR) ≫ πX = pullback.snd (ιS ≫ toBase) b ≫ b := by
    simp only [Category.assoc, hbase]
    exact pullback.condition
  let τ : pullback (ιS ≫ toBase) b ⟶ Xκ := hP.lift (pullback.fst _ _ ≫ ιS ≫ toDR) (pullback.snd _ _) hw
  have hτ₁ : τ ≫ p₁ = pullback.fst _ _ ≫ ιS ≫ toDR := hP.lift_fst _ _ _
  have hτ₂ : τ ≫ p₂ = pullback.snd _ _ := hP.lift_snd _ _ _

  let u : pullback (ιS ≫ toBase) b ⟶ pullback (ιS ≫ toDR) p₁ := pullback.lift (pullback.fst _ _) τ hτ₁.symm
  have hv : pullback.fst (ιS ≫ toDR) p₁ ≫ ιS ≫ toBase = (pullback.snd (ιS ≫ toDR) p₁ ≫ p₂) ≫ b := by
    rw [← hbase, Category.assoc, ← hP.w, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
      Category.assoc, Category.assoc]
  let v : pullback (ιS ≫ toDR) p₁ ⟶ pullback (ιS ≫ toBase) b :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p₂) hv
  have hvτ : v ≫ τ = pullback.snd (ιS ≫ toDR) p₁ := by
    apply hP.hom_ext
    · rw [Category.assoc, hτ₁, ← Category.assoc, pullback.lift_fst, pullback.condition]
    · rw [Category.assoc, hτ₂, pullback.lift_snd]
  have huv : u ≫ v = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, hτ₂, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, hvτ, Category.id_comp]
  haveI : IsIso u := ⟨⟨v, huv, hvu⟩⟩
  have hu : u ≫ pullback.snd (ιS ≫ toDR) p₁ = τ := pullback.lift_snd _ _ _

  haveI : IsClosedImmersion τ := by rw [← hu]; infer_instance
  have hsurj : Function.Surjective u.base := u.homeomorph.surjective
  have hτrange : Set.range τ.base = Set.range c.base := by
    rw [← hrange, ← hu, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_snd]
  obtain ⟨e, he⟩ := IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq τ c hτrange
  exact ⟨e.hom, inferInstance, by rw [← Category.assoc, he, hτ₂], by rw [← Category.assoc, he, hτ₁]⟩

end strict
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

section chart

variable {U Se Res F : Scheme.{u}} (f : U ⟶ Se) (ρ : Res ⟶ Se) (lam : F ⟶ Res)

theorem pullback_fst_snd_comp_fst_eq :
    pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ =
      (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.fst f (lam ≫ ρ) := by
  rw [pullbackLeftPullbackSndIso_hom_fst]

scoped instance isClosedImmersion_pullback_fst_snd_comp_fst [IsClosedImmersion (lam ≫ ρ)] :
    IsClosedImmersion (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ) := by
  rw [pullback_fst_snd_comp_fst_eq]
  infer_instance

theorem range_pullback_fst_snd_comp_fst :
    Set.range (pullback.fst (pullback.snd f ρ) lam ≫ pullback.fst f ρ).base =
      f.base ⁻¹' Set.range (lam ≫ ρ).base := by
  have hsurj : Function.Surjective (pullbackLeftPullbackSndIso f ρ lam).hom.base :=
    (pullbackLeftPullbackSndIso f ρ lam).hom.homeomorph.surjective
  rw [pullback_fst_snd_comp_fst_eq, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

scoped instance etale_pullback_snd_snd [Etale f] : Etale (pullback.snd (pullback.snd f ρ) lam) := by
  have : pullback.snd (pullback.snd f ρ) lam = (pullbackLeftPullbackSndIso f ρ lam).hom ≫ pullback.snd f (lam ≫ ρ) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
  rw [this]
  infer_instance

end chart
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry CategoryTheory TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen Hom.stalkSpecializes_stalkMap IdealSheafData.coe_support_vanishingIdeal Opens.range_ι Hom mk Γ empty Pullback.range_fst topIso IdealSheafData.range_subschemeι toSpecΓ_naturality IdealSheafData.vanishingIdeal functionField basicOpen_zero Hom.comp_base Pullback.range_snd affineOpens basicOpen basicOpen_appLE preimage_basicOpen_top openCoverOfIsOpenCover Opens.ι isBasis_affineOpens Opens residue Hom.id_base Pullback.exists_preimage_pullback restrict Hom.comp_apply IdealSheafData ΓSpecIso toSpecΓ branchIdeal"
namespace IdealSheafData
p2m_export "AlgebraicGeometry.Scheme.IdealSheafData" "radical coe_support_vanishingIdeal mk map subscheme range_subschemeι map_id vanishingIdeal vanishingIdeal_ideal ideal map_comp subschemeι comap subschemeCover support"
p2m_open "AlgebraicGeometry.Scheme.IdealSheafData AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem isReduced_Spec_of_isReduced (R : Type u) [CommRing R] [_root_.IsReduced R] :
    IsReduced (Spec (CommRingCat.of R)) := by
  haveI : _root_.IsReduced Γ(Spec (CommRingCat.of R), ⊤) :=
    isReduced_of_injective (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isAffine_isReduced _

theorem isReduced_subscheme_of_isRadical (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).IsRadical) : IsReduced I.subscheme := by
  haveI : ∀ i, IsReduced (I.subschemeCover.openCover.X i) := fun (U : X.affineOpens) => by
    change IsReduced (Spec (CommRingCat.of (Γ(X, (U : X.Opens)) ⧸ I.ideal U)))
    haveI : _root_.IsReduced (Γ(X, (U : X.Opens)) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (hI U)
    exact isReduced_Spec_of_isReduced _
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

scoped instance isReduced_subscheme_vanishingIdeal (Z : Closeds X) : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_of_isRadical _ fun U => by
    rw [vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isIntegral_subscheme_vanishingIdeal_closure_singleton (x : X) :
    IsIntegral (vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme := by
  set I : X.IdealSheafData := vanishingIdeal ⟨closure {x}, isClosed_closure⟩
  have hsupp : (I.support : Set X) = closure {x} := by
    rw [coe_support_vanishingIdeal]; rfl

  have hx : x ∈ Set.range I.subschemeι.base := by
    rw [range_subschemeι, hsupp]; exact subset_closure rfl
  obtain ⟨s, hs⟩ := hx

  have hind : Topology.IsInducing I.subschemeι.base := I.subschemeι.isClosedEmbedding.isInducing
  have hgen : closure ({s} : Set I.subscheme) = Set.univ := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hs, ← hsupp, ← range_subschemeι,
      Set.preimage_range]
  haveI : IrreducibleSpace I.subscheme := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hgen]
    exact isIrreducible_singleton.closure
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IdealSheafData
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

theorem isGenericPoint_image_genericPoint {R X : Scheme.{u}} [IsIntegral R] (h : R ⟶ X) :
    IsGenericPoint (h.base (genericPoint R)) (closure (Set.range h.base)) := by
  have := (genericPoint_spec R).image h.continuous
  rwa [Set.image_univ] at this

theorem range_specMap_of_ker_eq_maximalIdeal {O κ : Type u} [CommRing O] [IsLocalRing O] [Field κ]
    (φ : O →+* κ) (hker : RingHom.ker φ = IsLocalRing.maximalIdeal O) :
    Set.range (Spec.map (CommRingCat.ofHom φ)).base = {IsLocalRing.closedPoint O} := by
  have key : ∀ y : PrimeSpectrum κ, (Spec.map (CommRingCat.ofHom φ)).base y = IsLocalRing.closedPoint O := by
    intro y
    apply PrimeSpectrum.ext
    have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    change Ideal.comap φ y.asIdeal = IsLocalRing.maximalIdeal O
    rw [hy, ← RingHom.ker_eq_comap_bot, hker]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, key _⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact key y

theorem IsPullback.range_fst' {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective h.isoPullback.hom.base := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Pullback.range_fst]

theorem iff_mem_closure_of_orientation {R Xκ X : Scheme.{u}} (c : R ⟶ Xκ) (bcm : Xκ ⟶ X) {U : X.Opens}
    (P : U → Prop)
    (hfwd : ∀ y : U, P y → (y : X) ∈ Set.range (c ≫ bcm).base)
    (hconv : ∀ y : U, (y : X) ∈ Set.range (c ≫ bcm).base → P y)
    (hdesc : bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) = Set.range c.base)
    (hfib : closure (Set.range (c ≫ bcm).base) ⊆ Set.range bcm.base) (y : U) :
    P y ↔ (y : X) ∈ closure (Set.range (c ≫ bcm).base) := by
  have him : Set.range (c ≫ bcm).base = bcm.base '' Set.range c.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  constructor
  · exact fun h => subset_closure (hfwd y h)
  · intro h
    apply hconv
    obtain ⟨r, hr⟩ := hfib h
    rw [him] at h ⊢
    have hr' : r ∈ bcm.base ⁻¹' closure (bcm.base '' Set.range c.base) := by
      rw [Set.mem_preimage, hr]; exact h
    rw [hdesc] at hr'
    exact ⟨r, hr', hr⟩

theorem closure_subset_preimage_singleton {X B : Scheme.{u}} (π : X ⟶ B) {s : Set X} {b : B}
    (hb : IsClosed ({b} : Set B)) (hs : s ⊆ π.base ⁻¹' {b}) : closure s ⊆ π.base ⁻¹' {b} :=
  closure_minimal hs (hb.preimage π.continuous)

theorem preimage_basicOpen_eq_bot_of_forall_eq_closedPoint {S : Scheme.{u}} {O : Type u} [CommRing O] [IsLocalRing O]
    (f : S ⟶ Spec (CommRingCat.of O)) (hf : ∀ s : S, f.base s = IsLocalRing.closedPoint O) (r : O)
    (hr : r ∈ IsLocalRing.maximalIdeal O) :
    f ⁻¹ᵁ (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of O)).Opens) = ⊥ := by
  ext s
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hs
  have hs' : f.base s ∈ PrimeSpectrum.basicOpen r := hs
  rw [hf s] at hs'
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hs' hr

theorem forall_comp_eq_of_range_eq_closure {S Y B : Scheme.{u}} (ιS : S ⟶ Y) (g : Y ⟶ B) {y : Y} {b : B}
    (hS : Set.range ιS.base = closure {y}) (hy : g.base y = b) (hb : IsClosed ({b} : Set B)) (s : S) :
    (ιS ≫ g).base s = b := by
  have h1 : closure {y} ⊆ g.base ⁻¹' {b} :=
    closure_subset_preimage_singleton g hb (by rintro _ rfl; exact hy)
  have h2 : ιS.base s ∈ closure {y} := by rw [← hS]; exact ⟨s, rfl⟩
  exact h1 h2

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

section

variable {E F B Bκ : Scheme.{u}} (sE : E ⟶ B) (sF : F ⟶ B) (φ : E ≅ F) (hφ : φ.hom ≫ sF = sE) (b : Bκ ⟶ B)

noncomputable def pullbackIsoOfIsoOver : pullback sE b ≅ pullback sF b :=
  pullback.congrHom hφ.symm rfl ≪≫ (pullbackRightPullbackFstIso sF b φ.hom).symm ≪≫
    asIso (pullback.snd φ.hom (pullback.fst sF b))

@[reassoc]
theorem pullbackIsoOfIsoOver_hom_snd :
    (pullbackIsoOfIsoOver sE sF φ hφ b).hom ≫ pullback.snd sF b = pullback.snd sE b := by
  simp only [pullbackIsoOfIsoOver, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem pullbackIsoOfIsoOver_hom_fst :
    (pullbackIsoOfIsoOver sE sF φ hφ b).hom ≫ pullback.fst sF b = pullback.fst sE b ≫ φ.hom := by
  simp only [pullbackIsoOfIsoOver, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc, pullback.congrHom_hom, pullback.lift_fst_assoc,
    Category.comp_id]

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

theorem exists_iso_pullback_of_iso_over {E F B Bκ MC : Scheme.{u}} (sE : E ⟶ B) (sF : F ⟶ B) (b : Bκ ⟶ B)
    (φ : E ≅ F) (hφ : φ.hom ≫ sF = sE) (tM : MC ⟶ Bκ)
    (e : MC ≅ pullback sF b) (he : e.hom ≫ pullback.snd sF b = tM) :
    ∃ e' : MC ⟶ pullback sE b, IsIso e' ∧ e' ≫ pullback.snd sE b = tM := by
  refine ⟨e.hom ≫ (pullbackIsoOfIsoOver sE sF φ hφ b).inv, inferInstance, ?_⟩
  rw [Category.assoc, ← he]
  congr 1
  rw [Iso.inv_comp_eq, pullbackIsoOfIsoOver_hom_snd]

section liftOfIsIso

variable {F Res Yn : Scheme.{u}} (i : F ⟶ Res) (g : Yn ⟶ Res) [IsIso (pullback.fst i g)]

noncomputable def liftOfIsIso : F ⟶ Yn := inv (pullback.fst i g) ≫ pullback.snd i g

@[reassoc (attr := simp)]
theorem liftOfIsIso_comp : liftOfIsIso i g ≫ g = i := by
  rw [liftOfIsIso, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

scoped instance [IsClosedImmersion i] : IsClosedImmersion (liftOfIsIso i g) := by
  haveI : IsClosedImmersion (pullback.snd i g) := MorphismProperty.pullback_snd (P := @IsClosedImmersion) _ _ inferInstance
  rw [liftOfIsIso]; infer_instance

theorem range_liftOfIsIso : Set.range (liftOfIsIso i g).base = g.base ⁻¹' Set.range i.base := by
  have hsurj : Function.Surjective (inv (pullback.fst i g)).base := (inv (pullback.fst i g)).homeomorph.surjective
  rw [liftOfIsIso, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
    Scheme.Pullback.range_snd]

end liftOfIsIso
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

theorem exists_iso_of_range_eq_image {E F Yn Y : Scheme.{u}} (ιE : E ⟶ Y) [IsClosedImmersion ιE] [IsReduced E]
    (lam' : F ⟶ Yn) [IsClosedImmersion lam'] [IsReduced F] (ι : Yn ⟶ Y) [IsOpenImmersion ι]
    (hrange : Set.range ιE.base = ι.base '' Set.range lam'.base) :
    ∃ φ : E ≅ F, φ.hom ≫ lam' ≫ ι = ιE := by
  have hr : Set.range (lam' ≫ ι).base = Set.range ιE.base := by
    rw [hrange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  haveI : IsClosedImmersion (lam' ≫ ι) :=
    IsClosedImmersion.of_isPreimmersion _ (hr ▸ ιE.isClosedEmbedding.isClosed_range)
  exact IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq ιE (lam' ≫ ι) hr.symm

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

open CategoryTheory CategoryTheory.Limits

universe vG

namespace IsClosedImmersion p2m_export "AlgebraicGeometry.IsClosedImmersion" "Spec_iff of_isPreimmersion of_comp isClosedEmbedding comp spec_of_surjective lift mk exists_iso_hom_comp_eq_of_range_eq" end IsClosedImmersion
p2m_open_scoped "AlgebraicGeometry.IsClosedImmersion" in

theorem IsClosedImmersion.isIso_of_surjective_of_isReduced {A X : Scheme.{vG}} (f : A ⟶ X) [IsClosedImmersion f]
    [IsReduced A] [IsReduced X] (h : Function.Surjective f.base) : IsIso f := by
  obtain ⟨e, he⟩ := IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq f (𝟙 X)
    (by rw [Set.range_eq_univ.mpr h, Scheme.Hom.id_base, TopCat.coe_id, Set.range_id])
  rw [← he]
  infer_instance

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

open CategoryTheory IsLocalRing TopologicalSpace

universe v7

theorem exists_maximalIdeal_eq_comap_sup_span {Z X : Scheme.{v7}} (ι : Z ⟶ X) [IsClosedImmersion ι] {ζ z : Z} (hζz : ζ ⤳ z)
    (hprinc : (maximalIdeal (Z.presheaf.stalk z)).IsPrincipal) :
    ∃ t : X.presheaf.stalk (ι.base z), maximalIdeal (X.presheaf.stalk (ι.base z)) =
      Ideal.comap (X.presheaf.stalkSpecializes (hζz.map ι.continuous)).hom (maximalIdeal (X.presheaf.stalk (ι.base ζ))) ⊔
        Ideal.span {t} := by
  have hsurj : Function.Surjective (ι.stalkMap z).hom := ι.stalkMap_surjective z
  obtain ⟨s, hs⟩ := hprinc
  obtain ⟨t, ht⟩ := hsurj s

  have hkerP : ∀ a : X.presheaf.stalk (ι.base z), (ι.stalkMap z).hom a = 0 →
      (X.presheaf.stalkSpecializes (hζz.map ι.continuous)).hom a ∈ maximalIdeal (X.presheaf.stalk (ι.base ζ)) := by
    intro a ha
    have hsq := congrArg (fun f => f.hom a) (Scheme.Hom.stalkSpecializes_stalkMap ι ζ z hζz)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hsq
    rw [ha, map_zero] at hsq

    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map (ι.stalkMap ζ).hom
    rw [hsq] at hu'
    exact not_isUnit_zero hu'
  refine ⟨t, le_antisymm ?_ ?_⟩
  · intro m hm
    have hm' : (ι.stalkMap z).hom m ∈ maximalIdeal (Z.presheaf.stalk z) :=
      map_nonunit (ι.stalkMap z).hom m hm
    rw [hs, Ideal.submodule_span_eq, Ideal.mem_span_singleton'] at hm'
    obtain ⟨b', hb'⟩ := hm'
    obtain ⟨b, rfl⟩ := hsurj b'
    have hker : (ι.stalkMap z).hom (m - b * t) = 0 := by rw [map_sub, map_mul, ht, hb', sub_self]
    have hsplit : m = (m - b * t) + b * t := by ring
    rw [hsplit]
    exact Ideal.add_mem _ (Ideal.mem_sup_left ((Ideal.mem_comap).mpr (hkerP _ hker)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)))
  · refine sup_le ?_ ?_
    · intro a ha
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at ha
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => ha (hu.map _)
    · rw [Ideal.span_singleton_le_iff_mem, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (ι.stalkMap z).hom
      rw [ht] at hu'
      have hsmem : s ∈ maximalIdeal (Z.presheaf.stalk z) := by
        rw [hs, Ideal.submodule_span_eq]; exact Ideal.mem_span_singleton_self s
      exact (mem_maximalIdeal _ |>.mp hsmem) hu'

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)

private abbrev _root_.V3AsmMock.XO : Scheme.{0} := pullback toBaseZ (Spec.map (CommRingCat.ofHom τO))
p2m_export "V3AsmMock" "XO"

abbrev XK : Scheme.{0} := pullback toBaseZ (Spec.map (CommRingCat.ofHom (toκ.comp τO)))

abbrev πX : XO O XZ toBaseZ τO ⟶ Spec (CommRingCat.of O) := pullback.snd _ _

abbrev bc : XK O κ toκ XZ toBaseZ τO ⟶ XO O XZ toBaseZ τO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem isPullback_bc : IsPullback (bc O κ toκ XZ toBaseZ τO) (pullback.snd _ _) (πX O XZ toBaseZ τO)
    (Spec.map (CommRingCat.ofHom toκ)) :=
  AlgebraicGeometry.isPullback_map_snd_snd toBaseZ (Spec.map (CommRingCat.ofHom τO))
    (Spec.map (CommRingCat.ofHom (toκ.comp τO))) (Spec.map (CommRingCat.ofHom toκ))
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

include hϖ in
theorem ker_toκ : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
  refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (RingHom.ker_ne_top toκ) ?_).symm
  rw [hϖ, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

include hϖ in
theorem range_bc : Set.range (bc O κ toκ XZ toBaseZ τO).base = (πX O XZ toBaseZ τO).base ⁻¹' {IsLocalRing.closedPoint O} := by
  rw [AlgebraicGeometry.IsPullback.range_fst' (isPullback_bc O κ toκ XZ toBaseZ τO),
    AlgebraicGeometry.range_specMap_of_ker_eq_maximalIdeal toκ (ker_toκ q O hϖ κ toκ)]

abbrev iB : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)))

scoped instance : IsClosedImmersion (iB O) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

def resκ : O ⧸ IsLocalRing.maximalIdeal O →+* κ :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ (fun a ha => by
    rwa [← ker_toκ q O hϖ κ toκ, RingHom.mem_ker] at ha)

theorem resκ_comp_mk : (resκ q O hϖ κ toκ).comp (Ideal.Quotient.mk _) = toκ :=
  Ideal.Quotient.lift_comp_mk _ _ _

abbrev aB : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)) :=
  Spec.map (CommRingCat.ofHom (resκ q O hϖ κ toκ))

scoped instance : Flat (aB q O hϖ κ toκ) := by
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  letI := (resκ q O hϖ κ toκ).toAlgebra
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) κ)))
  infer_instance

theorem specMap_toκ_eq : Spec.map (CommRingCat.ofHom toκ) = aB q O hϖ κ toκ ≫ iB O := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, resκ_comp_mk]

include hϖ in

theorem πX_bc_apply (w : XK O κ toκ XZ toBaseZ τO) :
    (πX O XZ toBaseZ τO).base ((bc O κ toκ XZ toBaseZ τO).base w) = IsLocalRing.closedPoint O := by
  have : (bc O κ toκ XZ toBaseZ τO).base w ∈ Set.range (bc O κ toκ XZ toBaseZ τO).base := ⟨w, rfl⟩
  rw [range_bc q O hϖ κ toκ XZ toBaseZ τO] at this
  exact this

include hϖ in

theorem exists_factor {S Y : Scheme.{0}} (ιS : S ⟶ Y) [IsReduced S] (toDR : Y ⟶ XO O XZ toBaseZ τO)
    {y : Y} (hS : Set.range ιS.base = closure {y})
    (hy : (toDR ≫ πX O XZ toBaseZ τO).base y = IsLocalRing.closedPoint O) :
    ∃ s₀ : S ⟶ Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O)),
      ιS ≫ toDR ≫ πX O XZ toBaseZ τO = s₀ ≫ iB O := by
  have hall := AlgebraicGeometry.forall_comp_eq_of_range_eq_closure ιS (toDR ≫ πX O XZ toBaseZ τO) hS hy
    (IsLocalRing.isClosed_singleton_closedPoint O)
  obtain ⟨s₀, hs₀⟩ := AlgebraicGeometry.exists_lift_specQuotient (ιS ≫ toDR ≫ πX O XZ toBaseZ τO)
    (IsLocalRing.maximalIdeal O) (fun r hr =>
      AlgebraicGeometry.preimage_basicOpen_eq_bot_of_forall_eq_closedPoint _ hall r hr)
  exact ⟨s₀, hs₀.symm⟩

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)

abbrev K0 : Type := O ⧸ IsLocalRing.maximalIdeal O

scoped instance : Field (K0 O) := Ideal.Quotient.field _

abbrev XF : Scheme.{0} := pullback toBaseZ (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO)))

abbrev bck : XF O XZ toBaseZ τO ⟶ XO O XZ toBaseZ τO :=
  pullback.map _ _ _ _ (𝟙 _) (iB O) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

theorem isPullback_bck : IsPullback (bck O XZ toBaseZ τO) (pullback.snd _ _) (πX O XZ toBaseZ τO) (iB O) :=
  AlgebraicGeometry.isPullback_map_snd_snd toBaseZ (Spec.map (CommRingCat.ofHom τO))
    (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO))) (iB O)
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

scoped instance : IsClosedImmersion (bck O XZ toBaseZ τO) := by
  have := (isPullback_bck O XZ toBaseZ τO)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) this.flip inferInstance

abbrev bcκ : XK O κ toκ XZ toBaseZ τO ⟶ XF O XZ toBaseZ τO :=
  pullback.map _ _ _ _ (𝟙 _) (aB q O hϖ κ toκ) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, resκ_comp_mk])

theorem bcκ_bck : bcκ q O hϖ κ toκ XZ toBaseZ τO ≫ bck O XZ toBaseZ τO = bc O κ toκ XZ toBaseZ τO := by
  apply pullback.hom_ext
  · simp only [bcκ, bck, bc, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [bcκ, bck, bc, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← specMap_toκ_eq q O hϖ κ toκ]

theorem isPullback_bcκ :
    IsPullback (bcκ q O hϖ κ toκ XZ toBaseZ τO) (pullback.snd _ _) (pullback.snd _ _) (aB q O hϖ κ toκ) :=
  AlgebraicGeometry.isPullback_map_snd_snd toBaseZ (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO)))
    (Spec.map (CommRingCat.ofHom (toκ.comp τO))) (aB q O hϖ κ toκ)
    (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, resκ_comp_mk])

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)
  {R : Scheme.{0}} [IsIntegral R] (cI cZ : R ⟶ XK O κ toκ XZ toBaseZ τO)

abbrev ξb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : XO O XZ toBaseZ τO := (c ≫ bc O κ toκ XZ toBaseZ τO).base (genericPoint R)

abbrev Zb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : (XO O XZ toBaseZ τO).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξb O κ toκ XZ toBaseZ τO c}, isClosed_closure⟩

theorem range_ι_Zb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) :
    Set.range (Zb O κ toκ XZ toBaseZ τO c).subschemeι.base = closure {ξb O κ toκ XZ toBaseZ τO c} := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl

scoped instance (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : IsIntegral (Zb O κ toκ XZ toBaseZ τO c).subscheme :=
  Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure_singleton _

include hϖ in
theorem πX_ξb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : (πX O XZ toBaseZ τO).base (ξb O κ toκ XZ toBaseZ τO c) = closedPoint O :=
  πX_bc_apply q O hϖ κ toκ XZ toBaseZ τO _

include hϖ in

theorem exists_factor_Zb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) :
    ∃ s₀ : (Zb O κ toκ XZ toBaseZ τO c).subscheme ⟶ Spec (CommRingCat.of (K0 O)),
      (Zb O κ toκ XZ toBaseZ τO c).subschemeι ≫ πX O XZ toBaseZ τO = s₀ ≫ iB O := by
  have h := exists_factor q O hϖ XZ toBaseZ τO (Zb O κ toκ XZ toBaseZ τO c).subschemeι (𝟙 _)
    (y := ξb O κ toκ XZ toBaseZ τO c) (range_ι_Zb O κ toκ XZ toBaseZ τO c)
    (by rw [Category.id_comp]; exact πX_ξb q O hϖ κ toκ XZ toBaseZ τO c)
  simpa only [Category.id_comp] using h

def sZ (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : (Zb O κ toκ XZ toBaseZ τO c).subscheme ⟶ Spec (CommRingCat.of (K0 O)) :=
  (exists_factor_Zb q O hϖ κ toκ XZ toBaseZ τO c).choose

theorem ι_πX_eq_sZ_iB (c : R ⟶ XK O κ toκ XZ toBaseZ τO) :
    (Zb O κ toκ XZ toBaseZ τO c).subschemeι ≫ πX O XZ toBaseZ τO = sZ q O hϖ κ toκ XZ toBaseZ τO c ≫ iB O :=
  (exists_factor_Zb q O hϖ κ toκ XZ toBaseZ τO c).choose_spec

def sZF (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : (Zb O κ toκ XZ toBaseZ τO c).subscheme ⟶ XF O XZ toBaseZ τO :=
  pullback.lift ((Zb O κ toκ XZ toBaseZ τO c).subschemeι ≫ pullback.fst _ _) (sZ q O hϖ κ toκ XZ toBaseZ τO c) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ι_πX_eq_sZ_iB, Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    try (congr 3; exact RingHom.ext_int _ _))

@[reassoc (attr := simp)]
theorem sZF_bck (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : sZF q O hϖ κ toκ XZ toBaseZ τO c ≫ bck O XZ toBaseZ τO = (Zb O κ toκ XZ toBaseZ τO c).subschemeι := by
  apply pullback.hom_ext
  · simp only [sZF, bck, Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [sZF, bck, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← ι_πX_eq_sZ_iB]

@[reassoc (attr := simp)]
theorem sZF_snd (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : sZF q O hϖ κ toκ XZ toBaseZ τO c ≫ pullback.snd _ _ = sZ q O hϖ κ toκ XZ toBaseZ τO c :=
  pullback.lift_snd _ _ _

scoped instance (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : IsClosedImmersion (sZF q O hϖ κ toκ XZ toBaseZ τO c) := by
  have : IsClosedImmersion (sZF q O hϖ κ toκ XZ toBaseZ τO c ≫ bck O XZ toBaseZ τO) := by rw [sZF_bck]; infer_instance
  exact IsClosedImmersion.of_comp (sZF q O hϖ κ toκ XZ toBaseZ τO c) (bck O XZ toBaseZ τO)

abbrev Tb (c : R ⟶ XK O κ toκ XZ toBaseZ τO) : Scheme.{0} := pullback (sZ q O hϖ κ toκ XZ toBaseZ τO c) (aB q O hϖ κ toκ)

abbrev Uc (c' : R ⟶ XK O κ toκ XZ toBaseZ τO) : (XO O XZ toBaseZ τO).Opens :=
  ⟨(closure {ξb O κ toκ XZ toBaseZ τO c'})ᶜ, isClosed_closure.isOpen_compl⟩

variable (hcov : ∀ w : XK O κ toκ XZ toBaseZ τO, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
  (hZI : Set.range (cI ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cI})
  (hZZ : Set.range (cZ ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hne : ξb O κ toκ XZ toBaseZ τO cI ∉ closure {ξb O κ toκ XZ toBaseZ τO cZ})

include hcov hZI hZZ in

theorem preimage_Uc_subset_range_sZF :
    ((bck O XZ toBaseZ τO) ⁻¹ᵁ (Uc O κ toκ XZ toBaseZ τO cZ) : Set (XF O XZ toBaseZ τO)) ⊆
      Set.range (sZF q O hϖ κ toκ XZ toBaseZ τO cI).base := by
  intro f hf

  haveI : Surjective (aB q O hϖ κ toκ) := by
    letI : Field (K0 O) := inferInstance
    letI := (resκ q O hϖ κ toκ).toAlgebra
    change Surjective (Spec.map (CommRingCat.ofHom (algebraMap (K0 O) κ)))
    infer_instance
  haveI : Surjective (bcκ q O hϖ κ toκ XZ toBaseZ τO) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_bcκ q O hϖ κ toκ XZ toBaseZ τO).flip inferInstance
  obtain ⟨w, rfl⟩ := (bcκ q O hϖ κ toκ XZ toBaseZ τO).surjective f
  have hbw : (bck O XZ toBaseZ τO).base ((bcκ q O hϖ κ toκ XZ toBaseZ τO).base w) = (bc O κ toκ XZ toBaseZ τO).base w := by
    rw [← Scheme.Hom.comp_apply, bcκ_bck]
  have hmem : (bc O κ toκ XZ toBaseZ τO).base w ∈ closure {ξb O κ toκ XZ toBaseZ τO cI} := by
    rcases hcov w with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [← hZI]; exact ⟨r, rfl⟩
    · exfalso
      apply hf
      show (bck O XZ toBaseZ τO).base _ ∈ closure _
      rw [hbw, ← hZZ]; exact ⟨r, rfl⟩
  rw [← range_ι_Zb O κ toκ XZ toBaseZ τO cI, ← sZF_bck q O hϖ κ toκ XZ toBaseZ τO cI, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp] at hmem
  obtain ⟨_, ⟨ζ, rfl⟩, hζ⟩ := hmem
  exact ⟨ζ, (bck O XZ toBaseZ τO).isClosedEmbedding.injective (hζ.trans hbw.symm)⟩

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)
  {R : Scheme.{0}} [IsIntegral R] (cI cZ : R ⟶ XK O κ toκ XZ toBaseZ τO)
  (hcov : ∀ w : XK O κ toκ XZ toBaseZ τO, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
  (hZI : Set.range (cI ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cI})
  (hZZ : Set.range (cZ ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hne : ξb O κ toκ XZ toBaseZ τO cI ∉ closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hredF : IsReduced (XF O XZ toBaseZ τO)) (hredK : IsReduced (XK O κ toκ XZ toBaseZ τO))

abbrev Vb : (Zb O κ toκ XZ toBaseZ τO cI).subscheme.Opens :=
  (Zb O κ toκ XZ toBaseZ τO cI).subschemeι ⁻¹ᵁ (Uc O κ toκ XZ toBaseZ τO cZ)

abbrev UF : (XF O XZ toBaseZ τO).Opens := (bck O XZ toBaseZ τO) ⁻¹ᵁ (Uc O κ toκ XZ toBaseZ τO cZ)

theorem Vb_eq : Vb O κ toκ XZ toBaseZ τO cI cZ = (sZF q O hϖ κ toκ XZ toBaseZ τO cI) ⁻¹ᵁ (UF O κ toκ XZ toBaseZ τO cZ) := by
  ext x
  change (Zb O κ toκ XZ toBaseZ τO cI).subschemeι.base x ∈ (Uc O κ toκ XZ toBaseZ τO cZ : Set _) ↔
    (bck O XZ toBaseZ τO).base ((sZF q O hϖ κ toκ XZ toBaseZ τO cI).base x) ∈ (Uc O κ toκ XZ toBaseZ τO cZ : Set _)
  rw [← Scheme.Hom.comp_apply, sZF_bck]

include hcov hZI hZZ hredF in

theorem isIso_sZF_restrict : IsIso (sZF q O hϖ κ toκ XZ toBaseZ τO cI ∣_ UF O κ toκ XZ toBaseZ τO cZ) := by
  haveI := hredF
  haveI : IsReduced (↑((sZF q O hϖ κ toκ XZ toBaseZ τO cI) ⁻¹ᵁ UF O κ toκ XZ toBaseZ τO cZ) : Scheme.{0}) :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι _)
  haveI : IsReduced (↑(UF O κ toκ XZ toBaseZ τO cZ) : Scheme.{0}) := isReduced_of_isOpenImmersion (Scheme.Opens.ι _)
  refine IsClosedImmersion.isIso_of_surjective_of_isReduced _ ?_
  rintro ⟨f, hf⟩
  obtain ⟨ζ, hζ⟩ := preimage_Uc_subset_range_sZF q O hϖ κ toκ XZ toBaseZ τO cI cZ hcov hZI hZZ hf
  refine ⟨⟨ζ, show ζ ∈ (sZF q O hϖ κ toκ XZ toBaseZ τO cI) ⁻¹ᵁ UF O κ toκ XZ toBaseZ τO cZ by
    show (sZF q O hϖ κ toκ XZ toBaseZ τO cI).base ζ ∈ UF O κ toκ XZ toBaseZ τO cZ; rw [hζ]; exact hf⟩, ?_⟩
  have hζmem : ζ ∈ (sZF q O hϖ κ toκ XZ toBaseZ τO cI) ⁻¹ᵁ UF O κ toκ XZ toBaseZ τO cZ := by
    show (sZF q O hϖ κ toκ XZ toBaseZ τO cI).base ζ ∈ UF O κ toκ XZ toBaseZ τO cZ; rw [hζ]; exact hf
  apply Subtype.ext
  have h2 := congr($(morphismRestrict_ι (sZF q O hϖ κ toκ XZ toBaseZ τO cI) (UF O κ toκ XZ toBaseZ τO cZ)).base ⟨ζ, hζmem⟩)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2

  have h3 : ((UF O κ toκ XZ toBaseZ τO cZ).ι.base ((sZF q O hϖ κ toκ XZ toBaseZ τO cI ∣_ UF O κ toκ XZ toBaseZ τO cZ).base ⟨ζ, hζmem⟩)) =
      ((sZF q O hϖ κ toκ XZ toBaseZ τO cI ∣_ UF O κ toκ XZ toBaseZ τO cZ).base ⟨ζ, hζmem⟩).1 := rfl
  rw [← h3, h2]
  exact hζ

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)
  {R : Scheme.{0}} [IsIntegral R] (cI cZ : R ⟶ XK O κ toκ XZ toBaseZ τO)
  (hcov : ∀ w : XK O κ toκ XZ toBaseZ τO, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
  (hZI : Set.range (cI ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cI})
  (hZZ : Set.range (cZ ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hnsub : ¬ (Set.range cI.base ⊆ Set.range cZ.base))
  (hdescZ : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' closure ((bc O κ toκ XZ toBaseZ τO).base '' Set.range cZ.base) = Set.range cZ.base)
  (hredF : IsReduced (XF O XZ toBaseZ τO)) (hredK : IsReduced (XK O κ toκ XZ toBaseZ τO))

include hcov hZI hZZ hnsub hdescZ hredF hredK in

theorem isReduced_Tb : IsReduced (Tb q O hϖ κ toκ XZ toBaseZ τO cI) := by
  haveI := hredF; haveI := hredK
  set sZ0 := sZ q O hϖ κ toκ XZ toBaseZ τO cI with hsZ0
  set a := aB q O hϖ κ toκ with ha
  set g := sZF q O hϖ κ toκ XZ toBaseZ τO cI with hg
  set U := UF O κ toκ XZ toBaseZ τO cZ with hU
  haveI : Flat (pullback.fst sZ0 a) := MorphismProperty.pullback_fst _ _ inferInstance

  obtain ⟨_, ⟨r, rfl⟩, hr⟩ := Set.not_subset.mp hnsub
  have hξ : (bc O κ toκ XZ toBaseZ τO).base (cI.base r) ∈ Set.range (Zb O κ toκ XZ toBaseZ τO cI).subschemeι.base := by
    rw [range_ι_Zb, ← hZI]; exact ⟨r, rfl⟩
  obtain ⟨ζ, hζ⟩ := hξ
  have hV : ((g ⁻¹ᵁ U).carrier).Nonempty := by
    refine ⟨ζ, ?_⟩
    show (bck O XZ toBaseZ τO).base (g.base ζ) ∈ (Uc O κ toκ XZ toBaseZ τO cZ : Set _)
    rw [hg, ← Scheme.Hom.comp_apply, sZF_bck, hζ]
    intro hmem
    apply hr
    rw [← hdescZ]
    show (bc O κ toκ XZ toBaseZ τO).base (cI.base r) ∈ closure _
    have hmem' : (bc O κ toκ XZ toBaseZ τO).base (cI.base r) ∈ closure {ξb O κ toκ XZ toBaseZ τO cZ} := hmem
    rw [← hZZ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp] at hmem'
    exact subset_closure hmem'

  haveI := isIso_sZF_restrict q O hϖ κ toκ XZ toBaseZ τO cI cZ hcov hZI hZZ hredF
  have hφ : (asIso (g ∣_ U)).hom ≫ (U.ι ≫ pullback.snd _ _) = (g ⁻¹ᵁ U).ι ≫ sZ0 := by
    rw [asIso_hom, ← Category.assoc, morphismRestrict_ι, Category.assoc, hg, sZF_snd]

  haveI : IsReduced (pullback (pullback.snd toBaseZ (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO)))) a) :=
    isReduced_of_isOpenImmersion (isPullback_bcκ q O hϖ κ toκ XZ toBaseZ τO).isoPullback.inv
  haveI : IsReduced (pullback U.ι (pullback.fst (pullback.snd toBaseZ
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO)))) a)) :=
    isReduced_of_isOpenImmersion (pullback.snd _ _)
  haveI : IsReduced (pullback (U.ι ≫ pullback.snd toBaseZ (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp τO)))) a) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso _ a U.ι).inv
  haveI : IsReduced (pullback ((g ⁻¹ᵁ U).ι ≫ sZ0) a) :=
    isReduced_of_isOpenImmersion (AlgebraicGeometry.pullbackIsoOfIsoOver _ _ (asIso (g ∣_ U)) hφ a).hom
  haveI : IsReduced (pullback (g ⁻¹ᵁ U).ι (pullback.fst sZ0 a)) :=
    isReduced_of_isOpenImmersion (pullbackRightPullbackFstIso sZ0 a (g ⁻¹ᵁ U).ι).hom

  exact AlgebraicGeometry.isReduced_of_flat_of_isReduced_preimage (pullback.fst sZ0 a) (g ⁻¹ᵁ U) hV
    (pullback.snd (g ⁻¹ᵁ U).ι (pullback.fst sZ0 a))
    (fun x hx => by
      show x ∈ Set.range (pullback.snd (g ⁻¹ᵁ U).ι (pullback.fst sZ0 a)).base
      rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
      exact hx)

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.Hom.stalkSpecializes_stalkMap Surjective SmoothOfRelativeDimension IsClosedImmersion.of_isPreimmersion morphismRestrict_ι IsClosedImmersion.of_comp Scheme.IdealSheafData.coe_support_vanishingIdeal basicOpen_eq_bot_iff LocallyOfFiniteType.isLocallyNoetherian Scheme.Opens.range_ι Scheme.Hom Scheme.Pullback.range_fst LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme.toSpecΓ_naturality Scheme Scheme.IdealSheafData.vanishingIdeal isReduced_of_isReduced_stalk IsOpenImmersion Scheme.basicOpen_zero Scheme.Hom.comp_base IsReduced.of_openCover isIntegral_iff_irreducibleSpace_and_isReduced Scheme.Pullback.range_snd Flat.stalkMap Flat IsClosedImmersion.spec_of_surjective IsClosedImmersion IsReduced HasRingHomProperty.appLE HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Scheme.basicOpen_appLE Scheme.preimage_basicOpen_top Spec.map_id Etale Scheme.Opens.ι Scheme.Opens Scheme.Hom.id_base isReduced_of_isOpenImmersion Scheme.Pullback.exists_preimage_pullback isReduced_of_isAffine_isReduced HasRingHomProperty toSpecΓ Scheme.Hom.comp_apply basicOpen_eq_of_affine range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.branchIdeal IsClosedImmersion.exists_iso_hom_comp_eq_of_range_eq SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed"
p2m_open "AlgebraicGeometry"

theorem ValuationRing.of_ringEquiv' {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (e : A ≃+* B) [ValuationRing B] : ValuationRing A := by
  rw [ValuationRing.iff_dvd_total]
  constructor
  intro a b
  rcases (ValuationRing.iff_dvd_total.mp ‹ValuationRing B›).total (e a) (e b) with h | h
  · left; simpa using (map_dvd e.symm h)
  · right; simpa using (map_dvd e.symm h)

end AlgebraicGeometry
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)
  {R : Scheme.{0}} [IsIntegral R] (cI cZ : R ⟶ XK O κ toκ XZ toBaseZ τO) [IsClosedImmersion cI]
  (hcov : ∀ w : XK O κ toκ XZ toBaseZ τO, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
  (hZI : Set.range (cI ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cI})
  (hZZ : Set.range (cZ ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hnsub : ¬ (Set.range cI.base ⊆ Set.range cZ.base))
  (hdescZ : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' closure ((bc O κ toκ XZ toBaseZ τO).base '' Set.range cZ.base) = Set.range cZ.base)
  (hredF : IsReduced (XF O XZ toBaseZ τO)) (hredK : IsReduced (XK O κ toκ XZ toBaseZ τO))
  (hdesc : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' closure ((bc O κ toκ XZ toBaseZ τO).base '' Set.range cI.base) = Set.range cI.base)
  [IsLocallyNoetherian (XO O XZ toBaseZ τO)]

abbrev Tb' : Scheme.{0} :=
  pullback ((Zb O κ toκ XZ toBaseZ τO cI).subschemeι ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))

include hϖ hcov hZI hZZ hnsub hdescZ hredF hredK in
theorem isReduced_Tb' : IsReduced (Tb' O κ toκ XZ toBaseZ τO cI) := by
  haveI := isReduced_Tb q O hϖ κ toκ XZ toBaseZ τO cI cZ hcov hZI hZZ hnsub hdescZ hredF hredK
  exact isReduced_of_isOpenImmersion
    ((pullback.congrHom (ι_πX_eq_sZ_iB q O hϖ κ toκ XZ toBaseZ τO cI) (specMap_toκ_eq q O hϖ κ toκ)).hom ≫
      (pullbackCompMonoIso (sZ q O hϖ κ toκ XZ toBaseZ τO cI) (aB q O hϖ κ toκ) (iB O)).hom)

include hϖ in
theorem flat_fst_Tb' : Flat (pullback.fst ((Zb O κ toκ XZ toBaseZ τO cI).subschemeι ≫ πX O XZ toBaseZ τO)
    (Spec.map (CommRingCat.ofHom toκ))) := by
  have e : pullback.fst ((Zb O κ toκ XZ toBaseZ τO cI).subschemeι ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ)) =
      (pullback.congrHom (ι_πX_eq_sZ_iB q O hϖ κ toκ XZ toBaseZ τO cI) (specMap_toκ_eq q O hϖ κ toκ)).hom ≫
        pullback.fst (sZ q O hϖ κ toκ XZ toBaseZ τO cI ≫ iB O) (aB q O hϖ κ toκ ≫ iB O) := by
    rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  rw [e]
  haveI := AlgebraicGeometry.flat_pullback_fst_comp_mono (sZ q O hϖ κ toκ XZ toBaseZ τO cI) (aB q O hϖ κ toκ) (iB O)
  infer_instance

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace V3AsmMock

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry TopologicalSpace IsLocalRing"

variable (q : ℕ) [Fact q.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] (toκ : O →+* κ)
  (XZ : Scheme.{0}) {Rb : Type} [CommRing Rb] (toBaseZ : XZ ⟶ Spec (CommRingCat.of Rb)) (τO : Rb →+* O)
  {R : Scheme.{0}} [IsIntegral R] (cI cZ : R ⟶ XK O κ toκ XZ toBaseZ τO) [IsClosedImmersion cI]
  (hcov : ∀ w : XK O κ toκ XZ toBaseZ τO, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
  (hZI : Set.range (cI ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cI})
  (hZZ : Set.range (cZ ≫ bc O κ toκ XZ toBaseZ τO).base = closure {ξb O κ toκ XZ toBaseZ τO cZ})
  (hnsub : ¬ (Set.range cI.base ⊆ Set.range cZ.base))
  (hdescZ : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' closure ((bc O κ toκ XZ toBaseZ τO).base '' Set.range cZ.base) = Set.range cZ.base)
  (hredF : IsReduced (XF O XZ toBaseZ τO)) (hredK : IsReduced (XK O κ toκ XZ toBaseZ τO))
  (hdesc : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' closure ((bc O κ toκ XZ toBaseZ τO).base '' Set.range cI.base) = Set.range cI.base)
  [IsLocallyNoetherian (XO O XZ toBaseZ τO)]

include hϖ hcov hZI hZZ hnsub hdescZ hredF hredK hdesc in

theorem exists_maximalIdeal_eq_branch_sup_span (ξ x : XO O XZ toBaseZ τO) (h : ξ ⤳ x)
    (hξ : ξ = ξb O κ toκ XZ toBaseZ τO cI) (r₀ : R) (hr₀ : (cI ≫ bc O κ toκ XZ toBaseZ τO).base r₀ = x)
    (hval : ValuationRing (R.presheaf.stalk r₀)) :
    ∃ t : (XO O XZ toBaseZ τO).presheaf.stalk x, maximalIdeal ((XO O XZ toBaseZ τO).presheaf.stalk x) =
      Ideal.comap ((XO O XZ toBaseZ τO).presheaf.stalkSpecializes h).hom (maximalIdeal ((XO O XZ toBaseZ τO).presheaf.stalk ξ)) ⊔
        Ideal.span {t} := by
  haveI := hredK
  set ιZ := (Zb O κ toκ XZ toBaseZ τO cI).subschemeι with hιZ

  haveI := isReduced_Tb' q O hϖ κ toκ XZ toBaseZ τO cI cZ hcov hZI hZZ hnsub hdescZ hredF hredK
  haveI : IsClosedImmersion (ιZ ≫ 𝟙 (XO O XZ toBaseZ τO)) := by rw [Category.comp_id]; infer_instance
  have hrange : (bc O κ toκ XZ toBaseZ τO).base ⁻¹' Set.range (ιZ ≫ 𝟙 (XO O XZ toBaseZ τO)).base = Set.range cI.base := by
    rw [Category.comp_id, hιZ, range_ι_Zb, ← hdesc, ← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, hZI,
      closure_closure]
  obtain ⟨e, heIso, he₂, he₁⟩ := AlgebraicGeometry.exists_iso_pullback_of_isClosedImmersion_of_preimage_range_eq ιZ
    (𝟙 _) (πX O XZ toBaseZ τO) (πX O XZ toBaseZ τO) (Category.id_comp _) (Spec.map (CommRingCat.ofHom toκ))
    (bc O κ toκ XZ toBaseZ τO) (pullback.snd _ _) (isPullback_bc O κ toκ XZ toBaseZ τO) cI hrange
  haveI := heIso

  let t' : Tb' O κ toκ XZ toBaseZ τO cI := (inv e).base r₀
  have het' : e.base t' = r₀ := by
    show (inv e ≫ e).base r₀ = r₀
    rw [IsIso.inv_hom_id]; rfl
  have hval' : ValuationRing (R.presheaf.stalk (e.base t')) := by rw [het']; exact hval
  have hzx : ιZ.base ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t') = x := by
    have h0 := he₁
    rw [Category.comp_id] at h0
    have h1 : (pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ)) ≫ ιZ).base t' =
        (e ≫ cI ≫ bc O κ toκ XZ toBaseZ τO).base t' := by rw [h0]
    rw [Scheme.Hom.comp_apply] at h1
    rw [h1, Scheme.Hom.comp_apply, het', hr₀]
  subst hzx
  have hξ' : ξb O κ toκ XZ toBaseZ τO cI ∈ Set.range ιZ.base := by rw [hιZ, range_ι_Zb]; exact subset_closure rfl
  obtain ⟨ζ, hζ⟩ := hξ'
  rw [← hζ] at hξ
  subst hξ

  have hgen : IsGenericPoint ζ (Set.univ : Set (Zb O κ toκ XZ toBaseZ τO cI).subscheme) := by
    have h1 : IsGenericPoint (ιZ.base (genericPoint (Zb O κ toκ XZ toBaseZ τO cI).subscheme)) (closure (Set.range ιZ.base)) :=
      AlgebraicGeometry.isGenericPoint_image_genericPoint ιZ
    have h2 : IsGenericPoint (ιZ.base ζ) (closure (Set.range ιZ.base)) := by
      rw [hιZ, range_ι_Zb, closure_closure, ← hιZ, hζ]; exact isGenericPoint_closure
    have h3 : ζ = genericPoint _ := ιZ.isClosedEmbedding.injective (h2.eq h1)
    rw [h3]; exact genericPoint_spec _
  have hζz : ζ ⤳ (pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t' :=
    hgen.specializes (Set.mem_univ _)

  haveI : IsDomain ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t') :=
    MulEquiv.isDomain (R.presheaf.stalk (e.base t')) (asIso (e.stalkMap t')).commRingCatIsoToRingEquiv.symm.toMulEquiv
  haveI : ValuationRing ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t') :=
    @ValuationRing.of_ringEquiv' _ _ _ _ _ _ (asIso (e.stalkMap t')).commRingCatIsoToRingEquiv.symm hval'

  haveI : IsLocallyNoetherian (Zb O κ toκ XZ toBaseZ τO cI).subscheme := LocallyOfFiniteType.isLocallyNoetherian ιZ
  letI alg : Algebra ((Zb O κ toκ XZ toBaseZ τO cI).subscheme.presheaf.stalk ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t')) ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t') :=
    ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).stalkMap t').hom.toAlgebra
  haveI := flat_fst_Tb' q O hϖ κ toκ XZ toBaseZ τO cI
  haveI : Module.Flat ((Zb O κ toκ XZ toBaseZ τO cI).subscheme.presheaf.stalk ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t')) ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t') :=
    Flat.stalkMap (pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))) t'
  haveI : IsLocalHom (algebraMap ((Zb O κ toκ XZ toBaseZ τO cI).subscheme.presheaf.stalk ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t'))
      ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t')) :=
    inferInstanceAs (IsLocalHom ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).stalkMap t').hom)
  haveI : Module.FaithfullyFlat ((Zb O κ toκ XZ toBaseZ τO cI).subscheme.presheaf.stalk ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t'))
      ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t') := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hprinc := FaithfullyFlatRegularDescent.maximalIdeal_isPrincipal_of_faithfullyFlat
    ((Zb O κ toκ XZ toBaseZ τO cI).subscheme.presheaf.stalk ((pullback.fst (ιZ ≫ πX O XZ toBaseZ τO) (Spec.map (CommRingCat.ofHom toκ))).base t')) ((Tb' O κ toκ XZ toBaseZ τO cI).presheaf.stalk t')

  exact AlgebraicGeometry.exists_maximalIdeal_eq_comap_sup_span ιZ hζz hprinc

end V3AsmMock
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

noncomputable section

namespace ECL_MaxEqEng

private theorem surjective_fst_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₂]
    (h : i₁.base (genericPoint C) ∈ Set.range ⇑i₂.base) :
    Function.Surjective ⇑(pullback.fst i₁ i₂).base := by
  have hsub : Set.range ⇑i₁.base ⊆ Set.range ⇑i₂.base := by
    have h1 : Set.range ⇑i₁.base = ⇑i₁.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₁.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₂.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c c' hc'.symm
  exact ⟨z, hz⟩

private theorem surjective_snd_of_mem_range {C Z : Scheme} [IrreducibleSpace C] (i₁ i₂ : C ⟶ Z) [IsClosedImmersion i₁]
    (h : i₂.base (genericPoint C) ∈ Set.range ⇑i₁.base) :
    Function.Surjective ⇑(pullback.snd i₁ i₂).base := by
  have hsub : Set.range ⇑i₂.base ⊆ Set.range ⇑i₁.base := by
    have h1 : Set.range ⇑i₂.base = ⇑i₂.base '' closure {genericPoint C} := by
      rw [genericPoint_closure, Set.image_univ]
    rw [h1]
    refine (image_closure_subset_closure_image i₂.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
    exact closure_minimal (Set.singleton_subset_iff.mpr h) i₁.isClosedEmbedding.isClosed_range
  intro c
  obtain ⟨c', hc'⟩ := hsub ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i₁) (g := i₂) c' c hc'
  exact ⟨z, hz⟩

section Engine
variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)

private theorem not_surjective_of_crossing
    (f : ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) → ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) :
    ¬ Function.Surjective f := by
  intro hf
  haveI := 𝔛.isIntegral_fibre0 toκ
  haveI := 𝔛.smoothOfRelativeDimension_one_fibre0 toκ
  haveI : Infinite ↥(DRLevel.fibre0 (N₀ := N₀) toκ) := by
    have h := AlgebraicCurve.infinite_setOf_isClosed_singleton
      (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
    exact Set.infinite_univ_iff.mp (h.mono (Set.subset_univ _))
  haveI : Infinite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) := Infinite.of_surjective f hf
  haveI : Finite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1)) := 𝔛.finite_crossings toκ
  exact not_finite ↥(pullback (𝔛.comp κ toκ 0) (𝔛.comp κ toκ 1))

private theorem comp0_genericPoint_notMem_range_comp1 [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range ⇑(𝔛.comp κ toκ 1).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  not_surjective_of_crossing 𝔛 κ toκ _ (surjective_fst_of_mem_range _ _ h)

private theorem comp1_genericPoint_notMem_range_comp0 [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) ∉ Set.range ⇑(𝔛.comp κ toκ 0).base := fun h =>
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  not_surjective_of_crossing 𝔛 κ toκ _ (surjective_snd_of_mem_range _ _ h)

private theorem eq_of_specializes_comp0_genericPoint [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]
    (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔛.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  rcases 𝔛.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔛.comp κ toκ 0).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]
  · exact absurd (hz.mem_closed (𝔛.comp κ toκ 1).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp0_genericPoint_notMem_range_comp1 𝔛 κ toκ)

private theorem eq_of_specializes_comp1_genericPoint [IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)]
    (z : ↥(DRLevel.fibre (N₀ := N₀) toκ))
    (hz : z ⤳ (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) :
    z = (𝔛.comp κ toκ 1).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) := by
  haveI := 𝔛.comp_isClosedImmersion κ toκ 0
  haveI := 𝔛.comp_isClosedImmersion κ toκ 1
  rcases 𝔛.comp_jointly_surjective κ toκ z with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · exact absurd (hz.mem_closed (𝔛.comp κ toκ 0).isClosedEmbedding.isClosed_range ⟨c, rfl⟩)
      (comp1_genericPoint_notMem_range_comp0 𝔛 κ toκ)
  · have hc : c ⤳ genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ) :=
      (𝔛.comp κ toκ 1).isClosedEmbedding.isInducing.specializes_iff.mp hz
    rw [(hc.antisymm (genericPoint_specializes c)).eq]

end Engine
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end ECL_MaxEqEng
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

namespace ECL_MaxEq

open V3AsmMock IsLocalRing

private theorem isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (f : Y ⟶ X) [Flat f] [Surjective f] [IsReduced Y] :
    IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    obtain ⟨y, rfl⟩ := f.surjective x
    have hfl : (f.stalkMap y).hom.Flat := Flat.stalkMap f y
    letI := (f.stalkMap y).hom.toAlgebra
    haveI : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) := hfl
    haveI : IsLocalHom (algebraMap (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (f.base y)) (B := Y.presheaf.stalk y)
    exact isReduced_of_injective (algebraMap _ (Y.presheaf.stalk y)) (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk X

private theorem isReduced_fibre {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
    {k : Type} [Field k] (τ : DRLevel.R q →+* k) : IsReduced (DRLevel.fibre (N₀ := N₀) τ) := by
  let K := AlgebraicClosure k
  haveI : IsReduced (DRLevel.fibre (N₀ := N₀) ((algebraMap k K).comp τ)) :=
    ModularCurve.DRModelPackageLevel.isReduced_pullback_toBase_of_isAlgClosed N₀ q hqN 𝔛 K
      (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp τ)))
  let g : DRLevel.fibre (N₀ := N₀) ((algebraMap k K).comp τ) ⟶ DRLevel.fibre (N₀ := N₀) τ :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k K))) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have hg : IsPullback g (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    AlgebraicGeometry.isPullback_map_snd_snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom τ))
      (Spec.map (CommRingCat.ofHom ((algebraMap k K).comp τ))) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show RingHom.Flat (algebraMap k K)
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Flat g := MorphismProperty.of_isPullback hg.flip inferInstance
  haveI : Surjective g := MorphismProperty.of_isPullback hg.flip inferInstance
  exact isReduced_of_flat_of_surjective g

private theorem exists_maximalIdeal_eq_branchIdeal_sup_span_of_comp
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    [IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (cI cZ : DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO) ⟶ (DRLevel.fibre (N₀ := N₀) (toκ.comp ρO)))
    [IsClosedImmersion cI]
    (hcov : ∀ w, w ∈ Set.range cI.base ∨ w ∈ Set.range cZ.base)
    (hZI : Set.range (cI ≫ DRLevel.bcMap ρO toκ).base = closure {(cI ≫ DRLevel.bcMap ρO toκ).base (genericPoint _)})
    (hZZ : Set.range (cZ ≫ DRLevel.bcMap ρO toκ).base = closure {(cZ ≫ DRLevel.bcMap ρO toκ).base (genericPoint _)})
    (hnsub : ¬ (Set.range cI.base ⊆ Set.range cZ.base))
    (hdescI : (DRLevel.bcMap ρO toκ).base ⁻¹' closure ((DRLevel.bcMap ρO toκ).base '' Set.range cI.base) = Set.range cI.base)
    (hdescZ : (DRLevel.bcMap ρO toκ).base ⁻¹' closure ((DRLevel.bcMap ρO toκ).base '' Set.range cZ.base) = Set.range cZ.base)
    (r₀ : DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) (x : ↥(DRLevel.XO (N₀ := N₀) ρO)) (hr₀ : (cI ≫ DRLevel.bcMap ρO toκ).base r₀ = x)
    (h : (cI ≫ DRLevel.bcMap ρO toκ).base (genericPoint _) ⤳ x) :
    ∃ t : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x,
      IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk x) = Scheme.branchIdeal h ⊔ Ideal.span {t} := by

  haveI : CharP (O ⧸ IsLocalRing.maximalIdeal O) q := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)), Ideal.Quotient.eq_zero_iff_mem, hϖ]
    exact Ideal.mem_span_singleton_self _
  have hredF : IsReduced (XF O (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO) :=
    isReduced_fibre 𝔛 ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp ρO)
  have hredK : IsReduced (XK O κ toκ (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO) := 𝔛.fibre_reduced κ (toκ.comp ρO)

  haveI := 𝔛.isProper
  haveI : LocallyOfFiniteType (πX O (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO) := MorphismProperty.pullback_snd _ _ inferInstance
  haveI : IsLocallyNoetherian (XO O (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO) :=
    LocallyOfFiniteType.isLocallyNoetherian (πX O (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO)

  haveI := 𝔛.smoothOfRelativeDimension_one_fibre0 (toκ.comp ρO)
  have hval : ValuationRing ((DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)).presheaf.stalk r₀) := by
    by_cases hr : r₀ = genericPoint _
    · subst hr
      exact inferInstanceAs (ValuationRing (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)).functionField)
    · haveI := AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed
        (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) r₀
        (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint
          (pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO)))) r₀ hr)
      infer_instance
  exact V3AsmMock.exists_maximalIdeal_eq_branch_sup_span q O hϖ κ toκ (DRLevel.X N₀ q) (DRLevel.toBase N₀ q) ρO cI cZ hcov hZI hZZ
    hnsub hdescZ hredF hredK hdescI _ x h rfl r₀ hr₀ hval

end ECL_MaxEq
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.AlgebraicGeometry.Scheme.IdealSheafData P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton.V3AsmMock"

open IsLocalRing in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)))
    (hinf : 𝔛.ξinf ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) (hzero : 𝔛.ξzero ρO toκ ⤳ 𝔛.crossingPt ρO toκ n) :
    (∃ t : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n), IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) = Scheme.branchIdeal hinf ⊔ Ideal.span {t}) ∧
    (∃ t : (DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n), IsLocalRing.maximalIdeal ((DRLevel.XO (N₀ := N₀) ρO).presheaf.stalk (𝔛.crossingPt ρO toκ n)) = Scheme.branchIdeal hzero ⊔ Ideal.span {t}) := by
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 0
  haveI := 𝔛.comp_isClosedImmersion κ (toκ.comp ρO) 1
  have hbc₁ : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.fst _ _ =
      pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := by
    rw [DRLevel.bcMap, pullback.map, pullback.lift_fst, Category.comp_id]
  have hdesc := fun i => ModularCurve.DRModelPackageLevel.preimage_closure_image_range_comp_eq_of_comp_fst_eq N₀ q hqN 𝔛 O ρO κ toκ
    (DRLevel.bcMap ρO toκ) hbc₁ i
  have hZ := fun i => (ModularCurve.DRModelPackageLevel.range_comp_bcMap_eq_closure_and_isClosed N₀ q hqN 𝔛 O ρO hϖ κ toκ i).1
  have hcov : ∀ w, w ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0).base ∨ w ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1).base :=
    𝔛.comp_jointly_surjective κ (toκ.comp ρO)

  have hn01 : ¬ (Set.range (𝔛.comp κ (toκ.comp ρO) 0).base ⊆ Set.range (𝔛.comp κ (toκ.comp ρO) 1).base) := fun hs =>
    ECL_MaxEqEng.comp0_genericPoint_notMem_range_comp1 𝔛 κ (toκ.comp ρO) (hs ⟨_, rfl⟩)
  have hn10 : ¬ (Set.range (𝔛.comp κ (toκ.comp ρO) 1).base ⊆ Set.range (𝔛.comp κ (toκ.comp ρO) 0).base) := fun hs =>
    ECL_MaxEqEng.comp1_genericPoint_notMem_range_comp0 𝔛 κ (toκ.comp ρO) (hs ⟨_, rfl⟩)
  refine ⟨?_, ?_⟩
  · exact ECL_MaxEq.exists_maximalIdeal_eq_branchIdeal_sup_span_of_comp N₀ q hqN 𝔛 O ρO hϖ κ toκ
      (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1) hcov (hZ 0) (hZ 1)
      hn01 (hdesc 0) (hdesc 1) ((pullback.fst (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) _
      (Scheme.Hom.comp_apply _ _ _).symm hinf
  · have hcov' : ∀ w, w ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1).base ∨ w ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0).base :=
      fun w => (hcov w).symm
    have hx : (𝔛.comp κ (toκ.comp ρO) 1 ≫ DRLevel.bcMap ρO toκ).base
        ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) = 𝔛.crossingPt ρO toκ n := by
      rw [← Scheme.Hom.comp_apply, ← pullback.condition_assoc]
    exact ECL_MaxEq.exists_maximalIdeal_eq_branchIdeal_sup_span_of_comp N₀ q hqN 𝔛 O ρO hϖ κ toκ
      (𝔛.comp κ (toκ.comp ρO) 1) (𝔛.comp κ (toκ.comp ρO) 0) hcov' (hZ 1) (hZ 0)
      hn10 (hdesc 1) (hdesc 0) ((pullback.snd (𝔛.comp κ (toκ.comp ρO) 0) (𝔛.comp κ (toκ.comp ρO) 1)).base n) _ hx hzero

end S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_maximalIdeal_eq_branchIdeal_sup_span_singleton (solution)
