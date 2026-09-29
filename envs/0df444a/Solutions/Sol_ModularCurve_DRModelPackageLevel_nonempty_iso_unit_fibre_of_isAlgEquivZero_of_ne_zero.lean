-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4bf7cee2-7fb2-52ae-8cdf-054c39506570

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_twoAffineOpenCover_fibre0
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero.ModularCurve"

open ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.toBase DRModelPackageLevel IgusaScheme IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen ssPlaces_nonempty"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "smooth_generic isProper crossing_reduced geomIntegral_generic lfp nodeEquiv flat comp_isClosedImmersion fibre_reduced comp comp_jointly_surjective comp_over isProper_fibre0 smoothOfRelativeDimension_one_fibre0 isIntegral_fibre0 nonempty_twoAffineOpenCover_fibre0"
namespace HFIB
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime]

theorem isUnit_intCast_of_prime_ne {p : ℕ} (hp : p.Prime) (hpq : p ≠ q) : IsUnit ((p : ℤ) : R q) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  have hmem : (p : ℤ) ∈ (Ideal.span {(q : ℤ)}).primeCompl := by
    intro h
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at h
    have : (q : ℤ).natAbs ∣ (p : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at this
    exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp this).symm
  simpa using IsLocalization.map_units (R q) (⟨(p : ℤ), hmem⟩ : (Ideal.span {(q : ℤ)}).primeCompl)

theorem charZero_of_ringHom_of_ne_zero {k : Type} [Field k] (toκ : R q →+* k) (hq : (q : k) ≠ 0) : CharZero k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hpp | rfl
  · exfalso
    by_cases hpq : p = q
    · subst hpq; exact hq (CharP.cast_eq_zero k p)
    · have hu := (isUnit_intCast_of_prime_ne q hpp hpq).map toκ
      rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero k p] at hu
      exact not_isUnit_zero hu
  · exact CharP.charP_to_charZero k

theorem ringHom_eq_algebraMap_comp {k : Type} [Field k] [CharZero k] (toκ : R q →+* k) :
    toκ = (algebraMap ℚ k).comp (algebraMap (R q) ℚ) := by
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(q : ℤ)}).primeCompl (Subsingleton.elim _ _)

noncomputable def coverPullback {X S T : Scheme.{0}} (c : X ⟶ S) (t : T ⟶ S) [IsAffineHom t]
    (𝒱 : X.TwoAffineOpenCover) : (pullback c t).TwoAffineOpenCover :=
  haveI : IsAffineHom (pullback.fst c t) := MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  { U0 := (pullback.fst c t) ⁻¹ᵁ 𝒱.U0
    U1 := (pullback.fst c t) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

end ModularCurve.DRModelPackageLevel.HFIB

p2m_open "ModularCurve.DRModelPackageLevel P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero.ModularCurve.DRModelPackageLevel P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero.ModularCurve.DRModelPackageLevel.HFIB"

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q)))
      (L : (pullback (DRLevel.toBase N₀ q) x).Modules), Scheme.Modules.IsInvertible L →
      IsAlgEquivZero (pullback.snd (DRLevel.toBase N₀ q) x) L →
      ∀ s : 𝟙_ (pullback (DRLevel.toBase N₀ q) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (DRLevel.toBase N₀ q) x).Modules) := by
  intro k _ _ x
  classical
  haveI := 𝔓.isProper; haveI := 𝔓.flat; haveI := 𝔓.lfp
  obtain ⟨𝒱X, -, -⟩ := IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen (N₀ * q) q
  obtain ⟨toκ, rfl⟩ : ∃ toκ : R q →+* k, x = Spec.map (CommRingCat.ofHom toκ) :=
    ⟨(Spec.preimage x).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  by_cases hq : (q : k) = 0
  ·
    haveI : CharP k q := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hq
    intro L hL h0 s hs
    haveI : IsReduced (pullback (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.fibre_reduced k toκ
    haveI hp0 : IsProper (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) := 𝔓.isProper_fibre0 toκ
    haveI hs0 : SmoothOfRelativeDimension 1 (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
      𝔓.smoothOfRelativeDimension_one_fibre0 toκ
    haveI : IsIntegral (fibre0 (N₀ := N₀) toκ) := 𝔓.isIntegral_fibre0 toκ
    haveI hgi0 : GeometricallyIntegral (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ))) :=
      AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
    haveI := 𝔓.comp_isClosedImmersion k toκ 0
    haveI := 𝔓.comp_isClosedImmersion k toκ 1
    obtain ⟨𝒲⟩ := 𝔓.nonempty_twoAffineOpenCover_fibre0 toκ
    have hne : Nonempty ↥(pullback (𝔓.comp k toκ 0) (𝔓.comp k toκ 1)) := by
      obtain ⟨P, hP⟩ := ModularCurve.ssPlaces_nonempty q N₀ hqN k
      exact ⟨(𝔓.nodeEquiv k toκ).symm ⟨P, hP⟩⟩
    exact AlgebraicGeometry.RelPicard.nonempty_iso_unit_of_isAlgEquivZero_of_ne_zero_of_twoGluedSmoothCurves
      (pullback.snd (toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      (pullback.snd (toBase0 N₀ q) (Spec.map (CommRingCat.ofHom toκ)))
      ⟨𝔓.comp k toκ 0, 𝔓.comp_over k toκ 0⟩ ⟨𝔓.comp k toκ 1, 𝔓.comp_over k toκ 1⟩
      (𝔓.comp_jointly_surjective k toκ) (𝔓.crossing_reduced k toκ) hne 𝒲 𝒲 L hL h0 s hs
  ·
    haveI := charZero_of_ringHom_of_ne_zero q toκ hq
    obtain rfl := ringHom_eq_algebraMap_comp q toκ
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    set z : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (R q)) := Spec.map (CommRingCat.ofHom (algebraMap (R q) ℚ)) with hz
    set y : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℚ) := Spec.map (CommRingCat.ofHom (algebraMap ℚ k)) with hy
    intro L hL h0 s hs
    have hsnd : pullback.snd (toBase N₀ q) (y ≫ z) =
        (pullbackLeftPullbackSndIso (toBase N₀ q) z y).inv ≫ pullback.snd (pullback.snd (toBase N₀ q) z) y := by
      rw [← pullbackLeftPullbackSndIso_hom_snd, Iso.inv_hom_id_assoc]
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ q) z) := 𝔓.smooth_generic
    haveI : GeometricallyIntegral (pullback.snd (toBase N₀ q) z) := 𝔓.geomIntegral_generic
    haveI : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) := smoothOfRelativeDimension_isStableUnderBaseChange 1
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (pullback.snd (toBase N₀ q) z) y) :=
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ q) (y ≫ z)) := by
      rw [hsnd]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
    haveI : GeometricallyIrreducible (pullback.snd (toBase N₀ q) (y ≫ z)) := by
      rw [hsnd]; exact MorphismProperty.RespectsIso.precomp (P := @GeometricallyIrreducible) _ _ inferInstance
    exact AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_iso_tensorUnit_of_ne_zero
      (pullback.snd (toBase N₀ q) (y ≫ z)) (coverPullback (toBase N₀ q) (y ≫ z) 𝒱X) hL h0 s hs

end S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero (solution)
