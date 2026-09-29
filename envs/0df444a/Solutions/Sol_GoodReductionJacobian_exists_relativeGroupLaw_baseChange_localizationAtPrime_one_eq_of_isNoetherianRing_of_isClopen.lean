-- Prove2me | solution 1 for GoodReductionJacobian.exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/99ea4f44-ad53-57cd-9074-07300af0d97e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
p2m_attr_erase "instance" "AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instTopologicallyFGOfFiniteType"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.SubalgebraStages.specCone_π_app"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian NeronModelInfra"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle RelativeGroupLaw exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat"
namespace LLocalReduce
p2m_open "GoodReductionJacobian"

theorem exists_geomPoint {T : Type u} [CommRing T] (t : Spec (CommRingCat.of T)) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (g₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of T)),
      Set.range g₀.base = {t} := by
  let K : Type u := (Spec (CommRingCat.of T)).residueField t
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫
      (Spec (CommRingCat.of T)).fromSpecResidueField t, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have := Scheme.range_fromSpecResidueField (X := Spec (CommRingCat.of T)) t
    exact this ▸ Set.mem_range_self _
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))) := ⟨(default : PrimeSpectrum _)⟩
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply]
    have := Scheme.range_fromSpecResidueField (X := Spec (CommRingCat.of T)) t
    exact (this ▸ Set.mem_range_self _ : _ ∈ ({t} : Set _))

theorem isConnected_preimage_of_geomPoint {R T k : Type u} [CommRing R] [CommRing T] [Field k] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of T)) (g₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of T))
    (hg₀ : Set.range g₀.base = {t})
    (hA : AbelianSchemePropertyBundle k (pullback.snd f (g₀ ≫ ι))) :
    _root_.IsConnected ((pullback.snd f ι).base ⁻¹' {t}) := by

  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
  have huniv : _root_.IsConnected (Set.univ : Set ↥(pullback f (g₀ ≫ ι))) := by
    have h := hA.connectedFibres x₀
    rwa [show (pullback.snd f (g₀ ≫ ι)).base ⁻¹' {x₀} = Set.univ from
      Set.eq_univ_of_forall fun y => @Subsingleton.elim _ hsub _ _] at h

  have hfib : (pullback.snd f ι).base ⁻¹' {t}
      = Set.range (pullback.fst (pullback.snd f ι) g₀).base := by
    have := Scheme.Pullback.range_fst (pullback.snd f ι) g₀
    rw [hg₀] at this
    exact this.symm

  let e := pullbackLeftPullbackSndIso f ι g₀
  have hsurj : Function.Surjective e.inv.base := fun y =>
    ⟨e.hom.base y, by
      have := congr_arg (fun h : pullback (pullback.snd f ι) g₀ ⟶ _ => h.base y) e.hom_inv_id
      simpa using this⟩
  have hrange : Set.range (pullback.fst (pullback.snd f ι) g₀).base
      = (e.inv ≫ pullback.fst (pullback.snd f ι) g₀).base '' Set.univ := by
    rw [Set.image_univ]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, rfl⟩ := hsurj y
      exact ⟨w, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨e.inv.base w, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [hfib, hrange]
  exact huniv.image _ (e.inv ≫ pullback.fst (pullback.snd f ι) g₀).base.hom.continuous.continuousOn

theorem abelianSchemePropertyBundle_baseChange {R T : Type u} [CommRing R] [CommRing T] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hs : Smooth f) (hp : IsProper f)
    (W : Set ↥(Spec (CommRingCat.of R)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (hι : ∀ y, ι.base y ∈ W)
    (L : RelativeGroupLaw T (pullback.snd f ι)) :
    AbelianSchemePropertyBundle T (pullback.snd f ι) where
  smooth := MorphismProperty.pullback_snd (P := @Smooth) _ _ hs
  proper := MorphismProperty.pullback_snd (P := @IsProper) _ _ hp
  connectedFibres t := by
    obtain ⟨k, _, _, g₀, hg₀⟩ := exists_geomPoint t
    refine isConnected_preimage_of_geomPoint f ι t g₀ hg₀ (hfib k (g₀ ≫ ι) ?_)
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hι _
  hasGroupLaw := ⟨L⟩

theorem specMap_localizationAtPrime_mem {R : Type u} [CommRing R] (W : Set ↥(Spec (CommRingCat.of R)))
    (hW : IsOpen W) (s : Spec (CommRingCat.of R)) (hsW : s ∈ W)
    (y : Spec (CommRingCat.of (Localization.AtPrime s.asIdeal))) :
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime s.asIdeal)))).base y ∈ W := by
  have hy : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime s.asIdeal)) y
      ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime s.asIdeal))) := Set.mem_range_self _
  rw [PrimeSpectrum.localization_comap_range (Localization.AtPrime s.asIdeal) s.asIdeal.primeCompl] at hy
  have hle : PrimeSpectrum.comap (algebraMap R (Localization.AtPrime s.asIdeal)) y ≤ s := by
    intro x hx
    by_contra h
    exact Set.disjoint_left.mp hy h hx
  exact ((PrimeSpectrum.le_iff_specializes _ _).mp hle).mem_open hW hsW

theorem descend {R : Type u} [CommRing R] (S T : Type u) [CommRing S] [CommRing T] [Algebra S T]
    [Module.FaithfullyFlat S T] (φ : R →+* S) {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (hs : Smooth f) (hp : IsProper f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R)))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (hφ : ∀ y, (Spec.map (CommRingCat.ofHom φ)).base y ∈ W)
    (L' : RelativeGroupLaw T (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))))
    (hL' : (L'.one (𝟙 _)).1 =
      pullback.lift (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp])) :
    ∃ L : RelativeGroupLaw S (pullback.snd f (Spec.map (CommRingCat.ofHom φ))),
      (L.one (𝟙 _)).1 = pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by

  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ Spec.map (CommRingCat.ofHom φ)
      = Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]

  let c : pullback f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))
      ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)))
      (by rw [pullback.condition, Category.assoc, hcomp])
  have hc : IsPullback c (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (Spec.map (CommRingCat.ofHom (algebraMap S T))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ)))
    rw [pullback.lift_fst, hcomp]
    exact IsPullback.of_hasPullback _ _

  have hι : ∀ y, (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ))).base y ∈ W := by
    intro y
    rw [← hcomp, Scheme.Hom.comp_apply]
    exact hφ _
  have hA' := abelianSchemePropertyBundle_baseChange f hs hp W hfib _ hι L'

  let eS : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) :=
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
        (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]),
      by rw [pullback.lift_snd]⟩
  have he' : (L'.one (𝟙 _)).1 ≫ c = Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ eS.1 := by
    rw [hL']
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst,
        ← Category.assoc, hcomp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        Category.assoc, pullback.lift_snd, Category.comp_id]
  obtain ⟨L, hL⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
      T (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) eS
      (pullback.snd f (Spec.map (CommRingCat.ofHom ((algebraMap S T).comp φ)))) c hc hA' L' he'
  exact ⟨L, hL⟩

end GoodReductionJacobian.LLocalReduce

open GoodReductionJacobian.LLocalReduce in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (hs : Smooth f) (hp : IsProper f)
    (N : ℕ) (ι : A ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (hι : IsClosedImmersion ι)
    (hιf : ι ≫ ProjSpace.π R N = f)
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (W : Set ↥(Spec (CommRingCat.of R))) (hW : IsClopen W)
    (hc : ∀ s : Spec (CommRingCat.of R), s ∈ W → _root_.IsConnected (f.base ⁻¹' {s}))
    (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
    (s : Spec (CommRingCat.of R)) (hsW : s ∈ W) :
    ∃ L : RelativeGroupLaw (Localization.AtPrime s.asIdeal)
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime s.asIdeal))))),
      (L.one (𝟙 _)).1 =
        pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime s.asIdeal))) ≫ e.1) (𝟙 _)
          (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := by
  haveI : Module.FaithfullyFlat (Localization.AtPrime s.asIdeal)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal)) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal _
  obtain ⟨L', hL'⟩ :=
    GoodReductionJacobian.exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_isNoetherianRing_of_isClopen
      f hs hp N ι hι hιf e W hW hc hfib s hsW
  exact descend (Localization.AtPrime s.asIdeal)
    (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) (Localization.AtPrime s.asIdeal))
    (algebraMap R (Localization.AtPrime s.asIdeal)) f hs hp e W hfib
    (specMap_localizationAtPrime_mem W hW.isOpen s hsW) L' hL'

end S_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen
end P2MW
export P2MW.S_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_localizationAtPrime_one_eq_of_isNoetherianRing_of_isClopen (solution)
