-- Prove2me | solution 1 for GoodReductionJacobian.exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e25756b4-4946-554c-92a9-d9aeeafeef16

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_section
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_one_eq_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isCommutative
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase"
p2m_attr_erase "simp" "AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian NeronModelInfra"

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing RelativeGroupLaw.exists_one_eq_of_section RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle AbelianSchemePropertyBundle.isCommutative RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat"
namespace TowerLaw
p2m_open "GoodReductionJacobian"

section Restrict

variable {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T)
  {A₀ A : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of T)} {f : A ⟶ Spec (CommRingCat.of T')}
  {g : A₀ ⟶ A} (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))

def pushPt {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)} (P : SchemeHomOver t f₀) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom π)) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩

def pullPt {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)}
    (Q : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom π)) f) : SchemeHomOver t f₀ :=
  ⟨hg.lift Q.1 t Q.2, hg.lift_snd _ _ _⟩

@[scoped simp] theorem pushPt_coe {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)} (P : SchemeHomOver t f₀) :
    (pushPt π hg P).1 = P.1 ≫ g := rfl

@[scoped simp] theorem pullPt_coe {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)}
    (Q : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom π)) f) :
    (pullPt π hg Q).1 = hg.lift Q.1 t Q.2 := rfl

@[scoped simp] theorem pullPt_pushPt {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)} (P : SchemeHomOver t f₀) :
    pullPt π hg (pushPt π hg P) = P := by
  apply Subtype.ext
  apply hg.hom_ext
  · rw [pullPt_coe, hg.lift_fst, pushPt_coe]
  · rw [pullPt_coe, hg.lift_snd, P.2]

@[scoped simp] theorem pushPt_pullPt {S : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)}
    (Q : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom π)) f) :
    pushPt π hg (pullPt π hg Q) = Q := by
  apply Subtype.ext
  rw [pushPt_coe, pullPt_coe, hg.lift_fst]

theorem pushPt_schemeHomOverComp {S S' : Scheme.{u}} {t : S ⟶ Spec (CommRingCat.of T)}
    {t' : S' ⟶ Spec (CommRingCat.of T)} (ψ : S' ⟶ S) (hψ : ψ ≫ t = t') (P : SchemeHomOver t f₀) :
    pushPt π hg (schemeHomOverComp ψ hψ P) =
      schemeHomOverComp ψ (by rw [← Category.assoc, hψ]) (pushPt π hg P) := by
  apply Subtype.ext
  simp only [pushPt_coe, schemeHomOverComp_coe, Category.assoc]

def restrict (M : RelativeGroupLaw T' f) : RelativeGroupLaw T f₀ where
  mul t x y := pullPt π hg (M.mul _ (pushPt π hg x) (pushPt π hg y))
  one t := pullPt π hg (M.one _)
  inv t x := pullPt π hg (M.inv _ (pushPt π hg x))
  mul_assoc t x y z := by simp only [pushPt_pullPt, M.mul_assoc]
  one_mul t x := by simp only [pushPt_pullPt, M.one_mul, pullPt_pushPt]
  mul_one t x := by simp only [pushPt_pullPt, M.mul_one, pullPt_pushPt]
  inv_mul_cancel t x := by simp only [pushPt_pullPt, M.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply Subtype.ext
    apply hg.hom_ext
    · rw [schemeHomOverComp_coe, pullPt_coe, pullPt_coe, Category.assoc, hg.lift_fst, hg.lift_fst]
      have h := congrArg Subtype.val
        (M.mul_natural (t ≫ Spec.map (CommRingCat.ofHom π)) (t' ≫ Spec.map (CommRingCat.ofHom π)) ψ
          (by rw [← Category.assoc, hψ]) (pushPt π hg x) (pushPt π hg y))
      rw [schemeHomOverComp_coe] at h
      rw [h, pushPt_schemeHomOverComp, pushPt_schemeHomOverComp]
    · rw [schemeHomOverComp_coe, pullPt_coe, pullPt_coe, Category.assoc, hg.lift_snd, hg.lift_snd]
      exact hψ

theorem restrict_mul_coe (M : RelativeGroupLaw T' f) {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T))
    (x y : SchemeHomOver t f₀) :
    ((restrict π hg M).mul t x y).1 ≫ g =
      (M.mul (t ≫ Spec.map (CommRingCat.ofHom π)) (pushPt π hg x) (pushPt π hg y)).1 :=
  hg.lift_fst _ _ _

theorem restrict_one_coe (M : RelativeGroupLaw T' f) {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of T)) :
    ((restrict π hg M).one t).1 ≫ g = (M.one (t ≫ Spec.map (CommRingCat.ofHom π))).1 :=
  hg.lift_fst _ _ _

end Restrict

section Connected

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

theorem univ_connected_of_aspb {k : Type u} [Field k] {X : Scheme.{u}} {h : X ⟶ Spec (CommRingCat.of k)}
    (hA : AbelianSchemePropertyBundle k h) : _root_.IsConnected (Set.univ : Set ↥X) := by
  have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
  have hc := hA.connectedFibres x₀
  rwa [show h.base ⁻¹' {x₀} = Set.univ from
    Set.eq_univ_of_forall fun y => @Subsingleton.elim _ hsub _ _] at hc

theorem univ_connected_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (hX : _root_.IsConnected (Set.univ : Set ↥X)) :
    _root_.IsConnected (Set.univ : Set ↥Y) := by
  have hsurj : Function.Surjective e.hom.base := fun y =>
    ⟨e.inv.base y, by
      have := congr_arg (fun h : Y ⟶ Y => h.base y) e.inv_hom_id
      simpa using this⟩
  rw [← hsurj.range_eq, ← Set.image_univ]
  exact hX.image _ e.hom.base.hom.continuous.continuousOn

theorem isConnected_fibre {R T k : Type u} [CommRing R] [CommRing T] [Field k] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of T)) (g₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of T))
    (hg₀ : Set.range g₀.base = {t})
    (huniv : _root_.IsConnected (Set.univ : Set ↥(pullback f (g₀ ≫ ι)))) :
    _root_.IsConnected ((pullback.snd f ι).base ⁻¹' {t}) := by
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

end Connected

section Tower

variable {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
  (hs : Smooth f) (hp : IsProper f)
  (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
  (W : Set ↥(Spec (CommRingCat.of R)))
  (hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    Set.range s.base ⊆ W → AbelianSchemePropertyBundle k (pullback.snd f s))
  (O' : Type u) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O'] (φ : R →+* O')
  (hφ : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint O') ∈ W)

local notation "𝔪" => IsLocalRing.maximalIdeal O'
local notation "f′" => pullback.snd f (Spec.map (CommRingCat.ofHom φ))
local notation "Tq" n:arg => O' ⧸ IsLocalRing.maximalIdeal O' ^ (n + 1)
local notation "πq" n:arg => (Ideal.Quotient.factor
  (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
    IsLocalRing.maximalIdeal O' ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal O' ^ (n + 1)))
local notation "Xq" n:arg => adicThickening (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n
local notation "fq" n:arg => adicThickeningToBase (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n
local notation "gq" n:arg => adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n

theorem pow_ne_top (n : ℕ) : 𝔪 ^ (n + 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal O').ne_top (Ideal.pow_le_self n.succ_ne_zero)

scoped instance nontrivial_Tq (n : ℕ) : Nontrivial (Tq n) :=
  Ideal.Quotient.nontrivial_iff.mpr (pow_ne_top O' n)

scoped instance isLocalRing_Tq (n : ℕ) : IsLocalRing (Tq n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

scoped instance isNoetherianRing_Tq (n : ℕ) : IsNoetherianRing (Tq n) :=
  isNoetherianRing_of_surjective O' _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem isArtinianRing_Tq (n : ℕ) : IsArtinianRing (Tq n) := by
  refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ ?_
  refine ⟨⟨inferInstance, Ideal.pow_le_self n.succ_ne_zero⟩, fun q hq hqle x hx => ?_⟩
  exact hq.1.mem_of_pow_mem (n + 1) (hq.2 (Ideal.pow_mem_pow hx (n + 1)))

theorem πq_surjective (n : ℕ) : Function.Surjective (πq n) :=
  Ideal.Quotient.factor_surjective _

theorem πq_ker_nilpotent (n : ℕ) : IsNilpotent (RingHom.ker (πq n)) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.zero_eq_bot, eq_bot_iff,
    ← Ideal.map_quotient_self (𝔪 ^ (n + 1 + 1))]
  refine Ideal.map_mono ?_
  rw [← pow_mul]
  exact Ideal.pow_le_pow_right (by omega)

theorem isPullback_transition (n : ℕ) :
    IsPullback (gq n) (fq n) (fq (n + 1)) (Spec.map (CommRingCat.ofHom (πq n))) := by
  refine IsPullback.of_right (h₁₂ := adicThickeningι f′ 𝔪 (n + 1)) (v₁₃ := f′)
    (h₂₂ := adicThickeningBase 𝔪 (n + 1)) ?_ (adicThickeningTransition_toBase f′ 𝔪 n) ?_
  · rw [adicThickeningTransition_ι, adicThickeningBase_succ_comp]
    exact IsPullback.of_hasPullback f′ (adicThickeningBase 𝔪 n)
  · exact IsPullback.of_hasPullback f′ (adicThickeningBase 𝔪 (n + 1))

def eO : SchemeHomOver (𝟙 (Spec (CommRingCat.of O'))) f′ :=
  ⟨pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
      (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem eO_coe : (eO f e O' φ).1 = pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
      (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]) := rfl

def eq_ (n : ℕ) : SchemeHomOver (𝟙 (Spec (CommRingCat.of (Tq n)))) (fq n) :=
  ⟨pullback.lift (adicThickeningBase 𝔪 n ≫ (eO f e O' φ).1) (𝟙 _)
      (by rw [Category.assoc, (eO f e O' φ).2, Category.comp_id, Category.id_comp]),
    by rw [adicThickeningToBase_def]; exact pullback.lift_snd _ _ _⟩

theorem eq_coe_ι (n : ℕ) : (eq_ f e O' φ n).1 ≫ adicThickeningι f′ 𝔪 n = adicThickeningBase 𝔪 n ≫ (eO f e O' φ).1 := by
  rw [adicThickeningι_def]; exact pullback.lift_fst _ _ _

theorem eq_transition (n : ℕ) :
    (eq_ f e O' φ n).1 ≫ gq n = Spec.map (CommRingCat.ofHom (πq n)) ≫ (eq_ f e O' φ (n + 1)).1 := by
  have hP := isPullback_transition f O' φ n

  apply pullback.hom_ext
  · show _ ≫ adicThickeningι f′ 𝔪 (n + 1) = _ ≫ adicThickeningι f′ 𝔪 (n + 1)
    rw [Category.assoc, adicThickeningTransition_ι, eq_coe_ι, Category.assoc, eq_coe_ι, ← Category.assoc,
      adicThickeningBase_succ_comp]
  · show _ ≫ adicThickeningToBase f′ 𝔪 (n + 1) = _ ≫ adicThickeningToBase f′ 𝔪 (n + 1)
    rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, (eq_ f e O' φ n).2,
      Category.id_comp, Category.assoc, (eq_ f e O' φ (n + 1)).2, Category.comp_id]

include hs in
theorem smooth_fq (n : ℕ) : Smooth (fq n) :=
  MorphismProperty.pullback_snd (P := @Smooth) _ _ (MorphismProperty.pullback_snd (P := @Smooth) _ _ hs)

include hp in
theorem isProper_fq (n : ℕ) : IsProper (fq n) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ (MorphismProperty.pullback_snd (P := @IsProper) _ _ hp)

theorem adicThickeningBase_apply (n : ℕ) (y : Spec (CommRingCat.of (Tq n))) :
    (adicThickeningBase 𝔪 n).base y = IsLocalRing.closedPoint O' := by
  haveI : IsLocalHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hy : y = IsLocalRing.closedPoint (Tq n) := by

    apply PrimeSpectrum.ext
    refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le y.2.ne_top ?_).symm
    intro x hx

    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hxm : x ∈ 𝔪 := by
      by_contra h
      exact hx (((IsLocalRing.notMem_maximalIdeal.mp h).map (Ideal.Quotient.mk (𝔪 ^ (n + 1)))))
    have hnil : (Ideal.Quotient.mk (𝔪 ^ (n + 1)) x) ^ (n + 1) = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hxm _
    exact y.2.mem_of_pow_mem _ (hnil ▸ y.asIdeal.zero_mem)
  rw [hy]
  exact IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (𝔪 ^ (n + 1)))

include hφ hfib in

theorem isConnected_fibre_fq (n : ℕ) (t : Spec (CommRingCat.of (Tq n))) :
    _root_.IsConnected ((fq n).base ⁻¹' {t}) := by
  obtain ⟨k, _, _, g₀, hg₀⟩ := exists_geomPoint t

  have hW : Set.range ((g₀ ≫ adicThickeningBase 𝔪 n) ≫ Spec.map (CommRingCat.ofHom φ)).base ⊆ W := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, adicThickeningBase_apply]
    exact hφ
  have hA := hfib k _ hW
  have h1 := univ_connected_of_aspb hA
  have h2 := univ_connected_of_iso
    (pullbackLeftPullbackSndIso f (Spec.map (CommRingCat.ofHom φ)) (g₀ ≫ adicThickeningBase 𝔪 n)).symm h1
  rw [adicThickeningToBase_def]
  exact isConnected_fibre f′ (adicThickeningBase 𝔪 n) t g₀ hg₀ h2

include hs hp hφ hfib in

theorem exists_law_zero :
    ∃ L : RelativeGroupLaw (Tq 0) (fq 0), (L.one (𝟙 _)).1 = (eq_ f e O' φ 0).1 := by
  haveI hmax : (𝔪 ^ (0 + 1)).IsMaximal := by rw [zero_add, pow_one]; infer_instance
  letI instF : Field (Tq 0) := Ideal.Quotient.field _
  let k : Type u := AlgebraicClosure (Tq 0)

  let sbar : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k)) ≫ adicThickeningBase 𝔪 0 ≫
      Spec.map (CommRingCat.ofHom φ)
  have hW : Set.range sbar.base ⊆ W := by
    rintro _ ⟨x, rfl⟩
    simp only [sbar]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, adicThickeningBase_apply]
    exact hφ
  have hA := hfib k sbar hW
  obtain ⟨Lk⟩ := hA.hasGroupLaw

  let ek : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (pullback.snd f sbar) :=
    ⟨pullback.lift (sbar ≫ e.1) (𝟙 _) (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp]),
      pullback.lift_snd _ _ _⟩
  obtain ⟨L', hL', -⟩ := RelativeGroupLaw.exists_one_eq_of_section Lk ek

  let c₁ : pullback f sbar ⟶ pullback f (Spec.map (CommRingCat.ofHom φ)) :=
    pullback.lift (pullback.fst f sbar)
      (pullback.snd f sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k)) ≫ adicThickeningBase 𝔪 0)
      (by rw [pullback.condition]; simp only [sbar, Category.assoc])
  let c : pullback f sbar ⟶ Xq 0 :=
    pullback.lift c₁ (pullback.snd f sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k)))
      (by simp only [c₁, pullback.lift_snd, Category.assoc])
  have hcι : c ≫ adicThickeningι f′ 𝔪 0 = c₁ := by
    rw [adicThickeningι_def]; exact pullback.lift_fst _ _ _
  have hcf : c ≫ fq 0 = pullback.snd f sbar ≫ Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k)) := by
    rw [adicThickeningToBase_def]; exact pullback.lift_snd _ _ _
  have hbig : IsPullback (adicThickeningι f′ 𝔪 0 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ))) (fq 0) f
      (adicThickeningBase 𝔪 0 ≫ Spec.map (CommRingCat.ofHom φ)) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback f′ (adicThickeningBase 𝔪 0))
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ)))
  have hc : IsPullback c (pullback.snd f sbar) (fq 0) (Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k))) := by
    refine IsPullback.of_right ?_ hcf hbig
    have : c ≫ adicThickeningι f′ 𝔪 0 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom φ)) = pullback.fst f sbar := by
      rw [← Category.assoc, hcι]; exact pullback.lift_fst _ _ _
    rw [this]
    exact IsPullback.of_hasPullback f sbar

  haveI : Module.FaithfullyFlat (Tq 0) k := inferInstance
  have he' : (L'.one (𝟙 (Spec (CommRingCat.of k)))).1 ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap (Tq 0) k)) ≫ (eq_ f e O' φ 0).1 := by
    rw [hL']
    apply pullback.hom_ext
    · show _ ≫ adicThickeningι f′ 𝔪 0 = _ ≫ adicThickeningι f′ 𝔪 0
      rw [Category.assoc, hcι, Category.assoc, eq_coe_ι]
      apply pullback.hom_ext
      · simp only [c₁, ek, Category.assoc, pullback.lift_fst, eO_coe, sbar]
      · simp only [c₁, ek, Category.assoc, pullback.lift_snd, eO_coe, pullback.lift_snd_assoc,
          Category.id_comp, Category.comp_id]
    · show _ ≫ fq 0 = _ ≫ fq 0
      rw [Category.assoc, hcf, ← Category.assoc, ek.2, Category.id_comp, Category.assoc, (eq_ f e O' φ 0).2,
        Category.comp_id]
  obtain ⟨L₀, hL₀⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_one_eq_of_abelianSchemePropertyBundle_of_isPullback_of_faithfullyFlat
      k (fq 0) (eq_ f e O' φ 0) (pullback.snd f sbar) c hc hA L' he'
  exact ⟨L₀, hL₀⟩

include hs hp e hφ hfib in

theorem aspb_fq : ∀ n : ℕ, AbelianSchemePropertyBundle (Tq n) (fq n)
  | 0 => by
    obtain ⟨L₀, -⟩ := exists_law_zero f hs hp e W hfib O' φ hφ
    exact ⟨smooth_fq f hs O' φ 0, isProper_fq f hp O' φ 0, isConnected_fibre_fq f W hfib O' φ hφ 0, ⟨L₀⟩⟩
  | n + 1 => by
    have h₀ := aspb_fq n
    obtain ⟨L₀⟩ := h₀.hasGroupLaw
    have hcomm : L₀.IsCommutative := AbelianSchemePropertyBundle.isCommutative h₀ L₀
    haveI := isArtinianRing_Tq O' (n + 1)
    obtain ⟨L, _, hA, _⟩ :=
      RelativeGroupLaw.exists_isCommutative_comp_eq_mul_of_isPullback_of_isNilpotent_ker_of_isLocalRing
        (Tq (n + 1)) (Tq n) (πq n) (πq_surjective O' n) (πq_ker_nilpotent O' n) (fq n) L₀ hcomm h₀ (fq (n + 1))
        (smooth_fq f hs O' φ (n + 1)) (isProper_fq f hp O' φ (n + 1)) (gq n) (isPullback_transition f O' φ n)
    exact hA

include hs hp hφ hfib in
theorem main :
    ∃ L : ∀ n : ℕ, RelativeGroupLaw (Tq n) (fq n),
      (∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫ adicThickeningι f′ 𝔪 n =
        adicThickeningBase 𝔪 n ≫
          pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
            (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp])) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (Tq n)))
        (P Q : SchemeHomOver t (fq n)),
        ((L n).mul t P Q).1 ≫ gq n =
          ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (πq n)))
            ⟨P.1 ≫ gq n, by rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gq n, by rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) := by
  have hA := aspb_fq f hs hp e W hfib O' φ hφ
  have hex : ∀ n : ℕ, ∃ L : RelativeGroupLaw (Tq n) (fq n), L.one (𝟙 _) = eq_ f e O' φ n := fun n => by
    obtain ⟨L₀⟩ := (hA n).hasGroupLaw
    obtain ⟨L, h, -⟩ := RelativeGroupLaw.exists_one_eq_of_section L₀ (eq_ f e O' φ n)
    exact ⟨L, h⟩
  choose L hL using hex
  refine ⟨L, fun n => ?_, fun n T t P Q => ?_⟩
  · rw [hL n, eq_coe_ι, eO_coe]
  · have key : restrict (πq n) (isPullback_transition f O' φ n) (L (n + 1)) = L n := by
      apply RelativeGroupLaw.eq_of_one_eq_of_abelianSchemePropertyBundle (hA n)
      rw [hL n]
      apply Subtype.ext
      apply (isPullback_transition f O' φ n).hom_ext
      · rw [restrict_one_coe, eq_transition]
        have h1 := congrArg Subtype.val ((L (n + 1)).one_natural (𝟙 _)
          (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (πq n))) (Spec.map (CommRingCat.ofHom (πq n)))
          (by rw [Category.comp_id, Category.id_comp]))
        rw [schemeHomOverComp_coe] at h1
        rw [← h1, hL (n + 1)]
      · rw [((restrict (πq n) (isPullback_transition f O' φ n) (L (n + 1))).one (𝟙 _)).2,
          (eq_ f e O' φ n).2]
    have hmul := restrict_mul_coe (πq n) (isPullback_transition f O' φ n) (L (n + 1)) t P Q
    rw [key] at hmul
    exact hmul

end Tower

end GoodReductionJacobian.TowerLaw
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian.TowerLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen.GoodReductionJacobian.TowerLaw"

open GoodReductionJacobian.TowerLaw in
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
    (O' : Type u) [CommRing O'] [IsLocalRing O'] [IsNoetherianRing O'] (φ : R →+* O')
    (hφ : (Spec.map (CommRingCat.ofHom φ)).base (IsLocalRing.closedPoint O') ∈ W) :
    ∃ L : ∀ n : ℕ, RelativeGroupLaw (O' ⧸ IsLocalRing.maximalIdeal O' ^ (n + 1))
        (adicThickeningToBase (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n),
      (∀ n : ℕ, ((L n).one (𝟙 _)).1 ≫
          adicThickeningι (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n =
        adicThickeningBase (IsLocalRing.maximalIdeal O') n ≫
          pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ e.1) (𝟙 _)
            (by rw [Category.assoc, e.2, Category.comp_id, Category.id_comp])) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (O' ⧸ IsLocalRing.maximalIdeal O' ^ (n + 1))))
        (P Q : SchemeHomOver t (adicThickeningToBase (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n)),
        ((L n).mul t P Q).1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n =
          ((L (n + 1)).mul (t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
              (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) :
                IsLocalRing.maximalIdeal O' ^ (n + 1 + 1) ≤ IsLocalRing.maximalIdeal O' ^ (n + 1)))))
            ⟨P.1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n, by
              rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ adicThickeningTransition (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) (IsLocalRing.maximalIdeal O') n, by
              rw [Category.assoc, adicThickeningTransition_toBase, ← Category.assoc, Q.2]⟩).1) :=
  main f hs hp e W hfib O' φ hφ

end S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen
end P2MW
export P2MW.S_GoodReductionJacobian_exists_forall_relativeGroupLaw_adicThickening_one_eq_of_isNoetherianRing_of_isClopen (solution)
