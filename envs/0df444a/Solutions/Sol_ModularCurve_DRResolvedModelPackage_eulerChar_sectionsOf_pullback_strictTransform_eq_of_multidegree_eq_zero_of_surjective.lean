-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b2e29bf6-bb70-5029-8ae4-d90bc115f378

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support
import Theorems.Thm_AlgebraicGeometry_RelPicard_eulerChar_sectionsOf_pullback_foldr_sectionTwist_tensor_eq_add_sum
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorUnit_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4
import Theorems.Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl
import Theorems.Thm_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl
import Theorems.Thm_TwoChartCech_Sections_nonempty_linearEquiv_H0_and_H1_of_linearEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open AlgebraicCurve IsLocalRing ModularCurve.PlaceSpecialization

open AlgebraicGeometry.RelPicard

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry"

noncomputable section

namespace K5biiTransport

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme"

section Functoriality
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

section Iso
variable {L L' : X.Modules} (e : L ≅ L')

def appEquiv (U : X.Opens) : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(L', U) :=
  { toFun := fun t => e.hom.app U t
    invFun := fun t => e.inv.app U t
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r t => Scheme.Modules.Hom.app_smul e.hom r t
    left_inv := fun t => by
      change (e.hom ≫ e.inv).app U t = t
      rw [e.hom_inv_id]; rfl
    right_inv := fun t => by
      change (e.inv ≫ e.hom).app U t = t
      rw [e.inv_hom_id]; rfl }

theorem appEquiv_map {U V : X.Opens} (h : V ≤ U) (t : Γ(L, U)) :
    appEquiv e V (L.presheaf.map (homOfLE h).op t) = L'.presheaf.map (homOfLE h).op (appEquiv e U t) := by
  have := e.hom.val.naturality (homOfLE h).op
  exact congrArg (fun φ => (ModuleCat.Hom.hom φ) t) this

def isoM0 : (𝒱.sectionsOf c L).M0 ≃ₗ[R] (𝒱.sectionsOf c L').M0 :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L 𝒱.U0
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L' 𝒱.U0
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L 𝒱.U0
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L' 𝒱.U0
  (appEquiv e 𝒱.U0).restrictScalars R
def isoM1 : (𝒱.sectionsOf c L).M1 ≃ₗ[R] (𝒱.sectionsOf c L').M1 :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L 𝒱.U1
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L' 𝒱.U1
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L 𝒱.U1
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L' 𝒱.U1
  (appEquiv e 𝒱.U1).restrictScalars R
def isoM01 : (𝒱.sectionsOf c L).M01 ≃ₗ[R] (𝒱.sectionsOf c L').M01 :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L (𝒱.U0 ⊓ 𝒱.U1)
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c L' (𝒱.U0 ⊓ 𝒱.U1)
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L (𝒱.U0 ⊓ 𝒱.U1)
  haveI := Scheme.TwoAffineOpenCover.isScalarTower_sections c L' (𝒱.U0 ⊓ 𝒱.U1)
  (appEquiv e (𝒱.U0 ⊓ 𝒱.U1)).restrictScalars R

theorem isoM01_r0 (t) : isoM01 𝒱 c e ((𝒱.sectionsOf c L).r0 t) = (𝒱.sectionsOf c L').r0 (isoM0 𝒱 c e t) :=
  appEquiv_map e inf_le_left t
theorem isoM01_r1 (t) : isoM01 𝒱 c e ((𝒱.sectionsOf c L).r1 t) = (𝒱.sectionsOf c L').r1 (isoM1 𝒱 c e t) :=
  appEquiv_map e inf_le_right t

end Iso

theorem eulerChar_congr {L L' : X.Modules} (e : L ≅ L') :
    (Module.finrank R (𝒱.sectionsOf c L).H0 : ℤ) - Module.finrank R (𝒱.sectionsOf c L).H1 =
      (Module.finrank R (𝒱.sectionsOf c L').H0 : ℤ) - Module.finrank R (𝒱.sectionsOf c L').H1 := by
  obtain ⟨⟨-, ⟨e1⟩⟩, h0, -⟩ := TwoChartCech.Sections.nonempty_linearEquiv_H0_and_H1_of_linearEquiv
    (𝒱.sectionsOf c L) (𝒱.sectionsOf c L') (isoM0 𝒱 c e) (isoM1 𝒱 c e) (isoM01 𝒱 c e) (isoM01_r0 𝒱 c e) (isoM01_r1 𝒱 c e)
  rw [h0, e1.finrank_eq]

end Functoriality

theorem TwoAffineOpenCover.ext' {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover} (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) :
    𝒱 = 𝒲 := by
  cases 𝒱; cases 𝒲
  simp only at h0 h1
  subst h0; subst h1
  rfl

variable {R : Type u} [CommRing R] {X X' : Scheme.{u}}

theorem exists_preimage_cover_forall_eulerChar_pullback_eq (x : X ⟶ Spec (CommRingCat.of R))
    (x' : X' ⟶ Spec (CommRingCat.of R)) (φ : X ≅ X') (hφ : φ.hom ≫ x' = x) (𝒱' : X'.TwoAffineOpenCover) :
    ∃ 𝒱 : X.TwoAffineOpenCover, 𝒱.U0 = φ.hom ⁻¹ᵁ 𝒱'.U0 ∧ 𝒱.U1 = φ.hom ⁻¹ᵁ 𝒱'.U1 ∧
      ∀ M' : X'.Modules,
        (Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H1 =
          (Module.finrank R (𝒱'.sectionsOf x' M').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' M').H1 := by
  obtain ⟨𝒱, h0, h1, -, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x' φ hφ 𝒱'
    (𝟙_ X'.Modules) _ (Iso.refl _)
  refine ⟨𝒱, h0, h1, fun M' => ?_⟩
  obtain ⟨𝒱₂, h0', h1', ⟨f0⟩, ⟨f1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x' φ hφ 𝒱'
    M' _ (Iso.refl _)
  obtain rfl : 𝒱₂ = 𝒱 := TwoAffineOpenCover.ext' (h0'.trans h0.symm) (h1'.trans h1.symm)
  rw [f0.finrank_eq, f1.finrank_eq]

theorem eulerChar_eq_iff_of_preimage_cover (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R))
    (φ : X ≅ X') (𝒱 : X.TwoAffineOpenCover) (𝒱' : X'.TwoAffineOpenCover)
    (h : ∀ M' : X'.Modules,
        (Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H1 =
          (Module.finrank R (𝒱'.sectionsOf x' M').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' M').H1)
    (M' N' : X'.Modules) :
    ((Module.finrank R (𝒱'.sectionsOf x' M').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' M').H1 =
        (Module.finrank R (𝒱'.sectionsOf x' N').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' N').H1) ↔
      ((Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H1 =
        (Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj N')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj N')).H1) := by
  rw [h M', h N']

theorem eulerChar_tensorUnit_eq_of_preimage_cover (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R))
    (φ : X ≅ X') (𝒱 : X.TwoAffineOpenCover) (𝒱' : X'.TwoAffineOpenCover)
    (h : ∀ M' : X'.Modules,
        (Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H1 =
          (Module.finrank R (𝒱'.sectionsOf x' M').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' M').H1) :
    (Module.finrank R (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank R (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 =
      (Module.finrank R (𝒱'.sectionsOf x' (𝟙_ X'.Modules)).H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' (𝟙_ X'.Modules)).H1 := by
  rw [← h (𝟙_ X'.Modules), eulerChar_congr 𝒱 x (Scheme.Modules.pullbackTensorUnitObjIso φ.hom)]

theorem exists_preimage_cover (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R)) (φ : X ≅ X')
    (hφ : φ.hom ≫ x' = x) (𝒱' : X'.TwoAffineOpenCover) :
    ∃ 𝒱 : X.TwoAffineOpenCover, 𝒱.U0 = φ.hom ⁻¹ᵁ 𝒱'.U0 ∧ 𝒱.U1 = φ.hom ⁻¹ᵁ 𝒱'.U1 ∧
      (∀ M' : X'.Modules,
        (Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H0 : ℤ) -
            Module.finrank R (𝒱.sectionsOf x ((Scheme.Modules.pullback φ.hom).obj M')).H1 =
          (Module.finrank R (𝒱'.sectionsOf x' M').H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' M').H1) ∧
      (Module.finrank R (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank R (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 =
        (Module.finrank R (𝒱'.sectionsOf x' (𝟙_ X'.Modules)).H0 : ℤ) - Module.finrank R (𝒱'.sectionsOf x' (𝟙_ X'.Modules)).H1 := by
  obtain ⟨𝒱, h0, h1, h⟩ := exists_preimage_cover_forall_eulerChar_pullback_eq x x' φ hφ 𝒱'
  exact ⟨𝒱, h0, h1, h, eulerChar_tensorUnit_eq_of_preimage_cover x x' φ 𝒱 𝒱' h⟩

end K5biiTransport

end

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry"

noncomputable section

namespace K5biiT3b

p2m_open "AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{u}} (χ : X.Modules → ℤ)
  (hiso : ∀ L L' : X.Modules, Nonempty (L ≅ L') → χ L = χ L')
  (hadd : ∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
    χ (L ⊗ L') = χ L + χ L' - χ (𝟙_ X.Modules))

include hiso hadd

omit hiso hadd in

theorem isInvertible_prod' {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (hI : ∀ i ∈ s, (I i).IsInvertible) :
    (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_eq_top]; exact isInvertible_top
  | insert a s has ih =>
    rw [Finset.prod_insert has]
    exact (hI a (Finset.mem_insert_self a s)).mul (ih fun i hi => hI i (Finset.mem_insert_of_mem hi))

theorem chi_invModule_mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    χ ((I * J).invModule) = χ I.invModule + χ J.invModule - χ (𝟙_ X.Modules) := by
  rw [hiso _ _ (hI.nonempty_mul_invModule_iso_tensor hJ), hadd _ _ hI.isInvertible_invModule hJ.isInvertible_invModule]

theorem chi_invModule_top : χ ((⊤ : X.IdealSheafData).invModule) = χ (𝟙_ X.Modules) := by
  have h := chi_invModule_mul χ hiso hadd (isInvertible_top (X := X)) isInvertible_top
  rw [← one_eq_top, mul_one] at h
  rw [← one_eq_top]
  linarith

theorem chi_invModule_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    χ ((I ^ n).invModule) = χ (𝟙_ X.Modules) + (n : ℤ) * (χ I.invModule - χ (𝟙_ X.Modules)) := by
  induction n with
  | zero => rw [pow_zero, one_eq_top, chi_invModule_top χ hiso hadd]; simp
  | succ n ih => rw [pow_succ, chi_invModule_mul χ hiso hadd (hI.pow n) hI, ih]; push_cast; ring

theorem chi_invModule_prod_pow {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (hI : ∀ i ∈ s, (I i).IsInvertible)
    (n : ι → ℕ) :
    χ ((∏ i ∈ s, I i ^ n i).invModule) =
      χ (𝟙_ X.Modules) + ∑ i ∈ s, (n i : ℤ) * (χ (I i).invModule - χ (𝟙_ X.Modules)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, one_eq_top, chi_invModule_top χ hiso hadd, add_zero]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has,
      chi_invModule_mul χ hiso hadd ((hI a (Finset.mem_insert_self a s)).pow _)
        (isInvertible_prod' s _ fun i hi => (hI i (Finset.mem_insert_of_mem hi)).pow _),
      chi_invModule_pow χ hiso hadd (hI a (Finset.mem_insert_self a s)),
      ih fun i hi => hI i (Finset.mem_insert_of_mem hi)]
    ring

theorem chi_module_eq {I : X.IdealSheafData} (hI : I.IsInvertible) :
    χ I.module = χ (𝟙_ X.Modules) - (χ I.invModule - χ (𝟙_ X.Modules)) := by
  have h := hiso _ _ hI.nonempty_module_tensor_invModule_iso.1
  rw [hadd _ _ hI.isInvertible_module hI.isInvertible_invModule] at h
  linarith

theorem chi_module_prod_pow {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (hI : ∀ i ∈ s, (I i).IsInvertible)
    (n : ι → ℕ) :
    χ ((∏ i ∈ s, I i ^ n i).module) =
      χ (𝟙_ X.Modules) - ∑ i ∈ s, (n i : ℤ) * (χ (I i).invModule - χ (𝟙_ X.Modules)) := by
  rw [chi_module_eq χ hiso hadd (isInvertible_prod' s _ fun i hi => (hI i hi).pow _),
    chi_invModule_prod_pow χ hiso hadd s I hI n]
  ring

theorem chi_invModule_prod_pow_tensor_module_prod_pow {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) (a b : ι → ℕ) :
    χ ((∏ i ∈ s, I i ^ a i).invModule ⊗ (∏ i ∈ s, I i ^ b i).module) =
      χ (𝟙_ X.Modules) + ∑ i ∈ s, ((a i : ℤ) - b i) * (χ (I i).invModule - χ (𝟙_ X.Modules)) := by
  rw [hadd _ _ (isInvertible_prod' s _ fun i hi => (hI i hi).pow _).isInvertible_invModule
      (isInvertible_prod' s _ fun i hi => (hI i hi).pow _).isInvertible_module,
    chi_invModule_prod_pow χ hiso hadd s I hI a, chi_module_prod_pow χ hiso hadd s I hI b]
  have hs : ∑ i ∈ s, ((a i : ℤ) - b i) * (χ (I i).invModule - χ (𝟙_ X.Modules)) =
      ∑ i ∈ s, (a i : ℤ) * (χ (I i).invModule - χ (𝟙_ X.Modules)) -
        ∑ i ∈ s, (b i : ℤ) * (χ (I i).invModule - χ (𝟙_ X.Modules)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs]; ring

end K5biiT3b

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve"

noncomputable section

namespace K5biiT3b

p2m_open "AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{u}} (χ : X.Modules → ℤ)
  (hiso : ∀ L L' : X.Modules, Nonempty (L ≅ L') → χ L = χ L')
  (hadd : ∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
    χ (L ⊗ L') = χ L + χ L' - χ (𝟙_ X.Modules))

include hiso hadd in
theorem chi_sum_eq_zero_of_prod_invModule_iso {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) (hprod : Nonempty ((∏ i ∈ s, I i).invModule ≅ 𝟙_ X.Modules)) :
    ∑ i ∈ s, (χ (I i).invModule - χ (𝟙_ X.Modules)) = 0 := by
  have h := chi_invModule_prod_pow χ hiso hadd s I hI (fun _ => 1)
  simp only [pow_one, Nat.cast_one, one_mul] at h
  rw [hiso _ _ hprod] at h
  linarith

end K5biiT3b

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase comp_support node comp_isInvertible width comp_prod strict_iso_inf Y edgePt_exhaust edgePt_mem regular comp_integral edgePt smoothOffEdges one_le_width comp toDR eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}

theorem prod_comp_eq_ofIdealTop (R : DRResolvedModelPackage p 𝔛 O κ toκ) :
    ∏ v, R.comp v = Scheme.IdealSheafData.ofIdealTop (Ideal.span {((p : ℕ) : Γ(R.Y, ⊤))}) := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [R.comp_prod U, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton, map_natCast]

theorem nonempty_invModule_prod_comp_iso_unit (R : DRResolvedModelPackage p 𝔛 O κ toκ) :
    Nonempty ((∏ v, R.comp v).invModule ≅ 𝟙_ R.Y.Modules) := by
  obtain ⟨t, -, ht⟩ := Scheme.Modules.exists_hom_tensorUnit_app_eq_smul ((p : ℕ) : Γ(R.Y, ⊤))
  have h := Scheme.IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal
    R.comp R.comp_isInvertible (fun _ => 1) t (by
      simp only [pow_one]
      rw [prod_comp_eq_ofIdealTop, Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul t _ ht])
  simp only [pow_one] at h
  exact h

end ModularCurve.DRResolvedModelPackage

end

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.ker_comp_of_isIso Scheme.Modules.Hom.app_smul Surjective Scheme.IdealSheafData.ideal_mul Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom inr_ne_inl Scheme.Modules.Hom IsFinite LocallyOfFiniteType Spec IsIntegral Scheme.IdealSheafData.range_subschemeι Spec.map Scheme LocallyOfFiniteType.jacobsonSpace Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.Hom.comp_base Scheme.IdealSheafData.ker_subschemeι IsClosedImmersion.spec_of_surjective IsClosedImmersion IsSeparated exists_isAffineOpen_mem_and_subset Scheme.Modules.pullbackCongr IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Modules.pullbackId Scheme.Modules IsClosedImmersion.isIso_of_ker_eq isIso_of_isClosedImmersion_of_surjective IsAffineHom Scheme.IdealSheafData.ofIdealTop Scheme.Pullback.exists_preimage_pullback Scheme.IdealSheafData.ext Scheme.Hom.comp_apply Scheme.IdealSheafData.ofIdealTop_ideal Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover.isScalarTower_sections RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support RelPicard.eulerChar_sectionsOf_pullback_foldr_sectionTwist_tensor_eq_add_sum RelPicard.isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Scheme.IdealSheafData.ideal_comap_of_le Scheme.IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Scheme.Modules.exists_hom_tensorUnit_app_eq_smul Scheme.Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso exists_over_hom_base_closedPoint_eq_of_isClosed_singleton"
p2m_open "AlgebraicGeometry"

variable {A Y Z : Scheme.{u}} (ι : A ⟶ Y) [IsClosedImmersion ι] (g : Z ⟶ Y) (J : Z.IdealSheafData)
  (hJ : ι.ker.comap g = J)

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso Modules.Hom.app_smul IdealSheafData.ideal_mul IdealSheafData.support_comap ringCatSheaf Modules.pullback Hom Γ empty Modules.Hom IdealSheafData.range_subschemeι IdealSheafData.ker_fst_of_isClosedImmersion Hom.comp_base IdealSheafData.ker_subschemeι affineOpens basicOpen Modules.pullbackCongr Modules.pullbackId Modules Opens residue IdealSheafData.ofIdealTop Pullback.exists_preimage_pullback IdealSheafData.ext Hom.comp_apply IdealSheafData.ofIdealTop_ideal IdealSheafData Modules.pullbackComp ΓSpecIso Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso Modules.IsInvertible Modules.isInvertible_unit TwoAffineOpenCover TwoAffineOpenCover.algebraOfHom TwoAffineOpenCover.moduleSectionsOfHom TwoAffineOpenCover.isScalarTower_sections Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso IdealSheafData.ideal_comap_of_le IdealSheafData.nonempty_invModule_prod_pow_iso_tensorUnit_of_prod_pow_eq_zeroSchemeIdeal Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub Modules.exists_hom_tensorUnit_app_eq_smul Modules.zeroSchemeIdeal_eq_ofIdealTop_of_app_eq_smul TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "ker_comp_of_isIso image app injective comp_base naturality comp_app cover continuous ker isClosedEmbedding comp_apply appLE finrank isInvertible_ker_of_comp_eq_id_of_mem_opens nonempty_pullback_ker_pow_invModule_iso_of_isIso" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in
omit [IsClosedImmersion ι] in
theorem Scheme.Hom.ker_pullback_snd_eq_comap [IsClosedImmersion ι] : (pullback.snd ι g).ker = ι.ker.comap g := by
  have h : IsPullback (pullback.snd ι g) (pullback.fst ι g) g ι := (IsPullback.of_hasPullback ι g).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

include hJ

def subschemeToPullbackOfComapEq : J.subscheme ⟶ pullback ι g :=
  IsClosedImmersion.lift (pullback.snd ι g) J.subschemeι
    (by rw [Scheme.Hom.ker_pullback_snd_eq_comap, hJ, Scheme.IdealSheafData.ker_subschemeι])

@[reassoc]
theorem subschemeToPullbackOfComapEq_snd : subschemeToPullbackOfComapEq ι g J hJ ≫ pullback.snd ι g = J.subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

theorem isIso_subschemeToPullbackOfComapEq : IsIso (subschemeToPullbackOfComapEq ι g J hJ) :=
  IsClosedImmersion.isIso_of_ker_eq _ (pullback.snd ι g) _ (subschemeToPullbackOfComapEq_snd ι g J hJ)
    (by rw [Scheme.Hom.ker_pullback_snd_eq_comap, hJ, Scheme.IdealSheafData.ker_subschemeι])

def subschemeIsoPullbackOfComapEq : J.subscheme ≅ pullback ι g :=
  letI := isIso_subschemeToPullbackOfComapEq ι g J hJ
  asIso (subschemeToPullbackOfComapEq ι g J hJ)

@[reassoc]
theorem subschemeIsoPullbackOfComapEq_hom_snd :
    (subschemeIsoPullbackOfComapEq ι g J hJ).hom ≫ pullback.snd ι g = J.subschemeι :=
  subschemeToPullbackOfComapEq_snd ι g J hJ

@[reassoc]
theorem subschemeIsoPullbackOfComapEq_hom_fst_ι :
    (subschemeIsoPullbackOfComapEq ι g J hJ).hom ≫ pullback.fst ι g ≫ ι = J.subschemeι ≫ g := by
  rw [pullback.condition, ← Category.assoc, subschemeIsoPullbackOfComapEq_hom_snd]

end AlgebraicGeometry

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "chainPos toBase comp_support node comp_isInvertible width comp_prod strict_iso_inf Y edgePt_exhaust edgePt_mem regular comp_integral edgePt smoothOffEdges one_le_width comp toDR eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4"
p2m_open "ModularCurve.DRResolvedModelPackage ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (R : DRResolvedModelPackage p 𝔛 O κ toκ) (w : X0MqComponents R.width)

private theorem _root_.ModularCurve.DRResolvedModelPackage.ker_subschemeι_comap_fst_eq :
    ((R.comp w).subschemeι).ker.comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ))) =
      (R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ))) := by
  rw [Scheme.IdealSheafData.ker_subschemeι]

p2m_export "ModularCurve.DRResolvedModelPackage" "ker_subschemeι_comap_fst_eq"

private def _root_.ModularCurve.DRResolvedModelPackage.compFibreIso :
    ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subscheme ≅
      pullback ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)) :=
  subschemeIsoPullbackOfComapEq (R.comp w).subschemeι (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ))) _
      (R.ker_subschemeι_comap_fst_eq w) ≪≫
    pullbackRightPullbackFstIso R.toBase (Spec.map (CommRingCat.ofHom toκ)) (R.comp w).subschemeι

p2m_export "ModularCurve.DRResolvedModelPackage" "compFibreIso"
@[reassoc]
theorem compFibreIso_hom_fst_subschemeι :
    (R.compFibreIso w).hom ≫ pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)) ≫
        (R.comp w).subschemeι =
      ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subschemeι ≫
        pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)) := by
  rw [compFibreIso, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
    subschemeIsoPullbackOfComapEq_hom_fst_ι]

@[reassoc]
theorem compFibreIso_hom_snd :
    (R.compFibreIso w).hom ≫ pullback.snd ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)) =
      ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subschemeι ≫
        pullback.snd R.toBase (Spec.map (CommRingCat.ofHom toκ)) := by
  rw [compFibreIso, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    subschemeIsoPullbackOfComapEq_hom_snd_assoc]

private def _root_.ModularCurve.DRResolvedModelPackage.compFibreIsoComp [IsIso (pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)))] :
    ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subscheme ≅ (R.comp w).subscheme :=
  R.compFibreIso w ≪≫ asIso (pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)))

p2m_export "ModularCurve.DRResolvedModelPackage" "compFibreIsoComp"
@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.compFibreIsoComp_hom_subschemeι
    [IsIso (pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)))] :
    (R.compFibreIsoComp w).hom ≫ (R.comp w).subschemeι =
      ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subschemeι ≫
        pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)) := by
  rw [compFibreIsoComp, Iso.trans_hom, asIso_hom, Category.assoc, compFibreIso_hom_fst_subschemeι]

p2m_export "ModularCurve.DRResolvedModelPackage" "compFibreIsoComp_hom_subschemeι compFibreIsoComp_hom_subschemeι_assoc"

@[reassoc]
private theorem _root_.ModularCurve.DRResolvedModelPackage.compFibreIsoComp_hom_yComp
    [IsIso (pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)))]
    (yComp : (R.comp w).subscheme ⟶ Spec (CommRingCat.of κ))
    (hy : pullback.fst ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ)) ≫ yComp =
      pullback.snd ((R.comp w).subschemeι ≫ R.toBase) (Spec.map (CommRingCat.ofHom toκ))) :
    (R.compFibreIsoComp w).hom ≫ yComp =
      ((R.comp w).comap (pullback.fst R.toBase (Spec.map (CommRingCat.ofHom toκ)))).subschemeι ≫
        pullback.snd R.toBase (Spec.map (CommRingCat.ofHom toκ)) := by
  rw [compFibreIsoComp, Iso.trans_hom, asIso_hom, Category.assoc, hy, compFibreIso_hom_snd]

p2m_export "ModularCurve.DRResolvedModelPackage" "compFibreIsoComp_hom_yComp compFibreIsoComp_hom_yComp_assoc"
end ModularCurve.DRResolvedModelPackage

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
namespace Sigma
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

abbrev tκ (toκ : O →+* κ) : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom toκ)

abbrev Jb (b : Fin 2) : (pullback 𝔛reg.toBase (tκ toκ)).IdealSheafData :=
  (𝔛reg.comp (Sum.inl b)).comap (pullback.fst 𝔛reg.toBase (tκ toκ))

abbrev yJ (b : Fin 2) : (Jb 𝔛reg b).subscheme ⟶ Spec (CommRingCat.of κ) :=
  (Jb 𝔛reg b).subschemeι ≫ pullback.snd 𝔛reg.toBase (tκ toκ)

theorem tκ_base_apply (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (x : Spec (CommRingCat.of κ)) : (tκ toκ).base x = IsLocalRing.closedPoint O := by

  haveI : IsLocalHom toκ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).mpr hna
    rw [hϖ, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    have h0 : toκ ((p : ℕ) * c) = 0 := by rw [map_mul, map_natCast, CharP.cast_eq_zero κ p, zero_mul]
    exact ha.ne_zero h0
  have hx : x = IsLocalRing.closedPoint κ := Subsingleton.elim _ _
  subst hx
  change PrimeSpectrum.comap (CommRingCat.ofHom toκ).hom (IsLocalRing.closedPoint κ) = IsLocalRing.closedPoint O
  rw [CommRingCat.hom_ofHom]
  exact IsLocalRing.comap_closedPoint toκ

theorem range_subset_smoothOffEdges (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (hσ0 : σ.1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges) :
    Set.range σ.1 ⊆ (𝔛reg.smoothOffEdges : Set 𝔛reg.Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.1.base.hom.continuous).mem_open
    𝔛reg.smoothOffEdges.isOpen hσ0

theorem notMem_support_Jb (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (b : Fin 2)
    (hmiss : σ.1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp (Sum.inl b)).support) :
    ∀ x ∈ Set.range (rigSection 𝔛reg.toBase (tκ toκ) σ), x ∉ (Jb 𝔛reg b).support := by
  rintro _ ⟨z, rfl⟩ hz
  rw [Scheme.IdealSheafData.support_comap] at hz
  change (pullback.fst 𝔛reg.toBase (tκ toκ)).base ((rigSection 𝔛reg.toBase (tκ toκ) σ).base z) ∈
    ((𝔛reg.comp (Sum.inl b)).support : Set 𝔛reg.Y) at hz
  have hcomp : rigSection 𝔛reg.toBase (tκ toκ) σ ≫ pullback.fst 𝔛reg.toBase (tκ toκ) = tκ toκ ≫ σ.1 := by
    unfold rigSection; exact pullback.lift_fst _ _ _
  rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, hcomp, Scheme.Hom.comp_base, TopCat.comp_app, tκ_base_apply hϖ] at hz
  exact hmiss hz

theorem ideal_finsetProd {X : Scheme} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]; rfl
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

theorem ideal_eq_top_of_support_inter_eq_empty {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (h : (I.support : Set X) ∩ U = ∅) : I.ideal U = ⊤ := by
  have h1 := I.coe_support_inter U
  rw [h] at h1
  have h2 := U.2.fromSpec_image_zeroLocus (I.ideal U)
  rw [← h1, Set.image_eq_empty] at h2
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h2

theorem exists_affineOpens_ideal_Jb_eq_bot (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (σ : SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (b : Fin 2)
    (honly : ∀ w, w ≠ Sum.inl b → σ.1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support) :
    ∃ V : (pullback 𝔛reg.toBase (tκ toκ)).affineOpens,
      Set.range (rigSection 𝔛reg.toBase (tκ toκ) σ) ⊆ ((V : (pullback 𝔛reg.toBase (tκ toκ)).Opens) : Set _) ∧
        (Jb 𝔛reg b).ideal V = ⊥ := by
  classical
  set y₀ : 𝔛reg.Y := σ.1.base (IsLocalRing.closedPoint O) with hy₀

  let W : 𝔛reg.Y.Opens := ⟨⋂ w, ⋂ (_ : w ≠ Sum.inl b), ((𝔛reg.comp w).support : Set 𝔛reg.Y)ᶜ,
    isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun _ => (𝔛reg.comp w).support.isClosed.isOpen_compl⟩
  have hyW : y₀ ∈ W := Set.mem_iInter₂.mpr fun w hw => honly w hw
  obtain ⟨V', hV', hyV', hV'W⟩ := exists_isAffineOpen_mem_and_subset hyW
  let V'a : 𝔛reg.Y.affineOpens := ⟨V', hV'⟩

  have htop : ∀ w, w ≠ Sum.inl b → (𝔛reg.comp w).ideal V'a = ⊤ := by
    intro w hw
    apply ideal_eq_top_of_support_inter_eq_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxV⟩
    have hxW : x ∈ (W : Set 𝔛reg.Y) := hV'W hxV
    exact (Set.mem_iInter₂.mp hxW w hw) hx

  have hcomp : (𝔛reg.comp (Sum.inl b)).ideal V'a = Ideal.span {((p : ℕ) : Γ(𝔛reg.Y, V'a))} := by
    rw [← 𝔛reg.comp_prod V'a, ideal_finsetProd, Finset.prod_eq_single (Sum.inl b)]
    · intro w _ hw
      rw [htop w hw, ← Ideal.one_eq_top]
    · intro h; exact absurd (Finset.mem_univ _) h

  haveI : IsAffineHom (pullback.fst 𝔛reg.toBase (tκ toκ)) := MorphismProperty.pullback_fst _ _ inferInstance
  have hle : (pullback.fst 𝔛reg.toBase (tκ toκ)) ⁻¹ᵁ V' ≤ (pullback.fst 𝔛reg.toBase (tκ toκ)) ⁻¹ᵁ (V'a : 𝔛reg.Y.Opens) := le_rfl
  refine ⟨⟨(pullback.fst 𝔛reg.toBase (tκ toκ)) ⁻¹ᵁ V', hV'.preimage _⟩, ?_, ?_⟩
  ·
    rintro _ ⟨z, rfl⟩
    change (pullback.fst 𝔛reg.toBase (tκ toκ)).base ((rigSection 𝔛reg.toBase (tκ toκ) σ).base z) ∈ (V' : Set 𝔛reg.Y)
    have hcomp : rigSection 𝔛reg.toBase (tκ toκ) σ ≫ pullback.fst 𝔛reg.toBase (tκ toκ) = tκ toκ ≫ σ.1 := by
      unfold rigSection; exact pullback.lift_fst _ _ _
    rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, hcomp, Scheme.Hom.comp_base, TopCat.comp_app, tκ_base_apply hϖ]
    exact hyV'
  ·
    rw [Scheme.IdealSheafData.ideal_comap_of_le _ _ V'a _ hle, hcomp, Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.span_singleton_eq_bot]

    let ψ := (pullback.snd 𝔛reg.toBase (tκ toκ)).appLE ⊤ ((pullback.fst 𝔛reg.toBase (tκ toκ)) ⁻¹ᵁ V') le_top
    have h1 : ((p : ℕ) : Γ(Spec (CommRingCat.of κ), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom p]
      change (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom ((p : ℕ) : κ) = 0
      rw [CharP.cast_eq_zero κ p, map_zero]
    rw [← map_natCast ψ.hom p, h1, map_zero]

theorem section_inputs (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (b : Fin 2) (j : Fin m) :
    ((sectionIdeal 𝔛reg.toBase (σ j) (tκ toκ)).comap (Jb 𝔛reg b).subschemeι).IsInvertible ∧
      IsFinite (((sectionIdeal 𝔛reg.toBase (σ j) (tκ toκ)).comap (Jb 𝔛reg b).subschemeι).subschemeι ≫ yJ 𝔛reg b) ∧
      ∀ q : Spec (CommRingCat.of κ),
        (((sectionIdeal 𝔛reg.toBase (σ j) (tκ toκ)).comap (Jb 𝔛reg b).subschemeι).subschemeι ≫ yJ 𝔛reg b).finrank q =
          (if v j = Sum.inl b then 1 else 0) := by
  obtain ⟨hj1, hj2, hj3⟩ := hv j
  by_cases hvb : v j = Sum.inl b
  · have hJ := exists_affineOpens_ideal_Jb_eq_bot 𝔛reg hϖ (σ j) b (fun w hw => hj3 w (hvb ▸ hw))
    have h := AlgebraicGeometry.RelPicard.isInvertible_comap_sectionIdeal_and_finrank_eq_one_of_ideal_eq_bot 𝔛reg.toBase
      𝔛reg.smoothOffEdges (σ j) (range_subset_smoothOffEdges 𝔛reg (σ j) hj1) (tκ toκ) (Jb 𝔛reg b) hJ
    refine ⟨h.1, h.2.1, fun q => ?_⟩
    rw [if_pos hvb]
    exact h.2.2 q
  · have hmiss : (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp (Sum.inl b)).support := hj3 _ (Ne.symm hvb)
    have h := AlgebraicGeometry.RelPicard.comap_sectionIdeal_eq_top_and_finrank_eq_zero_of_forall_notMem_support 𝔛reg.toBase
      (σ j) (tκ toκ) (Jb 𝔛reg b) (notMem_support_Jb 𝔛reg hϖ (σ j) b hmiss)
    refine ⟨h.2.1, h.2.2.1, fun q => ?_⟩
    rw [if_neg hvb]
    exact h.2.2.2 q

theorem eulerChar_fibre (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (b : Fin 2) [IsProper (yJ 𝔛reg b)] (𝒲 : ((Jb 𝔛reg b).subscheme).TwoAffineOpenCover) :
    (Module.finrank κ (𝒲.sectionsOf (yJ 𝔛reg b) ((Scheme.Modules.pullback (Jb 𝔛reg b).subschemeι).obj
        ((List.finRange m).foldr
          (fun j M => (sectionTwist 𝔛reg.toBase (σ j) (tκ toκ) (pos j) ⊗
            ((sectionIdeal 𝔛reg.toBase (σ j) (tκ toκ)) ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback 𝔛reg.toBase (tκ toκ)).Modules)))).H0 : ℤ)
      - Module.finrank κ (𝒲.sectionsOf (yJ 𝔛reg b) ((Scheme.Modules.pullback (Jb 𝔛reg b).subschemeι).obj
        ((List.finRange m).foldr
          (fun j M => (sectionTwist 𝔛reg.toBase (σ j) (tκ toκ) (pos j) ⊗
            ((sectionIdeal 𝔛reg.toBase (σ j) (tκ toκ)) ^ (neg j)).module) ⊗ M)
          (𝟙_ (pullback 𝔛reg.toBase (tκ toκ)).Modules)))).H1
      = (Module.finrank κ (𝒲.sectionsOf (yJ 𝔛reg b) (𝟙_ ((Jb 𝔛reg b).subscheme).Modules)).H0 : ℤ)
        - Module.finrank κ (𝒲.sectionsOf (yJ 𝔛reg b) (𝟙_ ((Jb 𝔛reg b).subscheme).Modules)).H1
        + ∑ j : Fin m, ((pos j : ℤ) - (neg j : ℤ)) * ((if v j = Sum.inl b then 1 else 0 : ℕ) : ℤ) := by
  obtain ⟨hσ⟩ : Nonempty (∀ j, Set.range (σ j).1 ⊆ (𝔛reg.smoothOffEdges : Set 𝔛reg.Y)) :=
    ⟨fun j => range_subset_smoothOffEdges 𝔛reg (σ j) (hv j).1⟩
  have h := fun j => section_inputs 𝔛reg hϖ σ v hv b j
  exact AlgebraicGeometry.RelPicard.eulerChar_sectionsOf_pullback_foldr_sectionTwist_tensor_eq_add_sum
    𝔛reg.toBase 𝔛reg.smoothOffEdges σ hσ pos neg (tκ toκ) (Jb 𝔛reg b) (yJ 𝔛reg b)
    (fun j => (h j).1) (fun j => if v j = Sum.inl b then 1 else 0) (fun j => (h j).2.1) (fun j => (h j).2.2) 𝒲

end ModularCurve.K5bii.Sigma

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme"

section OverPoint
variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ) (htoκ : Function.Surjective toκ)

omit [Fact p.Prime] in
include hϖ in

theorem eq_closedPoint_of_not_mem_basicOpen (x : Spec (CommRingCat.of O))
    (hx : x ∉ (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens)) :
    x = IsLocalRing.closedPoint O := by
  have hp : ((p : ℕ) : O) ∈ x.asIdeal := by
    by_contra h; exact hx h
  apply PrimeSpectrum.ext
  show x.asIdeal = IsLocalRing.maximalIdeal O
  have hle : IsLocalRing.maximalIdeal O ≤ x.asIdeal := by
    rw [hϖ, Ideal.span_singleton_le_iff_mem]; exact hp
  exact ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le x.isPrime.ne_top hle).symm

omit [IsAlgClosed κ] in
include htoκ in

theorem specMap_base_eq_closedPoint (q : Spec (CommRingCat.of κ)) :
    (Spec.map (CommRingCat.ofHom toκ)).base q = IsLocalRing.closedPoint O := by
  apply PrimeSpectrum.ext
  show Ideal.comap toκ q.asIdeal = IsLocalRing.maximalIdeal O
  have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  rw [hq, ← RingHom.ker_eq_comap_bot]
  exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ htoκ)

include hϖ htoκ in

theorem isIso_fst_comp (w : X0MqComponents 𝔛reg.width) :
    IsIso (pullback.fst ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))) := by
  haveI : IsIntegral (𝔛reg.comp w).subscheme := 𝔛reg.comp_integral w
  haveI : Surjective (pullback.fst ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))) := by
    refine ⟨fun a => ?_⟩
    have ha : ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase).base a =
        (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint κ) := by
      rw [specMap_base_eq_closedPoint htoκ]
      apply eq_closedPoint_of_not_mem_basicOpen hϖ
      intro h
      have hmem : (𝔛reg.comp w).subschemeι.base a ∈ ((𝔛reg.comp w).support : Set 𝔛reg.Y) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨a, rfl⟩
      exact 𝔛reg.comp_support w ((𝔛reg.comp w).subschemeι.base a) hmem h
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase)
      (g := Spec.map (CommRingCat.ofHom toκ)) a (IsLocalRing.closedPoint κ) ha
    exact ⟨z, hz⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom toκ)) := IsClosedImmersion.spec_of_surjective _ htoκ
  haveI : IsClosedImmersion (pullback.fst ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isIso_of_isClosedImmersion_of_surjective _

def yComp (w : X0MqComponents 𝔛reg.width) : (𝔛reg.comp w).subscheme ⟶ Spec (CommRingCat.of κ) :=
  haveI := isIso_fst_comp hϖ 𝔛reg htoκ w
  inv (pullback.fst ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))) ≫ pullback.snd _ _

theorem yComp_specMap (w : X0MqComponents 𝔛reg.width) :
    yComp hϖ 𝔛reg htoκ w ≫ Spec.map (CommRingCat.ofHom toκ) = (𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase := by
  haveI := isIso_fst_comp hϖ 𝔛reg htoκ w
  rw [yComp, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

theorem fst_yComp (w : X0MqComponents 𝔛reg.width) :
    pullback.fst ((𝔛reg.comp w).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)) ≫ yComp hϖ 𝔛reg htoκ w =
      pullback.snd _ _ := by
  haveI := isIso_fst_comp hϖ 𝔛reg htoκ w
  rw [yComp, IsIso.hom_inv_id_assoc]

scoped instance isProper_yComp (w : X0MqComponents 𝔛reg.width) : IsProper (yComp hϖ 𝔛reg htoκ w) := by
  haveI := isIso_fst_comp hϖ 𝔛reg htoκ w
  unfold yComp; infer_instance

end OverPoint

section T4off
variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p}
  {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (R : DRResolvedModelPackage p 𝔛 O κ toκ)

theorem finite_closure_of_edge {v w : X0MqComponents R.width} (hvw : v ≠ w) (x : ↥(R.comp w).subscheme)
    (hxv : (R.comp w).subschemeι.base x ∈ ((R.comp v).support : Set R.Y)) :
    (closure ({x} : Set ↥(R.comp w).subscheme)).Finite := by

  let E : Set R.Y := Set.range (fun e : Σ n : R.node, Fin (R.width n) => R.edgePt e.1 e.2)
  have hE : E.Finite := Set.finite_range _
  have hsub : closure ({x} : Set ↥(R.comp w).subscheme) ⊆ (R.comp w).subschemeι.base ⁻¹' E := by
    intro x' hx'
    have hspec : (R.comp w).subschemeι.base x' ∈ closure {(R.comp w).subschemeι.base x} := by
      have := image_closure_subset_closure_image (R.comp w).subschemeι.base.hom.continuous
        (Set.mem_image_of_mem _ hx')
      rwa [Set.image_singleton] at this
    have hw' : (R.comp w).subschemeι.base x' ∈ ((R.comp w).support : Set R.Y) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x', rfl⟩
    have hv' : (R.comp w).subschemeι.base x' ∈ ((R.comp v).support : Set R.Y) :=
      (R.comp v).support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxv) hspec
    obtain ⟨n, d, he, -⟩ := R.edgePt_exhaust v w hvw _ ⟨hv', hw'⟩
    exact ⟨⟨n, d⟩, he.symm⟩
  exact (hE.preimage ((R.comp w).subschemeι.isClosedEmbedding.injective.injOn)).subset hsub

theorem isLocallyClosed_singleton_of_finite_closure {X : Type*} [TopologicalSpace X] [T0Space X] (x : X)
    (hfin : (closure ({x} : Set X)).Finite) : IsLocallyClosed ({x} : Set X) := by
  let T : Set X := closure ({x} : Set X) \ {x}
  have hT : T.Finite := hfin.subset Set.diff_subset

  have hxT : x ∉ closure T := by
    intro hx
    have heq : closure T = ⋃ t ∈ T, closure {t} := by
      rw [← hT.closure_biUnion (fun t => ({t} : Set X)), Set.biUnion_of_singleton]
    rw [heq, Set.mem_iUnion₂] at hx
    obtain ⟨t, htT, hxt⟩ := hx
    have h1 : t ⤳ x := specializes_iff_mem_closure.mpr hxt
    have h2 : x ⤳ t := specializes_iff_mem_closure.mpr htT.1
    exact htT.2 ((h1.antisymm h2).eq ▸ rfl)
  refine ⟨(closure T)ᶜ, closure {x}, isClosed_closure.isOpen_compl, isClosed_closure, ?_⟩
  ext z
  constructor
  · rintro rfl
    exact ⟨hxT, subset_closure rfl⟩
  · rintro ⟨hz1, hz2⟩
    by_contra hzx
    exact hz1 (subset_closure ⟨hz2, hzx⟩)

theorem isClosed_singleton_of_edge {v w : X0MqComponents R.width} (hvw : v ≠ w)
    {S : Scheme.{0}} [JacobsonSpace S] (y : (R.comp w).subscheme ⟶ S) [LocallyOfFiniteType y]
    (x : ↥(R.comp w).subscheme) (hxv : (R.comp w).subschemeι.base x ∈ ((R.comp v).support : Set R.Y)) :
    IsClosed ({x} : Set ↥(R.comp w).subscheme) := by
  haveI : JacobsonSpace ↥(R.comp w).subscheme := LocallyOfFiniteType.jacobsonSpace y
  exact isClosed_singleton_of_isLocallyClosed_singleton
    (isLocallyClosed_singleton_of_finite_closure x (finite_closure_of_edge R hvw x hxv))

theorem hrat_of_isAlgClosed {v w : X0MqComponents R.width} (hvw : v ≠ w)
    (y : (R.comp w).subscheme ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType y] :
    ∀ (n : R.node) (d : Fin (R.width n)),
      (v = DRResolvedModelPackage.chainPos R.width n d ∧ w = DRResolvedModelPackage.chainPos R.width n (d + 1)) ∨
          (w = DRResolvedModelPackage.chainPos R.width n d ∧ v = DRResolvedModelPackage.chainPos R.width n (d + 1)) →
      ∃ s : Spec (CommRingCat.of κ) ⟶ (R.comp w).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp w).subschemeι).base := by
  intro n d hadj

  have hmem := R.edgePt_mem n d
  have hv : R.edgePt n d ∈ ((R.comp v).support : Set R.Y) := by
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem.1
    · exact hmem.2
  have hw : R.edgePt n d ∈ ((R.comp w).support : Set R.Y) := by
    rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hmem.2
    · exact hmem.1

  rw [← Scheme.IdealSheafData.range_subschemeι] at hw
  obtain ⟨x, hx⟩ := hw
  have hxc : IsClosed ({x} : Set ↥(R.comp w).subscheme) :=
    isClosed_singleton_of_edge R hvw y x (by rw [hx]; exact hv)
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton κ y x hxc
  refine ⟨z.left, ?_, ⟨IsLocalRing.closedPoint κ, ?_⟩⟩
  · have := Over.w z
    simpa using this
  · rw [Scheme.Hom.comp_apply]
    exact (congrArg (fun q : ↥(R.comp w).subscheme => (R.comp w).subschemeι.base q) hz).trans hx

end T4off

section Main
variable {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p}
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (R : DRResolvedModelPackage p 𝔛 O κ toκ) (htoκ : Function.Surjective toκ)

theorem chi_invModule_comp_sub_eq_x0MqAdj (w F : X0MqComponents R.width) (hF : F ≠ w)
    (𝒲 : ((R.comp w).subscheme).TwoAffineOpenCover) :
    ((Module.finrank κ (𝒲.sectionsOf (yComp hϖ R htoκ w)
          ((Scheme.Modules.pullback (R.comp w).subschemeι).obj (R.comp F).invModule)).H0 : ℤ)
        - Module.finrank κ (𝒲.sectionsOf (yComp hϖ R htoκ w)
          ((Scheme.Modules.pullback (R.comp w).subschemeι).obj (R.comp F).invModule)).H1)
      - ((Module.finrank κ (𝒲.sectionsOf (yComp hϖ R htoκ w) (𝟙_ ((R.comp w).subscheme).Modules)).H0 : ℤ)
        - Module.finrank κ (𝒲.sectionsOf (yComp hϖ R htoκ w) (𝟙_ ((R.comp w).subscheme).Modules)).H1)
      = (x0MqAdj R.width F w : ℤ) := by
  have h := ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 p R F w hF
    (yComp hϖ R htoκ w) (hrat_of_isAlgClosed R hF (yComp hϖ R htoκ w)) 𝒲
  omega

end Main

end ModularCurve.K5bii
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve"
end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

namespace K4MON

noncomputable def foldrTensorIso {C : Type*} [Category C] [MonoidalCategory C] {ι : Type*} (A B : ι → C) (V : C) :
    ∀ l : List ι, l.foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ C)) ⊗ V
  | [] => (λ_ V).symm
  | j :: l => whiskerLeftIso (A j) (whiskerLeftIso (B j) (foldrTensorIso A B V l)) ≪≫
      (α_ (A j) (B j) _).symm ≪≫ (α_ (A j ⊗ B j) _ V).symm

theorem foldr_tensor_iso_foldr_tensorUnit_tensor {C : Type*} [Category C] [MonoidalCategory C] {ι : Type*}
    (A B : ι → C) (V : C) (l : List ι) :
    Nonempty (l.foldr (fun j N => A j ⊗ B j ⊗ N) V ≅ (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ C)) ⊗ V) :=
  ⟨foldrTensorIso A B V l⟩

noncomputable def pullbackFoldrIso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (A B : ι → Y.Modules) (A' B' : ι → X.Modules)
    (eA : ∀ j, (Scheme.Modules.pullback f).obj (A j) ≅ A' j) (eB : ∀ j, (Scheme.Modules.pullback f).obj (B j) ≅ B' j) :
    ∀ l : List ι, (Scheme.Modules.pullback f).obj (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)) ≅
      l.foldr (fun j M => (A' j ⊗ B' j) ⊗ M) (𝟙_ X.Modules)
  | [] => Scheme.Modules.pullbackTensorUnitObjIso f
  | j :: l => Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫
      tensorIso (Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ tensorIso (eA j) (eB j)) (pullbackFoldrIso f A B A' B' eA eB l)

theorem nonempty_pullback_foldr_iso {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (A B : ι → Y.Modules) (A' B' : ι → X.Modules)
    (eA : ∀ j, (Scheme.Modules.pullback f).obj (A j) ≅ A' j) (eB : ∀ j, (Scheme.Modules.pullback f).obj (B j) ≅ B' j) (l : List ι) :
    Nonempty ((Scheme.Modules.pullback f).obj (l.foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)) ≅
      l.foldr (fun j M => (A' j ⊗ B' j) ⊗ M) (𝟙_ X.Modules)) :=
  ⟨pullbackFoldrIso f A B A' B' eA eB l⟩

end K4MON
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme"

section AddOnA
variable {k : Type u} [Field k] [IsAlgClosed k] {A P : Scheme.{u}} (yA : A ⟶ Spec (CommRingCat.of k))
  (yP : P ⟶ Spec (CommRingCat.of k)) [IsIntegral P] [IsProper yP] [SmoothOfRelativeDimension 1 yP]
  (Φ : A ≅ P) (𝒲 : A.TwoAffineOpenCover) (𝒱 : P.TwoAffineOpenCover)
  (hW : ∀ M' : P.Modules,
    (Module.finrank k (𝒲.sectionsOf yA ((Scheme.Modules.pullback Φ.hom).obj M')).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf yA ((Scheme.Modules.pullback Φ.hom).obj M')).H1 =
      (Module.finrank k (𝒱.sectionsOf yP M').H0 : ℤ) - Module.finrank k (𝒱.sectionsOf yP M').H1)

def backIso (N : A.Modules) : (Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback Φ.inv).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp Φ.hom Φ.inv).app N ≪≫ (Scheme.Modules.pullbackCongr Φ.hom_inv_id).app N ≪≫
    (Scheme.Modules.pullbackId A).app N

include hW in
theorem chi_eq_chi_pullback_inv (N : A.Modules) :
    (Module.finrank k (𝒲.sectionsOf yA N).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf yA N).H1 =
      (Module.finrank k (𝒱.sectionsOf yP ((Scheme.Modules.pullback Φ.inv).obj N)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf yP ((Scheme.Modules.pullback Φ.inv).obj N)).H1 := by
  rw [← hW, K5biiTransport.eulerChar_congr 𝒲 yA (backIso Φ N)]

include hW in

theorem add_on_A (L L' : A.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L') :
    (Module.finrank k (𝒲.sectionsOf yA (L ⊗ L')).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf yA (L ⊗ L')).H1 =
      ((Module.finrank k (𝒲.sectionsOf yA L).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf yA L).H1) +
        ((Module.finrank k (𝒲.sectionsOf yA L').H0 : ℤ) - Module.finrank k (𝒲.sectionsOf yA L').H1) -
        ((Module.finrank k (𝒲.sectionsOf yA (𝟙_ A.Modules)).H0 : ℤ) - Module.finrank k (𝒲.sectionsOf yA (𝟙_ A.Modules)).H1) := by
  rw [chi_eq_chi_pullback_inv yA yP Φ 𝒲 𝒱 hW (L ⊗ L'), chi_eq_chi_pullback_inv yA yP Φ 𝒲 𝒱 hW L,
    chi_eq_chi_pullback_inv yA yP Φ 𝒲 𝒱 hW L', chi_eq_chi_pullback_inv yA yP Φ 𝒲 𝒱 hW (𝟙_ _),
    K5biiTransport.eulerChar_congr 𝒱 yP (Scheme.Modules.pullbackTensorObjIso Φ.inv L L'),
    K5biiTransport.eulerChar_congr 𝒱 yP (Scheme.Modules.pullbackTensorUnitObjIso Φ.inv)]
  exact Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub k yP _ _ (hL.pullback _) (hL'.pullback _) 𝒱

end AddOnA
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

end ModularCurve.K5bii
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
p2m_open "ModularCurve"

theorem chainPos_adj_ne_inl {node : Type} (width : node → ℕ) (hw : ∀ x, 1 ≤ width x) (x : node) (b : Fin 2) :
    DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) ≠ Sum.inl b := by
  unfold DRResolvedModelPackage.chainPos
  have hb : b = 0 ∨ b = 1 := by omega
  have hlt := Nat.sub_lt (hw x) Nat.one_pos
  rcases hb with rfl | rfl
  · rw [if_pos rfl, dif_neg one_ne_zero]
    by_cases h : 1 < width x
    · rw [dif_pos h]; exact Sum.inr_ne_inl
    · rw [dif_neg h]; simp
  · rw [if_neg (show (1 : Fin 2) ≠ 0 by decide)]
    by_cases h0 : width x - 1 = 0
    · rw [dif_pos h0]; simp
    · rw [dif_neg h0, dif_pos hlt]; exact Sum.inr_ne_inl

theorem arith {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x)
    (b : Fin 2) {m : ℕ} (v : Fin m → X0MqComponents width) (pos neg : Fin m → ℕ)
    (aplus aminus : X0MqComponents width → ℕ)
    (hdeg : (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inl b) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inl b) = 0)
    (d : X0MqComponents width → ℤ)
    (hd : ∀ F, F ≠ Sum.inl b → d F = (x0MqAdj width F (Sum.inl b) : ℤ))
    (hsum : ∑ F, d F = 0) :
    (∑ j, ((pos j : ℤ) - neg j) * (if v j = Sum.inl b then 1 else 0)) +
      ∑ F, (((aplus F : ℤ) - aminus F) * d F) = 0 := by
  classical
  obtain ⟨hα, hcard, hadj⟩ := ModularCurve.intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl width hw

  have hself : (x0MqAdj width (Sum.inl b) (Sum.inl b) : ℤ) = 0 := by
    rw [hadj b (Sum.inl b)]
    push_cast
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg (chainPos_adj_ne_inl width hw x b).symm]

  have hcol : ∑ F, (x0MqAdj width F (Sum.inl b) : ℤ) = Fintype.card node := by
    have h1 : ∑ F, (x0MqAdj width F (Sum.inl b) : ℤ) =
        ∑ F, ∑ x, (if F = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) then (1 : ℤ) else 0) := by
      refine Finset.sum_congr rfl fun F _ => ?_
      rw [hadj b F]; push_cast; rfl
    rw [h1, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

  have hrow : ∑ F, (x0MqAdj width (Sum.inl b) F : ℤ) = Fintype.card node := by
    have := hcard b; exact_mod_cast this

  have hhor : (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inl b) =
      ∑ j, ((pos j : ℤ) - neg j) * (if v j = Sum.inl b then 1 else 0) := by
    rw [Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.single_apply]
    split_ifs with h <;> simp

  set a : X0MqComponents width → ℤ := fun F => ((aplus F : ℤ) - (aminus F : ℤ)) with ha
  have hdB : d (Sum.inl b) = -∑ F ∈ Finset.univ.erase (Sum.inl b), d F := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Sum.inl b))] at hsum
    linarith

  have hdiff : ∀ F, d F = (x0MqAdj width F (Sum.inl b) : ℤ) + (if F = Sum.inl b then d (Sum.inl b) else 0) := by
    intro F
    by_cases hF : F = Sum.inl b
    · subst hF; rw [hself, if_pos rfl, zero_add]
    · rw [hd F hF, if_neg hF, add_zero]
  have hdB' : d (Sum.inl b) = -(Fintype.card node : ℤ) := by
    have h1 : ∑ F, d F = ∑ F, (x0MqAdj width F (Sum.inl b) : ℤ) + d (Sum.inl b) := by
      rw [Finset.sum_congr rfl fun F _ => hdiff F, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (Sum.inl b),
        if_pos (Finset.mem_univ _)]
    rw [hsum, hcol] at h1
    linarith
  have hsplit : ∑ F, a F * d F = ∑ F, a F * (x0MqAdj width F (Sum.inl b) : ℤ) -
      a (Sum.inl b) * ∑ F, (x0MqAdj width F (Sum.inl b) : ℤ) := by
    have h1 : ∑ F, a F * d F = ∑ F, a F * (x0MqAdj width F (Sum.inl b) : ℤ) + a (Sum.inl b) * d (Sum.inl b) := by
      have : ∀ F, a F * d F = a F * (x0MqAdj width F (Sum.inl b) : ℤ) + (if F = Sum.inl b then a (Sum.inl b) * d (Sum.inl b) else 0) := by
        intro F
        by_cases hF : F = Sum.inl b
        · subst hF; rw [if_pos rfl, hself, mul_zero, zero_add]
        · rw [if_neg hF, add_zero, hd F hF]
      rw [Finset.sum_congr rfl fun F _ => this F, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (Sum.inl b),
        if_pos (Finset.mem_univ _)]
    rw [h1, hdB', hcol]; ring
  have hαb := hα a (Sum.inl b)
  rw [← hhor, hsplit, hcol]
  rw [hrow] at hαb

  have : (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inl b) +
      (∑ F, a F * (x0MqAdj width F (Sum.inl b) : ℤ) - a (Sum.inl b) * (Fintype.card node : ℤ)) = 0 := by
    rw [← hαb]; exact hdeg
  linarith

end ModularCurve.K5bii
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme"

theorem count
    {p : ℕ} [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (hw : ∀ x, 1 ≤ R.width x)
    (χ : R.Y.Modules → ℤ)
    (hiso : ∀ L L' : R.Y.Modules, Nonempty (L ≅ L') → χ L = χ L')
    (hadd : ∀ L L' : R.Y.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      χ (L ⊗ L') = χ L + χ L' - χ (𝟙_ R.Y.Modules))
    {m : ℕ} (K : Fin m → R.Y.IdealSheafData) (hK : ∀ j, (K j).IsInvertible) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents R.width) (b : Fin 2)
    (aplus aminus : X0MqComponents R.width → ℕ)
    (hdeg : (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inl b) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable R.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inl b) = 0)
    (hS : χ ((List.finRange m).foldr (fun j M => ((K j ^ pos j).invModule ⊗ (K j ^ neg j).module) ⊗ M) (𝟙_ R.Y.Modules)) =
      χ (𝟙_ R.Y.Modules) + ∑ j, ((pos j : ℤ) - neg j) * (if v j = Sum.inl b then 1 else 0))
    (hd : ∀ F, F ≠ Sum.inl b → χ (R.comp F).invModule - χ (𝟙_ R.Y.Modules) = (x0MqAdj R.width F (Sum.inl b) : ℤ))
    (hsum : ∑ F, (χ (R.comp F).invModule - χ (𝟙_ R.Y.Modules)) = 0) :
    χ ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N)
        ((∏ F, R.comp F ^ aplus F).invModule ⊗ (∏ F, R.comp F ^ aminus F).module)) = χ (𝟙_ R.Y.Modules) := by
  classical
  set V := (∏ F, R.comp F ^ aplus F).invModule ⊗ (∏ F, R.comp F ^ aminus F).module with hV
  set S := (List.finRange m).foldr (fun j M => ((K j ^ pos j).invModule ⊗ (K j ^ neg j).module) ⊗ M) (𝟙_ R.Y.Modules)
    with hSdef

  have h1 : χ ((List.finRange m).foldr (fun j N => (K j ^ pos j).invModule ⊗ (K j ^ neg j).module ⊗ N) V) = χ (S ⊗ V) :=
    hiso _ _ ⟨K4MON.foldrTensorIso (fun j => (K j ^ pos j).invModule) (fun j => (K j ^ neg j).module) V _⟩

  have hSinv : Scheme.Modules.IsInvertible S := by
    rw [hSdef]
    induction (List.finRange m) with
    | nil => exact Scheme.Modules.isInvertible_unit _
    | cons j l ih => exact (((hK j).pow _).isInvertible_invModule.tensor ((hK j).pow _).isInvertible_module).tensor ih
  have hVinv : Scheme.Modules.IsInvertible V :=
    (K5biiT3b.isInvertible_prod' Finset.univ _ fun F _ => (R.comp_isInvertible F).pow _).isInvertible_invModule.tensor
      (K5biiT3b.isInvertible_prod' Finset.univ _ fun F _ => (R.comp_isInvertible F).pow _).isInvertible_module
  have h2 : χ (S ⊗ V) = χ S + χ V - χ (𝟙_ _) := hadd _ _ hSinv hVinv
  have h3 : χ V = χ (𝟙_ _) + ∑ F, ((aplus F : ℤ) - aminus F) * (χ (R.comp F).invModule - χ (𝟙_ _)) :=
    K5biiT3b.chi_invModule_prod_pow_tensor_module_prod_pow χ hiso hadd Finset.univ _ (fun F _ => R.comp_isInvertible F) _ _
  have h4 := arith R.width hw b v pos neg aplus aminus hdeg (fun F => χ (R.comp F).invModule - χ (𝟙_ _)) hd hsum
  rw [h1, h2, hS, h3]
  linarith

end ModularCurve.K5bii
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

noncomputable section
namespace ModularCurve
p2m_export "ModularCurve" "DRModel DRModel.toBase DRModelPackage DRResolvedModelPackage.chainPos DRResolvedModelPackage X0MqComponents x0MqAdj x0MqResolvedTable PlaceSpecialization DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4 intersectionAlpha_x0MqResolvedTable_eq_sum_x0MqAdj_and_sum_x0MqAdj_inl"
namespace K5bii
p2m_open "ModularCurve"

p2m_open "AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry AlgebraicGeometry.Scheme P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.AlgebraicGeometry.Scheme AlgebraicGeometry.RelPicard"

theorem isClosedImmersion_of_comp_eq_id' {Y S : Scheme.{0}} (π : Y ⟶ S) [IsSeparated π] (σ : S ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ π) := by rw [hσ]; infer_instance
  exact .of_comp σ π

set_option maxHeartbeats 3200000 in

theorem nonempty_pullback_fst_foldr_iso {O : Type} [CommRing O] {Y : Scheme.{0}} (c : Y ⟶ Spec (CommRingCat.of O))
    [IsSeparated c] (U : Y.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) c) (pos neg : Fin m → ℕ)
    (hσU : ∀ j, Set.range (σ j).1 ⊆ (U : Set Y)) (hker : ∀ j, ((σ j).1).ker.IsInvertible)
    {κ : Type} [Field κ] (t : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O)) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst c t)).obj
        ((List.finRange m).foldr (fun j M => ((((σ j).1.ker ^ pos j).invModule ⊗ ((σ j).1.ker ^ neg j).module)) ⊗ M)
          (𝟙_ Y.Modules)) ≅
      (List.finRange m).foldr (fun j M => (sectionTwist c (σ j) t (pos j) ⊗ ((sectionIdeal c (σ j) t) ^ (neg j)).module) ⊗ M)
        (𝟙_ (pullback c t).Modules)) := by
  classical
  let jη := pullback.fst c t
  let fst₁ := pullback.fst c (𝟙 (Spec (CommRingCat.of O)))
  haveI : IsIso fst₁ := inferInstance
  let ψ : SchemeHomOver t (𝟙 (Spec (CommRingCat.of O))) := ⟨t, Category.comp_id _⟩
  have hcomp : baseChangeSnd c ψ ≫ fst₁ = jη := by
    simp only [baseChangeSnd, fst₁, jη, pullback.lift_fst, Category.comp_id]
  let A : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (pos j)).invModule
  let B : Fin m → Y.Modules := fun j => ((σ j).1.ker ^ (neg j)).module
  let A₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j => sectionTwist c (σ j) (𝟙 _) (pos j)
  let B₁ : Fin m → (pullback c (𝟙 (Spec (CommRingCat.of O)))).Modules := fun j =>
    ((sectionIdeal c (σ j) (𝟙 _)) ^ (neg j)).module
  have hsec : ∀ j, (sectionIdeal c (σ j) (𝟙 (Spec (CommRingCat.of O)))).IsInvertible := fun j =>
    isInvertible_sectionIdeal_of_range_subset c (σ j) U (hσU j) (𝟙 _)
  haveI : ∀ j, IsClosedImmersion (σ j).1 := fun j => isClosedImmersion_of_comp_eq_id' c (σ j).1 (σ j).2
  have hrig : ∀ j, rigSection c (𝟙 (Spec (CommRingCat.of O))) (σ j) ≫ fst₁ = (σ j).1 := fun j => by
    show pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    rw [pullback.lift_fst, Category.id_comp]
  have eAB := fun j => Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso fst₁ (σ j).1
    (rigSection c (𝟙 _) (σ j)) (hrig j) (hker j) (hsec j)
  let eA : ∀ j, (Scheme.Modules.pullback fst₁).obj (A j) ≅ A₁ j := fun j => ((eAB j (pos j)).1).some
  let eB : ∀ j, (Scheme.Modules.pullback fst₁).obj (B j) ≅ B₁ j := fun j => ((eAB j (neg j)).2).some
  let S'' : Y.Modules := (List.finRange m).foldr (fun j M => (A j ⊗ B j) ⊗ M) (𝟙_ Y.Modules)
  let i3 : (Scheme.Modules.pullback jη).obj S'' ≅
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj ((Scheme.Modules.pullback fst₁).obj S'') :=
    ((Scheme.Modules.pullbackCongr hcomp).symm ≪≫ (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) fst₁).symm).app S''
  let i4 : (Scheme.Modules.pullback fst₁).obj S'' ≅
      (List.finRange m).foldr (fun j M => (A₁ j ⊗ B₁ j) ⊗ M) (𝟙_ _) := K4MON.pullbackFoldrIso fst₁ A B A₁ B₁ eA eB _
  obtain ⟨-, ⟨i5⟩⟩ := isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset c U σ hσU pos neg ψ
  exact ⟨i3 ≪≫ (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso i4 ≪≫ i5⟩

end ModularCurve.K5bii
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"
end
p2m_reactivate "P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective.ModularCurve.K5bii"

open ModularCurve.K5bii in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    (htoκ : Function.Surjective toκ)

    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ c : X0MqComponents 𝔛reg.width,
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c = 0)
    (M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules)
    (hMinv : Scheme.Modules.IsInvertible M)
    (eM : Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj M ≅
        (List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)))

    (b : Fin 2)
    (e : pullback ((𝔛reg.comp (Sum.inl b)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ)) ⟶ (𝔛.ratModel κ).C)
    [IsIso e] (he : e ≫ (𝔛.ratModel κ).toBase = pullback.snd _ _)
    (𝒱 : ((𝔛.ratModel κ).C).TwoAffineOpenCover) :
    (Module.finrank κ (𝒱.sectionsOf (𝔛.ratModel κ).toBase
        ((Scheme.Modules.pullback (inv e ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl b)).subschemeι ≫ 𝔛reg.toDR)).obj M)).H0 : ℤ) -
      Module.finrank κ (𝒱.sectionsOf (𝔛.ratModel κ).toBase
        ((Scheme.Modules.pullback (inv e ≫ pullback.fst _ _ ≫ (𝔛reg.comp (Sum.inl b)).subschemeι ≫ 𝔛reg.toDR)).obj M)).H1 =
    (Module.finrank κ (𝒱.sectionsOf (𝔛.ratModel κ).toBase
        (SheafOfModules.unit ((𝔛.ratModel κ).C).ringCatSheaf : ((𝔛.ratModel κ).C).Modules)).H0 : ℤ) -
      Module.finrank κ (𝒱.sectionsOf (𝔛.ratModel κ).toBase
        (SheafOfModules.unit ((𝔛.ratModel κ).C).ringCatSheaf : ((𝔛.ratModel κ).C).Modules)).H1 := by
  classical
  obtain ⟨eM⟩ := eM

  let t : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of O) := Spec.map (CommRingCat.ofHom toκ)
  let B : X0MqComponents 𝔛reg.width := Sum.inl b
  let ιA := (𝔛reg.comp (Sum.inl b)).subschemeι
  let fstC := pullback.fst ((𝔛reg.comp (Sum.inl b)).subschemeι ≫ 𝔛reg.toBase) (Spec.map (CommRingCat.ofHom toκ))
  haveI hfst : IsIso fstC := isIso_fst_comp hϖ 𝔛reg htoκ (Sum.inl b)
  let yA := yComp hϖ 𝔛reg htoκ (Sum.inl b)
  let P := (𝔛.ratModel κ).C
  let yP := (𝔛.ratModel κ).toBase
  let Φ : (𝔛reg.comp (Sum.inl b)).subscheme ≅ P := (asIso fstC).symm ≪≫ asIso e
  have hΦinv : Φ.inv = inv e ≫ fstC := rfl
  have hΦ : Φ.hom ≫ yP = yA := by
    show (inv fstC ≫ e) ≫ (𝔛.ratModel κ).toBase = yComp hϖ 𝔛reg htoκ (Sum.inl b)
    rw [Category.assoc, he]; rfl
  let Ldiv := (List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)

  have hfac : inv e ≫ pullback.fst _ _ ≫ ιA ≫ 𝔛reg.toDR = (Φ.inv ≫ ιA) ≫ 𝔛reg.toDR := by
    rw [hΦinv]; simp only [Category.assoc]; rfl
  let e1 : (Scheme.Modules.pullback (inv e ≫ pullback.fst _ _ ≫ ιA ≫ 𝔛reg.toDR)).obj M ≅
      (Scheme.Modules.pullback (Φ.inv ≫ ιA)).obj Ldiv :=
    (Scheme.Modules.pullbackCongr hfac).app M ≪≫ (Scheme.Modules.pullbackComp (Φ.inv ≫ ιA) 𝔛reg.toDR).symm.app M ≪≫
      (Scheme.Modules.pullback (Φ.inv ≫ ιA)).mapIso eM
  rw [K5biiTransport.eulerChar_congr 𝒱 yP e1]

  obtain ⟨𝒲, -, -, hW, hunit⟩ := K5biiTransport.exists_preimage_cover yA yP Φ hΦ 𝒱
  let e2 : (Scheme.Modules.pullback Φ.hom).obj ((Scheme.Modules.pullback (Φ.inv ≫ ιA)).obj Ldiv) ≅
      (Scheme.Modules.pullback ιA).obj Ldiv :=
    (Scheme.Modules.pullbackComp Φ.hom (Φ.inv ≫ ιA)).app Ldiv ≪≫
      (Scheme.Modules.pullbackCongr (show Φ.hom ≫ Φ.inv ≫ ιA = ιA by rw [Φ.hom_inv_id_assoc])).app Ldiv
  rw [← hW, K5biiTransport.eulerChar_congr 𝒲 yA e2, show (SheafOfModules.unit P.ringCatSheaf : P.Modules) = (𝟙_ P.Modules) from rfl,
    ← hunit]

  let χ : 𝔛reg.Y.Modules → ℤ := fun N =>
    (Module.finrank κ (𝒲.sectionsOf yA ((Scheme.Modules.pullback ιA).obj N)).H0 : ℤ) -
      Module.finrank κ (𝒲.sectionsOf yA ((Scheme.Modules.pullback ιA).obj N)).H1
  have hiso : ∀ L L' : 𝔛reg.Y.Modules, Nonempty (L ≅ L') → χ L = χ L' := fun L L' ⟨i⟩ =>
    K5biiTransport.eulerChar_congr 𝒲 yA ((Scheme.Modules.pullback ιA).mapIso i)
  have hχunit : χ (𝟙_ _) = (Module.finrank κ (𝒲.sectionsOf yA (𝟙_ _)).H0 : ℤ) - Module.finrank κ (𝒲.sectionsOf yA (𝟙_ _)).H1 :=
    K5biiTransport.eulerChar_congr 𝒲 yA (Scheme.Modules.pullbackTensorUnitObjIso ιA)
  have hadd : ∀ L L' : 𝔛reg.Y.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      χ (L ⊗ L') = χ L + χ L' - χ (𝟙_ _) := by
    intro L L' hL hL'
    show (_ : ℤ) = _
    rw [hχunit]
    simp only [χ]
    rw [K5biiTransport.eulerChar_congr 𝒲 yA (Scheme.Modules.pullbackTensorObjIso ιA L L')]
    exact add_on_A yA yP Φ 𝒲 𝒱 hW _ _ (hL.pullback _) (hL'.pullback _)
  show χ Ldiv = (Module.finrank κ (𝒲.sectionsOf yA (𝟙_ _)).H0 : ℤ) - Module.finrank κ (𝒲.sectionsOf yA (𝟙_ _)).H1
  rw [← hχunit]
  refine count 𝔛reg 𝔛reg.one_le_width χ hiso hadd (fun j => (σ j).1.ker) ?_ pos neg v b aplus aminus (hdeg (Sum.inl b)) ?_ ?_ ?_
  ·
    exact fun j => AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges
      (σ j).1 (σ j).2 (hv j).1
  ·

    let fstY := pullback.fst 𝔛reg.toBase (Spec.map (CommRingCat.ofHom toκ))
    let J := (𝔛reg.comp (Sum.inl b)).comap fstY
    let Ψ : J.subscheme ≅ (𝔛reg.comp (Sum.inl b)).subscheme := 𝔛reg.compFibreIsoComp (Sum.inl b)
    have hΨι : Ψ.hom ≫ ιA = J.subschemeι ≫ fstY := 𝔛reg.compFibreIsoComp_hom_subschemeι (Sum.inl b)
    have hΨy : Ψ.hom ≫ yA = J.subschemeι ≫ pullback.snd 𝔛reg.toBase (Spec.map (CommRingCat.ofHom toκ)) :=
      𝔛reg.compFibreIsoComp_hom_yComp (Sum.inl b) yA (fst_yComp hϖ 𝔛reg htoκ (Sum.inl b))
    haveI : IsProper (Sigma.yJ 𝔛reg b) := by
      show IsProper (J.subschemeι ≫ pullback.snd 𝔛reg.toBase (Spec.map (CommRingCat.ofHom toκ)))
      rw [← hΨy]; infer_instance
    obtain ⟨𝒲J, -, -, hWJ, hunitJ⟩ := K5biiTransport.exists_preimage_cover (Sigma.yJ 𝔛reg b) yA Ψ hΨy 𝒲

    set S := (List.finRange m).foldr (fun j M => ((((σ j).1.ker ^ pos j).invModule ⊗ ((σ j).1.ker ^ neg j).module)) ⊗ M)
      (𝟙_ 𝔛reg.Y.Modules) with hSdef
    have hσU : ∀ j, Set.range (σ j).1 ⊆ (𝔛reg.smoothOffEdges : Set 𝔛reg.Y) := fun j =>
      Sigma.range_subset_smoothOffEdges 𝔛reg (σ j) (hv j).1
    have hkerσ : ∀ j, ((σ j).1).ker.IsInvertible := fun j =>
      AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges
        (σ j).1 (σ j).2 (hv j).1
    obtain ⟨eL⟩ := nonempty_pullback_fst_foldr_iso 𝔛reg.toBase 𝔛reg.smoothOffEdges σ pos neg hσU hkerσ
      (Spec.map (CommRingCat.ofHom toκ))
    let e3 : (Scheme.Modules.pullback Ψ.hom).obj ((Scheme.Modules.pullback ιA).obj S) ≅
        (Scheme.Modules.pullback J.subschemeι).obj ((Scheme.Modules.pullback fstY).obj S) :=
      (Scheme.Modules.pullbackComp Ψ.hom ιA).app S ≪≫ (Scheme.Modules.pullbackCongr hΨι).app S ≪≫
        (Scheme.Modules.pullbackComp J.subschemeι fstY).symm.app S
    have hfib := Sigma.eulerChar_fibre 𝔛reg hϖ σ pos neg v hv b 𝒲J
    show (Module.finrank κ (𝒲.sectionsOf yA ((Scheme.Modules.pullback ιA).obj S)).H0 : ℤ) -
        Module.finrank κ (𝒲.sectionsOf yA ((Scheme.Modules.pullback ιA).obj S)).H1 = χ (𝟙_ _) + _
    rw [hχunit, ← hunitJ, ← hWJ, K5biiTransport.eulerChar_congr 𝒲J (Sigma.yJ 𝔛reg b) e3,
      K5biiTransport.eulerChar_congr 𝒲J (Sigma.yJ 𝔛reg b) ((Scheme.Modules.pullback J.subschemeι).mapIso eL), hfib]
    push_cast
    rfl
  ·
    intro F hF
    have := chi_invModule_comp_sub_eq_x0MqAdj hϖ 𝔛reg htoκ (Sum.inl b) F hF 𝒲
    rw [hχunit]
    exact this
  ·
    exact K5biiT3b.chi_sum_eq_zero_of_prod_invModule_iso χ hiso hadd Finset.univ _ (fun F _ => 𝔛reg.comp_isInvertible F)
      (ModularCurve.DRResolvedModelPackage.nonempty_invModule_prod_comp_iso_unit 𝔛reg)

end S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_eulerChar_sectionsOf_pullback_strictTransform_eq_of_multidegree_eq_zero_of_surjective (solution)
