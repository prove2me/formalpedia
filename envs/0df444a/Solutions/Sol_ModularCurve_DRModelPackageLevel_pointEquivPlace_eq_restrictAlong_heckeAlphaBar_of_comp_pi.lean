-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/43b0c760-10ee-5a25-96ec-df72b1f880e9

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq
import Theorems.Thm_ModularCurve_DRModelPackageLevel_fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar

import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A)
    (hint : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hyx : x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1) :
    M.Meta₀.pointEquivPlace x =
      (𝔓.Meta.pointEquivPlace y).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p) hint := by

  have hinv₀ : inv M.eeta₀ ≫ M.Meta₀.toBase = pullback.snd (IgusaScheme.igusaTo N₀ p) (genPt p) := by
    rw [IsIso.inv_comp_eq, M.heeta₀]
  let πM : 𝔓.Meta.C ⟶ M.Meta₀.C :=
    pullback.lift (𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1) (𝔓.eeta ≫ pullback.snd (toBase N₀ p) (genPt p))
      (by simp only [Category.assoc, 𝔓.π.2]; rw [pullback.condition]) ≫ inv M.eeta₀
  have hπM₁ : πM ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.π.1 := by
    simp only [πM, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hπM₂ : πM ≫ M.Meta₀.toBase = 𝔓.Meta.toBase := by
    simp only [πM, Category.assoc, hinv₀, pullback.lift_snd, 𝔓.heeta]

  have hxy : y.1 ≫ πM = x.1 := by
    rw [← cancel_mono M.eeta₀]
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hπM₁, hyx]
    · simp only [Category.assoc]; rw [M.heeta₀, hπM₂, y.2, x.2]

  obtain ⟨-, -, hfinα, -, -, -⟩ := ModularCurve.degeneracyPushforwardInputs N₀ p Fact.out
  letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p)
  haveI := isScalarTower_along (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p)
  haveI : Module.Finite ↥(modularFunctionFieldBar N₀) ↥(modularFunctionFieldBar (N₀ * p)) := hfinα

  obtain ⟨πu, -, -, -, -, -, hgenu, hplaces, huniq⟩ :=
    AlgebraicCurve.CurveModel.exists_hom_pointEquivPlace_restrict_eq M.Meta₀ 𝔓.Meta
  have hgenM := DRModelPackageLevel.fromSpecStalk_genericPoint_comp_eq_spec_map_heckeAlphaBar N₀ p hpN₀ 𝔓 A M πM hπM₁ hπM₂
  have heq : πM = πu := huniq πM (by rw [hgenM, hgenu])
  have hres := hplaces y x (by rw [← heq, hxy])
  rw [← hres]
  rfl

end S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi (solution)
