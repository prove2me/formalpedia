-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d47fb6d7-59df-58d0-8bac-e86e752a328c

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
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_Isogeny_ConditionalCurrency
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_ajbar_abelJacobi_eq
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_degeneracyHom_one_ajbar_abelJacobi_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

namespace DDEGPTSAssembly

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) : Divisor.degZero (K := K) (F := F) :=
  ⟨Finsupp.single P 1 - Finsupp.single Q₀ 1, by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]; simp⟩

@[scoped simp] theorem coe_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P : Place K F) :
    (gen hdeg Q₀ P : Divisor K F) = Finsupp.single P 1 - Finsupp.single Q₀ 1 := rfl

theorem closure_range_mk_gen_eq_top (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F) :
    AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) = ⊤ := by
  classical
  set S := AddSubgroup.closure (Set.range fun P : Place K F => Pic0.mk (gen hdeg Q₀ P)) with hS

  let θ : Divisor K F →+ Divisor K F :=
    AddMonoidHom.id _ - (zmultiplesHom (Divisor K F) (Finsupp.single Q₀ 1)).comp Divisor.degree
  have hθ : ∀ E : Divisor K F, θ E = E - Divisor.degree E • Finsupp.single Q₀ 1 := fun E => by
    simp [θ]
  have hθmem : ∀ E : Divisor K F, θ E ∈ Divisor.degZero (K := K) (F := F) := by
    intro E
    rw [Divisor.mem_degZero, hθ, map_sub, map_zsmul, Divisor.degree_single, hdeg]
    simp
  let ψ : Divisor K F →+ Pic0 K F := (QuotientAddGroup.mk' _).comp (θ.codRestrict _ hθmem)
  have hψ : ∀ E : Divisor K F, ψ E = Pic0.mk ⟨θ E, hθmem E⟩ := fun E => rfl
  have hψS : ∀ E : Divisor K F, ψ E ∈ S := by
    intro E
    induction E using Finsupp.induction with
    | zero => rw [map_zero]; exact S.zero_mem
    | single_add a b f _ _ ih =>
      rw [map_add]
      refine S.add_mem ?_ ih
      have h1 : ψ (Finsupp.single a 1) = Pic0.mk (gen hdeg Q₀ a) := by
        rw [hψ]; congr 1; apply Subtype.ext
        simp only [coe_gen, hθ, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, one_smul]
      have hb : Finsupp.single a b = b • Finsupp.single a (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hb, map_zsmul, h1]
      exact S.zsmul_mem (AddSubgroup.subset_closure ⟨a, rfl⟩) b
  rw [eq_top_iff]
  rintro c -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  have hD : Pic0.mk D = ψ (D : Divisor K F) := by
    rw [hψ]; congr 1; apply Subtype.ext
    simp only [hθ, (Divisor.mem_degZero.mp D.2), zero_smul, sub_zero]
  rw [hD]; exact hψS _

theorem addMonoidHom_ext_of_gen {G : Type*} [AddGroup G] (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ : Place K F)
    {f g : Pic0 K F →+ G} (h : ∀ P : Place K F, f (Pic0.mk (gen hdeg Q₀ P)) = g (Pic0.mk (gen hdeg Q₀ P))) :
    f = g :=
  AddMonoidHom.eq_of_eqOn_dense (closure_range_mk_gen_eq_top hdeg Q₀) (by rintro _ ⟨P, rfl⟩; exact h P)

theorem gen_sub_gen (hdeg : ∀ v : Place K F, v.deg = 1) (Q₀ P P' : Place K F) :
    gen hdeg Q₀ P - gen hdeg Q₀ P' = gen hdeg P' P :=
  Subtype.ext (by rw [AddSubgroupClass.coe_sub, coe_gen, coe_gen, coe_gen, sub_sub_sub_cancel_right])

theorem pushforwardAlongDegZero_gen {F' : Type*} [Field F'] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K F', w.deg = 1)
    (hinert : ∀ w : Place K F', w.inertiaDegAlong φ hφ = 1) (Q₀' P' : Place K F') :
    Pic0.pushforwardAlongDegZero φ hφ (gen hdeg' Q₀' P') = gen hdeg (Q₀'.restrictAlong φ hφ) (P'.restrictAlong φ hφ) := by
  apply Subtype.ext
  rw [Pic0.coe_pushforwardAlongDegZero, coe_gen, coe_gen, map_sub, Divisor.pushforwardAlong_single,
    Divisor.pushforwardAlong_single, hinert, hinert, Nat.cast_one, mul_one]

end Generic

set_option maxHeartbeats 3200000 in

theorem core (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    {DX : Scheme.{0}} (dD : DX ⟶ Spec (CommRingCat.of (R p)))
    (mulD : SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD → SchemeHomOver (genPt p) dD)
    (ajbar : 𝔓.Meta.C ⟶ DX) (hajbar_over : ajbar ≫ dD = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) dD)
    (hpts_add : ∀ x y : JZero (N₀ * p), pts (x + y) = mulD (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    (φ : ↥(modularFunctionFieldBar N₀) →ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (N₀ * p)))
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong (AlgebraicClosure ℚ) φ) (hN : NormFormulaAlong (AlgebraicClosure ℚ) φ hfin)
    (πg : X N₀ p ⟶ X0 N₀ p) (hπg : πg ≫ toBase0 N₀ p = toBase N₀ p)
    (d : SchemeHomOver dD M.D₀.toBase)
    (hdhom : ∀ x y : SchemeHomOver (genPt p) dD,
      schemeHomOverComp (mulD x y) d = M.law.mul (genPt p) (schemeHomOverComp x d) (schemeHomOverComp y d))

    (hplace : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _}),
      x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
        y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πg →
      M.Meta₀.pointEquivPlace x = (𝔓.Meta.pointEquivPlace y).restrictAlong φ hφ)

    (hnorm : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
        (x xinf : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _}),
      x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
        y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πg →
      xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
        εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πg →
      ∀ (a b c : SchemeHomOver (genPt p) M.D₀.toBase),
        a.1 = (y.1 ≫ ajbar) ≫ d.1 →
        b.1 = xinf.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1 →
        c.1 = x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1 →
        M.law.mul (genPt p) a b = c) :
    ∀ X : JZero (N₀ * p), (M.pts (Pic0.pushforwardAlongHom φ hφ hfin hN X)).1 = (pts X).1 ≫ d.1 := by
  classical

  have hinv₀ : inv M.eeta₀ ≫ M.Meta₀.toBase = pullback.snd (IgusaScheme.igusaTo N₀ p) (genPt p) := by
    rw [IsIso.inv_comp_eq, M.heeta₀]
  let under : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _} := fun y =>
    ⟨pullback.lift (y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πg)
        (y.1 ≫ 𝔓.eeta ≫ pullback.snd (toBase N₀ p) (genPt p))
        (by simp only [Category.assoc, hπg]; rw [pullback.condition]) ≫ inv M.eeta₀, by
      rw [Category.assoc, hinv₀, pullback.lift_snd, 𝔓.heeta, y.2]⟩
  have hunder : ∀ y, (under y).1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πg := by
    intro y; simp only [under, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  let s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _} :=
    ⟨pullback.lift (genPt p ≫ M.ε₀.1) (𝟙 _)
        (by rw [Category.assoc, M.ε₀.2, Category.comp_id, Category.id_comp]) ≫ inv M.eeta₀, by
      rw [Category.assoc, hinv₀, pullback.lift_snd]⟩
  have hs₀ : s₀.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ M.ε₀.1 := by
    simp only [s₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hMadd : ∀ u v : JZero N₀, M.pts (u + v) = M.law.mul (genPt p) (M.pts u) (M.pts v) := by
    have hJ := hM; unfold LevelData.IsJacobian at hJ; exact hJ.2.2.1
  let Φ : JZero (N₀ * p) → JZero N₀ := fun X => M.pts.symm (schemeHomOverComp (pts X) d)
  have hΦ : ∀ X, M.pts (Φ X) = schemeHomOverComp (pts X) d := fun X => M.pts.apply_symm_apply _
  have hΦadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y := by
    intro X Y; apply M.pts.injective
    rw [hMadd, hΦ, hΦ, hΦ, hpts_add, hdhom]
  let Φh : JZero (N₀ * p) →+ JZero N₀ := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : Pic0.pushforwardAlongHom φ hφ hfin hN = Φh by
    intro X; rw [hfun]; show (M.pts (Φ X)).1 = _; rw [hΦ]; rfl

  have hdeg := deg_eq_one_modularFunctionFieldBar (N₀ * p)
  refine addMonoidHom_ext_of_gen hdeg (𝔓.Meta.pointEquivPlace εbar) fun P => ?_
  obtain ⟨y, hPy⟩ := 𝔓.Meta.pointEquivPlace.surjective P
  subst hPy
  set x := under y with hx
  set xinf := under εbar with hxinf

  obtain ⟨Dv, hDv, hptsDv⟩ := hpts_aj y εbar hεbar
  obtain ⟨Ex, hEx, hptsEx⟩ := M.pts_aj x s₀ hs₀
  obtain ⟨Einf, hEinf, hptsEinf⟩ := M.pts_aj xinf s₀ hs₀
  have hgen : gen hdeg (𝔓.Meta.pointEquivPlace εbar) (𝔓.Meta.pointEquivPlace y) = Dv := Subtype.ext (by rw [coe_gen, hDv])

  have hdeg₀ := deg_eq_one_modularFunctionFieldBar N₀
  have hEx' : Ex = gen hdeg₀ (M.Meta₀.pointEquivPlace s₀) (M.Meta₀.pointEquivPlace x) := Subtype.ext (by rw [coe_gen, hEx])
  have hEinf' : Einf = gen hdeg₀ (M.Meta₀.pointEquivPlace s₀) (M.Meta₀.pointEquivPlace xinf) :=
    Subtype.ext (by rw [coe_gen, hEinf])
  have hpush : Pic0.pushforwardAlongDegZero φ hφ (gen hdeg (𝔓.Meta.pointEquivPlace εbar) (𝔓.Meta.pointEquivPlace y)) =
      Ex - Einf := by
    rw [pushforwardAlongDegZero_gen φ hφ hdeg₀ hdeg (inertiaDegAlong_eq_one_laurentBaseChange φ hφ),
      ← hplace y x (hunder y), ← hplace εbar xinf (hunder εbar), hEx', hEinf', gen_sub_gen]

  let a : SchemeHomOver (genPt p) M.D₀.toBase :=
    schemeHomOverComp (⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩ : SchemeHomOver (genPt p) dD) d
  have hmul : M.law.mul (genPt p) a (M.pts (Pic0.mk Einf)) = M.pts (Pic0.mk Ex) :=
    hnorm y x xinf (hunder y) (hunder εbar) a _ _ rfl hptsEinf hptsEx

  have hkey : M.pts (Pic0.mk (Ex - Einf)) = a := by
    have h1 : M.pts (Pic0.mk (Ex - Einf) + Pic0.mk Einf) = M.pts (M.pts.symm a + Pic0.mk Einf) := by
      rw [← Pic0.mk_add, sub_add_cancel, hMadd, Equiv.apply_symm_apply, hmul]
    have h2 := add_right_cancel (M.pts.injective h1)
    rw [h2, Equiv.apply_symm_apply]

  show Pic0.pushforwardAlongHom φ hφ hfin hN _ = Φ _
  apply M.pts.injective
  rw [hΦ, Pic0.pushforwardAlongHom_mk, hpush, hkey]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDv]

end DDEGPTSAssembly
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom.DDEGPTSAssembly"

open DDEGPTSAssembly

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1] (hrk : ∀ x, 𝔓.π.1.finrank x = p + 1)
    (δ : Fin 2 → SchemeHomOver D.toBase M.D₀.toBase)
    (hδ₀ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 0))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.π.1 𝔓.π.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδ₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((M.rep.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (δ 1))).L ≅
        Scheme.Modules.rigidify (rigSection (toBase0 N₀ p) t M.ε₀) (pullback.snd (toBase0 N₀ p) t)
          (Scheme.Modules.normModule (curveChange 𝔓.πw.1 𝔓.πw.2 t) (p + 1) (hD.poincare.pullbackAlong a).L)))
    (hδhom : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) (δ i) =
        M.law.mul t (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i))) :
    ∀ (i : Fin 2) (x : JZero (N₀ * p)),
      (M.pts (degeneracyPushforwardPair N₀ p i x)).1 = (pts x).1 ≫ (δ i).1 := by
  obtain ⟨hα, hβ, hfinα, hfinβ, hNα, hNβ⟩ := ModularCurve.degeneracyPushforwardInputs N₀ p Fact.out
  rw [degeneracyPushforwardPair_eq hα hβ hfinα hNα hfinβ hNβ]
  intro i
  match i with
  | 0 =>
    simp only [Matrix.cons_val_zero]
    exact core N₀ p hpN₀ 𝔓 D.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
      ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar A M hM (heckeAlphaBar (AlgebraicClosure ℚ) N₀ p) hα hfinα hNα
      𝔓.π.1 𝔓.π.2 (δ 0) (fun x y => hδhom 0 (genPt p) x y)
      (fun y x h => DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi N₀ p hpN₀ 𝔓 A M hα y x h)
      (fun y x xinf hyx hxinf a b c ha hb hc => DRModelPackageLevel.mul_degeneracyHom_ajbar_abelJacobi_eq N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ
        kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj A M hM hrk δ hδ₀ y x xinf hyx hxinf a b c ha hb hc)
  | 1 =>
    simp only [Matrix.cons_val_one]
    exact core N₀ p hpN₀ 𝔓 D.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
      ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar A M hM (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hβ hfinβ hNβ
      𝔓.πw.1 𝔓.πw.2 (δ 1) (fun x y => hδhom 1 (genPt p) x y)
      (fun y x h => DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw N₀ p hpN₀ 𝔓 A M hβ y x h)
      (fun y x xinf hyx hxinf a b c ha hb hc => DRModelPackageLevel.mul_degeneracyHom_one_ajbar_abelJacobi_eq N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ
        kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj A M hM hrk δ hδ₁ y x xinf hyx hxinf a b c ha hb hc)

end S_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pts_degeneracyPushforwardPair_eq_comp_degeneracyHom (solution)
