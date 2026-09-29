-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pts_atkinLehner_smul_eq_comp_atkinLehnerHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c79d8e71-b59f-5645-95b3-7d23adc2ad64

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
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

import Theorems.Thm_ModularCurve_DRModelPackageLevel_mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

namespace WSTARPTSAssembly

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
    (σ : ↥(modularFunctionFieldBar (N₀ * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (N₀ * p)))
    (d : SchemeHomOver dD dD)
    (hdhom : ∀ x y : SchemeHomOver (genPt p) dD,
      schemeHomOverComp (mulD x y) d = mulD (schemeHomOverComp x d) (schemeHomOverComp y d))

    (hplace : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) →
      𝔓.Meta.pointEquivPlace y' = σ • 𝔓.Meta.pointEquivPlace y)

    (hone : ∀ (y y' ε' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) →
      ε'.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom = εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) →
      ∀ (a b c : SchemeHomOver (genPt p) dD),
        a.1 = (y.1 ≫ ajbar) ≫ d.1 → b.1 = ε'.1 ≫ ajbar → c.1 = y'.1 ≫ ajbar → mulD a b = c) :
    ∀ X : JZero (N₀ * p), (pts (σ • X)).1 = (pts X).1 ≫ d.1 := by
  classical

  have hinv : inv 𝔓.eeta ≫ 𝔓.Meta.toBase = pullback.snd (toBase N₀ p) (genPt p) := by
    rw [IsIso.inv_comp_eq, 𝔓.heeta]
  have hwinv : 𝔓.w.inv ≫ toBase N₀ p = toBase N₀ p := by
    rw [Iso.inv_comp_eq, 𝔓.w_over]
  let under : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} := fun y =>
    ⟨pullback.lift (y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.inv)
        (y.1 ≫ 𝔓.eeta ≫ pullback.snd (toBase N₀ p) (genPt p))
        (by simp only [Category.assoc, hwinv]; rw [pullback.condition]) ≫ inv 𝔓.eeta, by
      rw [Category.assoc, hinv, pullback.lift_snd, 𝔓.heeta, y.2]⟩
  have hunder : ∀ y, (under y).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.w.hom =
      y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) := by
    intro y; simp only [under, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id]

  let Φ : JZero (N₀ * p) → JZero (N₀ * p) := fun X => pts.symm (schemeHomOverComp (pts X) d)
  have hΦ : ∀ X, pts (Φ X) = schemeHomOverComp (pts X) d := fun X => pts.apply_symm_apply _
  have hΦadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y := by
    intro X Y; apply pts.injective
    rw [hpts_add, hΦ, hΦ, hΦ, hpts_add, hdhom]
  let Φh : JZero (N₀ * p) →+ JZero (N₀ * p) := AddMonoidHom.mk' Φ hΦadd
  suffices hfun : DistribMulAction.toAddMonoidHom (JZero (N₀ * p)) σ = Φh by
    intro X
    have h1 : σ • X = Φ X := DFunLike.congr_fun hfun X
    rw [h1]; show (pts (Φ X)).1 = _; rw [hΦ]; rfl

  have hdeg := deg_eq_one_modularFunctionFieldBar (N₀ * p)
  refine addMonoidHom_ext_of_gen hdeg (𝔓.Meta.pointEquivPlace εbar) fun P => ?_
  obtain ⟨y, hPy⟩ := 𝔓.Meta.pointEquivPlace.surjective P
  subst hPy
  set y' := under y with hy'
  set ε' := under εbar with hε'

  obtain ⟨Dy, hDy, hptsDy⟩ := hpts_aj y εbar hεbar
  obtain ⟨Dy', hDy', hptsDy'⟩ := hpts_aj y' εbar hεbar
  obtain ⟨Dε', hDε', hptsDε'⟩ := hpts_aj ε' εbar hεbar
  have hgen : gen hdeg (𝔓.Meta.pointEquivPlace εbar) (𝔓.Meta.pointEquivPlace y) = Dy := Subtype.ext (by rw [coe_gen, hDy])

  have hsmul : σ • Pic0.mk (gen hdeg (𝔓.Meta.pointEquivPlace εbar) (𝔓.Meta.pointEquivPlace y)) = Pic0.mk (Dy' - Dε') := by
    rw [Pic0.smul_mk]
    congr 1
    apply Subtype.ext
    rw [Pic0.coe_degZeroSMulHom, coe_gen, smul_sub, Divisor.smul_single, Divisor.smul_single,
      ← hplace y y' (hunder y), ← hplace εbar ε' (hunder εbar), AddSubgroupClass.coe_sub, hDy', hDε',
      sub_sub_sub_cancel_right]

  let a : SchemeHomOver (genPt p) dD :=
    schemeHomOverComp (⟨y.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, reassoc_of% y.2]⟩ : SchemeHomOver (genPt p) dD) d
  have hmul : mulD a (pts (Pic0.mk Dε')) = pts (Pic0.mk Dy') :=
    hone y y' ε' (hunder y) (hunder εbar) a _ _ rfl hptsDε' hptsDy'

  have hkey : pts (Pic0.mk (Dy' - Dε')) = a := by
    have h1 : pts (Pic0.mk (Dy' - Dε') + Pic0.mk Dε') = pts (pts.symm a + Pic0.mk Dε') := by
      rw [← Pic0.mk_add, sub_add_cancel, hpts_add, Equiv.apply_symm_apply, hmul]
    have h2 := add_right_cancel (pts.injective h1)
    rw [h2, Equiv.apply_symm_apply]

  show σ • Pic0.mk _ = Φ _
  apply pts.injective
  rw [hΦ, hsmul, hkey]
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hgen, hptsDy]

theorem restrictAlong_algEquiv {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F)
    (hσ : σ.toAlgHom.toRingHom.IsIntegral) (w : Place K F) :
    w.restrictAlong σ.toAlgHom hσ = σ⁻¹ • w := by
  apply Place.ext
  ext x
  change σ.toAlgHom.toRingHom x ∈ w.toValuationSubring ↔ x ∈ (σ⁻¹ • w).toValuationSubring
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, AlgEquiv.smul_def]
  rfl

end WSTARPTSAssembly
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom.WSTARPTSAssembly"

open WSTARPTSAssembly

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

    (wstar : SchemeHomOver D.toBase D.toBase)
    (hw : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a wstar)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
          ((Scheme.Modules.pullback (curveChange 𝔓.w.hom 𝔓.w_over t)).obj (hD.poincare.pullbackAlong a).L)))
    (hwhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t x y) wstar =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
          (NeronModelInfra.schemeHomOverComp x wstar) (NeronModelInfra.schemeHomOverComp y wstar)) :
    ∀ x : JZero (N₀ * p),
      (pts ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)) • x)).1 =
        (pts x).1 ≫ wstar.1 := by
  exact core N₀ p hpN₀ 𝔓 D.toBase (fun x y => (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ x y)
    ajbar hajbar_over εbar pts hpts_add hpts_aj hεbar
    (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)) wstar (fun x y => hwhom (genPt p) x y)
    (fun y y' h => by
      have hint : ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)).toAlgHom).toRingHom.IsIntegral :=
        RingHom.isIntegral_of_surjective _ (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p)).surjective
      have h1 := ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_geomAut_of_comp_w N₀ p hpN₀ 𝔓 hint y' y h.symm
      rw [restrictAlong_algEquiv] at h1
      rw [h1, smul_inv_smul])
    (fun y y' ε' hy' hε' a b c ha hb hc => ModularCurve.DRModelPackageLevel.mul_atkinLehnerHom_ajbar_ajbar_eq_of_comp_w N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ
      kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hpts_galois hpts_aj wstar hw hwhom y y' ε' hy' hε' a b c ha hb hc)

end S_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pts_atkinLehner_smul_eq_comp_atkinLehnerHom (solution)
