-- Prove2me | solution 1 for ModularCurve.XOneP.pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/807d5640-c10a-5cd2-827f-663897d403ad

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_ModularCurve_XOneP_nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field
import Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_eq_arithmeticGalois_smul_of_chartPin_of_galoisTwist_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_hom_ext_of_iotaFin_comp_eq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

theorem TAUTR_isIso_ws
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))
    (s : L ≃ₐ[ℚ] L)
    (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) :
    IsIso ws := by
  subst hK

  letI : MulSemiringAction (L ≃ₐ[ℚ] L) ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
    MulSemiringAction.compHom _ (ModularCurve.arithmeticGalois (ModularCurve.x1FunctionField (M * p)))
  have hcoe : ∀ (t : L ≃ₐ[ℚ] L) (x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      ((t • x : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L) =
        ModularCurve.coeffMap (t : L →+* L) (x : LaurentSeries L) :=
    fun t x => ModularCurve.coe_arithmeticGalois_smul _ t x

  have hΓF : ∀ (t : L ≃ₐ[ℚ] L) (r : A),
      t • algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) r =
        algebraMap A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) (t • r) := by
    intro t r
    rw [IsScalarTower.algebraMap_eq A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))), RingHom.comp_apply, RingHom.comp_apply, hΓA]
    show AlgebraicCurve.SemilinearAut.toRingAut (ModularCurve.arithmeticGalois _ t) _ = _
    rw [ModularCurve.toRingAut_arithmeticGalois, ModularCurve.arithmeticRingAut_algebraMap]

  have hΓj : ∀ t : L ≃ₐ[ℚ] L, t • j = j := by
    intro t
    apply Subtype.ext
    rw [hcoe, hj, ModularCurve.coeffMap_coeffEmb]

  obtain ⟨w, θ, θ', hw_over, hw1, hwmul, hθ, -, hwfin, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_hom_comp_toBase_eq_and_iotaFin_comp_eq_of_mulSemiringAction_of_smul_eq
      A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) j (L ≃ₐ[ℚ] L) hΓF hΓj

  have hρθ : ρs = θ s := by
    refine RingEquiv.ext fun b => Subtype.ext (Subtype.ext ?_)
    have h1 := congrArg (fun y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) => (y : LaurentSeries L)) (hθ s b)
    try simp only at h1
    rw [hρs]
    refine Eq.trans ?_ h1.symm
    rw [hcoe]
    rfl

  have hfin : ModularCurve.TwoChart.ιFin A _ j ≫ ws = ModularCurve.TwoChart.ιFin A _ j ≫ w s := by
    rw [hwρ, hρθ]
    exact (hwfin s).symm
  have heq : ws = w s :=
    AlgebraicCurve.TwoChartIntegralModel.hom_ext_of_iotaFin_comp_eq A _ j ws (w s) (ModularCurve.TwoChart.modelTo A _ j)
      (by exact hws.trans (hw_over s).symm) hfin
  rw [heq]
  refine ⟨⟨w s⁻¹, ?_, ?_⟩⟩
  · exact ((hwmul s s⁻¹).symm.trans (by rw [mul_inv_cancel, hw1]; rfl))
  · exact ((hwmul s⁻¹ s).symm.trans (by rw [inv_mul_cancel, hw1]; rfl))

theorem TAUTR_N_mul_one
    {R : Type} [CommRing R] {C : Scheme.{0}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (β β' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (hβ : β' ≫ β = 𝟙 (Spec (CommRingCat.of R))) (hβ' : β ≫ β' = 𝟙 (Spec (CommRingCat.of R)))
    (f : C ⟶ C) (hf : f ≫ c = c ≫ β)
    (N : SchemeHomOver (D.toBase ≫ β') D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h.poincare.pullbackAlong
            (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ β') D.toBase)).L ≅
          Scheme.Modules.rigidify (rigSection c (t ≫ β') ε) (pullback.snd c (t ≫ β'))
            ((Scheme.Modules.pullback
                (pullback.map c (t ≫ β') c t f (𝟙 T) β hf.symm
                  (by rw [Category.assoc, hβ, Category.comp_id, Category.id_comp]))).obj
              (h.poincare.pullbackAlong a).L))) :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        (⟨((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y).1 ≫ N.1,
            by rw [Category.assoc, N.2, ← Category.assoc, ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y).2]⟩ :
            SchemeHomOver (t ≫ β') D.toBase) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul (t ≫ β')
            ⟨x.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)),
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one t).1 ≫ N.1 =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (t ≫ β')).1) := by
  obtain ⟨N', hN', hN'mul, hN'one⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_map_of_comp_eq_comp h β β' hβ hβ' f hf

  have hNN : N = N' := by
    let i : SchemeHomOver D.toBase D.toBase := ⟨𝟙 D.P, Category.id_comp _⟩
    have e1 := hN D.toBase i
    have e2 := hN' D.toBase i
    have h1 : (⟨i.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, i.2]⟩ : SchemeHomOver (D.toBase ≫ β') D.toBase) = N :=
      Subtype.ext (Category.id_comp _)
    have h2 : (⟨i.1 ≫ N'.1, by rw [Category.assoc, N'.2, ← Category.assoc, i.2]⟩ : SchemeHomOver (D.toBase ≫ β') D.toBase) = N' :=
      Subtype.ext (Category.id_comp _)
    rw [h1] at e1
    rw [h2] at e2
    exact h.ext_of_iso (D.toBase ≫ β') N N' ⟨e1.some ≪≫ e2.some.symm⟩
  subst hNN
  exact ⟨fun t x y => hN'mul t x y, fun t => hN'one t⟩

namespace TAUTR

theorem rhs_mul_one {R : Type} [CommRing R] {DP : Scheme.{0}} {f : DP ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (Si : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (N : SchemeHomOver (f ≫ Si) f)
    (hNmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(G.mul t x y).1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, (G.mul t x y).2]⟩ : SchemeHomOver (t ≫ Si) f) =
        G.mul (t ≫ Si) ⟨x.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, x.2]⟩ ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩)
    (hNone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 ≫ N.1 = (G.one (t ≫ Si)).1)
    {T : Scheme.{0}} (tQ : T ⟶ Spec (CommRingCat.of R)) (ψ : T ⟶ T) (hbase : ψ ≫ tQ ≫ Si = tQ) :
    let Φ : SchemeHomOver tQ f → SchemeHomOver tQ f := fun y =>
      ⟨ψ ≫ y.1 ≫ N.1, by rw [Category.assoc, Category.assoc, N.2, ← Category.assoc y.1, y.2, hbase]⟩
    (∀ x y : SchemeHomOver tQ f, Φ (G.mul tQ x y) = G.mul tQ (Φ x) (Φ y)) ∧ Φ (G.one tQ) = G.one tQ := by
  intro Φ
  have hbase' : ψ ≫ (tQ ≫ Si) = tQ := hbase
  have hΦ : ∀ y : SchemeHomOver tQ f, Φ y = GoodReductionJacobian.schemeHomOverComp ψ hbase'
      (⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩ : SchemeHomOver (tQ ≫ Si) f) :=
    fun y => Subtype.ext rfl
  refine ⟨fun x y => ?_, ?_⟩
  · rw [hΦ, hΦ, hΦ, hNmul tQ x y, G.mul_natural]
  · rw [hΦ]
    have h1 : (⟨(G.one tQ).1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, (G.one tQ).2]⟩ : SchemeHomOver (tQ ≫ Si) f) =
        G.one (tQ ≫ Si) := Subtype.ext (hNone tQ)
    rw [h1, G.one_natural]

private theorem _root_.TAUTR.closure {R : Type} [CommRing R] {DP : Scheme.{0}} {f : DP ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{0}} (tQ : T ⟶ Spec (CommRingCat.of R))
    {J : Type*} [AddCommGroup J] (F₁ F₂ : J → SchemeHomOver tQ f)
    (h₁ : ∀ x y, F₁ (x + y) = G.mul tQ (F₁ x) (F₁ y)) (h₂ : ∀ x y, F₂ (x + y) = G.mul tQ (F₂ x) (F₂ y))
    (S : Set J) (hS : ∀ x, x ∈ AddSubgroup.closure S) (hgen : ∀ x ∈ S, F₁ x = F₂ x) :
    ∀ x, F₁ x = F₂ x := by
  letI grp : Group (SchemeHomOver tQ f) := G.pointGroup tQ
  have one₁ : F₁ 0 = 1 := by
    have h := h₁ 0 0
    rw [add_zero] at h
    have h2 : F₁ 0 * F₁ 0 = F₁ 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h2
  have one₂ : F₂ 0 = 1 := by
    have h := h₂ 0 0
    rw [add_zero] at h
    have h2 : F₂ 0 * F₂ 0 = F₂ 0 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h2
  have neg₁ : ∀ x, F₁ (-x) = (F₁ x)⁻¹ := fun x => by
    symm; apply inv_eq_of_mul_eq_one_right
    show G.mul tQ (F₁ x) (F₁ (-x)) = 1
    rw [← h₁, add_neg_cancel, one₁]
  have neg₂ : ∀ x, F₂ (-x) = (F₂ x)⁻¹ := fun x => by
    symm; apply inv_eq_of_mul_eq_one_right
    show G.mul tQ (F₂ x) (F₂ (-x)) = 1
    rw [← h₂, add_neg_cancel, one₂]
  intro x
  refine AddSubgroup.closure_induction (p := fun x _ => F₁ x = F₂ x) ?_ ?_ ?_ ?_ (hS x)
  · exact fun x hx => hgen x hx
  · simp only [one₁, one₂]
  · intro x y _ _ hx hy
    try simp only at hx hy ⊢
    rw [h₁, h₂, hx, hy]
  · intro x _ hx
    try simp only at hx ⊢
    rw [neg₁, neg₂, hx]

p2m_export "TAUTR" "closure"

theorem stepD {R : Type} [CommRing R] {DP : Scheme.{0}} {f : DP ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (Si : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R)) (N : SchemeHomOver (f ≫ Si) f)
    (hNmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (⟨(G.mul t x y).1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, (G.mul t x y).2]⟩ : SchemeHomOver (t ≫ Si) f) =
        G.mul (t ≫ Si) ⟨x.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, x.2]⟩ ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩)
    (hNone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)), (G.one t).1 ≫ N.1 = (G.one (t ≫ Si)).1)
    {T : Scheme.{0}} (tQ : T ⟶ Spec (CommRingCat.of R)) (ψ : T ⟶ T) (hbase : ψ ≫ tQ ≫ Si = tQ)
    {J : Type*} [AddCommGroup J] (gpts : J → SchemeHomOver tQ f) (hgadd : ∀ x y, gpts (x + y) = G.mul tQ (gpts x) (gpts y))
    (act : J →+ J) (S : Set J) (hS : ∀ x, x ∈ AddSubgroup.closure S)
    (hgen : ∀ x ∈ S, (gpts (act x)).1 = ψ ≫ (gpts x).1 ≫ N.1) :
    ∀ x, (gpts (act x)).1 = ψ ≫ (gpts x).1 ≫ N.1 := by
  obtain ⟨hΦmul, hΦone⟩ := rhs_mul_one G Si N hNmul hNone tQ ψ hbase
  set Φ : SchemeHomOver tQ f → SchemeHomOver tQ f := fun y =>
    ⟨ψ ≫ y.1 ≫ N.1, by rw [Category.assoc, Category.assoc, N.2, ← Category.assoc y.1, y.2, hbase]⟩ with hΦdef
  have key := closure G tQ (fun x => gpts (act x)) (fun x => Φ (gpts x))
    (fun x y => by simp only [map_add, hgadd]) (fun x y => by simp only [hgadd]; exact hΦmul _ _) S hS
    (fun x hx => Subtype.ext (hgen x hx))
  intro x
  exact congrArg Subtype.val (key x)

end TAUTR

universe u in

theorem DR_pullback_ofPoint_iso_of_graph_comp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)]
    (cσ : pullback c t ⟶ pullback c t) [IsIso cσ] (ψ : T ⟶ T) [IsIso ψ]
    (y y' : T ⟶ C) (hy : y ≫ c = t) (hy' : y' ≫ c = t)
    (h : graphOver c y' hy' ≫ cσ = ψ ≫ graphOver c y hy) :
    Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint c y hy).lineBundle ≅
        (RelEffCartierDiv.ofPoint c y' hy').lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint c y hy).idealModule ≅
        (RelEffCartierDiv.ofPoint c y' hy').idealModule) := by
  have hp : (inv ψ ≫ graphOver c y' hy') ≫ cσ = graphOver c y hy := by
    rw [Category.assoc, h, IsIso.inv_hom_id_assoc]
  have hI : (graphOver c y hy).ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y hy)
  have hI' : (graphOver c y' hy').ker.IsInvertible :=
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) _ (graphOver_snd c y' hy')
  have hI'' : (inv ψ ≫ graphOver c y' hy').ker.IsInvertible := by
    rw [Scheme.Hom.ker_comp_of_isIso]; exact hI'
  have key := AlgebraicGeometry.Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso
    cσ (graphOver c y hy) (inv ψ ≫ graphOver c y' hy') hp hI hI'' 1
  rw [pow_one, pow_one, Scheme.Hom.ker_comp_of_isIso] at key
  exact key

set_option maxHeartbeats 24000000 in

theorem TAUTR_stepC
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (s : L ≃ₐ[ℚ] L)
    (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t ws (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
                hws.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L)))
    (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ' : ∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l))
    [IsIso ws]
    (hNmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver t D.toBase),
      (⟨((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul t x y).1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul t x y).2]⟩ :
          SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))
          ⟨x.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩)
    (hNone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)),
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one t).1 ≫ N.1 = ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).one (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))))).1) :
    letI := ModularCurve.heckeModuleOneBar (M * p)
    ∀ (a : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),
      (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace a) 1 - Finsupp.single (Mη.pointEquivPlace εbar) 1 →
      (gpts (σ' • Pic0.mk Dv)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts (Pic0.mk Dv)).1 ≫ N.1 := by
  letI := ModularCurve.heckeModuleOneBar (M * p)
  classical

  let Xm := ModularCurve.TwoChart.modelTo A (↥K) j
  let Qb := AlgebraicClosure ℚ
  let tQ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of A) := specMap A Qb
  let hh := hrep.some
  let P := hh.poincare
  let Glaw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut Xm ε) hh
  letI grp : Group (SchemeHomOver tQ D.toBase) := Glaw.pointGroup tQ
  let Si : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))
  let Ss : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))
  let ψ : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of Qb) := Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom)

  have hψt : ψ ≫ tQ = tQ ≫ Ss := by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap A Qb)) = Spec.map (CommRingCat.ofHom (algebraMap A Qb)) ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    change σ' (algebraMap A Qb a) = algebraMap A Qb (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s a)
    rw [IsScalarTower.algebraMap_apply A L Qb, hσ', IsScalarTower.algebraMap_apply A L Qb, MulSemiringAction.toRingHom_apply, hΓA]
  have hssinv : Ss ≫ Si = 𝟙 _ := by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s).comp (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹) = RingHom.id A := by
      ext a
      change s • s⁻¹ • a = a
      rw [smul_inv_smul]
    rw [this]
    exact Spec.map_id _
  have hbase : ψ ≫ tQ ≫ Si = tQ := by rw [← Category.assoc, hψt, Category.assoc, hssinv, Category.comp_id]

  let Φ : SchemeHomOver tQ D.toBase → SchemeHomOver tQ D.toBase := fun y =>
    ⟨ψ ≫ y.1 ≫ N.1, by rw [Category.assoc, Category.assoc, N.2, ← Category.assoc y.1, y.2, hbase]⟩
  have hbase' : ψ ≫ (tQ ≫ Si) = tQ := hbase
  have hΦ : ∀ y : SchemeHomOver tQ D.toBase, Φ y = GoodReductionJacobian.schemeHomOverComp ψ hbase'
      (⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩ : SchemeHomOver (tQ ≫ Si) D.toBase) :=
    fun y => Subtype.ext rfl
  have hΦmul : ∀ x y : SchemeHomOver tQ D.toBase, Φ (x * y) = Φ x * Φ y := by
    intro x y
    change Φ (Glaw.mul tQ x y) = Glaw.mul tQ (Φ x) (Φ y)
    rw [hΦ, hΦ, hΦ, hNmul tQ x y, Glaw.mul_natural]
  have hΦone : Φ 1 = 1 := by
    change Φ (Glaw.one tQ) = Glaw.one tQ
    rw [hΦ]
    have h1 : (⟨(Glaw.one tQ).1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, (Glaw.one tQ).2]⟩ : SchemeHomOver (tQ ≫ Si) D.toBase) =
        Glaw.one (tQ ≫ Si) := Subtype.ext (hNone tQ)
    rw [h1, Glaw.one_natural]
  have hΦinv : ∀ x : SchemeHomOver tQ D.toBase, Φ x⁻¹ = (Φ x)⁻¹ := by
    intro x
    apply eq_inv_of_mul_eq_one_left
    rw [← hΦmul, inv_mul_cancel, hΦone]

  have hgmul : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) = gpts x * gpts y := fun x y => hgadd x y
  have hg0 : gpts 0 = 1 := by
    have h00 := hgmul 0 0
    rw [add_zero] at h00
    have h2 : gpts 0 * gpts 0 = gpts 0 * 1 := by rw [mul_one]; exact h00.symm
    exact mul_left_cancel h2
  have hgneg : ∀ x : ModularCurve.JOne (M * p), gpts (-x) = (gpts x)⁻¹ := by
    intro x
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← hgmul, add_neg_cancel, hg0]
  have hgsub : ∀ x y : ModularCurve.JOne (M * p), gpts (x - y) = gpts x * (gpts y)⁻¹ := by
    intro x y; rw [sub_eq_add_neg, hgmul, hgneg]

  have hwi : inv ws ≫ Xm = Xm ≫ Si := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hws, Category.assoc, hssinv, Category.comp_id]
  have hρρ : Spec.map (CommRingCat.ofHom ρs.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom ρs.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : ρs.symm.toRingHom.comp ρs.toRingHom = RingHom.id _ := RingHom.ext fun b => ρs.symm_apply_apply b
    rw [this]
    exact Spec.map_id _
  have hwθ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ inv ws = Spec.map (CommRingCat.ofHom ρs.symm.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j :=
    calc ModularCurve.TwoChart.ιFin A (↥K) j ≫ inv ws
        = (Spec.map (CommRingCat.ofHom ρs.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom ρs.toRingHom)) ≫
            ModularCurve.TwoChart.ιFin A (↥K) j ≫ inv ws := by rw [hρρ, Category.id_comp]
      _ = Spec.map (CommRingCat.ofHom ρs.symm.toRingHom) ≫ (ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws) ≫ inv ws := by
            rw [hwρ]; simp only [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom ρs.symm.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
            rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

  have hθ' : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs.symm b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap ((s⁻¹ : L ≃ₐ[ℚ] L) : L →+* L) ((b : ↥K) : LaurentSeries L) := by
    intro b
    have h1 := hρs (ρs.symm b)
    rw [RingEquiv.apply_symm_apply] at h1

    have h2 := congrArg (ModularCurve.coeffMap ((s⁻¹ : L ≃ₐ[ℚ] L) : L →+* L)) h1
    rw [ModularCurve.coeffMap_coeffMap] at h2
    have h3 : ((s⁻¹ : L ≃ₐ[ℚ] L) : L →+* L).comp (s.toAlgHom.toRingHom) = RingHom.id L := RingHom.ext fun l => s.symm_apply_apply l
    rw [h3, ModularCurve.coeffMap_id] at h2
    exact h2.symm

  have hsndi : inv eη ≫ Mη.toBase = pullback.snd Xm tQ := by rw [← heη, IsIso.inv_hom_id_assoc]
  let AJ : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} → SchemeHomOver tQ D.toBase :=
    fun b => ⟨b.1 ≫ ajbar, by rw [Category.assoc, hajbar_over, ← Category.assoc, b.2, Category.id_comp]⟩
  have hτ_over : ∀ b : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _},
      (ψ ≫ b.1 ≫ eη ≫ pullback.fst Xm tQ ≫ inv ws) ≫ Xm = 𝟙 _ ≫ tQ := by
    intro b
    rw [Category.id_comp]
    simp only [Category.assoc]
    rw [hwi, pullback.condition_assoc, ← Category.assoc eη, heη, ← Category.assoc b.1, b.2, Category.id_comp, hbase]
  let τ : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} → {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun b => ⟨pullback.lift (ψ ≫ b.1 ≫ eη ≫ pullback.fst Xm tQ ≫ inv ws) (𝟙 _) (hτ_over b) ≫ inv eη, by
      rw [Category.assoc, hsndi, pullback.lift_snd]⟩
  have hτ : ∀ b, (τ b).1 ≫ eη ≫ pullback.fst Xm tQ = ψ ≫ b.1 ≫ eη ≫ pullback.fst Xm tQ ≫ inv ws := by
    intro b
    show (pullback.lift _ _ _ ≫ inv eη) ≫ eη ≫ pullback.fst Xm tQ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  have hplτ : ∀ b, Mη.pointEquivPlace (τ b) =
      ModularCurve.arithmeticGalois (L := Qb) (ModularCurve.x1FunctionField (M * p)) σ' • Mη.pointEquivPlace b := by
    intro b
    exact ModularCurve.XOneP.pointEquivPlace_eq_arithmeticGalois_smul_of_chartPin_of_galoisTwist_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj Mη eη heη hMηpin hΓA σ' s hσ' (inv ws) hwi ρs.symm hθ' hwθ b (τ b) (hτ b)

  have hone : ((1 : SchemeHomOver tQ D.toBase)).1 = tQ ≫ D.zeroSection := by
    have hn := RelativeGroupLaw.one_natural Glaw (𝟙 _) tQ tQ (Category.comp_id _)
    have h1 : (Glaw.one (𝟙 _)).1 = D.zeroSection := RepresentsRelSubPic.relativeGroupLaw_one (P := algEquivZeroGroupCut Xm ε) hh
    change (Glaw.one tQ).1 = _
    rw [← hn, GoodReductionJacobian.schemeHomOverComp_coe, h1]
  have hAJε : AJ εbar = 1 := by
    apply Subtype.ext
    change εbar.1 ≫ ajbar = (1 : SchemeHomOver tQ D.toBase).1
    rw [hone]; exact hεbar_aj

  let ψσ : SchemeHomOver tQ (tQ ≫ Si) := ⟨ψ, hbase'⟩
  let bcσ : pullback Xm tQ ⟶ pullback Xm (tQ ≫ Si) := baseChangeSnd Xm ψσ
  let cws : pullback Xm (tQ ≫ Si) ⟶ pullback Xm tQ :=
    pullback.map Xm (tQ ≫ Si) Xm tQ ws (𝟙 _) Ss hws.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp])
  let cσ : pullback Xm tQ ⟶ pullback Xm tQ := bcσ ≫ cws

  have hΦP : ∀ y : SchemeHomOver tQ D.toBase,
      Nonempty ((P.pullbackAlong (Φ y)).L ≅ (Scheme.Modules.pullback cσ).obj (P.pullbackAlong y).L) := by
    intro y
    let z : SchemeHomOver (tQ ≫ Si) D.toBase := ⟨y.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, y.2]⟩
    have hΦz : Φ y = postComp z ψσ := Subtype.ext rfl

    have e1 : (P.pullbackAlong (Φ y)).L ≅ (Scheme.Modules.pullback bcσ).obj (P.pullbackAlong z).L := by
      rw [hΦz]
      change (Scheme.Modules.pullback (baseChangeSnd Xm (postComp z ψσ))).obj P.L ≅
        (Scheme.Modules.pullback bcσ).obj ((Scheme.Modules.pullback (baseChangeSnd Xm z)).obj P.L)
      exact (Scheme.Modules.pullbackCongr (baseChangeSnd_comp Xm z ψσ).symm).app P.L ≪≫
        ((Scheme.Modules.pullbackComp bcσ (baseChangeSnd Xm z)).app P.L).symm

    obtain ⟨e2⟩ := hN tQ y
    obtain ⟨e3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field (ε := ε) (tQ ≫ Si)
      (L := (Scheme.Modules.pullback cws).obj (P.pullbackAlong y).L) ((P.pullbackAlong y).isInvertible.pullback _)
    refine ⟨e1 ≪≫ (Scheme.Modules.pullback bcσ).mapIso (e2 ≪≫ e3) ≪≫ (Scheme.Modules.pullbackComp bcσ cws).app ((P.pullbackAlong y).L)⟩

  haveI hsmQ : SmoothOfRelativeDimension 1 (pullback.snd Xm tQ) := by
    rw [← hsndi]; exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (inv eη ≫ Mη.toBase))
  haveI : IsSeparated Xm := inferInstance
  haveI hψiso : IsIso ψ := by
    refine ⟨⟨Spec.map (CommRingCat.ofHom σ'.symm.toRingEquiv.toRingHom), ?_, ?_⟩⟩
    · change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : σ'.toRingEquiv.toRingHom.comp σ'.symm.toRingEquiv.toRingHom = RingHom.id _ := RingHom.ext fun x => σ'.apply_symm_apply x
      rw [this]; exact Spec.map_id _
    · change Spec.map _ ≫ Spec.map _ = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : σ'.symm.toRingEquiv.toRingHom.comp σ'.toRingEquiv.toRingHom = RingHom.id _ := RingHom.ext fun x => σ'.symm_apply_apply x
      rw [this]; exact Spec.map_id _
  haveI hSsiso : IsIso Ss := ⟨⟨Si, hssinv, hsinv⟩⟩
  haveI : IsIso bcσ := by
    show IsIso (baseChangeSnd Xm ψσ)
    unfold baseChangeSnd
    infer_instance
  haveI : IsIso cws := by
    show IsIso (pullback.map Xm (tQ ≫ Si) Xm tQ ws (𝟙 _) Ss hws.symm _)
    infer_instance
  haveI hcσiso : IsIso cσ := IsIso.comp_isIso

  let bar : {q : Spec (CommRingCat.of Qb) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} → SchemeHomOver tQ Xm :=
    fun b => ⟨b.1 ≫ eη ≫ pullback.fst Xm tQ, by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc, b.2,
        Category.id_comp]⟩
  have hgraph : ∀ b, graphOver Xm (bar (τ b)).1 (bar (τ b)).2 ≫ cσ = ψ ≫ graphOver Xm (bar b).1 (bar b).2 := by
    intro b
    apply pullback.hom_ext
    · have hfst : cσ ≫ pullback.fst Xm tQ = pullback.fst Xm tQ ≫ ws := by
        simp only [cσ, bcσ, cws, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
      rw [Category.assoc, hfst, graphOver_fst_assoc]
      simp only [Category.assoc, graphOver_fst]
      change (τ b).1 ≫ eη ≫ pullback.fst Xm tQ ≫ ws = ψ ≫ b.1 ≫ eη ≫ pullback.fst Xm tQ
      have hτ' := hτ b
      try simp only [Category.assoc] at hτ'
      rw [reassoc_of% hτ']
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · have hsnd : cσ ≫ pullback.snd Xm tQ = pullback.snd Xm tQ ≫ ψ := by
        simp only [cσ, bcσ, cws, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
        rfl
      rw [Category.assoc, hsnd, graphOver_snd_assoc]
      simp only [Category.assoc, graphOver_snd, Category.comp_id, Category.id_comp]

  have hOσ : ∀ b, Nonempty ((Scheme.Modules.pullback cσ).obj (RelEffCartierDiv.ofPoint Xm (bar b).1 (bar b).2).lineBundle ≅
      (RelEffCartierDiv.ofPoint Xm (bar (τ b)).1 (bar (τ b)).2).lineBundle) := fun b =>
    (DR_pullback_ofPoint_iso_of_graph_comp_eq Xm tQ cσ ψ (bar b).1 (bar (τ b)).1 (bar b).2 (bar (τ b)).2 (hgraph b)).1

  have hI1 : ∀ b, Nonempty ((P.pullbackAlong (AJ b)).L ≅
      (RelEffCartierDiv.ofPoint Xm (bar b).1 (bar b).2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint Xm (tQ ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule) := by
    intro b
    exact ModularCurve.XOneP.nonempty_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint_idealModule_of_eq_comp_ajbar_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ε D hrep hsm hsep hsmL hgiL hprL hgcL Mη eη heη hMηpin hgal hin hcomm hΓA gpts hDL ajL kL
      ajbar εbar hPL hajLε hajL hkL₁ hkL₂ hajbar hajbar_over hεbar hεbar_aj hpts_aj b (bar b) rfl (AJ b) rfl

  have hkey2 : ∀ b b', Φ (AJ b) * AJ (τ b') = AJ (τ b) * Φ (AJ b') := by
    intro b b'
    apply hh.ext_of_iso tQ
    obtain ⟨m1⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut Xm ε) hh
      (T := Over.mk tQ) (schemeHomOverToOverHom (Φ (AJ b))) (schemeHomOverToOverHom (AJ (τ b')))
    obtain ⟨m2⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut Xm ε) hh
      (T := Over.mk tQ) (schemeHomOverToOverHom (AJ (τ b))) (schemeHomOverToOverHom (Φ (AJ b')))
    obtain ⟨t1⟩ := hΦP (AJ b)
    obtain ⟨t2⟩ := hΦP (AJ b')
    obtain ⟨i1⟩ := hI1 b
    obtain ⟨i2⟩ := hI1 b'
    obtain ⟨i3⟩ := hI1 (τ b)
    obtain ⟨i4⟩ := hI1 (τ b')
    obtain ⟨o1⟩ := hOσ b
    obtain ⟨o2⟩ := hOσ b'
    let Ob := (RelEffCartierDiv.ofPoint Xm (bar (τ b)).1 (bar (τ b)).2).lineBundle
    let Ob' := (RelEffCartierDiv.ofPoint Xm (bar (τ b')).1 (bar (τ b')).2).lineBundle
    let Iε := (RelEffCartierDiv.ofPoint Xm (tQ ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (tQ ≫ ·) ε.2).trans (Category.comp_id _)))).idealModule
    let Iw := (Scheme.Modules.pullback cσ).obj Iε
    have eθb : (P.pullbackAlong (Φ (AJ b))).L ≅ Ob ⊗ Iw :=
      t1 ≪≫ (Scheme.Modules.pullback cσ).mapIso i1 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o1 ⊗ᵢ Iso.refl _)
    have eθb' : (P.pullbackAlong (Φ (AJ b'))).L ≅ Ob' ⊗ Iw :=
      t2 ≪≫ (Scheme.Modules.pullback cσ).mapIso i2 ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (o2 ⊗ᵢ Iso.refl _)
    have eL : (P.pullbackAlong (Φ (AJ b) * AJ (τ b'))).L ≅ (Ob ⊗ Iw) ⊗ (Ob' ⊗ Iε) :=
      m1 ≪≫ (eθb ⊗ᵢ i4)
    have eR : (P.pullbackAlong (AJ (τ b) * Φ (AJ b'))).L ≅ (Ob ⊗ Iε) ⊗ (Ob' ⊗ Iw) :=
      m2 ≪≫ (i3 ⊗ᵢ eθb')
    exact ⟨eL ≪≫ Scheme.Modules.tensorTensorTensorComm Ob Iw Ob' Iε ≪≫ (Iso.refl _ ⊗ᵢ β_ Iw Iε) ≪≫
      (Scheme.Modules.tensorTensorTensorComm Ob Iε Ob' Iw).symm ≪≫ eR.symm⟩

  have hkey : ∀ b, Φ (AJ b) = AJ (τ b) * (AJ (τ εbar))⁻¹ := by
    intro b
    have hk := hkey2 b εbar
    rw [hAJε, hΦone, mul_one] at hk
    rw [← hk, mul_inv_cancel_right]

  intro a Dv hDv
  obtain ⟨Dv', hDv', hgp⟩ := hpts_aj a εbar hεbar
  obtain rfl : Dv = Dv' := Subtype.ext (hDv.trans hDv'.symm)
  obtain ⟨D1, hD1, hgp1⟩ := hpts_aj (τ a) εbar hεbar
  obtain ⟨D2, hD2, hgp2⟩ := hpts_aj (τ εbar) εbar hεbar
  have hA0 : gpts (Pic0.mk Dv) = AJ a := Subtype.ext hgp
  have hA1 : gpts (Pic0.mk D1) = AJ (τ a) := Subtype.ext hgp1
  have hA2 : gpts (Pic0.mk D2) = AJ (τ εbar) := Subtype.ext hgp2

  have hsm : σ' • Pic0.mk Dv = Pic0.mk D1 - Pic0.mk D2 := by
    rw [ModularCurve.galois_smul_pic0_def, AlgebraicCurve.SemilinearAut.pic0_smul_mk]
    have hcoe : (AlgebraicCurve.SemilinearAut.degZeroSMulHom
          (ModularCurve.arithmeticGalois (L := Qb) (ModularCurve.x1FunctionField (M * p)) σ') Dv) = D1 - D2 := by
      apply Subtype.ext
      rw [AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom, AddSubgroupClass.coe_sub, hD1, hD2, hDv, smul_sub,
        AlgebraicCurve.SemilinearAut.smul_single, AlgebraicCurve.SemilinearAut.smul_single, hplτ, hplτ]
      abel
    rw [hcoe]
    exact QuotientAddGroup.mk_sub _ D1 D2
  have hfin : gpts (σ' • Pic0.mk Dv) = Φ (gpts (Pic0.mk Dv)) := by
    rw [hsm, hgsub, hA1, hA2, hA0, hkey]
  exact congrArg Subtype.val hfin

set_option maxHeartbeats 3200000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (hprL : IsProper (pullback.snd D.toBase (specMap A L)))
    (hgcL : GeometricallyConnected (pullback.snd D.toBase (specMap A L)))

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)

    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hMηpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L))

    (hgal : ∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
      (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
      Mη.pointEquivPlace x' =
        ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x)
    (hin : ModularCurve.HeckeDiamondInputsAll (M * p)) (hcomm : ModularCurve.HeckeDiamondCommuteBar (M * p))

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (gpts : ModularCurve.JOne (M * p) ≃ SchemeHomOver (specMap A (AlgebraicClosure ℚ)) D.toBase)
    (hgadd : ∀ x y : ModularCurve.JOne (M * p), gpts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some).mul _ (gpts x) (gpts y))
    (hDL : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)
        (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (sectionBaseChange L ε)) (D.baseChange L))
    (ajL : SchemeHomOver (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (D.baseChange L).toBase)
    (kL : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L))
    (ajbar : Mη.C ⟶ D.P)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε L
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A L), pullback.condition⟩)).L))
    (hajLε : (sectionBaseChange L ε).1 ≫ ajL.1 = (D.baseChange L).zeroSection)
    (hajL : (∀ (K' : Type) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of L))
        (x : SchemeHomOver t (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L)),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L) (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
              (Category.comp_id t)))).idealModule)))
    (hkL₁ : kL ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
    (hkL₂ : kL ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A L) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ specMap L (AlgebraicClosure ℚ))
    (hajbar : ajbar = eη ≫ kL ≫ ajL.1 ≫ pullback.fst D.toBase (specMap A L))
    (hajbar_over : ajbar ≫ D.toBase = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ))
    (hεbar : εbar.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1)
    (hεbar_aj : εbar.1 ≫ ajbar = specMap A (AlgebraicClosure ℚ) ≫ D.zeroSection)
    (hpts_aj : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = specMap A (AlgebraicClosure ℚ) ≫ ε.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p))) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (gpts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (s : L ≃ₐ[ℚ] L)
    (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j)
    (hws : ws ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = (ModularCurve.TwoChart.modelTo A (↥K) j) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))))
    (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρs : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
        ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L))
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (hsinv : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) = 𝟙 (Spec (CommRingCat.of A)))

    (N : SchemeHomOver (D.toBase ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)
    (hN : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hrep.some.poincare.pullbackAlong
          (⟨a.1 ≫ N.1, by rw [Category.assoc, N.2, ← Category.assoc, a.2]⟩ : SchemeHomOver (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) D.toBase)).L ≅
        Scheme.Modules.rigidify (rigSection (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) ε) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))))
          ((Scheme.Modules.pullback
              (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (t ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹)))) (ModularCurve.TwoChart.modelTo A (↥K) j) t ws (𝟙 T) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)))
                hws.symm (by rw [Category.assoc, hsinv, Category.comp_id, Category.id_comp]))).obj
            (hrep.some.poincare.pullbackAlong a).L))) :
    letI := ModularCurve.heckeModuleOneBar (M * p)
    ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ l : L, σ' (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) (s l)) →
      ∀ x : ModularCurve.JOne (M * p),
        (gpts (σ' • x)).1 = Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ (gpts x).1 ≫ N.1 := by
  letI := ModularCurve.heckeModuleOneBar (M * p)
  intro σ' hσ'

  haveI hwsIso : IsIso ws := TAUTR_isIso_ws p M L K hK A j hj hΓA s ws hws ρs hρs hwρ

  have hsinv' : (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) = 𝟙 (Spec (CommRingCat.of A)) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    show MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹ a) = a
    simp [MulSemiringAction.toRingHom_apply, smul_smul]
  obtain ⟨hNmul, hNone⟩ := TAUTR_N_mul_one hrep.some (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s))) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) hsinv hsinv' ws hws N (fun t a => hN t a)

  have hpt := TAUTR_stepC
    p M hM hpM L ζ hζ K hK A hAp hζA j hj ε D hrep hsm hsep hsmL hgiL hprL hgcL Mη eη heη hMηpin hgal hin hcomm hΓA gpts hgadd hDL ajL kL ajbar εbar hPL hajLε hajL hkL₁ hkL₂ hajbar hajbar_over hεbar hεbar_aj hpts_aj s ws hws ρs hρs hwρ hsinv N hN σ' hσ' hNmul hNone

  have hbase : Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom) ≫ specMap A (AlgebraicClosure ℚ) ≫ (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) = specMap A (AlgebraicClosure ℚ) := by
    simp only [specMap, ← Spec.map_comp]
    congr 1
    ext a
    show σ'.toRingEquiv.toRingHom (algebraMap A (AlgebraicClosure ℚ) (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹ a)) = algebraMap A (AlgebraicClosure ℚ) a
    rw [MulSemiringAction.toRingHom_apply, IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ), hΓA,
      IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ)]
    show σ' (algebraMap L (AlgebraicClosure ℚ) (s⁻¹ (algebraMap A L a))) = _
    rw [hσ', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  have hdeg1 : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)), v.deg = 1 := fun v =>
    ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ)
      (CongruenceSubgroup.Gamma1 (M * p)) hT (ModularCurve.x1FunctionField (M * p)) rfl v
  refine TAUTR.stepD (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep.some) (Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s⁻¹))) N hNmul hNone (specMap A (AlgebraicClosure ℚ)) (Spec.map (CommRingCat.ofHom σ'.toRingEquiv.toRingHom)) hbase
    (fun x => gpts x) (fun x y => hgadd x y) (DistribMulAction.toAddMonoidHom (ModularCurve.JOne (M * p)) σ')
    {y | ∃ (V : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)))
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single (Mη.pointEquivPlace εbar) 1 ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ModularCurve.x1FunctionFieldBar (M * p))),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single (Mη.pointEquivPlace εbar) 1, h⟩}
    (fun x => AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single hdeg1 (Mη.pointEquivPlace εbar) x) ?_
  rintro _ ⟨V, hV, rfl⟩
  exact hpt (Mη.pointEquivPlace.symm V) ⟨_, hV⟩ (by rw [Equiv.apply_symm_apply])

#print axioms solution

end S_ModularCurve_XOneP_pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pts_smul_eq_specMap_comp_comp_of_galoisModelAut_of_classifies_abelJacobi_twoChartModel_x1_mul (solution)
