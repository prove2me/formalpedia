-- Prove2me | solution 1 for ModularCurve.XOneP.exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/78b47273-cd2e-522c-adff-70475b0dd692

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
import Theorems.Thm_ModularCurve_TwoChart_exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct

universe u

namespace B1PrimeExport

section ExportTools
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _

  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]

  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]

  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]

  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]

  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]

  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]

  simp only [← CategoryTheory.comp_apply]
  rfl

end ExportTools

section ExportGenerator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicCurve AlgebraicCurve.CurveModel
open scoped IntermediateField

theorem glued_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    {X : Scheme.{u}} (f : glued K t ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((gluedFunctionFieldEquiv K t).symm
      ((glued K t).germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) := by
  set U : (glued K t).Opens := f ⁻¹ᵁ (ι ''ᵁ ⊤) with hU
  set σ : Γ(glued K t, U) := (f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a)) with hσ
  let V' : (X₀ K t).Opens := (ι₀ K t) ⁻¹ᵁ U
  have hV'U : (ι₀ K t) ''ᵁ V' ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hx

  have hηU : genericPoint (glued K t) ∈ U := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact ((genericPoint_spec (glued K t)).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hξV' : genericPoint (X₀ K t) ∈ V' := by
    show (ι₀ K t).base (genericPoint (X₀ K t)) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion]
    exact hηU
  have hη : genericPoint (glued K t) ∈ (ι₀ K t) ''ᵁ V' :=
    ⟨genericPoint (X₀ K t), hξV', genericPoint_eq_of_isOpenImmersion _⟩

  have step1 : (glued K t).germToFunctionField U σ =
      (glued K t).presheaf.germ ((ι₀ K t) ''ᵁ V') (genericPoint (glued K t)) hη
        (((ι₀ K t).appIso V').inv (((ι₀ K t).appIso V').hom
          ((glued K t).presheaf.map (homOfLE hV'U).op σ))) := by
    rw [Iso.hom_inv_id_apply, TopCat.Presheaf.germ_res_apply]

  have step2 : ((ι₀ K t).appIso V').hom ((glued K t).presheaf.map (homOfLE hV'U).op σ) =
      (X₀ K t).presheaf.map (homOfLE le_top).op (secTop K (chartRing K ({t} : Set L)) (θ a)) :=
    appIso_hom_res_app_appIso_inv_apply f ι (ι₀ K t) θ hfac a V' hV'U
  rw [step1, step2]

  rw [ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
    (fun b => coe_chartIncl K _ b) rfl V' _ (genericPoint (X₀ K t)) hξV' hη]

  rw [germ_res_secTop]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun b => coe_chartIncl K _ b) _ _

theorem ofGenerator_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht : Transcendental K t)
    {X : Scheme.{u}} (f : (CurveModel.ofGenerator K t ht).C ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((CurveModel.ofGenerator K t ht).ffEquiv.symm
      ((CurveModel.ofGenerator K t ht).C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) :=
  @glued_ffEquiv_symm_germToFunctionField K _ L _ _ t _ _ X f A₀ ι _ θ hfac a hne

end ExportGenerator

end B1PrimeExport

section GalEngine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel IsDedekindDomain IntermediateField

open scoped Pointwise TensorProduct

namespace TwoChartGlueGal
namespace C

variable {L : Type u} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
variable (g : L ≃ₐ[ℚ] L)

private theorem arithmeticRingAut_symm_apply (x : ↥(laurentBaseChange L F₀)) :
    (arithmeticRingAut F₀ g).symm x = arithmeticRingAut F₀ g.symm x :=
  rfl

private theorem galois_smul_eq (x : ↥(laurentBaseChange L F₀)) :
    arithmeticGalois F₀ g • x = arithmeticRingAut F₀ g x :=
  rfl

private theorem galois_inv_smul_eq (x : ↥(laurentBaseChange L F₀)) :
    (arithmeticGalois F₀ g)⁻¹ • x = (arithmeticRingAut F₀ g).symm x :=
  rfl

variable {F₀ g} in
private theorem symm_fix {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s) :
    (arithmeticRingAut F₀ g).symm s = s :=
  (arithmeticRingAut F₀ g).symm_apply_eq.mpr hs.symm

variable {F₀ g} in
private theorem arithmeticRingAut_mem_adjoin {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) {x : ↥(laurentBaseChange L F₀)}
    (hx : x ∈ Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) :
    arithmeticRingAut F₀ g x ∈ Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)) := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx, hs]
    exact Algebra.subset_adjoin rfl
  | algebraMap a =>
    rw [arithmeticRingAut_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

variable {F₀ g} in

private theorem arithmeticRingAut_mem_chartRing {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) {x : ↥(laurentBaseChange L F₀)}
    (hx : x ∈ chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) :
    arithmeticRingAut F₀ g x ∈ chartRing L ({s} : Set ↥(laurentBaseChange L F₀)) := by
  obtain ⟨p, hp, hx0⟩ :=
    (id hx : IsIntegral ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) x)
  let ψ : ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) →+*
      ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) :=
    ((arithmeticRingAut F₀ g).toRingHom.comp
      (Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))).val.toRingHom).codRestrict
      (Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
      fun a => arithmeticRingAut_mem_adjoin hs a.2
  have hψ : (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
      ↥(laurentBaseChange L F₀)).comp ψ =
      (arithmeticRingAut F₀ g).toRingHom.comp
        (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀)))
          ↥(laurentBaseChange L F₀)) :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map ψ, hp.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ]
  have key := Polynomial.hom_eval₂ p
    (algebraMap ↥(Algebra.adjoin L ({s} : Set ↥(laurentBaseChange L F₀))) ↥(laurentBaseChange L F₀))
    (arithmeticRingAut F₀ g).toRingHom x
  rw [hx0, map_zero] at key
  exact key.symm

variable {F₀ g} in

private def chartAut {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s) :
    ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) ≃+*
      ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) where
  toFun a := ⟨arithmeticRingAut F₀ g a, arithmeticRingAut_mem_chartRing hs a.2⟩
  invFun a := ⟨(arithmeticRingAut F₀ g).symm a,
    arithmeticRingAut_mem_chartRing (g := g.symm)
      (show arithmeticRingAut F₀ g.symm s = s from symm_fix hs) a.2⟩
  left_inv a := Subtype.ext
    ((arithmeticRingAut F₀ g).symm_apply_apply (a : ↥(laurentBaseChange L F₀)))
  right_inv a := Subtype.ext
    ((arithmeticRingAut F₀ g).apply_symm_apply (a : ↥(laurentBaseChange L F₀)))
  map_mul' a b := Subtype.ext
    (map_mul (arithmeticRingAut F₀ g) (a : ↥(laurentBaseChange L F₀)) (b : ↥(laurentBaseChange L F₀)))
  map_add' a b := Subtype.ext
    (map_add (arithmeticRingAut F₀ g) (a : ↥(laurentBaseChange L F₀)) (b : ↥(laurentBaseChange L F₀)))

variable {F₀ g} in
@[scoped simp]
private theorem coe_chartAut {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    (chartAut hs a : ↥(laurentBaseChange L F₀)) = arithmeticRingAut F₀ g a :=
  rfl

variable {F₀ g} in
@[scoped simp]
private theorem coe_chartAut_symm {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    ((chartAut hs).symm a : ↥(laurentBaseChange L F₀)) = (arithmeticRingAut F₀ g).symm a :=
  rfl

variable {F₀ g} in
private theorem chartAut_symm_algebraMap {s : ↥(laurentBaseChange L F₀)}
    (hs : arithmeticRingAut F₀ g s = s) (c : L) :
    (chartAut hs).symm (algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) c) =
      algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) (g.symm c) := by
  apply Subtype.ext
  show (arithmeticRingAut F₀ g).symm (algebraMap L ↥(laurentBaseChange L F₀) c) =
    algebraMap L ↥(laurentBaseChange L F₀) (g.symm c)
  exact arithmeticRingAut_algebraMap F₀ g.symm c

private theorem mem_nonunits_smul_iff (h : SemilinearAut L ↥(laurentBaseChange L F₀))
    (O : ValuationSubring ↥(laurentBaseChange L F₀)) (x : ↥(laurentBaseChange L F₀)) :
    x ∈ (h • O).nonunits ↔ h⁻¹ • x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

variable {F₀ g} in

private theorem smul_mem_chartPlaces {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s) :
    arithmeticGalois F₀ g • v ∈ chartPlaces L s := by
  show s ∈ (arithmeticGalois F₀ g • v).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    galois_inv_smul_eq, symm_fix hs]
  exact hv

set_option synthInstance.maxHeartbeats 1600000 in

private scoped instance (priority := high) isScalarTower_chartRing (S : Set ↥(laurentBaseChange L F₀)) :
    IsScalarTower L ↥(chartRing L S) ↥(laurentBaseChange L F₀) :=
  ⟨fun a b c => by
    show a • (b : ↥(laurentBaseChange L F₀)) * c = a • ((b : ↥(laurentBaseChange L F₀)) * c)
    rw [Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩

section Dictionary

variable [CharZero L] (s : ↥(laurentBaseChange L F₀))
  [FiniteDimensional L⟮s⟯ ↥(laurentBaseChange L F₀)]

private theorem mem_prime_iff_nonunits {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    a ∈ ((primeEquivChartPlaces L s).symm ⟨v, hv⟩).asIdeal ↔
      (a : ↥(laurentBaseChange L F₀)) ∈ v.toValuationSubring.nonunits := by
  have hv𝔭 : Place.ofHeightOneSpectrum (K := L) ((primeEquivChartPlaces L s).symm ⟨v, hv⟩) = v :=
    congrArg Subtype.val ((primeEquivChartPlaces L s).apply_symm_apply ⟨v, hv⟩)
  have hO : v.toValuationSubring =
      (((primeEquivChartPlaces L s).symm ⟨v, hv⟩).valuation ↥(laurentBaseChange L F₀)).valuationSubring :=
    (congrArg Place.toValuationSubring hv𝔭).symm
  rw [hO, ValuationSubring.mem_nonunits_iff,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥(laurentBaseChange L F₀))]
  exact (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one

variable {s} in

private theorem prime_smul (hs : arithmeticRingAut F₀ g s = s)
    {v : Place L ↥(laurentBaseChange L F₀)} (hv : v ∈ chartPlaces L s) :
    ((primeEquivChartPlaces L s).symm ⟨arithmeticGalois F₀ g • v, smul_mem_chartPlaces hs hv⟩).asIdeal =
      Ideal.map (chartAut hs) ((primeEquivChartPlaces L s).symm ⟨v, hv⟩).asIdeal := by
  ext a
  rw [mem_prime_iff_nonunits F₀ s, ← Ideal.comap_symm, Ideal.mem_comap, mem_prime_iff_nonunits F₀ s,
    SemilinearAut.smul_toValuationSubring, mem_nonunits_smul_iff]
  rfl

variable {s} in

private theorem ofHeightOneSpectrum_eq_smul (hs : arithmeticRingAut F₀ g s = s)
    (𝔭 𝔭' : HeightOneSpectrum ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))))
    (h : 𝔭'.asIdeal = Ideal.map (chartAut hs) 𝔭.asIdeal) :
    Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭' =
      arithmeticGalois F₀ g •
        Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭 := by
  have h𝔭 : (primeEquivChartPlaces L s).symm ⟨Place.ofHeightOneSpectrum (K := L) 𝔭,
      mem_ofHeightOneSpectrum L s 𝔭⟩ = 𝔭 :=
    (primeEquivChartPlaces L s).symm_apply_apply 𝔭
  have key := prime_smul F₀ g hs (mem_ofHeightOneSpectrum L s 𝔭)
  rw [h𝔭, ← h] at key
  have h𝔭' : (primeEquivChartPlaces L s).symm
      ⟨arithmeticGalois F₀ g • Place.ofHeightOneSpectrum (K := L) 𝔭,
        smul_mem_chartPlaces hs (mem_ofHeightOneSpectrum L s 𝔭)⟩ = 𝔭' :=
    HeightOneSpectrum.ext key
  have := congrArg Subtype.val ((primeEquivChartPlaces L s).apply_symm_apply
    ⟨arithmeticGalois F₀ g • Place.ofHeightOneSpectrum (K := L) 𝔭,
      smul_mem_chartPlaces hs (mem_ofHeightOneSpectrum L s 𝔭)⟩)
  rw [h𝔭'] at this
  exact this

end Dictionary

variable {F₀ g} in

private def conjAlgHom {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L) :
    ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L :=
  { (g : L →+* L).comp (φ.toRingHom.comp (chartAut hs).symm.toRingHom) with
    commutes' := fun c => by
      show g (φ ((chartAut hs).symm
        (algebraMap L ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) c))) = algebraMap L L c
      rw [chartAut_symm_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply,
        Algebra.algebraMap_self_apply]
      exact g.apply_symm_apply c }

variable {F₀ g} in
private theorem conjAlgHom_apply {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (a : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))) :
    conjAlgHom hs φ a = g (φ ((chartAut hs).symm a)) :=
  rfl

variable {F₀ g} in

private theorem ker_conjAlgHom {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    (φ : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L) :
    RingHom.ker (conjAlgHom hs φ) = Ideal.map (chartAut hs) (RingHom.ker φ) := by
  ext a
  rw [RingHom.mem_ker, conjAlgHom_apply, map_eq_zero_iff g g.injective, ← Ideal.comap_symm,
    Ideal.mem_comap, RingHom.mem_ker]

variable {F₀ g} in

private theorem eq_conjAlgHom_of_eqOn {s : ↥(laurentBaseChange L F₀)} (hs : arithmeticRingAut F₀ g s = s)
    {T : Set ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))}
    (hT : Algebra.adjoin L T = ⊤) (hfix : ∀ t ∈ T, chartAut hs t = t)
    (φ φ' : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (hconj : ∀ t ∈ T, φ' t = g (φ t)) :
    φ' = conjAlgHom hs φ := by
  refine AlgHom.ext_of_adjoin_eq_top hT fun t ht => ?_
  show φ' t = g (φ ((chartAut hs).symm t))
  rw [hconj t ht, (chartAut hs).symm_apply_eq.mpr (hfix t ht).symm]

variable {F₀ g} in

private theorem ofHeightOneSpectrum_ker_eq_smul [CharZero L] {s : ↥(laurentBaseChange L F₀)}
    [FiniteDimensional L⟮s⟯ ↥(laurentBaseChange L F₀)]
    (hs : arithmeticRingAut F₀ g s = s)
    {T : Set ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀)))}
    (hT : Algebra.adjoin L T = ⊤) (hfix : ∀ t ∈ T, chartAut hs t = t)
    (φ φ' : ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))) →ₐ[L] L)
    (hconj : ∀ t ∈ T, φ' t = g (φ t))
    (𝔭 𝔭' : HeightOneSpectrum ↥(chartRing L ({s} : Set ↥(laurentBaseChange L F₀))))
    (h𝔭 : 𝔭.asIdeal = RingHom.ker φ) (h𝔭' : 𝔭'.asIdeal = RingHom.ker φ') :
    Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭' =
      arithmeticGalois F₀ g •
        Place.ofHeightOneSpectrum (K := L) (F := ↥(laurentBaseChange L F₀)) 𝔭 := by
  refine ofHeightOneSpectrum_eq_smul F₀ g hs 𝔭 𝔭' ?_
  rw [h𝔭', h𝔭, eq_conjAlgHom_of_eqOn hs hT hfix φ φ' hconj, ker_conjAlgHom]

end TwoChartGlueGal.C
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal"

namespace TwoChartGlueGal
namespace P

section Cancel

variable {A B : Type u} [CommRing A] [CommRing B] {X : Scheme.{u}}

private theorem ringHom_eq_of_SpecMap_comp_eq (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι] (ψ ψ' : A →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι = Spec.map (CommRingCat.ofHom ψ) ≫ ι) : ψ' = ψ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ') = Spec.map (CommRingCat.ofHom ψ) := (cancel_mono ι).mp h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

private theorem ringHom_eq_comp_of_SpecMap_comp (ι : Spec (CommRingCat.of A) ⟶ X) [Mono ι]
    (ψ ψ' : A →+* B) (g : B →+* B)
    (h : Spec.map (CommRingCat.ofHom ψ') ≫ ι =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ ι) :
    ψ' = g.comp ψ := by
  apply ringHom_eq_of_SpecMap_comp_eq ι
  rw [h, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end Cancel
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C"

section AlgHom

variable (K : Type u) [Field K]

private def _root_.TwoChartGlueGal.P.toAlgHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : R →ₐ[K] K :=
  { φ with commutes' := fun c => RingHom.congr_fun hφ c }

p2m_export "TwoChartGlueGal.P" "toAlgHom"
@[scoped simp]
private theorem toAlgHom_toRingHom {R : Type u} [CommRing R] [Algebra K R] (φ : R →+* K)
    (hφ : φ.comp (algebraMap K R) = RingHom.id K) : (toAlgHom K φ hφ).toRingHom = φ :=
  rfl

end AlgHom
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C"

section Points

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
  [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]

private theorem exists_algHom_eq_SpecMap_comp_ι₀ (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (hx : x.1 (IsLocalRing.closedPoint K) ∈ Set.range (ι₀ K t)) :
    ∃ φ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι₀ K t = x.1 := by
  have hrange : Set.range x.1 ⊆ Set.range (ι₀ K t) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (ι₀ K t) x.1 hrange
  have h1 : IsOpenImmersion.lift (ι₀ K t) x.1 hrange ≫ (ι₀ K t ≫ gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact x.2
  rw [ι₀_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (ι₀ K t) x.1 hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (ι₀ K t) x.1 hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem pointEquivPlace_of_eq_SpecMap_comp_ι₀ [IsAlgClosed K] (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (φ : ↥(chartRing K ({t} : Set L)) →ₐ[K] K)
    (hx : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι₀ K t = x.1) :
    ∃ 𝔭 : HeightOneSpectrum ↥(chartRing K ({t} : Set L)),
      𝔭.asIdeal = RingHom.ker φ.toRingHom ∧
      (ofGenerator K t ht).pointEquivPlace x = Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭 := by
  have hpt : x.1 (IsLocalRing.closedPoint K) =
      ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := by
    rw [← hx]
    rfl
  have hx₀ : (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker φ.toRingHom := by
    show Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal K) = RingHom.ker φ.toRingHom
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hc : ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) ∈
      closedPoints (glued K t) := by
    have h2 := (pointEquivClosedPoint (ofGenerator K t ht).toBase x).2
    have h3 : ((pointEquivClosedPoint (ofGenerator K t ht).toBase x : (ofGenerator K t ht).C)) =
        ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := hpt
    rw [h3] at h2
    exact h2
  refine ⟨primeOfι₀ K t ht _ hc, hx₀, ?_⟩
  rw [pointEquivPlace_apply]
  have h4 : pointEquivClosedPoint (ofGenerator K t ht).toBase x =
      (⟨ι₀ K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)), hc⟩ :
        closedPoints (glued K t)) :=
    Subtype.ext hpt
  rw [h4]
  exact gluedPlaceOfPoint_ι₀ K t ht _ hc

private theorem exists_algHom_eq_SpecMap_comp_ιInf (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (hx : x.1 (IsLocalRing.closedPoint K) ∈ Set.range (ιInf K t)) :
    ∃ φ : ↥(chartRing K ({t⁻¹} : Set L)) →ₐ[K] K,
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf K t = x.1 := by
  have hrange : Set.range x.1 ⊆ Set.range (ιInf K t) := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [hp]
    exact hx
  have hfac := IsOpenImmersion.lift_fac (ιInf K t) x.1 hrange
  have h1 : IsOpenImmersion.lift (ιInf K t) x.1 hrange ≫ (ιInf K t ≫ gluedToBase K t) = 𝟙 _ := by
    rw [← Category.assoc, hfac]
    exact x.2
  rw [ιInf_gluedToBase, ← Spec.map_preimage (IsOpenImmersion.lift (ιInf K t) x.1 hrange),
    ← Spec.map_comp] at h1
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective (h1.trans (Spec.map_id _).symm))
  refine ⟨toAlgHom K (Spec.preimage (IsOpenImmersion.lift (ιInf K t) x.1 hrange)).hom h2, ?_⟩
  rw [toAlgHom_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

private theorem pointEquivPlace_of_eq_SpecMap_comp_ιInf [IsAlgClosed K] (ht : Transcendental K t)
    (x : {p : Spec (CommRingCat.of K) ⟶ (ofGenerator K t ht).C // p ≫ (ofGenerator K t ht).toBase = 𝟙 _})
    (φ : ↥(chartRing K ({t⁻¹} : Set L)) →ₐ[K] K)
    (hx : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ιInf K t = x.1)
    (h₀ : x.1 (IsLocalRing.closedPoint K) ∉ Set.range (ι₀ K t)) :
    ∃ 𝔭 : HeightOneSpectrum ↥(chartRing K ({t⁻¹} : Set L)),
      𝔭.asIdeal = RingHom.ker φ.toRingHom ∧
      (ofGenerator K t ht).pointEquivPlace x = Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭 := by
  have hpt : x.1 (IsLocalRing.closedPoint K) =
      ιInf K t (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)) := by
    rw [← hx]
    rfl
  have hx₀ : (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K)).asIdeal =
      RingHom.ker φ.toRingHom := by
    show Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal K) = RingHom.ker φ.toRingHom
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  have hc : x.1 (IsLocalRing.closedPoint K) ∈ closedPoints (glued K t) :=
    (pointEquivClosedPoint (ofGenerator K t ht).toBase x).2
  refine ⟨primeOfιInf K t ht (Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint K))
    (by rw [← hpt]; exact hc), hx₀, ?_⟩
  rw [pointEquivPlace_apply]
  exact gluedPlaceOfPoint_of_not_mem K t ht ⟨x.1 (IsLocalRing.closedPoint K), hc⟩ h₀ _ hpt.symm

end Points
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C"

end TwoChartGlueGal.P
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C"

namespace TwoChartGlueGal
namespace GX

open TwoChartGlueGal.C TwoChartGlueGal.P AlgebraicCurve.CurveModel

local notation "Qb" => AlgebraicClosure ℚ

private theorem SpecMap_ι₀_f (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X)
    {AFin : Type} [CommRing AFin] (ιFin : Spec (CommRingCat.of AFin) ⟶ X) [IsOpenImmersion ιFin]
    (ρFin : AFin →+* ↥(chartRing (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqFin : ι₀ Qb t ≫ f = Spec.map (CommRingCat.ofHom ρFin) ≫ ιFin)
    (ψ : ↥(chartRing Qb ({t} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ι₀ Qb t ≫ f = Spec.map (CommRingCat.ofHom (ψ.comp ρFin)) ≫ ιFin := by
  rw [hsqFin, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem SpecMap_ιInf_f (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X)
    {AInf : Type} [CommRing AInf] (ιInf' : Spec (CommRingCat.of AInf) ⟶ X) [IsOpenImmersion ιInf']
    (ρInf : AInf →+* ↥(chartRing (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqInf : CurveModel.ιInf Qb t ≫ f = Spec.map (CommRingCat.ofHom ρInf) ≫ ιInf')
    (ψ : ↥(chartRing Qb ({t⁻¹} : Set (↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) →+* Qb) :
    Spec.map (CommRingCat.ofHom ψ) ≫ CurveModel.ιInf Qb t ≫ f = Spec.map (CommRingCat.ofHom (ψ.comp ρInf)) ≫ ιInf' := by
  rw [hsqInf, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem f_closedPoint_eq (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X) (g : Qb ≃ₐ[ℚ] Qb)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C // q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).toBase = 𝟙 _})
    (h : x'.1 ≫ f = Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ f) :
    f (x'.1 (IsLocalRing.closedPoint Qb)) = f (x.1 (IsLocalRing.closedPoint Qb)) :=
  calc f (x'.1 (IsLocalRing.closedPoint Qb))
      = (x'.1 ≫ f) (IsLocalRing.closedPoint Qb) := rfl
    _ = (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ f) (IsLocalRing.closedPoint Qb) := by rw [h]
    _ = (x.1 ≫ f) (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb)) := rfl
    _ = (x.1 ≫ f) (IsLocalRing.closedPoint Qb) := by
        rw [Subsingleton.elim (α := PrimeSpectrum Qb)
          (Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) (IsLocalRing.closedPoint Qb))
          (IsLocalRing.closedPoint Qb)]
    _ = f (x.1 (IsLocalRing.closedPoint Qb)) := rfl

private theorem hgal_fin (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X)
    {AFin : Type} [CommRing AFin] (ιFin : Spec (CommRingCat.of AFin) ⟶ X) [IsOpenImmersion ιFin]
    (ρFin : AFin →+* ↥(chartRing (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqFin : ι₀ Qb t ≫ f = Spec.map (CommRingCat.ofHom ρFin) ≫ ιFin)
    (g : Qb ≃ₐ[ℚ] Qb) (hgt : arithmeticRingAut F₀ g t = t)
    (hfixFin : ∀ s ∈ Set.range ρFin, chartAut hgt s = s)
    (hAfin : Algebra.adjoin Qb (Set.range ρFin) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C // q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).toBase = 𝟙 _})
    (h : x'.1 ≫ f = Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ f)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb t))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb t)) :
    (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x' =
      arithmeticGalois (L := Qb) F₀ g • (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x := by
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb t ht x hx
  obtain ⟨φ', hφ'⟩ := exists_algHom_eq_SpecMap_comp_ι₀ Qb t ht x' hx'
  obtain ⟨𝔭, h𝔭, hx𝔭⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb t ht x φ hφ
  obtain ⟨𝔭', h𝔭', hx𝔭'⟩ := pointEquivPlace_of_eq_SpecMap_comp_ι₀ Qb t ht x' φ' hφ'
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ ι₀ Qb t) ≫ f =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι₀ Qb t) ≫ f := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ι₀_f F₀ t ht f ιFin ρFin hsqFin, SpecMap_ι₀_f F₀ t ht f ιFin ρFin hsqFin] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp ιFin _ _ _ h1
  have hconj : ∀ s ∈ Set.range ρFin, φ' s = g (φ s) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) F₀ g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul hgt hAfin hfixFin φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

private theorem hgal_inf (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X)
    {AInf : Type} [CommRing AInf] (ιInf' : Spec (CommRingCat.of AInf) ⟶ X) [IsOpenImmersion ιInf']
    (ρInf : AInf →+* ↥(chartRing (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqInf : CurveModel.ιInf Qb t ≫ f = Spec.map (CommRingCat.ofHom ρInf) ≫ ιInf')
    (g : Qb ≃ₐ[ℚ] Qb) (hgt_inv : arithmeticRingAut F₀ g t⁻¹ = t⁻¹)
    (hfixInf : ∀ s ∈ Set.range ρInf, chartAut hgt_inv s = s)
    (hAinf : Algebra.adjoin Qb (Set.range ρInf) = ⊤)
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C // q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).toBase = 𝟙 _})
    (h : x'.1 ≫ f = Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ f)
    (hx : x.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb t))
    (hx' : x'.1 (IsLocalRing.closedPoint Qb) ∉ Set.range (ι₀ Qb t)) :
    (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x' =
      arithmeticGalois (L := Qb) F₀ g • (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x := by
  obtain ⟨φ, hφ⟩ := exists_algHom_eq_SpecMap_comp_ιInf Qb t ht x
    (mem_range_ιInf_of_not_mem_range_ι₀ Qb t hx)
  obtain ⟨φ', hφ'⟩ := exists_algHom_eq_SpecMap_comp_ιInf Qb t ht x'
    (mem_range_ιInf_of_not_mem_range_ι₀ Qb t hx')
  obtain ⟨𝔭, h𝔭, hx𝔭⟩ :=
    pointEquivPlace_of_eq_SpecMap_comp_ιInf Qb t ht x φ hφ hx
  obtain ⟨𝔭', h𝔭', hx𝔭'⟩ :=
    pointEquivPlace_of_eq_SpecMap_comp_ιInf Qb t ht x' φ' hφ' hx'
  have h1 : (Spec.map (CommRingCat.ofHom φ'.toRingHom) ≫ CurveModel.ιInf Qb t) ≫ f =
      Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        CurveModel.ιInf Qb t) ≫ f := by
    rw [hφ, hφ']
    exact h
  simp only [Category.assoc] at h1
  rw [SpecMap_ιInf_f F₀ t ht f ιInf' ρInf hsqInf, SpecMap_ιInf_f F₀ t ht f ιInf' ρInf hsqInf] at h1
  have hP2 := ringHom_eq_comp_of_SpecMap_comp ιInf' _ _ _ h1
  have hconj : ∀ s ∈ Set.range ρInf, φ' s = g (φ s) := by
    rintro _ ⟨b, rfl⟩
    exact RingHom.congr_fun hP2 b
  refine hx𝔭'.trans (Eq.trans ?_
    (congrArg (arithmeticGalois (L := Qb) F₀ g • ·) hx𝔭).symm)
  exact ofHeightOneSpectrum_ker_eq_smul hgt_inv hAinf hfixInf φ φ' hconj 𝔭 𝔭' h𝔭 h𝔭'

theorem hgal (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (t : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) [Fact (t ≠ 0)]
    (ht : Transcendental (AlgebraicClosure ℚ) t)
    [hfd : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    {X : Scheme.{0}} (f : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C ⟶ X)
    {AFin : Type} [CommRing AFin] (ιFin : Spec (CommRingCat.of AFin) ⟶ X) [IsOpenImmersion ιFin]
    (ρFin : AFin →+* ↥(chartRing (AlgebraicClosure ℚ) ({t} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqFin : ι₀ Qb t ≫ f = Spec.map (CommRingCat.ofHom ρFin) ≫ ιFin)
    {AInf : Type} [CommRing AInf] (ιInf' : Spec (CommRingCat.of AInf) ⟶ X) [IsOpenImmersion ιInf']
    (ρInf : AInf →+* ↥(chartRing (AlgebraicClosure ℚ) ({t⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))))
    (hsqInf : CurveModel.ιInf Qb t ≫ f = Spec.map (CommRingCat.ofHom ρInf) ≫ ιInf')
    (g : Qb ≃ₐ[ℚ] Qb) (hgt : arithmeticRingAut F₀ g t = t)
    (hfixFin : ∀ b, arithmeticRingAut F₀ g (ρFin b : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = ρFin b)
    (hfixInf : ∀ b, arithmeticRingAut F₀ g (ρInf b : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) = ρInf b)
    (hAfin : Algebra.adjoin Qb (Set.range ρFin) = ⊤)
    (hAinf : Algebra.adjoin Qb (Set.range ρInf) = ⊤)
    (hP3 : ∀ y : (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C,
      f y ∈ Set.range ιFin ↔ y ∈ Set.range (ι₀ Qb t))
    (x x' : {q : Spec (CommRingCat.of Qb) ⟶ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).C // q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).toBase = 𝟙 _})
    (h : x'.1 ≫ f = Spec.map (CommRingCat.ofHom (g : Qb →+* Qb)) ≫ x.1 ≫ f) :
    (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x' =
      arithmeticGalois (L := Qb) F₀ g • (CurveModel.ofGenerator (AlgebraicClosure ℚ) t ht).pointEquivPlace x := by
  have hgt_inv : arithmeticRingAut F₀ g t⁻¹ = t⁻¹ := by rw [map_inv₀, hgt]
  have hfixFin' : ∀ s ∈ Set.range ρFin, chartAut hgt s = s := by
    rintro _ ⟨b, rfl⟩; exact Subtype.ext (hfixFin b)
  have hfixInf' : ∀ s ∈ Set.range ρInf, chartAut hgt_inv s = s := by
    rintro _ ⟨b, rfl⟩; exact Subtype.ext (hfixInf b)
  have hsame : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb t) ↔
      x'.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb t) := by
    have h2 := hP3 (x'.1 (IsLocalRing.closedPoint Qb))
    rw [f_closedPoint_eq F₀ t ht f g x x' h] at h2
    exact (hP3 (x.1 (IsLocalRing.closedPoint Qb))).symm.trans h2
  by_cases hx : x.1 (IsLocalRing.closedPoint Qb) ∈ Set.range (ι₀ Qb t)
  · exact hgal_fin F₀ t ht f ιFin ρFin hsqFin g hgt hfixFin' hAfin x x' h hx (hsame.mp hx)
  · exact hgal_inf F₀ t ht f ιInf' ρInf hsqInf g hgt_inv hfixInf' hAinf x x' h hx (fun hx' => hx (hsame.mpr hx'))

end TwoChartGlueGal.GX
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"

end GalEngine
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"

namespace X1Meta

open ModularCurve AlgebraicCurve.CurveModel

theorem adjoin_range_comp_includeRight_eq_top {R : Type} [CommRing R] {Q : Type} [Field Q] [Algebra R Q]
    {B : Type} [CommRing B] [Algebra R B] {C : Type} [CommRing C] [Algebra Q C]
    (e : Q ⊗[R] B ≃ₐ[Q] C) :
    Algebra.adjoin Q (Set.range (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := B)).toRingHom)) = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  obtain ⟨z, rfl⟩ := e.surjective c
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Subalgebra.zero_mem _
  | tmul a b =>
      have : a ⊗ₜ[R] b = a • ((1 : Q) ⊗ₜ[R] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) a
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy

section ChartMatch

variable (A : Type) [CommRing A] (K : Type) [Field K] [Algebra A K] (j : K) [Fact (j ≠ 0)]
  (Q : Type) [Field Q] {Lf : Type} [Field Lf] [Algebra Q Lf] (t : Lf) [Fact (t ≠ 0)]

private theorem tc_ιFin_eq_ιInf_iff (x₀ : TwoChart.XFin A K j) (xi : TwoChart.XInf A K j) :
    (TwoChart.ιFin A K j).base x₀ = (TwoChart.ιInf A K j).base xi ↔
      ∃ w : TwoChart.XMid A K j, (TwoChart.fFin A K j).base w = x₀ ∧ (TwoChart.fInf A K j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (TwoChart.fFin A K j) (TwoChart.fInf A K j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (TwoChart.fFin A K j ≫ TwoChart.ιFin A K j).base w = (TwoChart.fInf A K j ≫ TwoChart.ιInf A K j).base w
    rw [TwoChart.glue_condition]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem tc_range_fInf : Set.range (TwoChart.fInf A K j).base =
    ((PrimeSpectrum.basicOpen (TwoChart.jInvChartInf A K j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(TwoChart.chartAlgInf A K j))) : Set (PrimeSpectrum ↥(TwoChart.chartAlgInf A K j))) := by
  letI := (TwoChart.inclInf A K j).toRingHom.toAlgebra
  haveI := TwoChart.isLocalization_away_inclInf A K j
  exact PrimeSpectrum.localization_away_comap_range ↥(TwoChart.chartAlgMid A K j) (TwoChart.jInvChartInf A K j)

private theorem tc_ιInf_mem_range_ιFin_iff (xi : TwoChart.XInf A K j) :
    (TwoChart.ιInf A K j).base xi ∈ Set.range (TwoChart.ιFin A K j).base ↔ TwoChart.jInvChartInf A K j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← tc_range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (tc_ιFin_eq_ιInf_iff A K j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(TwoChart.fFin A K j).base w, (tc_ιFin_eq_ιInf_iff A K j _ _).mpr ⟨w, rfl, rfl⟩⟩

theorem mem_range_ιFin_iff (f : glued Q t ⟶ TwoChartModel A K j)
    (ρFin : ↥(TwoChart.chartAlgFin A K j) →+* ↥(chartRing Q ({t} : Set Lf)))
    (ρInf : ↥(TwoChart.chartAlgInf A K j) →+* ↥(chartRing Q ({t⁻¹} : Set Lf)))
    (hsqFin : ι₀ Q t ≫ f = Spec.map (CommRingCat.ofHom ρFin) ≫ TwoChart.ιFin A K j)
    (hsqInf : CurveModel.ιInf Q t ≫ f = Spec.map (CommRingCat.ofHom ρInf) ≫ TwoChart.ιInf A K j)
    (hρ : ρInf (TwoChart.jInvChartInf A K j) = tInvChart Q t) (y : glued Q t) :
    f.base y ∈ Set.range (TwoChart.ιFin A K j).base ↔ y ∈ Set.range (ι₀ Q t).base := by
  rcases mem_range_ι₀_or_mem_range_ιInf Q t y with ⟨x₀, rfl⟩ | ⟨z, rfl⟩
  · refine ⟨fun _ => ⟨x₀, rfl⟩, fun _ => ⟨(Spec.map (CommRingCat.ofHom ρFin)).base x₀, ?_⟩⟩
    change (Spec.map (CommRingCat.ofHom ρFin) ≫ TwoChart.ιFin A K j).base x₀ = (ι₀ Q t ≫ f).base x₀
    rw [hsqFin]
  · have hz : f.base ((CurveModel.ιInf Q t).base z) =
        (TwoChart.ιInf A K j).base ((Spec.map (CommRingCat.ofHom ρInf)).base z) := by
      change (CurveModel.ιInf Q t ≫ f).base z = (Spec.map (CommRingCat.ofHom ρInf) ≫ TwoChart.ιInf A K j).base z
      rw [hsqInf]
    rw [hz, tc_ιInf_mem_range_ιFin_iff, ιInf_mem_range_ι₀_iff]
    show TwoChart.jInvChartInf A K j ∉ Ideal.comap ρInf z.asIdeal ↔ _
    rw [Ideal.mem_comap, hρ]

end ChartMatch
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"

theorem coeffMap_mem_laurentBaseChange (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (K : IntermediateField L (LaurentSeries L)) (hK : K = ModularCurve.laurentBaseChange L F₀) (b : ↥K) :
    ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀ := by
  have hx : ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L F₀ := hK ▸ b.2
  rw [ModularCurve.mem_laurentBaseChange_iff] at hx
  generalize ((b : ↥K) : LaurentSeries L) = x at hx ⊢
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single,
          ← ModularCurve.algebraMap_laurentSeries_eq_single]
        exact (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₀).algebraMap_mem _
      · have hcomp : (algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ) :=
          Subsingleton.elim _ _
        rw [ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hcomp]
        exact ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end X1Meta
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)] :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
      (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) (_ : IsIso eη)
      (_ : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))),

      eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase ∧

      (∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        ((Mη.ffEquiv.symm
            (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
              (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
                (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
            : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L)) ∧

      (∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)),
        (∀ l : L, g (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
        ∀ (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) →
        Mη.pointEquivPlace x' =
          ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField (M * p)) g • Mη.pointEquivPlace x) := by
  classical

  have hmem : ∀ b : ↥K, ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) ∈
      ModularCurve.x1FunctionFieldBar (M * p) :=
    fun b => X1Meta.coeffMap_mem_laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) K hK b
  let jb : ↥(ModularCurve.x1FunctionFieldBar (M * p)) := ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((j : ↥K) : LaurentSeries L), hmem j⟩
  have hcompQ : (algebraMap L (AlgebraicClosure ℚ)).comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ) :=
    Subsingleton.elim _ _
  have hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq := by
    show ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((j : ↥K) : LaurentSeries L) = _
    rw [hj, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hcompQ]
    rfl

  have hjq : (jb : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) :=
    hjb.trans (ModularCurve.coeffEmb_jq (AlgebraicClosure ℚ))
  obtain ⟨htrans, hfd⟩ :
      Transcendental (AlgebraicClosure ℚ) jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))
        ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 (M * p)) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]) jb hjq
  haveI hjb0 : Fact (jb ≠ 0) := ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI := hfd
  have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))) =
      IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (jb⁻¹ : ↥(ModularCurve.x1FunctionFieldBar (M * p)))
      simpa using inv_mem h
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) jb)
  haveI hfd_inv : FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))
      ↥(ModularCurve.x1FunctionFieldBar (M * p)) := hadj ▸ hfd

  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ :=
    ModularCurve.XOneP.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj jb hjb hmem

  obtain ⟨es, hesIso, hes_snd, hes_fin, hes_inf⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
      A (↥K) (j : ↥K) (AlgebraicClosure ℚ) jb eFin eInf
      (by
        refine (hFin (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j)).trans ?_
        rfl)
      (by
        refine (hInf (AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j)).trans ?_
        apply Subtype.ext
        show ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) (((j : ↥K)⁻¹ : ↥K) : LaurentSeries L) =
          (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((j : ↥K) : LaurentSeries L))⁻¹
        push_cast
        rw [map_inv₀])
      (by
        intro b b' n hb
        refine Eq.trans (hFin b) ?_
        refine Eq.trans ?_ (congrArg (· * jb ^ n) (hInf b')).symm
        apply Subtype.ext
        show ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b' : ↥K) : LaurentSeries L) *
            (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((j : ↥K) : LaurentSeries L)) ^ n
        rw [hb]; push_cast; rw [map_mul, map_pow])

  obtain ⟨e, he_base, he_fin, he_inf⟩ :=
    ModularCurve.TwoChart.exists_iso_twoChartIntegralModel_hom_comp_toBase_eq_modelTo A (↥K) (j : ↥K)
  have he_inv_base : e.inv ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j := by
    rw [← he_base, Iso.inv_hom_id_assoc]
  let κ : pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ⟶
      pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) :=
    pullback.map _ _ _ _ e.inv (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he_inv_base]) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsIso κ := inferInstance
  let Mη : CurveModel (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans
  haveI : IsIso es := hesIso
  have hκ_fst : κ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ≫ e.inv :=
    pullback.lift_fst _ _ _
  have hκ_snd : κ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      pullback.snd (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  let eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) :=
    (es ≫ κ : CurveModel.glued (AlgebraicClosure ℚ) jb ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
  have heη_def : eη = (es ≫ κ : CurveModel.glued (AlgebraicClosure ℚ) jb ⟶ _) := rfl
  haveI hiso : IsIso eη := by change IsIso (es ≫ κ); infer_instance
  have heη_fst : eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      es ≫ pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ≫ e.inv := by
    show (es ≫ κ) ≫ _ = _
    rw [Category.assoc, hκ_fst]
  have heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase := by
    show (es ≫ κ) ≫ _ = CurveModel.gluedToBase (AlgebraicClosure ℚ) jb
    rw [Category.assoc, hκ_snd, Category.comp_id]
    exact hes_snd

  have he_inv_fin : AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j ≫ e.inv = ModularCurve.TwoChart.ιFin A (↥K) j :=
    (Iso.comp_inv_eq e).mpr he_fin.symm
  let θr : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))) :=
    eFin.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := AlgebraicClosure ℚ) (B := ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).toRingHom
  have hθr : ∀ a, ((θr a : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) : ↥(ModularCurve.x1FunctionFieldBar (M * p))) =
      ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L), hmem a⟩ :=
    fun a => hFin a
  let θ : CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⟶ CommRingCat.of ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))) :=
    CommRingCat.ofHom θr
  have hfac : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) = Spec.map θ ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
    calc AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
        = AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ es ≫
            pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ≫ e.inv := by
          show AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ (es ≫ κ) ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = _
          rw [Category.assoc, hκ_fst]
      _ = (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ es ≫
            pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ))))) ≫ e.inv := by
          simp only [Category.assoc]
      _ = Spec.map θ ≫ ModularCurve.TwoChart.ιFin A (↥K) j := by
          rw [hes_fin, Category.assoc, he_inv_fin]
          rfl
  have hUne : ∀ ξ : ↥(AlgebraicCurve.CurveModel.X₀ (AlgebraicClosure ℚ) jb),
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb).base ξ ∈ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) := by
    intro ξ
    have e := congrArg (fun g => g.base ξ) hfac
    exact ⟨(Spec.map θ).base ξ, trivial, e.symm⟩
  have hne : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))) :=
    ⟨⟨(AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb).base (Classical.arbitrary _), hUne _⟩⟩
  refine ⟨Mη, eη, inferInstance, hne, heη, ?_, ?_⟩

  · intro a
    have key := B1PrimeExport.ofGenerator_ffEquiv_symm_germToFunctionField (AlgebraicClosure ℚ) jb htrans (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) (ModularCurve.TwoChart.ιFin A (↥K) j) θ hfac a
    refine (congrArg (fun y : ↥(ModularCurve.x1FunctionFieldBar (M * p)) => (y : LaurentSeries (AlgebraicClosure ℚ))) key).trans ?_
    simp only [θ, CommRingCat.hom_ofHom, hθr]

  ·
    have he_inv_inf : AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j ≫ e.inv = ModularCurve.TwoChart.ιInf A (↥K) j :=
      (Iso.comp_inv_eq e).mpr he_inf.symm
    let θrI : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))) :=
      eInf.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A) (A := AlgebraicClosure ℚ) (B := ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j))).toRingHom
    have hθrI : ∀ a, ((θrI a : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) : ↥(ModularCurve.x1FunctionFieldBar (M * p))) =
        ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((a : ↥K) : LaurentSeries L), hmem a⟩ :=
      fun a => hInf a
    have hfacI : AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) = Spec.map (CommRingCat.ofHom θrI) ≫ ModularCurve.TwoChart.ιInf A (↥K) j := by
      calc AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
          = AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ es ≫
              pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) ≫ e.inv := by
            show AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ (es ≫ κ) ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = _
            rw [Category.assoc, hκ_fst]
        _ = (AlgebraicCurve.CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫ es ≫
              pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ))))) ≫ e.inv := by
            simp only [Category.assoc]
        _ = Spec.map (CommRingCat.ofHom θrI) ≫ ModularCurve.TwoChart.ιInf A (↥K) j := by
            rw [hes_inf, Category.assoc, he_inv_inf]
            rfl

    have hAfin : Algebra.adjoin (AlgebraicClosure ℚ) (Set.range θr) = ⊤ := X1Meta.adjoin_range_comp_includeRight_eq_top eFin
    have hAinf : Algebra.adjoin (AlgebraicClosure ℚ) (Set.range θrI) = ⊤ := X1Meta.adjoin_range_comp_includeRight_eq_top eInf

    have hρ : θrI (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = AlgebraicCurve.CurveModel.tInvChart (AlgebraicClosure ℚ) jb := by
      apply Subtype.ext
      refine (hθrI _).trans ?_
      apply Subtype.ext
      show ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) (((j : ↥K)⁻¹ : ↥K) : LaurentSeries L) =
        (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((j : ↥K) : LaurentSeries L))⁻¹
      push_cast
      rw [map_inv₀]
    have hP3 : ∀ y : Mη.C, (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) y ∈ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j) ↔ y ∈ Set.range (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb) :=
      fun y => X1Meta.mem_range_ιFin_iff A (↥K) j (AlgebraicClosure ℚ) jb (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) θr θrI hfac hfacI hρ y
    intro g hg x x' hxx'
    have hσL : (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)).comp (algebraMap L (AlgebraicClosure ℚ)) = algebraMap L (AlgebraicClosure ℚ) := RingHom.ext hg
    have hfixK : ∀ b : ↥K, ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) g
        ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L), hmem b⟩ =
        ⟨ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L), hmem b⟩ := by
      intro b
      apply Subtype.ext
      show ModularCurve.coeffMap (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) (ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L)) = _
      rw [ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hσL]
    have hgt : ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) g jb = jb := hfixK j
    have hfixFin : ∀ b, ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) g
        (θr b : ↥(ModularCurve.x1FunctionFieldBar (M * p))) = θr b := fun b => by rw [hθr]; exact hfixK b
    have hfixInf : ∀ b, ModularCurve.arithmeticRingAut (ModularCurve.x1FunctionField (M * p)) g
        (θrI b : ↥(ModularCurve.x1FunctionFieldBar (M * p))) = θrI b := fun b => by rw [hθrI]; exact hfixK b
    have hconv : x'.1 ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) = Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) := by
      simpa only [Category.assoc] using hxx'
    exact TwoChartGlueGal.GX.hgal (ModularCurve.x1FunctionField (M * p)) jb htrans (eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)))
      (ModularCurve.TwoChart.ιFin A (↥K) j) θr hfac (ModularCurve.TwoChart.ιInf A (↥K) j) θrI hfacI
      g hgt hfixFin hfixInf hAfin hAinf hP3 x x' hconv

end
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.C P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul.TwoChartGlueGal.P"

end S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_curveModel_x1FunctionFieldBar_iso_pullback_chartPin_galoisCompat_twoChartModel_x1_mul (solution)
