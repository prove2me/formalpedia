-- Prove2me | solution 1 for ModularCurve.XOneP.pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5bc26db6-940b-52c3-8749-948e508bbb26

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve
open scoped TensorProduct Pointwise

universe u

namespace DiamPlacesTools

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

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

theorem e3_genericPoint_specializes :
    θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

noncomputable def e3_ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (e3_genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
theorem e3_SpecMap_ffMap_fromSpecStalk :
    Spec.map (e3_ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [e3_ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem e3_germ_ffMap (U : Y.Opens) (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ e3_ffMap θ =
      θ.app U ≫ X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) := by
  rw [e3_ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

theorem e3_ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    e3_ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, e3_germ_ffMap]; rfl

theorem e3_ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    e3_ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [e3_ffMap_germ_apply]
  rfl

end FFMap

section Misc

theorem spec_map_comp_eq_id {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) (b : B →+* A)
    (hab : ∀ x, a (b x) = x) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show a.comp b = RingHom.id B from RingHom.ext hab, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem isIso_spec_map_equiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
  ⟨⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom),
    spec_map_comp_eq_id _ _ (fun x => e.apply_symm_apply x),
    spec_map_comp_eq_id _ _ (fun x => e.symm_apply_apply x)⟩⟩

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

end Misc

end DiamPlacesTools

namespace DiamPlacesTools

open ModularCurve in

theorem coe_baseChangeAut_coeffMap (L : Type) [Field L] [CharZero L] [Algebra L (AlgebraicClosure ℚ)]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (σ₀ : ↥F₀ ≃ₐ[ℚ] ↥F₀)
    (z : ↥(laurentBaseChange L F₀))
    (hz' : coeffMap (algebraMap L (AlgebraicClosure ℚ)) (z : LaurentSeries L) ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    ((baseChangeAut (AlgebraicClosure ℚ) σ₀ ⟨coeffMap (algebraMap L (AlgebraicClosure ℚ)) (z : LaurentSeries L), hz'⟩ :
        ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((baseChangeAut L σ₀ z : ↥(laurentBaseChange L F₀)) : LaurentSeries L) := by
  classical
  let φ : L →+* (AlgebraicClosure ℚ) := algebraMap L (AlgebraicClosure ℚ)
  have hQ : IsBaseChangeAutOf (AlgebraicClosure ℚ) σ₀ (baseChangeAut (AlgebraicClosure ℚ) σ₀) :=
    isBaseChangeAutOf_baseChangeAut (exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) F₀ (σ₀ : ↥F₀ ≃+* ↥F₀))
  have hL : IsBaseChangeAutOf L σ₀ (baseChangeAut L σ₀) :=
    isBaseChangeAutOf_baseChangeAut (exists_algEquiv_laurentBaseChange_cover L F₀ (σ₀ : ↥F₀ ≃+* ↥F₀))
  have hcomp : φ.comp (algebraMap ℚ L) = algebraMap ℚ (AlgebraicClosure ℚ) := Subsingleton.elim _ _
  have hmem : ∀ w : ↥(laurentBaseChange L F₀), coeffMap φ (w : LaurentSeries L) ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀ := by
    intro w
    have hx := w.2
    rw [mem_laurentBaseChange_iff] at hx
    generalize (w : LaurentSeries L) = x at hx ⊢
    induction hx using Subfield.closure_induction with
    | mem y hy =>
        rcases hy with ⟨a, rfl⟩ | ⟨t, ht, rfl⟩
        · rw [algebraMap_laurentSeries_eq_single, coeffMap_single, ← algebraMap_laurentSeries_eq_single]
          exact (laurentBaseChange (AlgebraicClosure ℚ) F₀).algebraMap_mem _
        · rw [coeffEmb, coeffMap_coeffMap, coeffMap_congr hcomp]
          exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ht
    | one => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | neg x _ hx => simpa using neg_mem hx
    | inv x _ hx => simpa using inv_mem hx
    | mul x y _ _ hx hy => simpa using mul_mem hx hy

  let Φ : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
    ((coeffMap φ).comp (algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L))).codRestrict (laurentBaseChange (AlgebraicClosure ℚ) F₀) hmem
  have hΦ : ∀ w, ((Φ w : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap φ (w : LaurentSeries L) := fun _ => rfl

  let f₁ : ↥(laurentBaseChange L F₀) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (LaurentSeries (AlgebraicClosure ℚ))).comp ((baseChangeAut (AlgebraicClosure ℚ) σ₀ : _ ≃ₐ[(AlgebraicClosure ℚ)] _).toRingEquiv.toRingHom.comp Φ)
  let f₂ : ↥(laurentBaseChange L F₀) →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (coeffMap φ).comp ((algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L)).comp (baseChangeAut L σ₀ : _ ≃ₐ[L] _).toRingEquiv.toRingHom)

  let S : Set (LaurentSeries L) := Set.range (algebraMap L (LaurentSeries L)) ∪ (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))
  let S' : Set ↥(laurentBaseChange L F₀) := Subtype.val ⁻¹' S
  have hS'S : Subtype.val '' S' = S := by
    refine Set.image_preimage_eq_of_subset (fun x hx => ?_)
    exact ⟨⟨x, Subfield.subset_closure hx⟩, rfl⟩
  have hgen : Subfield.closure S' = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    have hw : (w : LaurentSeries L) ∈ (Subfield.closure S').map (algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L)) := by
      rw [RingHom.map_field_closure]
      show (w : LaurentSeries L) ∈ Subfield.closure ((fun v : ↥(laurentBaseChange L F₀) => (v : LaurentSeries L)) '' S')
      rw [hS'S]
      exact w.2
    obtain ⟨w', hw', hww'⟩ := hw
    obtain rfl : w' = w := Subtype.ext hww'
    exact hw'
  have hf : f₁ = f₂ := by
    apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
    intro w hw
    rcases hw with ⟨a, ha⟩ | ⟨t, ht, htw⟩
    ·
      have hw1 : w = algebraMap L _ a := Subtype.ext ha.symm
      subst hw1
      have hΦa : Φ (algebraMap L _ a) = algebraMap (AlgebraicClosure ℚ) _ (φ a) := by
        apply Subtype.ext
        rw [hΦ]
        show coeffMap φ (algebraMap L (LaurentSeries L) a) = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (φ a)
        rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]
      show ((baseChangeAut (AlgebraicClosure ℚ) σ₀ (Φ (algebraMap L _ a)) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap φ ((baseChangeAut L σ₀ (algebraMap L _ a) : ↥(laurentBaseChange L F₀)) : LaurentSeries L)
      rw [hΦa, AlgEquiv.commutes, AlgEquiv.commutes]
      show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (φ a) = coeffMap φ (algebraMap L (LaurentSeries L) a)
      symm
      rw [algebraMap_laurentSeries_eq_single, coeffMap_single, algebraMap_laurentSeries_eq_single]
    ·
      have hw1 : w = ⟨coeffEmb L t, coeffEmb_mem_laurentBaseChange L ht⟩ := Subtype.ext htw.symm
      subst hw1
      have hΦt : Φ ⟨coeffEmb L t, coeffEmb_mem_laurentBaseChange L ht⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) t, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) ht⟩ := by
        apply Subtype.ext
        rw [hΦ]
        show coeffMap φ (coeffEmb L t) = coeffEmb (AlgebraicClosure ℚ) t
        rw [coeffEmb, coeffMap_coeffMap, coeffMap_congr hcomp]; rfl
      show ((baseChangeAut (AlgebraicClosure ℚ) σ₀ (Φ ⟨coeffEmb L t, _⟩) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap φ ((baseChangeAut L σ₀ ⟨coeffEmb L t, _⟩ : ↥(laurentBaseChange L F₀)) : LaurentSeries L)
      rw [hΦt, hQ ⟨t, ht⟩, hL ⟨t, ht⟩, coeffEmb, coeffEmb, coeffMap_coeffMap, coeffMap_congr hcomp]
  have key := RingHom.congr_fun hf z
  have hzΦ : Φ z = ⟨coeffMap φ (z : LaurentSeries L), hz'⟩ := Subtype.ext (hΦ z)
  change ((baseChangeAut (AlgebraicClosure ℚ) σ₀ (Φ z) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffMap φ ((baseChangeAut L σ₀ z : ↥(laurentBaseChange L F₀)) : LaurentSeries L) at key
  rw [hzΦ] at key
  exact key

end DiamPlacesTools

open DiamPlacesTools

set_option maxHeartbeats 12800000 in
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
    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

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

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (w : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j) [IsIso w]
    (hw : w ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), ((ρ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = θ b)
    (hwρ : ModularCurve.TwoChart.ιFin A (↥K) j ≫ w = Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
    (h : x'.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ w) :
    Mη.pointEquivPlace x' =
      (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d))⁻¹ • Mη.pointEquivPlace x := by
  classical

  let Qb := AlgebraicClosure ℚ
  let F₀ : IntermediateField ℚ (LaurentSeries ℚ) := (ModularCurve.x1FunctionField (M * p))
  let β : Spec (CommRingCat.of Qb) ⟶ Spec (CommRingCat.of A) := specMap A Qb
  let g₂ : Mη.C ⟶ ModularCurve.TwoChartModel A (↥K) j := eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))
  have e₁ : ModularCurve.TwoChart.modelTo A (↥K) j ≫ 𝟙 _ = w ≫ ModularCurve.TwoChart.modelTo A (↥K) j := (Category.comp_id _).trans hw.symm
  have e₂ : β ≫ 𝟙 _ = 𝟙 _ ≫ β := by rw [Category.comp_id, Category.id_comp]

  let W : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A Qb) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A Qb) :=
    pullback.map _ _ _ _ w (𝟙 _) (𝟙 _) e₁ e₂
  have hW_fst : W ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) ≫ w := pullback.lift_fst _ _ _
  have hW_snd : W ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  haveI : IsIso W := inferInstance
  let Wt : Mη.C ⟶ Mη.C := eη ≫ W ≫ inv eη
  haveI : IsIso Wt := by change IsIso (eη ≫ W ≫ inv eη); infer_instance
  have hWt_g₂ : Wt ≫ g₂ = g₂ ≫ w := by
    show (eη ≫ W ≫ inv eη) ≫ eη ≫ _ = (eη ≫ _) ≫ w
    simp only [Category.assoc, IsIso.inv_hom_id_assoc, hW_fst]
  have hinv_snd : inv eη ≫ Mη.toBase = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := by
    rw [← heη, IsIso.inv_hom_id_assoc]
  have hWt_base : Wt ≫ Mη.toBase = Mη.toBase := by
    show (eη ≫ W ≫ inv eη) ≫ Mη.toBase = Mη.toBase
    simp only [Category.assoc, hinv_snd, hW_snd]
    exact heη

  have hpt : x'.1 ≫ eη = x.1 ≫ eη ≫ W := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hW_fst]
      simpa only [Category.assoc] using h
    · simp only [Category.assoc, hW_snd]
      rw [heη, x'.2, x.2]
  have hx' : x'.1 = x.1 ≫ Wt := by
    rw [← cancel_mono eη]
    show x'.1 ≫ eη = (x.1 ≫ (eη ≫ W ≫ inv eη)) ≫ eη
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact hpt
  have hxx' : x'.1.base (IsLocalRing.closedPoint Qb) = Wt.base (x.1.base (IsLocalRing.closedPoint Qb)) := by
    rw [hx']; rfl

  have hmem : ∀ b : ↥K, ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.x1FunctionFieldBar (M * p) :=
    fun b => DiamPlacesTools.coeffMap_mem_laurentBaseChange L F₀ K hK b
  let jb : ↥(ModularCurve.x1FunctionFieldBar (M * p)) := ⟨ModularCurve.coeffMap (algebraMap L Qb) ((j : ↥K) : LaurentSeries L), hmem j⟩
  have hcompQ : (algebraMap L Qb).comp (algebraMap ℚ L) = algebraMap ℚ Qb := Subsingleton.elim _ _
  have hjb : (jb : LaurentSeries Qb) = ModularCurve.coeffEmb Qb ModularCurve.jq := by
    show ModularCurve.coeffMap (algebraMap L Qb) ((j : ↥K) : LaurentSeries L) = _
    rw [hj, ModularCurve.coeffEmb, ModularCurve.coeffMap_coeffMap, ModularCurve.coeffMap_congr hcompQ]
    rfl
  have hjq : (jb : LaurentSeries Qb) = ModularCurve.jqModC Qb := hjb.trans (ModularCurve.coeffEmb_jq Qb)
  obtain ⟨htrans, hfd⟩ :
      Transcendental Qb jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin Qb ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))) ↥(ModularCurve.x1FunctionFieldBar (M * p)) :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      Qb (CongruenceSubgroup.Gamma1 (M * p)) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]) jb hjq
  haveI hjb0 : Fact (jb ≠ 0) := ⟨fun h0 => htrans (by rw [h0]; exact isAlgebraic_zero)⟩
  haveI := hfd
  obtain ⟨⟨eFin, hFin⟩, -⟩ :=
    ModularCurve.XOneP.exists_algEquiv_tensor_chartAlgFin_chartRing_and_chartAlgInf_x1FunctionFieldBar_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj jb hjb hmem

  let δ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[Qb] ↥(ModularCurve.x1FunctionFieldBar (M * p)) := ModularCurve.diamondAutBar (M * p) d
  let αinv : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃+* ↥(ModularCurve.x1FunctionFieldBar (M * p)) := δ.toRingEquiv
  have hαinv : ∀ y, αinv y = δ y := fun _ => rfl
  have hgen : Subfield.closure (Set.range (algebraMap Qb ↥(ModularCurve.x1FunctionFieldBar (M * p))) ∪
      Set.range (fun b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) =>
        (⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p))))) = ⊤ := by
    set S : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)) := Set.range (algebraMap Qb ↥(ModularCurve.x1FunctionFieldBar (M * p))) ∪
      Set.range (fun b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) =>
        (⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩ : ↥(ModularCurve.x1FunctionFieldBar (M * p)))) with hS

    have hR : ∀ r : ↥(AlgebraicCurve.CurveModel.chartRing Qb ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p)))),
        (r : ↥(ModularCurve.x1FunctionFieldBar (M * p))) ∈ Subfield.closure S := by
      intro r
      obtain ⟨t, rfl⟩ := eFin.surjective r
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact (Subfield.closure S).zero_mem
      | tmul c b =>
          have htm : (c ⊗ₜ[A] b : Qb ⊗[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = c • ((1 : Qb) ⊗ₜ[A] b) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [htm, map_smul]
          change c • ((eFin ((1 : Qb) ⊗ₜ[A] b) : ↥(AlgebraicCurve.CurveModel.chartRing Qb ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) : ↥(ModularCurve.x1FunctionFieldBar (M * p))) ∈ Subfield.closure S
          rw [hFin b, Algebra.smul_def]
          exact (Subfield.closure S).mul_mem (Subfield.subset_closure (Or.inl ⟨c, rfl⟩))
            (Subfield.subset_closure (Or.inr ⟨b, rfl⟩))
      | add x y hx hy => rw [map_add]; exact (Subfield.closure S).add_mem hx hy
    rw [eq_top_iff]
    intro f _
    obtain ⟨a, b', -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(AlgebraicCurve.CurveModel.chartRing Qb ({jb} : Set ↥(ModularCurve.x1FunctionFieldBar (M * p))))) f
    exact (Subfield.closure S).div_mem (hR a) (hR b')
  have hconst : ∀ c : Qb, e3_ffMap Wt (Mη.ffEquiv (algebraMap Qb ↥(ModularCurve.x1FunctionFieldBar (M * p)) c)) = Mη.ffEquiv (αinv (algebraMap Qb ↥(ModularCurve.x1FunctionFieldBar (M * p)) c)) := by
    intro c
    rw [hαinv, AlgEquiv.commutes, Mη.ffEquiv_algebraMap]

    exact e3_ffMap_germ_of_eq Wt Mη.toBase Mη.toBase hWt_base.symm ⊤
      (show genericPoint Mη.C ∈ Mη.toBase ⁻¹ᵁ ⊤ from trivial) (show genericPoint Mη.C ∈ Mη.toBase ⁻¹ᵁ ⊤ from trivial)
      ((Scheme.ΓSpecIso (CommRingCat.of Qb)).inv c)
  have hchart : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      e3_ffMap Wt (Mη.ffEquiv ⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩) =
        Mη.ffEquiv (αinv ⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩) := by
    intro b

    let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
    let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun a =>
      ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)
    have hηV : genericPoint Mη.C ∈ g₂ ⁻¹ᵁ V := by
      obtain ⟨⟨y, hy⟩⟩ := Mη_chart_nonempty
      exact ((genericPoint_spec Mη.C).mem_open_set_iff (g₂ ⁻¹ᵁ V).2).mpr ⟨y, Set.mem_univ _, hy⟩

    have hpin : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        Mη.ffEquiv ⟨ModularCurve.coeffMap (algebraMap L Qb) ((a : ↥K) : LaurentSeries L), hmem a⟩ =
          Mη.C.presheaf.germ (g₂ ⁻¹ᵁ V) (genericPoint Mη.C) hηV (g₂.app V (sec a)) := by
      intro a
      rw [← Mη.ffEquiv.apply_symm_apply (Mη.C.presheaf.germ (g₂ ⁻¹ᵁ V) (genericPoint Mη.C) hηV (g₂.app V (sec a)))]
      congr 1
      apply Subtype.ext
      exact (hMηpin a).symm

    have hα : αinv ⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩ =
        ⟨ModularCurve.coeffMap (algebraMap L Qb) (((ρ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L), hmem _⟩ := by
      rw [hαinv]
      apply Subtype.ext
      have hbK : ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L F₀ := hK ▸ (b : ↥K).2
      have hc := DiamPlacesTools.coe_baseChangeAut_coeffMap L F₀ (ModularCurve.diamondAut (M * p) d) ⟨((b : ↥K) : LaurentSeries L), hbK⟩ (hmem b)
      show ((ModularCurve.diamondAutBar (M * p) d ⟨ModularCurve.coeffMap (algebraMap L Qb) ((b : ↥K) : LaurentSeries L), hmem b⟩ :
          ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries Qb) =
        ModularCurve.coeffMap (algebraMap L Qb) (((ρ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L)
      rw [hρ b, hθ (b : ↥K) ⟨((b : ↥K) : LaurentSeries L), hbK⟩ rfl]
      exact hc
    rw [hα, hpin, hpin]

    have hle : V ≤ w ⁻¹ᵁ V := by
      rintro v ⟨z, -, rfl⟩
      refine ⟨(Spec.map (CommRingCat.ofHom ρ.toRingHom)).base z, trivial, ?_⟩
      have := congrArg (fun f => f.base z) hwρ
      simpa using this.symm
    have key := e3_ffMap_germ_of_eq Wt g₂ (g₂ ≫ w) hWt_g₂.symm V hηV
      (show genericPoint Mη.C ∈ (g₂ ≫ w) ⁻¹ᵁ V from hle hηV) (sec b)
    rw [key]
    have hres : (ModularCurve.TwoChartModel A (↥K) j).presheaf.map (homOfLE hle).op (w.app V (sec b)) = sec (ρ b) := by
      apply ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).commRingCatIsoToRingEquiv.injective
      change ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom _ = ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom _
      rw [DiamPlacesTools.appIso_hom_res_app_appIso_inv_apply w (ModularCurve.TwoChart.ιFin A (↥K) j)
        (ModularCurve.TwoChart.ιFin A (↥K) j) (CommRingCat.ofHom ρ.toRingHom) hwρ b ⊤ hle]
      change _ = (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ≫ ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom) _
      rw [Iso.inv_hom_id]
      simp
    rw [Scheme.Hom.comp_app]
    change Mη.C.presheaf.germ ((g₂ ≫ w) ⁻¹ᵁ V) (genericPoint Mη.C) _ (g₂.app (w ⁻¹ᵁ V) (w.app V (sec b))) = _
    have hnat := CategoryTheory.ConcreteCategory.congr_hom (g₂.naturality (homOfLE hle).op) (w.app V (sec b))
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hres] at hnat
    rw [hnat]
    exact (TopCat.Presheaf.germ_res_apply Mη.C.presheaf _ (genericPoint Mη.C) hηV _).symm
  have hff : (e3_ffMap Wt).hom.comp Mη.ffEquiv.toRingHom = Mη.ffEquiv.toRingHom.comp αinv.toRingHom := by
    apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
    rintro f (⟨c, rfl⟩ | ⟨b, rfl⟩)
    · exact hconst c
    · exact hchart b
  have hffMap : e3_ffMap Wt = CommRingCat.ofHom
      (Mη.ffEquiv.toRingHom.comp (αinv.toRingHom.comp Mη.ffEquiv.symm.toRingHom)) := by
    ext v
    have := RingHom.congr_fun hff (Mη.ffEquiv.symm v)
    simpa using this

  let g : SemilinearAut Qb ↥(ModularCurve.x1FunctionFieldBar (M * p)) := (SemilinearAut.ofAlgAut δ)⁻¹
  have hg : (SemilinearAut.toRingAut g).symm = αinv := rfl
  have hθgen : Mη.C.fromSpecStalk (genericPoint Mη.C) ≫ Wt =
      Spec.map (CommRingCat.ofHom (Mη.ffEquiv.toRingHom.comp
        ((SemilinearAut.toRingAut g).symm.toRingHom.comp Mη.ffEquiv.symm.toRingHom))) ≫
        Mη.C.fromSpecStalk (genericPoint Mη.C) := by
    rw [hg, ← e3_SpecMap_ffMap_fromSpecStalk Wt, hffMap]

  exact AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
    Mη g Wt hθgen x x' hxx'

end

end S_ModularCurve_XOneP_pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_diamondAutBar_inv_smul_of_chartPin_of_diamondModelAut_twoChartModel_x1_mul (solution)
