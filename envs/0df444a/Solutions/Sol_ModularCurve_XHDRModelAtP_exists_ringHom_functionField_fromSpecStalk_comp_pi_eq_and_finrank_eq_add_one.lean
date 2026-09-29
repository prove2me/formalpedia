-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5b069734-23d7-5f82-8c51-4a75e1d735e5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_XHDRLevel_relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open Topology
open scoped TensorProduct

universe u

noncomputable section

namespace S2Sol

theorem AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply
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

  simp only [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

section FieldMap

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

theorem apply_genericPoint_eq (f : X ⟶ Y) [Flat f] : f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨a, ha, hfa⟩ := Flat.generalizingMap f (genericPoint_specializes (f.base (genericPoint X)))
  have hgen : IsGenericPoint a (Set.univ : Set X) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact ha.trans (genericPoint_specializes y)
  have : a = genericPoint X := hgen.eq (genericPoint_spec X)
  rw [← this]; exact hfa

noncomputable def fieldMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (f.stalkMap (genericPoint X)).hom.comp
    (Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y)).hom

theorem fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    CommRingCat.ofHom (fieldMap f h) =
      Y.presheaf.stalkSpecializes (specializes_of_eq h : f.base (genericPoint X) ⤳ genericPoint Y) ≫
        f.stalkMap (genericPoint X) := rfl

theorem algebraMap_stalkMap (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (p : X) (s : Y.presheaf.stalk (f.base p)) :
    algebraMap _ X.functionField (f.stalkMap p s) = fieldMap f h (algebraMap _ Y.functionField s) := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes p)).hom (f.stalkMap p s) =
    (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes (f.base p))).hom s))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) p (genericPoint_specializes p) s]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem fieldMap_germToFunctionField (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (U : Scheme.{u})] [hU' : Nonempty ((f ⁻¹ᵁ U : X.Opens) : Scheme.{u})]
    (s : Γ(Y, U)) :
    fieldMap f h (Y.germToFunctionField U s) = X.germToFunctionField (f ⁻¹ᵁ U) (f.app U s) := by
  have hη : f.base (genericPoint X) ∈ U := by
    rw [h]
    exact ((genericPoint_spec Y).mem_open_set_iff U.2).mpr
      ⟨(Classical.arbitrary (U : Scheme.{u})).1, Set.mem_univ _, (Classical.arbitrary (U : Scheme.{u})).2⟩
  change (f.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes _).hom
      ((Y.presheaf.germ U (genericPoint Y) _).hom s)) = (X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) _).hom (f.app U s)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem fieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) = genericPoint Y)
    (hg : g.base (genericPoint Y) = genericPoint Z) (hfg : (f ≫ g).base (genericPoint X) = genericPoint Z) :
    fieldMap (f ≫ g) hfg = (fieldMap f hf).comp (fieldMap g hg) := by
  apply RingHom.ext
  intro t

  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := Z.presheaf) (x := genericPoint Z) t
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨_, hU⟩⟩
  have hηY : g.base (genericPoint Y) ∈ U := by rw [hg]; exact hU
  haveI : Nonempty ((g ⁻¹ᵁ U : Y.Opens) : Scheme.{u}) := ⟨⟨_, hηY⟩⟩
  have hηX : (f ≫ g).base (genericPoint X) ∈ U := by rw [hfg]; exact hU
  haveI : Nonempty (((f ≫ g) ⁻¹ᵁ U : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX⟩⟩
  have hηX' : f.base (genericPoint X) ∈ g ⁻¹ᵁ U := by
    show (f ≫ g).base (genericPoint X) ∈ U; exact hηX
  haveI : Nonempty ((f ⁻¹ᵁ (g ⁻¹ᵁ U) : X.Opens) : Scheme.{u}) := ⟨⟨_, hηX'⟩⟩
  have e1 := fieldMap_germToFunctionField (f ≫ g) hfg U s
  have e2 := fieldMap_germToFunctionField g hg U s
  have e3 := fieldMap_germToFunctionField f hf (g ⁻¹ᵁ U) (g.app U s)
  change fieldMap (f ≫ g) hfg (Z.germToFunctionField U s) = fieldMap f hf (fieldMap g hg (Z.germToFunctionField U s))
  rw [e1, e2, e3]
  rfl

theorem fieldMap_eq_of_fromSpecStalk_comp_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (c : Y.functionField →+* X.functionField)
    (hc : X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y)) :
    fieldMap f h = c := by
  have key : Spec.map (CommRingCat.ofHom (fieldMap f h)) ≫ Y.fromSpecStalk (genericPoint Y) =
      Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [← hc, fieldMap_eq, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  have := (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp key
  have := Spec.map_injective this
  exact congrArg CommRingCat.Hom.hom this

end FieldMap

theorem base_genericPoint_eq_of_chart {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    {B : CommRingCat.{u}} (G : Spec B ⟶ Y) [IsOpenImmersion G]
    (hξ : f.base (genericPoint X) ∈ G ''ᵁ ⊤)
    (hinj : ∀ b : B, X.presheaf.germ (f ⁻¹ᵁ (G ''ᵁ ⊤)) (genericPoint X) hξ
        (f.app (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b))) = 0 → b = 0) :
    f.base (genericPoint X) = genericPoint Y := by
  obtain ⟨𝔮, -, h𝔮⟩ := id hξ

  have hbot : ∀ b ∈ 𝔮.asIdeal, b = 0 := by
    intro b hb
    apply hinj

    set s : Γ(Y, G ''ᵁ ⊤) := (G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv b) with hs

    have h1 : 𝔮 ∉ G ⁻¹ᵁ Y.basicOpen s := by
      rw [Scheme.preimage_basicOpen, hs, Scheme.Hom.appIso_inv_app_apply, Scheme.basicOpen_res_eq,
        basicOpen_eq_of_affine]
      exact fun h => (PrimeSpectrum.mem_basicOpen _ _ ).mp h hb

    have h2 : genericPoint X ∉ X.basicOpen (f.app (G ''ᵁ ⊤) s) := by
      rw [← Scheme.preimage_basicOpen]
      show f.base (genericPoint X) ∉ Y.basicOpen s
      rw [← h𝔮]; exact h1
    rw [Scheme.mem_basicOpen X _ (genericPoint X) hξ] at h2
    exact not_ne_iff.mp fun hne => h2 (isUnit_iff_ne_zero.mpr hne)

  haveI : Nonempty (Spec B) := ⟨𝔮⟩
  haveI : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion G
  haveI : IsDomain B := MulEquiv.isDomain Γ(Spec B, ⊤) (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have h𝔮bot : 𝔮 = genericPoint (Spec B) := by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext (le_bot_iff.mp fun b hb => ?_)
    rw [hbot b hb]
    exact Ideal.zero_mem _
  rw [← h𝔮, h𝔮bot]
  exact genericPoint_eq_of_isOpenImmersion G

section ChartExt

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem germToFunctionField_appIso_inv_chart {A B : CommRingCat.{u}} (ι : Spec A ⟶ Z) [IsOpenImmersion ι]
    (G : Spec B ⟶ Y) [IsOpenImmersion G] (π : Y ⟶ Z) (θ : A ⟶ B) (hfac : G ≫ π = Spec.map θ ≫ ι)
    (hWle : G ''ᵁ ⊤ ≤ π ⁻¹ᵁ (ι ''ᵁ ⊤))
    [Nonempty ((G ''ᵁ ⊤ : Y.Opens) : Scheme.{u})] [Nonempty ((π ⁻¹ᵁ (ι ''ᵁ ⊤) : Y.Opens) : Scheme.{u})] (a : A) :
    Y.germToFunctionField (G ''ᵁ ⊤) ((G.appIso ⊤).inv ((Scheme.ΓSpecIso B).inv (θ a))) =
      Y.germToFunctionField (π ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((π.app (ι ''ᵁ ⊤)).hom (((ι.appIso ⊤).inv) ((Scheme.ΓSpecIso A).inv a))) := by
  have hA := AlgebraicGeometry.Scheme.appIso_hom_res_app_appIso_inv_apply π ι G θ hfac a ⊤ hWle
  have htop : (homOfLE le_top : (⊤ : (Spec B).Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
  rw [htop, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at hA
  have hA' := congrArg (G.appIso ⊤).inv hA
  rw [Iso.hom_inv_id_apply] at hA'
  rw [← hA']
  exact TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hWle) _ _ _

theorem fromSpecStalk_comp_eq_of_fieldMap_eq (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (c : Y.functionField →+* X.functionField) (hc : fieldMap f h = c) :
    X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (CommRingCat.ofHom c) ≫ Y.fromSpecStalk (genericPoint Y) := by
  subst hc
  rw [fieldMap_eq, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end ChartExt

section Chart

open AlgebraicCurve.TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

abbrev sec (a : ↥(chartAlgFin R F j)) : Γ(TwoChartIntegralModel R F j, (ιFin R F j) ''ᵁ ⊤) :=
  ((ιFin R F j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv a)

scoped instance nonempty_chartFin : Nonempty (Scheme.Opens.toScheme ((ιFin R F j) ''ᵁ (⊤ : (Spec (CommRingCat.of ↥(chartAlgFin R F j))).Opens))) := by
  haveI : Nonempty (Spec (CommRingCat.of ↥(chartAlgFin R F j))) := inferInstance
  obtain ⟨z⟩ := this
  exact ⟨⟨(ιFin R F j).base z, ⟨z, trivial, rfl⟩⟩⟩

set_option maxHeartbeats 3200000 in

theorem exists_ringEquiv_functionField
    (hfrac : IsFractionRing ↥(chartAlgFin R F j) F)
    [IsIntegral (TwoChartIntegralModel R F j)] :
    ∃ e : F ≃+* (TwoChartIntegralModel R F j).functionField,
      ∀ a : ↥(chartAlgFin R F j),
        e (a : F) = (TwoChartIntegralModel R F j).germToFunctionField ((ιFin R F j) ''ᵁ ⊤) (sec R F j a) := by
  classical
  let X := TwoChartIntegralModel R F j
  let A := ↥(chartAlgFin R F j)
  let U : X.Opens := (ιFin R F j) ''ᵁ ⊤

  let τ : A ≃+* Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫ ((ιFin R F j).appIso ⊤).symm).commRingCatIsoToRingEquiv
  have hτ : ∀ a : A, τ a = sec R F j a := fun a => rfl

  have hU : IsAffineOpen U := by
    have : U = (ιFin R F j).opensRange := Scheme.Hom.image_top_eq_opensRange _
    rw [this]; exact isAffineOpen_opensRange _
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : IsFractionRing A F := hfrac

  have H : (nonZeroDivisors A).map τ.toMonoidHom = nonZeroDivisors Γ(X, U) := by
    ext x
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      change τ a ∈ nonZeroDivisors _
      rw [mem_nonZeroDivisors_iff_ne_zero] at ha ⊢
      exact fun h => ha (τ.injective (h.trans (map_zero τ).symm))
    · intro hx
      refine ⟨τ.symm x, ?_, ?_⟩
      · rw [mem_nonZeroDivisors_iff_ne_zero] at hx ⊢
        intro h
        apply hx
        rw [← τ.apply_symm_apply x, h, map_zero]
      · change τ (τ.symm x) = x
        exact τ.apply_symm_apply x
  refine ⟨IsLocalization.ringEquivOfRingEquiv F X.functionField τ H, fun a => ?_⟩
  have := IsLocalization.ringEquivOfRingEquiv_eq (M := nonZeroDivisors A) (T := nonZeroDivisors Γ(X, U)) (S := F) (Q := X.functionField) H a
  rw [show (algebraMap A F) a = (a : F) from rfl] at this
  rw [this, hτ]
  rfl

end Chart

theorem fieldRange_val_comp_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (hAB : A ≤ B) :
    (B.val.comp (IntermediateField.inclusion hAB)).fieldRange = A := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem finiteDimensional_adjoin_congr_inst {F : Type*} [Field F] {i₁ i₂ : Algebra ℚ F} (j : F)
    (h : letI := i₁; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F) :
    letI := i₂; FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set F)) F := by
  have : i₁ = i₂ := Subsingleton.elim _ _
  subst this
  exact h

def inclRingHom {K E : Type*} [Field K] [Field E] [Algebra K E] {A B : IntermediateField K E} (h : A ≤ B) : ↥A →+* ↥B :=
  { toFun := fun x => ⟨x.1, h x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

@[scoped simp] theorem coe_inclRingHom_apply {K E : Type*} [Field K] [Field E] [Algebra K E] {A B : IntermediateField K E} (h : A ≤ B) (x : ↥A) :
    ((inclRingHom h x : ↥B) : E) = (x : E) := rfl

theorem finrankAlong_inclusion {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (hAB : A ≤ B) :
    finrankAlong K (IntermediateField.inclusion hAB) = IntermediateField.relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange, fieldRange_val_comp_inclusion]

theorem finrank_inclRingHom {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (hAB : A ≤ B) :
    (letI := (inclRingHom hAB).toAlgebra; Module.finrank ↥A ↥B) = IntermediateField.relfinrank A B := by
  rw [← finrankAlong_inclusion hAB]
  rfl

end S2Sol
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one.S2Sol"

end
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one.S2Sol"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel S2Sol

open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsIntegral (X p (ΓM M H) hj)] [IsIntegral (X p (ΓN p M H hpM) hj)] :
    ∃ φ : (X p (ΓN p M H hpM) hj).functionField →+* (X p (ΓM M H) hj).functionField,
      (X p (ΓM M H) hj).fromSpecStalk (genericPoint (X p (ΓM M H) hj)) ≫ 𝔛.π.1 =
        Spec.map (CommRingCat.ofHom φ) ≫ (X p (ΓN p M H hpM) hj).fromSpecStalk (genericPoint (X p (ΓN p M H hpM) hj)) ∧
      φ.Finite ∧
      (letI := φ.toAlgebra; Module.finrank (X p (ΓN p M H hpM) hj).functionField (X p (ΓM M H) hj).functionField) = p + 1 := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : IsDomain (R p) := inferInstance

  let FM := ↥(qExpFunctionFieldC ℚ (ΓM M H))
  let FN := ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
  let XM := X p (ΓM M H) hj
  let XN := X p (ΓN p M H hpM) hj

  have hTM : ModularGroup.T ∈ ΓM M H := by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]
  have hTN : ModularGroup.T ∈ ΓN p M H hpM := by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]
  have hfdM0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓM M H) hTM
      (ΓM M H) le_rfl (fun γ h => Or.inl h) (jAt (ΓM M H) hj) (coe_jAt _ hj)).1
  have hfdN0 := (ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index ℚ (ΓN p M H hpM) hTN
      (ΓN p M H hpM) le_rfl (fun γ h => Or.inl h) (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)).1
  have hfracM : IsFractionRing ↥(chartAlgFin p (ΓM M H) hj) FM := by
    haveI : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (ΓM M H) hj} : Set FM)) FM :=
      S2Sol.finiteDimensional_adjoin_congr_inst _ hfdM0
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jAt (ΓM M H) hj} : Set FM)) FM := Algebra.IsAlgebraic.of_finite _ _
    exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (R p) ℚ FM ({jAt (ΓM M H) hj} : Set FM)
  have hfracN : IsFractionRing ↥(chartAlgFin p (ΓN p M H hpM) hj) FN := by
    haveI : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({jAt (ΓN p M H hpM) hj} : Set FN)) FN :=
      S2Sol.finiteDimensional_adjoin_congr_inst _ hfdN0
    haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({jAt (ΓN p M H hpM) hj} : Set FN)) FN := Algebra.IsAlgebraic.of_finite _ _
    exact AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg (R p) ℚ FN ({jAt (ΓN p M H hpM) hj} : Set FN)

  obtain ⟨eM, heM⟩ := S2Sol.exists_ringEquiv_functionField (R p) FM (jAt (ΓM M H) hj) hfracM
  obtain ⟨eN, heN⟩ := S2Sol.exists_ringEquiv_functionField (R p) FN (jAt (ΓN p M H hpM) hj) hfracN

  have hWle : (ιFin p (ΓM M H) hj) ''ᵁ ⊤ ≤ 𝔛.π.1 ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤) := by
    rintro _ ⟨z, -, rfl⟩
    show (ιFin p (ΓM M H) hj ≫ 𝔛.π.1).base z ∈ (ιFin p (ΓN p M H hpM) hj) ''ᵁ (⊤ : (Spec _).Opens)
    rw [𝔛.pi_chart]
    exact ⟨(Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)).base z, trivial,
      (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom 𝔛.iota0.toRingHom)) (ιFin p (ΓN p M H hpM) hj) z).symm⟩
  haveI : Nonempty (Scheme.Opens.toScheme (𝔛.π.1 ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ (⊤ : (Spec _).Opens)))) := by
    obtain ⟨⟨x, hx⟩⟩ := S2Sol.nonempty_chartFin (R p) FM (jAt (ΓM M H) hj)
    exact ⟨⟨x, hWle hx⟩⟩

  have hread : ∀ a : ↥(chartAlgFin p (ΓN p M H hpM) hj),
      XM.germToFunctionField (𝔛.π.1 ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          ((𝔛.π.1.app ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (S2Sol.sec (R p) FN (jAt (ΓN p M H hpM) hj) a)) =
        eM ((𝔛.iota0 a : ↥(chartAlgFin p (ΓM M H) hj)) : FM) := by
    intro a
    rw [heM]
    exact (S2Sol.germToFunctionField_appIso_inv_chart (ιFin p (ΓN p M H hpM) hj) (ιFin p (ΓM M H) hj) 𝔛.π.1
      (CommRingCat.ofHom 𝔛.iota0.toRingHom) 𝔛.pi_chart hWle a).symm

  have hξ : 𝔛.π.1.base (genericPoint XM) = genericPoint XN := by
    refine S2Sol.base_genericPoint_eq_of_chart 𝔛.π.1 (ιFin p (ΓN p M H hpM) hj) ?_ ?_
    · apply hWle
      exact ((genericPoint_spec XM).mem_open_set_iff ((ιFin p (ΓM M H) hj) ''ᵁ ⊤).2).mpr
        ⟨(Classical.arbitrary (Scheme.Opens.toScheme ((ιFin p (ΓM M H) hj) ''ᵁ (⊤ : (Spec _).Opens)))).1, Set.mem_univ _,
          (Classical.arbitrary (Scheme.Opens.toScheme ((ιFin p (ΓM M H) hj) ''ᵁ (⊤ : (Spec _).Opens)))).2⟩
    · intro b hb
      have h := hread b
      have hgerm : XM.germToFunctionField (𝔛.π.1 ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          ((𝔛.π.1.app ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (S2Sol.sec (R p) FN (jAt (ΓN p M H hpM) hj) b)) = 0 := hb
      rw [hgerm] at h
      have h0 : ((𝔛.iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : FM) = 0 := eM.injective (by rw [← h, map_zero])
      have h1 : ((b : FN) : LaurentSeries ℚ) = 0 := by
        rw [← 𝔛.iota0_spec b, show ((𝔛.iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : FM) = 0 from h0]; rfl
      exact Subtype.ext (Subtype.ext h1)

  let φ : XN.functionField →+* XM.functionField := S2Sol.fieldMap 𝔛.π.1 hξ

  have hle : qExpFunctionFieldC ℚ (ΓN p M H hpM) ≤ qExpFunctionFieldC ℚ (ΓM M H) :=
    qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM)

  let incl : FN →+* FM := S2Sol.inclRingHom hle

  have hcompat : φ.comp eN.toRingHom = eM.toRingHom.comp incl := by
    haveI : IsFractionRing ↥(chartAlgFin p (ΓN p M H hpM) hj) FN := hfracN
    apply IsLocalization.ringHom_ext (nonZeroDivisors ↥(chartAlgFin p (ΓN p M H hpM) hj))
    ext a
    show φ (eN ((a : FN))) = eM (incl (a : FN))
    rw [heN]
    show S2Sol.fieldMap 𝔛.π.1 hξ _ = _
    rw [S2Sol.fieldMap_germToFunctionField 𝔛.π.1 hξ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤), hread a]
    congr 1
    apply Subtype.ext
    rw [𝔛.iota0_spec a]
    exact (S2Sol.coe_inclRingHom_apply hle _).symm

  have hrank : (letI := incl.toAlgebra; Module.finrank FN FM) = p + 1 := by
    have h := S2Sol.finrank_inclRingHom hle
    rw [ModularCurve.XHDRLevel.relfinrank_qExpFunctionFieldC_gammaH_infSubgroup_gammaH_eq_add_one p M H hpM hpM2 hHp] at h
    exact h
  have hfr : (letI := φ.toAlgebra; Module.finrank XN.functionField XM.functionField) = p + 1 := by
    rw [← hrank]
    letI := incl.toAlgebra
    letI := φ.toAlgebra
    symm
    exact Algebra.finrank_eq_of_equiv_equiv eN eM hcompat
  refine ⟨φ, S2Sol.fromSpecStalk_comp_eq_of_fieldMap_eq 𝔛.π.1 hξ φ rfl, ?_, hfr⟩

  letI := φ.toAlgebra
  have : Module.Finite XN.functionField XM.functionField :=
    Module.finite_of_finrank_pos (by rw [show Module.finrank _ _ = p + 1 from hfr]; omega)
  exact this

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_ringHom_functionField_fromSpecStalk_comp_pi_eq_and_finrank_eq_add_one (solution)
