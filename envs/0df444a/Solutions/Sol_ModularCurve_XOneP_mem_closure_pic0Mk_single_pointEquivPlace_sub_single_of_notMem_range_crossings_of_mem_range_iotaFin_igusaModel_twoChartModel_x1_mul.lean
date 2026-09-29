-- Prove2me | solution 1 for ModularCurve.XOneP.mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0540c81d-c68d-531d-9d79-37c6c94bd36c

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
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
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_X1HeckeModule

import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace GenChartTools

theorem pic0Mk_congr {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
    {d d' : AlgebraicCurve.Divisor K F} (e : d = d')
    (h : d ∈ AlgebraicCurve.Divisor.degZero (K := K) (F := F)) (h' : d' ∈ AlgebraicCurve.Divisor.degZero (K := K) (F := F)) :
    AlgebraicCurve.Pic0.mk ⟨d, h⟩ = AlgebraicCurve.Pic0.mk ⟨d', h'⟩ := by
  subst e; rfl

theorem pointEquivPlace_symm_base {K : Type*} [Field K] [IsAlgClosed K] {L : Type*} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (V : AlgebraicCurve.Place K L) :
    (M.pointEquivPlace.symm V).1.base (IsLocalRing.closedPoint K) = (M.placeEquiv.symm V).1 := by
  change (((pointEquivClosedPoint M.toBase).symm (M.placeEquiv.symm V)).1).base (IsLocalRing.closedPoint K) = _
  rw [pointEquivClosedPoint_symm_apply_coe]
  exact pointOfClosedPoint_apply M.toBase _ _ _

theorem essFiniteType_of_curveModel {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) : Algebra.EssFiniteType K L := by
  letI := M.functionFieldAlgebra
  haveI : Algebra.EssFiniteType K M.C.functionField := AlgebraicCurve.essFiniteType_functionField M.toBase
  exact (Algebra.EssFiniteType.iff_of_algEquiv M.ffAlgEquiv).mpr inferInstance

theorem good_point {K : Type} [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (Mdl : AlgebraicCurve.CurveModel K F) {C Y : Scheme.{0}} (cb : C ⟶ Spec (CommRingCat.of K))
    (e : Mdl.C ≅ C) (he : e.hom ≫ cb = Mdl.toBase) (g : C ⟶ Y) (R : Set ↥C) (W : Set ↥Y)
    (V : AlgebraicCurve.Place K F)
    (hR : e.hom.base ((Mdl.pointEquivPlace.symm V).1.base (IsLocalRing.closedPoint K)) ∉ R)
    (hW : g.base (e.hom.base ((Mdl.pointEquivPlace.symm V).1.base (IsLocalRing.closedPoint K))) ∈ W) :
    ∃ c : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) cb,
      (∀ t, c.1.base t ∉ R) ∧ (∀ t, (c.1 ≫ g).base t ∈ W) ∧
      Mdl.pointEquivPlace ⟨c.1 ≫ e.inv, by rw [← he, Category.assoc, e.inv_hom_id_assoc]; exact c.2⟩ = V := by
  refine ⟨⟨(Mdl.pointEquivPlace.symm V).1 ≫ e.hom, by rw [Category.assoc, he]; exact (Mdl.pointEquivPlace.symm V).2⟩,
    ?_, ?_, ?_⟩
  · intro t
    obtain rfl : t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change ((Mdl.pointEquivPlace.symm V).1 ≫ e.hom).base (IsLocalRing.closedPoint K) ∉ R
    exact hR
  · intro t
    obtain rfl : t = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change (((Mdl.pointEquivPlace.symm V).1 ≫ e.hom) ≫ g).base (IsLocalRing.closedPoint K) ∈ W
    exact hW
  · rw [Equiv.apply_eq_iff_eq_symm_apply]
    apply Subtype.ext
    change ((Mdl.pointEquivPlace.symm V).1 ≫ e.hom) ≫ e.inv = (Mdl.pointEquivPlace.symm V).1
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]

end GenChartTools

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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    ∀ x : AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w),
      x ∈ AddSubgroup.closure
        {y : AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w) |
          ∃ (c c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
            (_ : (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base))
            (_ : (∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base))
            (_ : (∀ t, c'.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base))
            (_ : (∀ t, (c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base))
            (h : Finsupp.single (Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩) (1 : ℤ) -
                Finsupp.single (Mdl₁.pointEquivPlace ⟨c'.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c'.2⟩) 1 ∈
              Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w))),
            y = Pic0.mk ⟨_, h⟩} := by
  intro x
  classical

  let Φ : Mdl₁.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let U : Mdl₁.C.Opens := Φ ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)
  let R : Set ↥C₁ := Set.range (pullback.fst i₁.1 i₂.1).base
  let Bad : Set ↥Mdl₁.C := e₁.hom.base ⁻¹' R ∪ (U : Set ↥Mdl₁.C)ᶜ

  haveI : IsCurveOver k ↥(ModularCurve.igusaFunctionFieldX1C k M w) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      Mdl₁.toBase Mdl₁.ffEquiv Mdl₁.ffEquiv_algebraMap
  haveI : Algebra.EssFiniteType k ↥(ModularCurve.igusaFunctionFieldX1C k M w) := GenChartTools.essFiniteType_of_curveModel Mdl₁
  haveI : Infinite (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := Mdl₁.infinite_place

  have he₁inj : Function.Injective e₁.hom.base := by
    intro a b hab
    have := congrArg e₁.inv.base hab
    change (e₁.hom ≫ e₁.inv).base a = (e₁.hom ≫ e₁.inv).base b at this
    rwa [e₁.hom_inv_id] at this
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
  have hR : R.Finite := Set.finite_range _
  have hUne : (U : Set ↥Mdl₁.C).Nonempty := by
    obtain ⟨⟨u, hu⟩⟩ := hne₁
    exact ⟨u, hu⟩
  have hBad : Bad.Finite :=
    (hR.preimage he₁inj.injOn).union (AlgebraicCurve.finite_compl_of_isOpen Mdl₁.toBase U hUne)

  let pt : AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w) → ↥Mdl₁.C :=
    fun V => (Mdl₁.pointEquivPlace.symm V).1.base (IsLocalRing.closedPoint k)
  have hpt : ∀ V, pt V = (Mdl₁.placeEquiv.symm V).1 := fun V => GenChartTools.pointEquivPlace_symm_base Mdl₁ V
  have hptinj : Function.Injective pt := by
    intro V W h
    rw [hpt, hpt] at h
    exact Mdl₁.placeEquiv.symm.injective (Subtype.ext h)
  let S : Set (AlgebraicCurve.Place k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) := pt ⁻¹' Bad
  have hS : S.Finite := hBad.preimage hptinj.injOn

  obtain ⟨V₀, hV₀⟩ := Infinite.exists_notMem_finset hS.toFinset

  have good : ∀ V, V ∉ hS.toFinset →
      ∃ c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
        (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
        (∀ t, (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base t ∈
          Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) ∧
        Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩ = V := by
    intro V hV
    rw [Set.Finite.mem_toFinset] at hV
    have hV' : pt V ∉ Bad := hV
    rw [Set.mem_union, not_or, Set.mem_preimage, Set.mem_compl_iff, not_not] at hV'
    obtain ⟨hVR, hVU⟩ := hV'
    have hVU' : Φ.base (pt V) ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤ : Set _) := hVU
    obtain ⟨a, -, ha⟩ := hVU'
    refine GenChartTools.good_point Mdl₁ c₁ e₁ he₁
      (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
      (Set.range (pullback.fst i₁.1 i₂.1).base) (Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base) V hVR ⟨a, ?_⟩
    exact ha

  have key := AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single_of_notMem hS.toFinset V₀ hV₀ x
  refine AddSubgroup.closure_mono ?_ key
  rintro y ⟨V, hV, h, rfl⟩
  obtain ⟨c, hc1, hc2, hc⟩ := good V hV
  obtain ⟨c', hc'1, hc'2, hc'⟩ := good V₀ hV₀
  refine ⟨c, c', hc1, hc2, hc'1, hc'2, ?_, ?_⟩
  · rw [hc, hc']; exact h
  · exact GenChartTools.pic0Mk_congr (by rw [hc, hc']) _ _

end S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul (solution)
