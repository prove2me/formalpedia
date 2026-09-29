-- Prove2me | solution 1 for ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/da00491a-d58f-57a4-ba93-1324f9e3674e

import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_X1
import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

namespace O6Aux

open scoped MatrixGroups

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  refine @Subgroup.finiteIndex_of_le _ _ (CongruenceSubgroup.Gamma1 M) _ inferInstance ?_
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma1_in_Gamma0 M hA
  refine ⟨h0, ?_⟩
  have h1 := ((CongruenceSubgroup.Gamma1_mem M A).mp hA).2.1
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h1
  rw [this]; exact H.one_mem

end O6Aux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic.O6Aux"

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀))

    (hj0 : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ≠ 0) (hj1728 : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ≠ 1728) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∉ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) 𝔔 := by
  intro 𝔔 _inst h𝔔y hQ1 hϖQ
  classical

  letI algBB : Algebra ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := ι.toAlgebra
  set φK : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion hle₀ with hφKdef

  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K) j) := isIntegrallyClosed_chartAlg A (↥K) _
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  haveI : IsFractionRing ↥(chartAlgFin A (↥K) j) ↥K := isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _
  haveI : IsNoetherianRing ↥(chartAlgFin A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
    exact Algebra.FiniteType.isNoetherianRing A _

  have hιj : ι (jChartFin A (↥K₀) j₀) = jChartFin A (↥K) j := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((jChartFin A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) = ((jChartFin A (↥K) j : ↥K) : LaurentSeries L)
    rw [coe_jChartFin, coe_jChartFin, hj₀, hj]
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    symm
    apply Subtype.ext
    show ((ι (algebraMap A ↥(chartAlgFin A (↥K₀) j₀) a) : ↥(chartAlgFin A (↥K) j)) : ↥K) = (algebraMap A ↥(chartAlgFin A (↥K) j) a : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  haveI : Module.Finite ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
    letI algP : Algebra (Polynomial A) ↥(chartAlgFin A (↥K) j) := (polynomialToChartFin A (↥K) j).toRingHom.toAlgebra
    letI algP₀ : Algebra (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) := (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
    haveI hfinP : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K) j) :=
      (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
    have hcomp : ι.comp (polynomialToChartFin A (↥K₀) j₀).toRingHom = (polynomialToChartFin A (↥K) j).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        show ι (polynomialToChartFin A (↥K₀) j₀ (Polynomial.C a)) = polynomialToChartFin A (↥K) j (Polynomial.C a)
        rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
        exact (IsScalarTower.algebraMap_apply A ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) a).symm
      · show ι (polynomialToChartFin A (↥K₀) j₀ Polynomial.X) = polynomialToChartFin A (↥K) j Polynomial.X
        rw [polynomialToChartFin_X, polynomialToChartFin_X, hιj]
    haveI : IsScalarTower (Polynomial A) ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      show polynomialToChartFin A (↥K) j p = ι (polynomialToChartFin A (↥K₀) j₀ p)
      exact (congrArg (fun g : Polynomial A →+* ↥(chartAlgFin A (↥K) j) => g p) hcomp).symm
    exact Module.Finite.of_restrictScalars_finite (Polynomial A) _ _
  have hιK : ∀ x : ↥(chartAlgFin A (↥K₀) j₀),
      algebraMap ↥(chartAlgFin A (↥K) j) ↥K (algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥(chartAlgFin A (↥K) j) x) =
        φK (algebraMap ↥(chartAlgFin A (↥K₀) j₀) ↥K₀ x) := fun x => hι x
  have hint : φK.toRingHom.IsIntegral := by

    set R : IntermediateField L ↥K := IntermediateField.map φK ⊤ with hRdef
    have hjR : j ∈ R := by
      rw [hRdef, IntermediateField.mem_map]
      refine ⟨j₀, IntermediateField.mem_top, ?_⟩
      apply Subtype.ext
      show ((j₀ : ↥K₀) : LaurentSeries L) = ((j : ↥K) : LaurentSeries L)
      rw [hj₀, hj]
    have hER : IntermediateField.adjoin L ({j} : Set ↥K) ≤ R := IntermediateField.adjoin_le_iff.mpr (by
      intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hjR)

    letI algER : Algebra ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R := (IntermediateField.inclusion hER).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R ↥K := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI hAlgR : Algebra.IsAlgebraic ↥R ↥K := Algebra.IsAlgebraic.tower_top (K := ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ↥R
    have hRint : (R.val.toRingHom : ↥R →+* ↥K).IsIntegral := fun x => (Algebra.IsIntegral.isIntegral (R := ↥R) x)

    let e : ↥K₀ ≃ₐ[L] ↥R := (IntermediateField.topEquiv).symm.trans (IntermediateField.equivMap ⊤ φK)
    have hcompφ : φK.toRingHom = (R.val.toRingHom : ↥R →+* ↥K).comp e.toAlgHom.toRingHom := by
      ext x; rfl
    rw [hcompφ]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ e.surjective) hRint

  have he : ∀ w : AlgebraicCurve.Place L ↥K, (∀ r : ↥(chartAlgFin A (↥K) j), 0 ≤ w.ord (algebraMap _ ↥K r)) →
      (∀ r : ↥(chartAlgFin A (↥K) j), r ≠ 0 → (0 < w.ord (algebraMap _ ↥K r) ↔ r ∈ 𝔔)) →
      AlgebraicCurve.Place.ramificationIndexAlong φK w = 1 := by
    intro w hw0 hw1
    have hjQ : jChartFin A (↥K) j ∉ 𝔔 := by
      intro h; apply hj0
      have : jChartFin A (↥K) j ∈ RingHom.ker φ := hφ ▸ h𝔔y h
      exact (RingHom.mem_ker).mp this
    have hj1728Q : jChartFin A (↥K) j - 1728 ∉ 𝔔 := by
      intro h; apply hj1728
      have : jChartFin A (↥K) j - 1728 ∈ RingHom.ker φ := hφ ▸ h𝔔y h
      rw [RingHom.mem_ker, map_sub] at this
      have h2 : φ 1728 = 1728 := map_ofNat φ 1728
      rw [h2] at this
      exact sub_eq_zero.mp this
    have hjne : jChartFin A (↥K) j ≠ 0 := fun h => hjQ (h ▸ 𝔔.zero_mem)
    have hj1728ne : jChartFin A (↥K) j - 1728 ≠ 0 := fun h => hj1728Q (h ▸ 𝔔.zero_mem)
    have hord0 : w.ord j = 0 := by
      have h1 := hw0 (jChartFin A (↥K) j)
      have h2 := (hw1 _ hjne).not.mpr hjQ
      have h3 : algebraMap ↥(chartAlgFin A (↥K) j) ↥K (jChartFin A (↥K) j) = j := rfl
      rw [h3] at h1 h2
      omega
    have hord1728 : w.ord (j - 1728) = 0 := by
      have h1 := hw0 (jChartFin A (↥K) j - 1728)
      have h2 := (hw1 _ hj1728ne).not.mpr hj1728Q
      have h3 : algebraMap ↥(chartAlgFin A (↥K) j) ↥K (jChartFin A (↥K) j - 1728) = j - 1728 := by
        rw [map_sub]; rfl
      rw [h3] at h1 h2
      omega
    rw [hφKdef]
    exact ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH
      q hq M' hqM' L K hK K₀ hK₀ hle₀ j hj w hord0 hord1728
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
    L A ↥K ↥K₀ φK ↥(chartAlgFin A (↥K) j) ↥(chartAlgFin A (↥K₀) j₀) hιK hint 𝔔 hQ1 he ϖ hϖ hϖQ

end S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic
end P2MW
export P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_map_jChartFin_ne_zero_of_ne_1728_xH_of_isAlgebraic (solution)
