-- Prove2me | solution 1 for ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/bf2ac211-076a-5958-a8c4-a4b588eec41f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
import Theorems.Thm_ModularCurve_ramificationIndexAlong_val_adjoin_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_laurentBaseChange_gamma0
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
p2m_attr_erase "instance" "ModularCurve.FullLevel.instAddCommGroupJac ModularCurve.FullLevel.instFintypeIdx ModularCurve.FullLevel.instMulActionAlgEquivRatAlgebraicClosureIdx ModularCurve.FullLevel.instDecidableEqIdx CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.FullLevel.coe_diagOneElem ModularCurve.FullLevel.Jac.eval_neg ModularCurve.FullLevel.Jac.eval_zsmul ModularCurve.FullLevel.Jac.mapIdx_eval ModularCurve.FullLevel.Idx.val_pow ModularCurve.FullLevel.Idx.val_mk ModularCurve.FullLevel.Idx.val_smul ModularCurve.FullLevel.diagJac_eval ModularCurve.FullLevel.Jac.eval_add ModularCurve.FullLevel.Jac.eval_nsmul ModularCurve.FullLevel.Jac.eval_sub ModularCurve.FullLevel.slJac_eval ModularCurve.FullLevel.Jac.eval_zero ModularCurve.FullLevel.Jac.eval_mk ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace HRAMAux

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem isFractionRing_polynomial_adjoin_simple
    (A L : Type*) [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L]
    (E : Type*) [Field E] [Algebra L E] [Algebra A E] [IsScalarTower A L E]
    (t : E) (ht : Transcendental A t) :
    letI F' := IntermediateField.adjoin L ({t} : Set E)
    letI : Algebra A ↥F' := ((algebraMap L ↥F').comp (algebraMap A L)).toAlgebra
    letI : Algebra (Polynomial A) ↥F' :=
      (Polynomial.aeval (R := A) (⟨t, IntermediateField.mem_adjoin_simple_self L t⟩ : ↥F')).toRingHom.toAlgebra
    IsFractionRing (Polynomial A) ↥F' := by
  set F' := IntermediateField.adjoin L ({t} : Set E) with hF'
  letI algAF : Algebra A ↥F' := ((algebraMap L ↥F').comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let tF : ↥F' := ⟨t, IntermediateField.mem_adjoin_simple_self L t⟩
  letI algPF : Algebra (Polynomial A) ↥F' := (Polynomial.aeval (R := A) tF).toRingHom.toAlgebra
  have halg : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥F' p = Polynomial.aeval (R := A) tF p := fun _ => rfl

  have hcoe : ∀ p : Polynomial A, ((Polynomial.aeval (R := A) tF p : ↥F') : E) = Polynomial.aeval (R := A) t p := by
    intro p
    have h := Polynomial.aeval_algHom_apply ((IntermediateField.val F').restrictScalars A) tF p
    exact h.symm

  have htF : Transcendental A tF := by
    rw [transcendental_iff_injective] at ht ⊢
    intro p₁ p₂ h
    apply ht
    rw [← hcoe, ← hcoe, h]

  have hAL : ∀ p : Polynomial A, Polynomial.aeval (R := A) t p = Polynomial.aeval (R := L) t (p.map (algebraMap A L)) :=
    fun p => (Polynomial.aeval_map_algebraMap L t p).symm
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    intro y
    rw [halg]
    apply isUnit_iff_ne_zero.mpr
    intro h0
    apply nonZeroDivisors.ne_zero y.2
    exact (transcendental_iff_injective.mp htF) (by rw [h0, map_zero])
  ·
    intro z
    obtain ⟨r, s, hz⟩ := (IntermediateField.mem_adjoin_simple_iff (F := L) (z : E)).mp z.2
    obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors A) (S := L) r
    obtain ⟨c, hc⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors A) (S := L) s
    set r' := IsLocalization.integerNormalization (nonZeroDivisors A) r with hr'
    set s' := IsLocalization.integerNormalization (nonZeroDivisors A) s with hs'
    rcases eq_or_ne (Polynomial.aeval (R := L) t s) 0 with hs0 | hs0
    · refine ⟨(0, 1), ?_⟩
      have : z = 0 := by
        apply Subtype.ext
        rw [hz, hs0, div_zero]; rfl
      rw [this]; simp
    · have hs'ne : s' ≠ 0 := by
        intro h
        apply hs0
        have : ((c : A) : A) • s = 0 := by rw [← hc, h, Polynomial.map_zero]
        rcases smul_eq_zero.mp this with h1 | h1
        · exact absurd h1 (nonZeroDivisors.ne_zero c.2)
        · rw [h1, map_zero]
      have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
      refine ⟨(C (c : A) * r', ⟨C (b : A) * s', mul_mem (mem_nonZeroDivisors_of_ne_zero (C_ne_zero.mpr hb0))
        (mem_nonZeroDivisors_of_ne_zero hs'ne)⟩), ?_⟩
      apply Subtype.ext
      show ((z : E)) * ((Polynomial.aeval (R := A) tF (C (b : A) * s') : ↥F') : E) =
        ((Polynomial.aeval (R := A) tF (C (c : A) * r') : ↥F') : E)
      rw [hcoe, hcoe, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, hAL s', hAL r', hc, hb,
        ← algebraMap_smul L (b : A) r, ← algebraMap_smul L (c : A) s, map_smul, map_smul,
        Algebra.smul_def, Algebra.smul_def, hz,
        IsScalarTower.algebraMap_apply A L E (b : A), IsScalarTower.algebraMap_apply A L E (c : A)]
      field_simp
  ·
    intro x y h
    refine ⟨1, ?_⟩
    rw [halg, halg] at h
    have := (transcendental_iff_injective.mp htF) h
    rw [this]

end HRAMAux

open HRAMAux AlgebraicCurve.TwoChartIntegralModel in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem solution
    (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔)
    (hj𝔔 : AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀ ∉ 𝔔)
    (hj𝔔' : AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀ - 1728 ∉ 𝔔) :
    letI : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) :=
      (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
    Algebra.IsUnramifiedAt (Polynomial A) 𝔔 := by
  classical
  letI algP₀ : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra

  set F' := IntermediateField.adjoin L ({j₀} : Set ↥K₀) with hF'
  letI algAF : Algebra A ↥F' := ((algebraMap L ↥F').comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let jF : ↥F' := ⟨j₀, IntermediateField.mem_adjoin_simple_self L j₀⟩
  letI algPF : Algebra (Polynomial A) ↥F' := (Polynomial.aeval (R := A) jF).toRingHom.toAlgebra
  haveI : IsScalarTower A (Polynomial A) ↥F' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A ↥F' a = Polynomial.aeval (R := A) jF (Polynomial.C a)
    rw [Polynomial.aeval_C])
  haveI : IsScalarTower A (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A _ a = polynomialToChartFin A (↥K₀) j₀ (algebraMap A (Polynomial A) a)
    rw [AlgHom.commutes])

  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  haveI : Module.Finite (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) :=
    (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _
  haveI : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) ({j₀} : Set ↥K₀)
  haveI : IsFractionRing (Polynomial A) ↥F' := isFractionRing_polynomial_adjoin_simple A L (↥K₀) j₀ htj₀

  let φ : ↥F' →ₐ[L] ↥K₀ := IntermediateField.val F'
  have hint : φ.toRingHom.IsIntegral := fun x =>
    (Algebra.IsIntegral.isIntegral (R := ↥F') (x : ↥K₀))
  have hcoeF : ∀ p : Polynomial A, ((Polynomial.aeval (R := A) jF p : ↥F') : ↥K₀) = Polynomial.aeval (R := A) j₀ p := by
    intro p
    exact (Polynomial.aeval_algHom_apply ((IntermediateField.val F').restrictScalars A) jF p).symm
  have hcoeB : ∀ p : Polynomial A, ((polynomialToChartFin A (↥K₀) j₀ p : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) : ↥K₀) = Polynomial.aeval (R := A) j₀ p := by
    intro p
    show (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀).val (polynomialToChartFin A (↥K₀) j₀ p) = _
    rw [polynomialToChartFin, ← Polynomial.aeval_algHom_apply]
    rfl
  have hι : ∀ x : Polynomial A, algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) x) =
      φ (algebraMap (Polynomial A) ↥F' x) := by
    intro x
    show ((polynomialToChartFin A (↥K₀) j₀ x : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) : ↥K₀) = ((Polynomial.aeval (R := A) jF x : ↥F') : ↥K₀)
    rw [hcoeB, hcoeF]

  have he : ∀ w : AlgebraicCurve.Place L ↥K₀, (∀ r : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), 0 ≤ w.ord (algebraMap _ ↥K₀ r)) →
      (∀ r : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀), r ≠ 0 → (0 < w.ord (algebraMap _ ↥K₀ r) ↔ r ∈ 𝔔)) →
      AlgebraicCurve.Place.ramificationIndexAlong φ w = 1 := by
    intro w hw0 hw1
    have hjne : jChartFin A (↥K₀) j₀ ≠ 0 := fun h => hj𝔔 (h ▸ 𝔔.zero_mem)
    have hj1728ne : jChartFin A (↥K₀) j₀ - 1728 ≠ 0 := fun h => hj𝔔' (h ▸ 𝔔.zero_mem)
    have hord0 : w.ord j₀ = 0 := by
      have h1 := hw0 (jChartFin A (↥K₀) j₀)
      have h2 := (hw1 _ hjne).not.mpr hj𝔔
      have h3 : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (jChartFin A (↥K₀) j₀) = j₀ := rfl
      rw [h3] at h1 h2
      omega
    have hord1728 : w.ord (j₀ - 1728) = 0 := by
      have h1 := hw0 (jChartFin A (↥K₀) j₀ - 1728)
      have h2 := (hw1 _ hj1728ne).not.mpr hj𝔔'
      have h3 : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ (jChartFin A (↥K₀) j₀ - 1728) = j₀ - 1728 := by
        rw [map_sub]; rfl
      rw [h3] at h1 h2
      omega
    exact ModularCurve.ramificationIndexAlong_val_adjoin_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_laurentBaseChange_gamma0 M' L K₀ hK₀ j₀ hj₀ w hord0 hord1728
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
    L A (↥K₀) (↥F') φ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) (Polynomial A) hι hint 𝔔 h𝔔 he ϖ hϖ hϖ𝔔

end S_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
end P2MW
export P2MW.S_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem (solution)
