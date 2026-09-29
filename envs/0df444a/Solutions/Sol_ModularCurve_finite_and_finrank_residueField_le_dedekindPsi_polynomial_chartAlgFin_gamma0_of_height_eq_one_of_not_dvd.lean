-- Prove2me | solution 1 for ModularCurve.finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a70d35df-8371-5630-a9da-68b2f07a5458

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_Ideal_finrank_residueField_le_finrank_of_height_eq_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_Gamma0_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel ModularCurve

namespace E147G2

universe u

theorem coe_polynomialToChartFin {R F : Type u} [CommRing R] [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (p : Polynomial R) : ((polynomialToChartFin R F j p : ↥(chartAlgFin R F j)) : F) = Polynomial.aeval j p := by
  have h : ((Subalgebra.val (chartAlgFin R F j)).comp (polynomialToChartFin R F j)) = Polynomial.aeval j := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, polynomialToChartFin_X, Polynomial.aeval_X]
    rfl
  exact congrArg (fun g : Polynomial R →ₐ[R] F => g p) h

theorem laurentMap_jqInt_geom (K : Type*) [Field K] : laurentMap (Int.castRingHom K) jqInt = jqModC K := by
  rw [jqModC, jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, map_one]

theorem coeffEmb_jq_eq_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  rw [← laurentMap_jqInt_geom, ← laurentMap_jqInt]
  ext k
  rw [coeffEmb_coeff, laurentMap_coeff, laurentMap_coeff]
  simp

end E147G2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ 𝔔)
    [Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)]
    (halg : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) p =
      AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K₀) j₀ p)
    [Algebra (Localization.AtPrime (𝔔.under (Polynomial A))) (Localization.AtPrime 𝔔)]
    [Localization.AtPrime.IsLiesOverAlgebra (𝔔.under (Polynomial A)) 𝔔] :
    Module.Finite (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField ∧
      Module.finrank (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField ≤ ModularCurve.dedekindPsi M' := by
  have hinst : ‹Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)› = (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra :=
    Algebra.algebra_ext _ _ (fun p => by rw [halg]; rfl)
  subst hinst
  letI algP : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := (polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
  classical
  have hqprime : q.Prime := Fact.out

  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀

  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _
  haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI : Module.Finite (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) :=
    (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).1
  have halgP : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) p = polynomialToChartFin A (↥K₀) j₀ p := fun _ => rfl
  have hinjP : Function.Injective (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) := by
    intro p₁ p₂ h
    rw [halgP, halgP] at h
    have h' := congrArg (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) => (b : ↥K₀)) h
    simp only [E147G2.coe_polynomialToChartFin] at h'
    exact (transcendental_iff_injective.mp htj₀) h'
  haveI : NoZeroSMulDivisors (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun hc => hinjP (by rw [map_zero]; exact hc)⟩
  haveI : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _

  have hinjOK : Function.Injective ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀).comp (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀))) :=
    (Subtype.val_injective).comp hinjP
  letI algK₁ : Algebra (FractionRing (Polynomial A)) ↥K₀ :=
    (IsFractionRing.lift (K := FractionRing (Polynomial A)) hinjOK).toAlgebra
  letI algOK : Algebra (Polynomial A) ↥K₀ := ((algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀).comp (algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀))).toAlgebra
  haveI : IsScalarTower (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Polynomial A) (FractionRing (Polynomial A)) ↥K₀ :=
    IsScalarTower.of_algebraMap_eq (fun p => (IsFractionRing.lift_algebraMap (K := FractionRing (Polynomial A)) hinjOK p).symm)
  have hg : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥K₀ p = (polynomialToChartFin A (↥K₀) j₀ p : ↥K₀) := fun _ => rfl

  have hgmem : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥K₀ p ∈ IntermediateField.adjoin L ({j₀} : Set ↥K₀) := by
    intro p
    rw [hg, E147G2.coe_polynomialToChartFin, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    refine sum_mem (fun i _ => mul_mem ?_ (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _))
    rw [IsScalarTower.algebraMap_apply A L ↥K₀]
    exact (IntermediateField.adjoin L ({j₀} : Set ↥K₀)).algebraMap_mem _
  have hrange1 : ∀ x : FractionRing (Polynomial A),
      algebraMap (FractionRing (Polynomial A)) ↥K₀ x ∈ IntermediateField.adjoin L ({j₀} : Set ↥K₀) := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial A) x
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact div_mem (hgmem a) (hgmem b)
  have hrange2 : ∀ y : ↥K₀, y ∈ IntermediateField.adjoin L ({j₀} : Set ↥K₀) →
      ∃ x : FractionRing (Polynomial A), algebraMap (FractionRing (Polynomial A)) ↥K₀ x = y := by
    let F₁ : IntermediateField L ↥K₀ := Subfield.toIntermediateField (algebraMap (FractionRing (Polynomial A)) ↥K₀).fieldRange
      (fun l => by
        obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) l
        refine ⟨algebraMap (Polynomial A) (FractionRing (Polynomial A)) (Polynomial.C a) /
          algebraMap (Polynomial A) (FractionRing (Polynomial A)) (Polynomial.C b), ?_⟩
        rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hg, hg,
          Polynomial.C_eq_algebraMap, Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes,
          ← IsScalarTower.algebraMap_apply A L ↥K₀ a, ← IsScalarTower.algebraMap_apply A L ↥K₀ b,
          IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ a, IsScalarTower.algebraMap_apply A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ↥K₀ b]
        rfl)
    have hle : IntermediateField.adjoin L ({j₀} : Set ↥K₀) ≤ F₁ := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      refine ⟨algebraMap (Polynomial A) (FractionRing (Polynomial A)) Polynomial.X, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, hg, polynomialToChartFin_X]
      rfl
    intro y hy
    exact RingHom.mem_fieldRange.mp (hle hy)
  let iL₀ : FractionRing (Polynomial A) →+* ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) :=
    (algebraMap (FractionRing (Polynomial A)) ↥K₀).codRestrict (IntermediateField.adjoin L ({j₀} : Set ↥K₀)) hrange1
  have hiL₀ : Function.Bijective iL₀ := by
    refine ⟨fun a b h => (algebraMap (FractionRing (Polynomial A)) ↥K₀).injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hrange2 y y.2
    exact ⟨x, Subtype.ext hx⟩
  let iL : FractionRing (Polynomial A) ≃+* ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) := RingEquiv.ofBijective iL₀ hiL₀
  have hcL : (algebraMap ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀).comp iL.toRingHom =
      (RingEquiv.refl ↥K₀).toRingHom.comp (algebraMap (FractionRing (Polynomial A)) ↥K₀) :=
    RingHom.ext fun _ => rfl
  have hfr : Module.finrank (FractionRing (Polynomial A)) ↥K₀ =
      Module.finrank ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.finrank_eq_of_equiv_equiv iL (RingEquiv.refl ↥K₀) hcL
  haveI : FiniteDimensional (FractionRing (Polynomial A)) ↥K₀ :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)

  obtain ⟨hfin, hle⟩ := Ideal.finrank_residueField_le_finrank_of_height_eq_one
    (O := Polynomial A) (C := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) (FractionRing (Polynomial A)) ↥K₀ 𝔔 h𝔔
  refine ⟨hfin, hle.trans ?_⟩
  rw [hfr]

  have hj₀' : (j₀ : LaurentSeries L) = jqModC L := by rw [hj₀, E147G2.coeffEmb_jq_eq_jqModC]
  subst hK₀
  have h53 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index L
    (CongruenceSubgroup.Gamma0 M') hT₀ (CongruenceSubgroup.Gamma0 M') le_rfl (fun γ h => Or.inl h) j₀ hj₀'
  rw [ModularCurve.Gamma0_index] at h53
  exact h53

end S_ModularCurve_finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_finite_and_finrank_residueField_le_dedekindPsi_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_not_dvd (solution)
