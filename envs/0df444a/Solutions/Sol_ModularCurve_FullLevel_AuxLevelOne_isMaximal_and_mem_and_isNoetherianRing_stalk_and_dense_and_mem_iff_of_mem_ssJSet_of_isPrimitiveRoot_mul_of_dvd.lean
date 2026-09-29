-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3717b03f-5bc1-5fb0-ab7b-a55f98dbeaf5

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 80000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
      ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
          ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
        ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

    y.asIdeal.IsMaximal ∧
    algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal ∧

    IsNoetherianRing STK ∧

    (∀ (r : STK) (n : ℕ), ∃ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      r - germY c ∈ (IsLocalRing.maximalIdeal STK) ^ n) ∧

    (∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      germY c ∈ IsLocalRing.maximalIdeal STK ↔ c ∈ y.asIdeal) := by
  subst hy
  intro STK germY
  classical
  have hp : q.Prime := Fact.out
  haveI hyp : y.asIdeal.IsPrime := y.isPrime

  obtain ⟨eIso, he1, he2⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y ⟨y, trivial, rfl⟩
  let Loc := Localization.AtPrime y.asIdeal
  let E : STK ≃+* Loc := eIso.commRingCatIsoToRingEquiv
  have hE : ∀ x, E x = eIso.hom.hom x := fun x => rfl

  let germA : A →+* STK :=
    ((((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom).comp
      ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgermA : ∀ a : A, germA a = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := fun a => rfl
  have hEA : ∀ a : A, E (germA a) = algebraMap A Loc a := fun a => by rw [hE, hgermA]; exact he1 a
  have hgermY : ∀ c : ↥(chartAlgFin A (↥K) j), germY c = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤)
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) ⟨y, trivial, rfl⟩).hom
      ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom)
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom c)) := by
    intro c; simp only [germY, RingHom.comp_apply]
  have hEY : ∀ c : ↥(chartAlgFin A (↥K) j), E (germY c) = algebraMap (↥(chartAlgFin A (↥K) j)) Loc c := fun c => by rw [hE, hgermY]; exact he2 c

  have h𝔪E : ∀ x : STK, x ∈ IsLocalRing.maximalIdeal STK ↔ E x ∈ IsLocalRing.maximalIdeal Loc := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact ⟨fun h hu => h (by simpa using hu.map E.symm), fun h hu => h (hu.map E)⟩
  have h𝔪Epow : ∀ (n : ℕ) (x : Loc), x ∈ IsLocalRing.maximalIdeal Loc ^ n →
      E.symm x ∈ IsLocalRing.maximalIdeal STK ^ n := by
    intro n x hx
    have h1 : (IsLocalRing.maximalIdeal Loc).map (E.symm : Loc →+* STK) = IsLocalRing.maximalIdeal STK :=
      IsLocalRing.map_ringEquiv_maximalIdeal E.symm
    have := Ideal.mem_map_of_mem (E.symm : Loc →+* STK) hx
    rw [Ideal.map_pow, h1] at this
    exact this

  have hPT : ∀ c : ↥(chartAlgFin A (↥K) j), germY c ∈ IsLocalRing.maximalIdeal STK ↔ c ∈ y.asIdeal := by
    intro c
    rw [h𝔪E, hEY]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff Loc y.asIdeal c

  obtain ⟨htj, hFD, hsep⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
      (q ^ 2 * M') H₁ L K hK A j hj

  have hinj : Function.Injective (algebraMap A ↥K) := by
    by_contra hni
    exact htj ((Algebra.isAlgebraic_of_not_injective hni).isAlgebraic j)
  obtain ⟨hFT, hFT'⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep
  letI algSTK : Algebra A STK := germA.toAlgebra
  have hN : IsNoetherianRing STK :=
    (AlgebraicCurve.TwoChartIntegralModel.isNoetherianRing_stalk_and_essFiniteType_and_isDomain_and_injective
      A (↥K) hinj j hFT hFT' ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) (fun r => rfl)).1

  have hYA : ∀ a : A, germY (algebraMap A ↥(chartAlgFin A (↥K) j) a) = germA a := by
    intro a
    apply E.injective
    rw [hEY, hEA, ← IsScalarTower.algebraMap_apply]

  have hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
    rw [← hPT, hYA]
    have : germA ϖ = ϖz := by rw [hgermA, hϖz]
    rw [this]; exact hz

  haveI : IsDomain (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := Ideal.Quotient.isDomain y.asIdeal
  have hpy : ((q : ℕ) : ↥(chartAlgFin A (↥K) j)) ∈ y.asIdeal := by
    have hmem : ((q : ℕ) : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    have : ((q : ℕ) : ↥(chartAlgFin A (↥K) j)) = algebraMap A ↥(chartAlgFin A (↥K) j) a * algebraMap A ↥(chartAlgFin A (↥K) j) ϖ := by
      rw [← map_natCast (algebraMap A ↥(chartAlgFin A (↥K) j)), ← ha, map_mul]
    rw [this]
    exact y.asIdeal.mul_mem_left _ hyϖ
  have h0T : ((q : ℕ) : ↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk y.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hpy
  haveI : CharP (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) q := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp h0T)
  let Ω := AlgebraicClosure (FractionRing (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal))
  have hinjΩ : Function.Injective (algebraMap (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω) := by
    rw [IsScalarTower.algebraMap_eq (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) (FractionRing (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)) Ω]
    exact (algebraMap (FractionRing (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)) Ω).injective.comp (IsFractionRing.injective _ _)
  haveI : CharP Ω q := charP_of_injective_algebraMap hinjΩ q
  let φ : ↥(chartAlgFin A (↥K) j) →+* Ω := (algebraMap (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω).comp (Ideal.Quotient.mk y.asIdeal)
  have hker : RingHom.ker φ = y.asIdeal := by
    ext b
    rw [RingHom.mem_ker, RingHom.comp_apply, ← map_zero (algebraMap (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω), hinjΩ.eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  have hssj := hss Ω φ hker
  have hpow := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q hssj
  set jb : ↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal := Ideal.Quotient.mk y.asIdeal (jChartFin A (↥K) j) with hjb
  have hjb2 : jb ^ (q ^ 2) = jb := hinjΩ (by rw [map_pow]; exact hpow)
  have hjint : IsIntegral A jb := by
    refine ⟨Polynomial.X ^ (q ^ 2) - Polynomial.X, Polynomial.monic_X_pow_sub ?_, ?_⟩
    · rw [Polynomial.degree_X]
      exact_mod_cast Nat.one_lt_pow two_ne_zero hp.one_lt
    · simp [hjb2]
  let S : Subalgebra A (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := Algebra.adjoin A {jb}
  haveI : Algebra.IsIntegral A ↥S := Algebra.IsIntegral.adjoin (by rintro x rfl; exact hjint)
  have hR₀ : Algebra.adjoin A ({j} : Set ↥K) ≤ chartAlgFin A (↥K) j := AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K) _
  let ρ : ↥(Algebra.adjoin A ({j} : Set ↥K)) →ₐ[A] (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) :=
    (Ideal.Quotient.mkₐ A y.asIdeal).comp (Subalgebra.inclusion hR₀)
  have hρS : ∀ r, ρ r ∈ S := by
    intro r
    obtain ⟨Q, hQ⟩ : (r : ↥K) ∈ (Polynomial.aeval (R := A) (j : ↥K)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    have hcoe : ((Polynomial.aeval (jChartFin A (↥K) j) Q : ↥(chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (R := A) (j : ↥K) Q :=
      (Polynomial.aeval_algHom_apply (chartAlgFin A (↥K) j).val (jChartFin A (↥K) j) Q).symm
    have hr : Subalgebra.inclusion hR₀ r = Polynomial.aeval (jChartFin A (↥K) j) Q := by
      apply Subtype.ext
      show (r : ↥K) = ((Polynomial.aeval (jChartFin A (↥K) j) Q : ↥(chartAlgFin A (↥K) j)) : ↥K)
      rw [hcoe]
      exact hQ.symm
    show (Ideal.Quotient.mkₐ A y.asIdeal) (Subalgebra.inclusion hR₀ r) ∈ S
    rw [hr, ← Polynomial.aeval_algHom_apply]
    exact Polynomial.aeval_mem_adjoin_singleton A _
  let ρ' : ↥(Algebra.adjoin A ({j} : Set ↥K)) →+* ↥S := (ρ : _ →+* (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)).codRestrict S hρS
  have hint : Algebra.IsIntegral A (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨P, hPm, hPb⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K)).mp b.2
    have hz : IsIntegral ↥S (Ideal.Quotient.mk y.asIdeal b) := by
      refine ⟨P.map ρ', hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap ↥S (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)).comp ρ' = (Ideal.Quotient.mk y.asIdeal).comp (Subalgebra.inclusion hR₀).toRingHom := by
        ext r; rfl
      rw [hcomp, ← Polynomial.hom_eval₂]
      have h0 : Polynomial.eval₂ (Subalgebra.inclusion hR₀).toRingHom b P = 0 := by
        apply Subtype.ext
        have h := Polynomial.hom_eval₂ P (Subalgebra.inclusion hR₀).toRingHom ((chartAlgFin A (↥K) j).val.toRingHom) b
        have hcomp2 : ((chartAlgFin A (↥K) j).val.toRingHom).comp (Subalgebra.inclusion hR₀).toRingHom =
            algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K)) ↥K := by ext r; rfl
        rw [hcomp2] at h
        change ((chartAlgFin A (↥K) j).val.toRingHom) (Polynomial.eval₂ (Subalgebra.inclusion hR₀).toRingHom b P) = _
        rw [h]
        simpa using hPb
      rw [h0, map_zero]
    exact isIntegral_trans _ hz
  have hkerA : IsLocalRing.maximalIdeal A ≤ RingHom.ker ((Ideal.Quotient.mk y.asIdeal).comp (algebraMap A ↥(chartAlgFin A (↥K) j))) := by
    rw [hϖ, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hyϖ
  let ψ : IsLocalRing.ResidueField A →+* ↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((Ideal.Quotient.mk y.asIdeal).comp (algebraMap A ↥(chartAlgFin A (↥K) j))) (fun a ha => hkerA ha)
  letI algRes : Algebra (IsLocalRing.ResidueField A) (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := ψ.toAlgebra
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := Algebra.IsIntegral.tower_top (R := A)
  have hψinj : Function.Injective (algebraMap (IsLocalRing.ResidueField A) (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)) :=
    (algebraMap (IsLocalRing.ResidueField A) (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal)).injective
  have hfield : IsField (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) :=
    (Algebra.IsIntegral.isField_iff_isField (R := IsLocalRing.ResidueField A)
      (S := ↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) hψinj).mp (Field.toIsField _)
  have hymax : y.asIdeal.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield

  have h𝔪Loc : y.asIdeal.map (algebraMap (↥(chartAlgFin A (↥K) j)) Loc) = IsLocalRing.maximalIdeal Loc :=
    IsLocalization.AtPrime.map_eq_maximalIdeal y.asIdeal Loc
  have hDENSE : ∀ (r : STK) (n : ℕ), ∃ c : ↥(chartAlgFin A (↥K) j), r - germY c ∈ (IsLocalRing.maximalIdeal STK) ^ n := by
    intro r n
    obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl (E r)
    have hs : (s : ↥(chartAlgFin A (↥K) j)) ∉ y.asIdeal := s.2
    obtain ⟨b, i, hi, hbi⟩ := hymax.exists_inv hs

    set g : ↥(chartAlgFin A (↥K) j) := ∑ k ∈ Finset.range n, i ^ k with hg
    have hsb : (s : ↥(chartAlgFin A (↥K) j)) * (b * g) = 1 - i ^ n := by
      have h1 : (s : ↥(chartAlgFin A (↥K) j)) * b = 1 - i := by rw [mul_comm]; linear_combination hbi
      rw [← mul_assoc, h1, mul_comm, hg, geom_sum_mul_neg]
    refine ⟨a * (b * g), ?_⟩
    have hu : IsUnit (algebraMap (↥(chartAlgFin A (↥K) j)) Loc s) := IsLocalization.map_units Loc s
    have hspec : E r * algebraMap (↥(chartAlgFin A (↥K) j)) Loc s = algebraMap (↥(chartAlgFin A (↥K) j)) Loc a := by
      rw [← has]; exact IsLocalization.mk'_spec Loc a s
    have hdiff : E r - algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * (b * g)) =
        algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * i ^ n) * ↑hu.unit⁻¹ := by
      have h2 : (E r - algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * (b * g))) * algebraMap (↥(chartAlgFin A (↥K) j)) Loc s =
          algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * i ^ n) := by
        rw [sub_mul, hspec, ← map_mul, ← map_sub]
        congr 1
        linear_combination (-(a : ↥(chartAlgFin A (↥K) j))) * hsb
      rw [← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]
    have hmem : E r - algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * (b * g)) ∈ IsLocalRing.maximalIdeal Loc ^ n := by
      rw [hdiff]
      refine Ideal.mul_mem_right _ _ ?_
      rw [map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [← h𝔪Loc, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hi n)
    have key : E (r - germY (a * (b * g))) = E r - algebraMap (↥(chartAlgFin A (↥K) j)) Loc (a * (b * g)) := by
      rw [map_sub, hEY]
    have := h𝔪Epow n _ hmem
    rw [← key, RingEquiv.symm_apply_apply] at this
    exact this
  exact ⟨hymax, hyϖ, hN, hDENSE, hPT⟩

end S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd (solution)
