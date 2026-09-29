-- Prove2me | solution 1 for ModularCurve.XZeroP.exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b5af86f6-7969-50dd-aa2e-162fccf7971d

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_IsCyclotomicExtension_exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace B3CARRIER

section Dominate

variable (A : Type) [CommRing A] [IsLocalRing A] (Ω : Type) [Field Ω] [Algebra A Ω]

theorem exists_valuationSubring_dominating :
    ∃ (B : ValuationSubring Ω) (hB : ∀ a : A, algebraMap A Ω a ∈ B),
      ∀ a : A, (⟨algebraMap A Ω a, hB a⟩ : ↥B) ∈ maximalIdeal ↥B ↔ a ∈ maximalIdeal A := by
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A Ω)
  refine ⟨B, hB, fun a => ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  constructor
  · intro h
    exact (hloc.map_nonunit a h)
  · intro h
    exact h.map ((algebraMap A Ω).codRestrict B.toSubring hB)

end Dominate

section Intersect

variable {A : Type} [CommRing A] [IsDomain A] [ValuationRing A] {L : Type} [Field L] [Algebra A L]
  [IsFractionRing A L] {Ω : Type} [Field Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower A L Ω]
  {B : ValuationSubring Ω} (hB : ∀ a : A, algebraMap A Ω a ∈ B)
  (hdom : ∀ a : A, (⟨algebraMap A Ω a, hB a⟩ : ↥B) ∈ maximalIdeal ↥B ↔ a ∈ maximalIdeal A)

include hdom in

theorem mem_range_of_algebraMap_mem {x : L} (hx : algebraMap L Ω x ∈ B) :
    x ∈ Set.range (algebraMap A L) := by
  rcases (ValuationRing.iff_isInteger_or_isInteger A L).mp inferInstance x with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  · by_cases hx0 : x = 0
    · exact ⟨0, by rw [map_zero, hx0]⟩
    have hainv : algebraMap A Ω a = (algebraMap L Ω x)⁻¹ := by
      rw [IsScalarTower.algebraMap_apply A L Ω, show algebraMap A L a = x⁻¹ from ha, map_inv₀]
    have hunit : IsUnit (⟨algebraMap A Ω a, hB a⟩ : ↥B) := by
      refine IsUnit.of_mul_eq_one ⟨algebraMap L Ω x, hx⟩ (Subtype.ext ?_)
      rw [MulMemClass.coe_mul, OneMemClass.coe_one]
      change algebraMap A Ω a * algebraMap L Ω x = 1
      rw [hainv, inv_mul_cancel₀ ((map_ne_zero _).mpr hx0)]
    have ha_unit : IsUnit a := by
      by_contra hna
      have hmem : a ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hna
      exact (IsLocalRing.mem_maximalIdeal _).mp ((hdom a).mpr hmem) hunit
    obtain ⟨u, rfl⟩ := ha_unit
    refine ⟨↑u⁻¹, ?_⟩
    rw [map_units_inv, show algebraMap A L ↑u = x⁻¹ from ha, inv_inv]

end Intersect

section Coeff

variable {A : Type} [CommRing A] [IsDomain A] [ValuationRing A] {L : Type} [Field L] [Algebra A L]
  [IsFractionRing A L] [Algebra L (AlgebraicClosure ℚ)] [Algebra A (AlgebraicClosure ℚ)]
  [IsScalarTower A L (AlgebraicClosure ℚ)]
  {B : ValuationSubring (AlgebraicClosure ℚ)} {K : IntermediateField ℚ (AlgebraicClosure ℚ)}

abbrev HB (B : ValuationSubring (AlgebraicClosure ℚ)) : Prop := ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a ∈ B
abbrev HD {B : ValuationSubring (AlgebraicClosure ℚ)} (hB : HB (A := A) B) : Prop :=
  ∀ a : A, (⟨algebraMap A (AlgebraicClosure ℚ) a, hB a⟩ : ↥B) ∈ maximalIdeal ↥B ↔ a ∈ maximalIdeal A
abbrev HK (L : Type) [Field L] [Algebra L (AlgebraicClosure ℚ)] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
  ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range (algebraMap L (AlgebraicClosure ℚ))

theorem algebraMap_mem_coeffSubring (hB : HB (A := A) B) (hK : HK L K) (a : A) :
    algebraMap A (AlgebraicClosure ℚ) a ∈ ModularCurve.NodeLocalized.coeffSubring B K :=
  ⟨hB a, (hK _).mpr ⟨algebraMap A L a, (IsScalarTower.algebraMap_apply A L _ a).symm⟩⟩

def coeffHom (hB : HB (A := A) B) (hK : HK L K) : A →+* ↥(ModularCurve.NodeLocalized.coeffSubring B K) :=
  (algebraMap A (AlgebraicClosure ℚ)).codRestrict _ (algebraMap_mem_coeffSubring hB hK)

theorem coe_coeffHom (hB : HB (A := A) B) (hK : HK L K) (a : A) :
    (coeffHom hB hK a : AlgebraicClosure ℚ) = algebraMap A (AlgebraicClosure ℚ) a := rfl

theorem coeffHom_bijective (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K) :
    Function.Bijective (coeffHom hB hK) := by
  constructor
  · intro a b h
    have h' := congrArg (fun z : ↥(ModularCurve.NodeLocalized.coeffSubring B K) => (z : AlgebraicClosure ℚ)) h
    simp only [coe_coeffHom] at h'
    rw [IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ),
      IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ)] at h'
    exact IsFractionRing.injective A L ((algebraMap L (AlgebraicClosure ℚ)).injective h')
  · rintro ⟨x, hxB, hxK⟩
    obtain ⟨y, rfl⟩ := (hK x).mp hxK
    obtain ⟨a, rfl⟩ := mem_range_of_algebraMap_mem hB hdom hxB
    exact ⟨a, Subtype.ext (IsScalarTower.algebraMap_apply A L (AlgebraicClosure ℚ) a)⟩

def coeffEquiv (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K) : A ≃+* ↥(ModularCurve.NodeLocalized.coeffSubring B K) :=
  RingEquiv.ofBijective (coeffHom hB hK) (coeffHom_bijective hB hdom hK)

theorem coe_coeffEquiv (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K) (a : A) :
    ((coeffEquiv hB hdom hK a : ↥(ModularCurve.NodeLocalized.coeffSubring B K)) : AlgebraicClosure ℚ) =
      algebraMap A (AlgebraicClosure ℚ) a := rfl

theorem redRestrict_coeffEquiv_eq_zero_iff (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K) (a : A) :
    ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥B) K (coeffEquiv hB hdom hK a) = 0 ↔
      a ∈ maximalIdeal A := by
  rw [← hdom a, ← IsLocalRing.residue_eq_zero_iff]
  rfl

theorem redRestrict_eq_zero_iff_exists (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K)
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (d : ↥(ModularCurve.NodeLocalized.coeffSubring B K)) :
    ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥B) K d = 0 ↔
      ∃ d', d = coeffEquiv hB hdom hK ϖ * d' := by
  obtain ⟨a, rfl⟩ := (coeffEquiv hB hdom hK).surjective d
  rw [redRestrict_coeffEquiv_eq_zero_iff, hϖ, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨coeffEquiv hB hdom hK c, by rw [← map_mul, mul_comm]⟩
  · rintro ⟨d', hd'⟩
    obtain ⟨c, rfl⟩ := (coeffEquiv hB hdom hK).surjective d'
    rw [← map_mul] at hd'
    exact ⟨c, by rw [mul_comm, (coeffEquiv hB hdom hK).injective hd']⟩

theorem exists_isUnit_natCast_eq (hB : HB (A := A) B) (hdom : HD hB) (hK : HK L K)
    (p : ℕ) (ϖ : A) (u : Aˣ) (hu : (p : A) = ↑u * ϖ ^ (p - 1)) :
    ∃ ε : ↥(ModularCurve.NodeLocalized.coeffSubring B K), IsUnit ε ∧
      ((p : ℕ) : ↥(ModularCurve.NodeLocalized.coeffSubring B K)) = coeffEquiv hB hdom hK ϖ ^ (p - 1) * ε := by
  refine ⟨coeffEquiv hB hdom hK u, (Units.isUnit u).map _, ?_⟩
  rw [← map_natCast (coeffEquiv hB hdom hK) p, hu, map_mul, map_pow, mul_comm]

end Coeff

section Residue

variable {A : Type} [CommRing A] [IsLocalRing A] {Ω : Type} [Field Ω] [Algebra A Ω]
  {B : ValuationSubring Ω} (hB : ∀ a : A, algebraMap A Ω a ∈ B)
  (hdom : ∀ a : A, (⟨algebraMap A Ω a, hB a⟩ : ↥B) ∈ maximalIdeal ↥B ↔ a ∈ maximalIdeal A)

include hdom in

theorem charP_residueField (p : ℕ) [Fact p.Prime] (hAp : (p : A) ∈ maximalIdeal A) :
    CharP (ResidueField ↥B) p := by
  have h0 : IsLocalRing.residue ↥B ((p : ℕ) : ↥B) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    have : ((p : ℕ) : ↥B) = ⟨algebraMap A Ω p, hB p⟩ := Subtype.ext (by simp)
    rw [this]
    exact (hdom _).mpr hAp
  rw [map_natCast] at h0
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

end Residue

theorem C1 (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (e : L →+* AlgebraicClosure ℚ)
      (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range e)
      (Ab : ValuationSubring (AlgebraicClosure ℚ)) (_ : Ab.LiesOverPrime p)
      (hA : ∀ a : A, e (algebraMap A L a) ∈ Ab)
      (_ : ∀ a : A, (⟨e (algebraMap A L a), hA a⟩ : ↥Ab) ∈ IsLocalRing.maximalIdeal ↥Ab ↔ a ∈ IsLocalRing.maximalIdeal A)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ ModularCurve.NodeLocalized.coeffSubring Ab K ↔ ∃ a : A, x = e (algebraMap A L a))
      (ϖb : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K))
      (_ : (ϖb : AlgebraicClosure ℚ) = e (algebraMap A L ϖ))
      (_ : ∀ d : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
        ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
      (ε : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (_ : IsUnit ε),
      ((p : ℕ) : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) = ϖb ^ (p - 1) * ε := by

  haveI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {p} ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let eA : L →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  let e : L →+* AlgebraicClosure ℚ := eA.toRingHom
  letI : Algebra L (AlgebraicClosure ℚ) := e.toAlgebra
  letI : Algebra A (AlgebraicClosure ℚ) := (e.comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halg : ∀ a : A, algebraMap A (AlgebraicClosure ℚ) a = e (algebraMap A L a) := fun _ => rfl
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := eA.fieldRange
  have hK : ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range (algebraMap L (AlgebraicClosure ℚ)) := fun x =>
    AlgHom.mem_fieldRange
  haveI : FiniteDimensional ℚ ↥K := by
    change FiniteDimensional ℚ ↥eA.fieldRange.toSubalgebra
    rw [AlgHom.fieldRange_toSubalgebra]
    exact Module.Finite.of_surjective eA.rangeRestrict.toLinearMap eA.rangeRestrict_surjective

  obtain ⟨B, hB, hdom⟩ := exists_valuationSubring_dominating A (AlgebraicClosure ℚ)
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.exists_isUnit_natCast_eq_mul_uniformizer_pow_sub_one
    p L ζ hζ A hAp hζA ϖ hϖ
  obtain ⟨ε, hε, hpε⟩ := exists_isUnit_natCast_eq hB hdom hK p ϖ u hu
  have hlies : B.LiesOverPrime p := by
    change ((p : ℕ) : AlgebraicClosure ℚ) ∈ B.nonunits
    have hp : ((p : ℕ) : AlgebraicClosure ℚ) = ((⟨algebraMap A (AlgebraicClosure ℚ) p, hB p⟩ : ↥B) : AlgebraicClosure ℚ) := by
      simp
    rw [hp, ValuationSubring.coe_mem_nonunits_iff]
    exact (hdom _).mpr hAp
  refine ⟨e, K, inferInstance, hK, B, hlies, hB, hdom, fun x => ⟨fun hx => ?_, ?_⟩,
    coeffEquiv hB hdom hK ϖ, rfl, redRestrict_eq_zero_iff_exists hB hdom hK ϖ hϖ, ε, hε, hpε⟩
  · obtain ⟨a, ha⟩ := (coeffEquiv hB hdom hK).surjective ⟨x, hx⟩
    exact ⟨a, (congrArg (fun z : ↥(ModularCurve.NodeLocalized.coeffSubring B K) => (z : AlgebraicClosure ℚ)) ha).symm⟩
  · rintro ⟨a, rfl⟩
    exact algebraMap_mem_coeffSubring hB hK a

end B3CARRIER

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq"

namespace B3FIELD

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ hk, qExpand_coeff_of_not_dvd _ _ hk, map_zero]

theorem coeffEmb_jq (C : Type*) [Field C] [Algebra ℚ C] : coeffEmb C jq = jqModC C := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ C)

theorem coeffEmb_qExpand_jq (C : Type*) [Field C] [Algebra ℚ C] (N : ℕ) [NeZero N] :
    coeffEmb C (qExpand ℚ N jq) = jqNModC C N := by
  rw [jqNModC, ← coeffEmb_jq C, coeffEmb, coeffMap_qExpand]

variable {L : Type} [Field L] [CharZero L] (e : L →+* AlgebraicClosure ℚ)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range e)

theorem coeffMap_algebraMap (c : L) :
    coeffMap e (algebraMap L (LaurentSeries L) c) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (e c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

include hK in

theorem image_range_algebraMap :
    ⇑(coeffMap e) '' Set.range (algebraMap L (LaurentSeries L)) =
      Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) := by
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨⟨e c, (hK _).mpr ⟨c, rfl⟩⟩, by rw [coeffMap_algebraMap]; rfl⟩
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (hK x).mp hx
    exact ⟨_, ⟨c, rfl⟩, by rw [coeffMap_algebraMap]; rfl⟩

theorem coeffMap_coeffEmb (x : LaurentSeries ℚ) :
    coeffMap e (coeffEmb L x) = coeffEmb (AlgebraicClosure ℚ) x := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) _

theorem adjoin_le_comap (N : ℕ) [NeZero N] :
    ∀ x ∈ IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)),
      coeffEmb (AlgebraicClosure ℚ) x ∈ NodeLocalized.fieldOver N K := by

  let T : IntermediateField ℚ (LaurentSeries ℚ) :=
    Subfield.toIntermediateField ((NodeLocalized.fieldOver N K).comap (coeffEmb (AlgebraicClosure ℚ)))
      fun r => by
        rw [Subfield.mem_comap, coeffEmb, coeffMap_algebraMap]
        exact Subfield.subset_closure (Or.inl ⟨⟨algebraMap ℚ (AlgebraicClosure ℚ) r, K.algebraMap_mem r⟩, rfl⟩)
  have hle : IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) ≤ T := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · show coeffEmb (AlgebraicClosure ℚ) jq ∈ NodeLocalized.fieldOver N K
      rw [coeffEmb_jq]
      exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
    · show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) ∈ NodeLocalized.fieldOver N K
      rw [coeffEmb_qExpand_jq]
      exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  intro x hx
  exact hle hx

include hK in

theorem mem_fieldOver_iff (N : ℕ) [NeZero N] (y : LaurentSeries (AlgebraicClosure ℚ)) :
    y ∈ NodeLocalized.fieldOver N K ↔
      ∃ x : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))),
        coeffMap e ((x : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)))) :
          LaurentSeries L) = y := by
  have hF₀ : qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N) =
      IntermediateField.adjoin ℚ ({jq, qExpand ℚ N jq} : Set (LaurentSeries ℚ)) := by
    rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull, ← modularFunctionField_eq_full]
    rfl

  have himage : ((laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N))).toSubfield.map
      (coeffMap e)) = NodeLocalized.fieldOver N K := by
    rw [laurentBaseChange, IntermediateField.adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
      image_range_algebraMap e K hK]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro y (hy | ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
      · exact Subfield.subset_closure (Or.inl hy)
      · rw [coeffMap_coeffEmb]
        rw [hF₀] at hx
        exact adjoin_le_comap K N x hx
    · rw [NodeLocalized.fieldOver, Subfield.closure_le]
      rintro y (hy | hy)
      · exact Subfield.subset_closure (Or.inl hy)
      · have hjq : jq ∈ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N) : Set (LaurentSeries ℚ)) := by
          rw [hF₀]; exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
        have hjqN : qExpand ℚ N jq ∈ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N) : Set (LaurentSeries ℚ)) := by
          rw [hF₀]; exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
        rcases hy with rfl | hy
        · refine Subfield.subset_closure (Or.inr ⟨coeffEmb L jq, ⟨jq, hjq, rfl⟩, ?_⟩)
          rw [coeffMap_coeffEmb, coeffEmb_jq]
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          refine Subfield.subset_closure (Or.inr ⟨coeffEmb L (qExpand ℚ N jq), ⟨_, hjqN, rfl⟩, ?_⟩)
          rw [coeffMap_coeffEmb, coeffEmb_qExpand_jq]
  rw [← himage, Subfield.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

end B3FIELD

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq AlgebraicCurve.TwoChartIntegralModel Polynomial"

namespace B3CHART

section Transport

variable {B B' : Type*} [CommRing B] [CommRing B'] [Nontrivial B'] (f : B →+* B') (hf : Function.Injective f)
  (S : Subring B) (S' : Subring B') (hSS' : ∀ y : B', y ∈ S' ↔ ∃ s ∈ S, f s = y)

include hSS' in
theorem map_mem (s : ↥S) : f s ∈ S' := (hSS' _).mpr ⟨s, s.2, rfl⟩

def restr : ↥S →+* ↥S' := (f.comp S.subtype).codRestrict S' (map_mem f S S' hSS')

include hSS' in
theorem restr_surjective : Function.Surjective (restr f S S' hSS') := by
  rintro ⟨y, hy⟩
  obtain ⟨s, hs, rfl⟩ := (hSS' y).mp hy
  exact ⟨⟨s, hs⟩, rfl⟩

include hf hSS' in

theorem isIntegral_iff (x : B) : IsIntegral ↥S x ↔ IsIntegral ↥S' (f x) := by
  constructor
  · intro hx
    exact hx.map_of_comp_eq (restr f S S' hSS') f (RingHom.ext fun _ => rfl)
  · rintro ⟨P', hP'm, hP'⟩
    have hlift : P' ∈ Polynomial.lifts (restr f S S' hSS') := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact restr_surjective f S S' hSS' _
    obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hP'm
    refine ⟨Q, hQm, hf ?_⟩
    rw [map_zero, Polynomial.hom_eval₂, ← hP', ← hQ, Polynomial.eval₂_map]
    rfl

end Transport

variable {L : Type} [Field L] [CharZero L] (e : L →+* AlgebraicClosure ℚ)
  (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (Ab : ValuationSubring (AlgebraicClosure ℚ))
  (A : Type) [CommRing A] [Algebra A L]
  (hcoeff : ∀ x : AlgebraicClosure ℚ, x ∈ NodeLocalized.coeffSubring Ab K ↔ ∃ a : A, x = e (algebraMap A L a))
  (K₂ : IntermediateField L (LaurentSeries L)) [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
  (N : ℕ) [NeZero N]
  (hfield : ∀ y : LaurentSeries (AlgebraicClosure ℚ), y ∈ NodeLocalized.fieldOver N K ↔
    ∃ x : ↥K₂, coeffMap e ((x : ↥K₂) : LaurentSeries L) = y)
  (j₂ : ↥K₂) [Fact (j₂ ≠ 0)] (hj₂ : coeffMap e ((j₂ : ↥K₂) : LaurentSeries L) = jqModC (AlgebraicClosure ℚ))

def rd : ↥K₂ →+* LaurentSeries (AlgebraicClosure ℚ) := (coeffMap e).comp (SubringClass.subtype K₂)

theorem rd_apply (x : ↥K₂) : rd e K₂ x = coeffMap e ((x : ↥K₂) : LaurentSeries L) := rfl

theorem rd_injective : Function.Injective (rd e K₂) := by
  intro x y h
  apply Subtype.ext
  apply HahnSeries.coeff_inj.mp
  funext k
  have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff k) h
  simp only [rd_apply, coeffMap_coeff] at this
  exact e.injective this

theorem rd_algebraMap (a : A) :
    rd e K₂ (algebraMap A ↥K₂ a) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (e (algebraMap A L a)) := by
  rw [rd_apply, IsScalarTower.algebraMap_apply A L ↥K₂]
  change coeffMap e (algebraMap L (LaurentSeries L) (algebraMap A L a)) = _
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

include hcoeff hj₂ in

theorem mem_jRing_iff (y : LaurentSeries (AlgebraicClosure ℚ)) :
    y ∈ NodeLocalized.jRing Ab K ↔
      ∃ s ∈ (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring, rd e K₂ s = y := by

  have himage : (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring.map (rd e K₂) = NodeLocalized.jRing Ab K := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      change s ∈ Algebra.adjoin A ({j₂} : Set ↥K₂) at hs
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [rd_apply, hj₂]
          exact Subring.subset_closure (Or.inr rfl)
      | algebraMap a =>
          rw [rd_algebraMap]
          refine Subring.subset_closure (Or.inl ⟨⟨e (algebraMap A L a), (hcoeff _).mpr ⟨a, rfl⟩⟩, rfl⟩)
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    · rw [NodeLocalized.jRing, Subring.closure_le]
      rintro y (⟨⟨c, hc⟩, rfl⟩ | hy)
      · obtain ⟨a, rfl⟩ := (hcoeff c).mp hc
        exact ⟨algebraMap A ↥K₂ a, Subalgebra.algebraMap_mem _ a, rd_algebraMap e A K₂ a⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨j₂, Algebra.subset_adjoin rfl, hj₂⟩
  rw [← himage, Subring.mem_map]

include hcoeff hfield hj₂ in

theorem exists_ringEquiv :
    ∃ Φ : ↥(chartAlgFin A (↥K₂) j₂) ≃+* ↥(NodeLocalized.jIntegralClosure N Ab K),
      ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
        ((Φ b : ↥(NodeLocalized.jIntegralClosure N Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffMap e ((b : ↥K₂) : LaurentSeries L) := by
  have hint : ∀ x : ↥K₂, x ∈ chartAlgFin A (↥K₂) j₂ ↔ IsIntegral ↥(NodeLocalized.jRing Ab K) (rd e K₂ x) := fun x =>
    isIntegral_iff (rd e K₂) (rd_injective e K₂) (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring
      (NodeLocalized.jRing Ab K) (mem_jRing_iff e K Ab A hcoeff K₂ j₂ hj₂) x
  have hmem : ∀ b : ↥(chartAlgFin A (↥K₂) j₂), rd e K₂ b ∈ NodeLocalized.jIntegralClosure N Ab K := fun b =>
    ⟨(hfield _).mpr ⟨b, rfl⟩, (hint b).mp b.2⟩
  let φ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(NodeLocalized.jIntegralClosure N Ab K) :=
    ((rd e K₂).comp (chartAlgFin A (↥K₂) j₂).val.toRingHom).codRestrict _ hmem
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h' := congrArg (fun z : ↥(NodeLocalized.jIntegralClosure N Ab K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
      exact Subtype.ext (rd_injective e K₂ h')
    · rintro ⟨y, hyF, hyI⟩
      obtain ⟨x, rfl⟩ := (hfield y).mp hyF
      exact ⟨⟨x, (hint x).mpr hyI⟩, rfl⟩
  exact ⟨RingEquiv.ofBijective φ hφ, fun b => rfl⟩

def constAlgHom : ↥(NodeLocalized.coeffSubring Ab K) →+* ↥(NodeLocalized.fieldOver N K) :=
  (CharPReduction.constSeries (NodeLocalized.coeffSubring Ab K)).codRestrict _ fun c =>
    Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩)

include hfield in

def rdF : ↥K₂ →+* ↥(NodeLocalized.fieldOver N K) :=
  (rd e K₂).codRestrict _ fun x => (hfield _).mpr ⟨x, rfl⟩

include hfield in
theorem coe_rdF (x : ↥K₂) : ((rdF e K K₂ N hfield x : ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) =
    coeffMap e ((x : ↥K₂) : LaurentSeries L) := rfl

include hfield in
theorem rdF_injective : Function.Injective (rdF e K K₂ N hfield) := fun x y h =>
  rd_injective e K₂ (congrArg (fun z : ↥(NodeLocalized.fieldOver N K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)

include hcoeff hfield hj₂ in

theorem exists_algebra_ringEquiv :
    ∃ (inst : Algebra ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K))
      (_ : ∀ c : ↥(NodeLocalized.coeffSubring Ab K),
        ((algebraMap ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) c :
            ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          CharPReduction.constSeries (NodeLocalized.coeffSubring Ab K) c)
      (jK : ↥(NodeLocalized.fieldOver N K))
      (_ : ((jK : ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
      (_ : Fact (jK ≠ 0))
      (Φ : ↥(chartAlgFin A (↥K₂) j₂) ≃+*
        ↥(chartAlgFin ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) jK)),
      ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
        (((Φ b : ↥(chartAlgFin ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) jK)) :
            ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffMap e ((b : ↥K₂) : LaurentSeries L) := by
  letI inst : Algebra ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) :=
    (constAlgHom K Ab N).toAlgebra
  have hlaw : ∀ c : ↥(NodeLocalized.coeffSubring Ab K),
      ((algebraMap ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) c :
          ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) =
        CharPReduction.constSeries (NodeLocalized.coeffSubring Ab K) c := fun _ => rfl

  let jK : ↥(NodeLocalized.fieldOver N K) := rdF e K K₂ N hfield j₂
  have hjK : ((jK : ↥(NodeLocalized.fieldOver N K)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
    hj₂
  have hjK0 : jK ≠ 0 := fun h =>
    (Fact.out : j₂ ≠ 0) (rdF_injective e K K₂ N hfield (h.trans (map_zero _).symm))
  haveI : Fact (jK ≠ 0) := ⟨hjK0⟩

  have halgMap : ∀ a : A, rdF e K K₂ N hfield (algebraMap A ↥K₂ a) =
      algebraMap ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K)
        ⟨e (algebraMap A L a), (hcoeff _).mpr ⟨a, rfl⟩⟩ := fun a =>
    Subtype.ext (by rw [coe_rdF, ← rd_apply, rd_algebraMap, hlaw]; rfl)
  have hSS' : ∀ y : ↥(NodeLocalized.fieldOver N K),
      y ∈ (Algebra.adjoin ↥(NodeLocalized.coeffSubring Ab K) ({jK} : Set ↥(NodeLocalized.fieldOver N K))).toSubring ↔
        ∃ s ∈ (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring, rdF e K K₂ N hfield s = y := by
    have himage : (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring.map (rdF e K K₂ N hfield) =
        (Algebra.adjoin ↥(NodeLocalized.coeffSubring Ab K) ({jK} : Set ↥(NodeLocalized.fieldOver N K))).toSubring := by
      apply le_antisymm
      · rintro _ ⟨s, hs, rfl⟩
        change s ∈ Algebra.adjoin A ({j₂} : Set ↥K₂) at hs
        change rdF e K K₂ N hfield s ∈ Algebra.adjoin ↥(NodeLocalized.coeffSubring Ab K) ({jK} : Set ↥(NodeLocalized.fieldOver N K))
        induction hs using Algebra.adjoin_induction with
        | mem x hx =>
            rw [Set.mem_singleton_iff] at hx
            subst hx
            exact Algebra.subset_adjoin rfl
        | algebraMap a =>
            rw [halgMap]
            exact Subalgebra.algebraMap_mem _ _
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
      · intro y hy
        change y ∈ Algebra.adjoin ↥(NodeLocalized.coeffSubring Ab K) ({jK} : Set ↥(NodeLocalized.fieldOver N K)) at hy
        induction hy using Algebra.adjoin_induction with
        | mem x hx =>
            rw [Set.mem_singleton_iff] at hx
            subst hx
            exact ⟨j₂, Algebra.subset_adjoin rfl, rfl⟩
        | algebraMap c =>
            obtain ⟨a, ha⟩ := (hcoeff c).mp c.2
            refine ⟨algebraMap A ↥K₂ a, Subalgebra.algebraMap_mem _ a, ?_⟩
            rw [halgMap]
            congr 1
            exact Subtype.ext ha.symm
        | add x y _ _ hx hy => exact add_mem hx hy
        | mul x y _ _ hx hy => exact mul_mem hx hy
    intro y
    rw [← himage, Subring.mem_map]
  have hint : ∀ x : ↥K₂, x ∈ chartAlgFin A (↥K₂) j₂ ↔
      rdF e K K₂ N hfield x ∈ chartAlgFin ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) jK := fun x =>
    isIntegral_iff (rdF e K K₂ N hfield) (rdF_injective e K K₂ N hfield) (Algebra.adjoin A ({j₂} : Set ↥K₂)).toSubring
      (Algebra.adjoin ↥(NodeLocalized.coeffSubring Ab K) ({jK} : Set ↥(NodeLocalized.fieldOver N K))).toSubring hSS' x
  let φ : ↥(chartAlgFin A (↥K₂) j₂) →+* ↥(chartAlgFin ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) jK) :=
    ((rdF e K K₂ N hfield).comp (chartAlgFin A (↥K₂) j₂).val.toRingHom).codRestrict _ fun b => (hint b).mp b.2
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b h
      have h' := congrArg (fun z : ↥(chartAlgFin ↥(NodeLocalized.coeffSubring Ab K) ↥(NodeLocalized.fieldOver N K) jK) =>
        (z : ↥(NodeLocalized.fieldOver N K))) h
      exact Subtype.ext (rdF_injective e K K₂ N hfield h')
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (hfield y).mp y.2
      obtain rfl : rdF e K K₂ N hfield x = y := Subtype.ext hx
      exact ⟨⟨x, (hint x).mpr hy⟩, rfl⟩
  exact ⟨inst, hlaw, jK, hjK, ⟨hjK0⟩, RingEquiv.ofBijective φ hφ, fun b => rfl⟩

end B3CHART

end

open AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₂] [IsScalarTower A L ↥K₂]
    (j₂ : ↥K₂) (hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₂ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (e : L →+* AlgebraicClosure ℚ)
      (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥K)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ K ↔ x ∈ Set.range e)
      (Ab : ValuationSubring (AlgebraicClosure ℚ)) (_ : Ab.LiesOverPrime p)
      (hA : ∀ a : A, e (algebraMap A L a) ∈ Ab)

      (_ : ∀ a : A, (⟨e (algebraMap A L a), hA a⟩ : ↥Ab) ∈ IsLocalRing.maximalIdeal ↥Ab ↔ a ∈ IsLocalRing.maximalIdeal A)
      (_ : ∀ x : AlgebraicClosure ℚ, x ∈ ModularCurve.NodeLocalized.coeffSubring Ab K ↔ ∃ a : A, x = e (algebraMap A L a))
      (ϖb : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K))
      (_ : (ϖb : AlgebraicClosure ℚ) = e (algebraMap A L ϖ))
      (_ : ∀ d : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
        ModularCurve.NodeLocalized.redRestrict (IsLocalRing.residue ↥Ab) K d = 0 ↔ ∃ d', d = ϖb * d')
      (ε : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) (_ : IsUnit ε)
      (_ : ((p : ℕ) : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)) = ϖb ^ (p - 1) * ε)

      (_ : ∀ y : LaurentSeries (AlgebraicClosure ℚ),
        y ∈ ModularCurve.NodeLocalized.fieldOver (M * p) K ↔
          ∃ x : ↥K₂, ModularCurve.coeffMap e ((x : ↥K₂) : LaurentSeries L) = y)

      (inst : Algebra ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K))
      (_ : ∀ c : ↥(ModularCurve.NodeLocalized.coeffSubring Ab K),
        ((algebraMap ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) c :
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.CharPReduction.constSeries (ModularCurve.NodeLocalized.coeffSubring Ab K) c)
      (jK : ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K))
      (_ : ((jK : ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.jqModC (AlgebraicClosure ℚ))
      (_ : Fact (jK ≠ 0))
      (Φ : ↥(chartAlgFin A (↥K₂) j₂) ≃+*
        ↥(chartAlgFin ↥(ModularCurve.NodeLocalized.coeffSubring Ab K) ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) jK)),
      (∀ b : ↥(chartAlgFin A (↥K₂) j₂),
        (((Φ b : ↥(chartAlgFin ↥(ModularCurve.NodeLocalized.coeffSubring Ab K)
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K) jK)) :
            ↥(ModularCurve.NodeLocalized.fieldOver (M * p) K)) : LaurentSeries (AlgebraicClosure ℚ)) =
          ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L)) ∧

      ∃ Ψ : ↥(chartAlgFin A (↥K₂) j₂) ≃+* ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K),
        ∀ b : ↥(chartAlgFin A (↥K₂) j₂),
          ((Ψ b : ↥(ModularCurve.NodeLocalized.jIntegralClosure (M * p) Ab K)) : LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.coeffMap e ((b : ↥K₂) : LaurentSeries L) := by
  obtain ⟨e, K, hKfd, hK, Ab, hlies, hA, hdom, hcoeff, ϖb, hϖbe, hϖb, ε, hε, hpε⟩ :=
    B3CARRIER.C1 p L ζ hζ A hAp hζA ϖ hϖ
  have hfield := B3FIELD.mem_fieldOver_iff e K hK (M * p)
  have hj₂' : ModularCurve.coeffMap e ((j₂ : ↥K₂) : LaurentSeries L) = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
    rw [hj₂, B3FIELD.coeffMap_coeffEmb, B3FIELD.coeffEmb_jq]
  subst hK₂
  obtain ⟨inst, hlaw, jK, hjK, hfact, Φ, hΦ⟩ :=
    B3CHART.exists_algebra_ringEquiv e K Ab A hcoeff _ (M * p) hfield j₂ hj₂'
  obtain ⟨Ψ, hΨ⟩ := B3CHART.exists_ringEquiv e K Ab A hcoeff _ (M * p) hfield j₂ hj₂'
  exact ⟨e, K, hKfd, hK, Ab, hlies, hA, hdom, hcoeff, ϖb, hϖbe, hϖb, ε, hε, hpε, hfield,
    inst, hlaw, jK, hjK, hfact, Φ, hΦ, Ψ, hΨ⟩

end S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul
end P2MW
export P2MW.S_ModularCurve_XZeroP_exists_ringHom_valuationSubring_algebra_ringEquiv_chartAlgFin_coeffSubring_fieldOver_twoChartIntegralModel_gamma0_mul (solution)
