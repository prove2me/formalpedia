-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/bdba62f6-5896-59d3-8807-49fbd46a4f0d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReductionMap
import Theorems.Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC qExpFunctionFieldC intFormRatiosC_subset jNum coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index JOneES.exists_transcendental_finiteDimensional_laurentBaseChange transcendental_jqModC jqModC_mem_intFormRatiosC"
namespace DegKDeuring
p2m_open "ModularCurve"

section Residue

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

include hA in
theorem isAlgebraic_residueField :
    letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
      (Fact.out : p.Prime) hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := by
  letI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def
    (Fact.out : p.Prime) hA
  letI := ZMod.algebra (IsLocalRing.ResidueField A) p
  have hp : p.Prime := Fact.out
  refine ⟨fun ybar => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective ybar

  have hyQ : IsAlgebraic ℚ (y : AlgebraicClosure ℚ) := by
    have h := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (y : AlgebraicClosure ℚ)
    convert h using 2
    rfl
    rfl
  have hyalg : IsAlgebraic ℤ (y : AlgebraicClosure ℚ) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr hyQ
  obtain ⟨P, hP0, hPy⟩ := hyalg
  set Q := P.primPart with hQ
  have hc0 : P.content ≠ 0 := fun h => hP0 (content_eq_zero_iff.mp h)
  have hQy : aeval (y : AlgebraicClosure ℚ) Q = 0 := by
    have h1 : aeval (y : AlgebraicClosure ℚ) (C P.content * Q) = 0 := by
      rw [← eq_C_content_mul_primPart]; exact hPy
    rw [map_mul, aeval_C, mul_eq_zero] at h1
    exact h1.resolve_left ((map_ne_zero_iff _ (RingHom.injective_int _)).mpr hc0)

  have hQyA : eval₂ (Int.castRingHom A) y Q = 0 := by
    have hinj : Function.Injective A.subtype := Subtype.val_injective
    apply hinj
    rw [hom_eval₂, map_zero]
    have h2 : (A.subtype.comp (Int.castRingHom A)) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [h2]
    exact hQy

  set Qbar := Q.map (Int.castRingHom (ZMod p)) with hQbar
  have hQbar0 : Qbar ≠ 0 := by
    intro h0
    have hdvd : ∀ i, (p : ℤ) ∣ Q.coeff i := by
      intro i
      have hi := congrArg (fun R : (ZMod p)[X] => R.coeff i) h0
      simp only [hQbar, coeff_map, coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hi
    have hunit : IsUnit (p : ℤ) := (isPrimitive_primPart P) (p : ℤ) ((C_dvd_iff_dvd_coeff _ _).mpr hdvd)
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact hp.one_lt.ne' hunit
  refine ⟨Qbar, hQbar0, ?_⟩
  rw [aeval_def, hQbar, eval₂_map]
  have h3 : (algebraMap (ZMod p) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod p)) =
      (IsLocalRing.residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
  rw [h3, ← hom_eval₂, hQyA, map_zero]

end Residue

section CharZero

variable (K : Type*) [Field K]

theorem coe_eq_zero_of_mem_maximalIdeal_top {a : (⊤ : ValuationSubring K)}
    (ha : a ∈ IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) : (a : K) = 0 := by
  by_contra h
  apply (IsLocalRing.mem_maximalIdeal _).mp ha
  refine ⟨⟨a, ⟨(a : K)⁻¹, trivial⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h)
  · exact Subtype.ext (inv_mul_cancel₀ h)

def residueTopHom : IsLocalRing.ResidueField (⊤ : ValuationSubring K) →+* K :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (⊤ : ValuationSubring K)) (⊤ : ValuationSubring K).subtype
    fun _ ha => coe_eq_zero_of_mem_maximalIdeal_top K ha

end CharZero

theorem jqModC_eq_div (K : Type*) [Field K] :
    ModularCurve.jqModC K = ModularCurve.intSeriesC K ModularCurve.jNum / ModularCurve.intSeriesC K PowerSeries.X := by
  have hX : ModularCurve.intSeriesC K PowerSeries.X = HahnSeries.single 1 1 := by
    simp [ModularCurve.intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  have hne : (HahnSeries.single (1 : ℤ) (1 : K) : LaurentSeries K) ≠ 0 := by simp
  rw [hX, eq_div_iff hne, ModularCurve.jqModC, mul_comm (HahnSeries.single (-1 : ℤ) (1 : K)), mul_assoc,
    HahnSeries.single_mul_single]
  simp [ModularCurve.intSeriesC]

theorem jqModC_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    ModularCurve.jqModC L ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
  have h : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ Γ :=
    ModularCurve.intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ)
  have e : ModularCurve.coeffEmb L (ModularCurve.jqModC ℚ) = ModularCurve.jqModC L :=
    ModularCurve.map_jqModC (algebraMap ℚ L)
  exact e ▸ ModularCurve.coeffEmb_mem_laurentBaseChange L h

theorem bound_of_place (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ') (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ) (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L) (π : A →+* K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical
  have hF := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L Γ hT
  set X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ) :=
    ⟨ModularCurve.jqModC L, jqModC_mem_laurentBaseChange L Γ⟩ with hXdef
  have hXab : (X : LaurentSeries L) =
      ModularCurve.intSeriesC L ModularCurve.jNum / ModularCurve.intSeriesC L PowerSeries.X := jqModC_eq_div L
  have hxab : (x : LaurentSeries K) =
      ModularCurve.intSeriesC K ModularCurve.jNum / ModularCurve.intSeriesC K PowerSeries.X :=
    hx.trans (jqModC_eq_div K)
  have htr : Transcendental K x := by
    have hinj : Function.Injective (algebraMap (ModularCurve.qExpFunctionFieldC K Γ) (LaurentSeries K)) :=
      (algebraMap (ModularCurve.qExpFunctionFieldC K Γ) (LaurentSeries K)).injective
    rw [← transcendental_algebraMap_iff hinj]
    change Transcendental K (x : LaurentSeries K)
    rw [hx]
    exact ModularCurve.transcendental_jqModC K
  obtain ⟨hfin, hle⟩ := ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring A π Γ hF
    ModularCurve.jNum PowerSeries.X X hXab x hxab htr
  exact ⟨hfin, hle.trans (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
    L Γ hT Γ' hΓ' hneg X rfl)⟩

end ModularCurve.DegKDeuring

end

open ModularCurve.DegKDeuring in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
    haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA
    letI := ZMod.algebra (IsLocalRing.ResidueField A) p
    letI := ZMod.algebra K p
    haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := isAlgebraic_residueField p A hA
    let φ : IsLocalRing.ResidueField A →+* K :=
      (IsAlgClosed.lift (R := ZMod p) (S := IsLocalRing.ResidueField A) (M := K)).toRingHom
    exact bound_of_place K Γ hT Γ' hΓ' hneg x hx (AlgebraicClosure ℚ) A (φ.comp (IsLocalRing.residue A))
  ·
    haveI : CharZero K := CharP.charP_to_charZero K
    exact bound_of_place K Γ hT Γ' hΓ' hneg x hx K (⊤ : ValuationSubring K) (⊤ : ValuationSubring K).subtype

end S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed (solution)
