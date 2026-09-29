-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9c44d813-2772-5705-bc73-38ccdb26c533

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_isIntegral_adjoin_mk_coeffMap
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace B69E4

local notation "𝕂" => AlgebraicClosure ℚ

theorem isIntegral_adjoin_jGeomGen_jNGeomGen (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (Algebra.adjoin K ({jGeomGen K N} : Set (modularFunctionFieldC K N))) (jNGeomGen K N) := by
  have hz : jqNModC K N = ((Polynomial.X : Polynomial (Polynomial K)).map
      (Polynomial.aeval (jqModC K)).toRingHom).eval (jqNModC K N) := by
    rw [Polynomial.map_X, Polynomial.eval_X]
  have hmem : coeffMap (RingHom.id K) (jqNModC K N) ∈ modularFunctionFieldC K N := by
    rw [coeffMap_id]; exact jqNModC_mem K N
  have h := ModularCurve.isIntegral_adjoin_mk_coeffMap (RingHom.id K) N Polynomial.X (jqNModC K N) hz hmem
  have e : (⟨coeffMap (RingHom.id K) (jqNModC K N), hmem⟩ : modularFunctionFieldC K N) = jNGeomGen K N :=
    Subtype.ext (coeffMap_id _)
  rw [e] at h
  exact h

theorem isAffineGeomPlace_of_jGeomGen_mem {K : Type*} [Field K] {N : ℕ} [NeZero N]
    (v : Place K (modularFunctionFieldC K N)) (hj : jGeomGen K N ∈ v.toValuationSubring) :
    IsAffineGeomPlace K N v :=
  ⟨hj, v.mem_toValuationSubring_of_isIntegral_adjoin hj (isIntegral_adjoin_jGeomGen_jNGeomGen K N)⟩

section Packet

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral 𝕂 N q}
  {hβ : HeckeBetaBarIntegral 𝕂 N q}

def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (modularFunctionField_le_full N (jq_mem N))⟩

theorem mem_of_ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (g : F) (c : K) (h : 0 < v.ord (g - algebraMap K F c)) :
    g ∈ v.toValuationSubring := by
  have hcm : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hdm : g - algebraMap K F c ∈ v.toValuationSubring := by
    by_cases h0 : g - algebraMap K F c = 0
    · rw [h0]; exact zero_mem _
    · exact v.mem_of_ord_nonneg h0 h.le
  have := add_mem hdm hcm
  rwa [sub_add_cancel] at this

theorem isAffineGeomPlace_sp_of_ord_pos (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place 𝕂 (modularFunctionFieldBar N)) (a : A)
    (h : 0 < w.ord (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂))) :
    IsAffineGeomPlace k N (P.sp w) :=
  isAffineGeomPlace_of_jGeomGen_mem _
    (mem_of_ord_sub_algebraMap_pos (P.sp w) (jGeomGen k N) (red a) (P.d0_j w a h))

theorem forall_ord_le_zero_of_not_isAffineGeomPlace_sp (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place 𝕂 (modularFunctionFieldBar N)) (hw : ¬ IsAffineGeomPlace k N (P.sp w)) :
    ∀ a : A, w.ord (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) ≤ 0 :=
  fun a => not_lt.mp fun h => hw (isAffineGeomPlace_sp_of_ord_pos P w a h)

end Packet

section Bridge

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

theorem exists_place_over_hasValue_tInfty (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral 𝕂 N q) (hqN : ¬ q ∣ N)
    (w : Place 𝕂 (modularFunctionFieldBar N))
    (hw : ∀ a : A, w.ord (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) ≤ 0) :
    ∃ c : Place 𝕂 (modularFunctionFieldBar (N * q)),
      c.restrictAlong (heckeAlphaBar 𝕂 N q) hα = w ∧
      ∃ τ : A, red τ = 1 ∧ c.HasValue (tInfty N q) (τ : 𝕂) := by
  classical
  set I : Ideal A := RingHom.ker red with hI
  haveI : I.IsPrime := RingHom.ker_isPrime red
  let k₀ : Type := FractionRing (A ⧸ I)
  let red₀ : A →+* k₀ := (algebraMap (A ⧸ I) k₀).comp (Ideal.Quotient.mk I)

  have hqA : ((q : ℕ) : A) ∈ I := by
    rw [hI, RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hq0 : ((q : ℕ) : k₀) = 0 := by
    have : red₀ (q : A) = 0 := by
      simp only [red₀, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hqA, map_zero]
    rwa [map_natCast] at this
  haveI : CharP k₀ q := by
    apply ringChar.of_eq
    have hdvd : ringChar k₀ ∣ q := (ringChar.spec k₀ q).mp hq0
    rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exfalso
      have : ((1 : ℕ) : k₀) = 0 := (ringChar.spec k₀ 1).mpr (by rw [h1])
      rw [Nat.cast_one] at this
      exact one_ne_zero this
    · exact h1
  obtain ⟨c, hc, τ, hτ, hval⟩ :=
    ModularCurve.exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty q A N k₀ red₀ data hKr hα
      hqN w hw
  refine ⟨c, hc, τ, ?_, hval⟩

  have h1 : (Ideal.Quotient.mk I τ : A ⧸ I) = 1 := by
    apply IsFractionRing.injective (A ⧸ I) k₀
    rw [map_one]
    simpa [red₀] using hτ
  have h2 : τ - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, h1, map_one]
  rw [hI, RingHom.mem_ker, map_sub, map_one] at h2
  exact sub_eq_zero.mp h2

end Bridge

section Clauses

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring 𝕂}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral 𝕂 N q}
  {hβ : HeckeBetaBarIntegral 𝕂 N q}

theorem inftySide (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    ∃ C : Place 𝕂 (modularFunctionFieldBar (N * q)), IsInftySide P C ∧ P.reduceFst C = v := by
  obtain ⟨w, hw⟩ := P.d4 v
  have hwc : ∀ a : A, w.ord (jBarN N - algebraMap 𝕂 (modularFunctionFieldBar N) (a : 𝕂)) ≤ 0 :=
    forall_ord_le_zero_of_not_isAffineGeomPlace_sp P w (by rw [hw]; exact hv)
  obtain ⟨c, hcα, τ, hτ, hval⟩ := exists_place_over_hasValue_tInfty red data hKr hα hqN w hwc
  have hred : P.reduceFst c = v := by
    show P.sp (c.restrictAlong (heckeAlphaBar 𝕂 N q) hα) = v
    rw [hcα, hw]
  refine ⟨c, ⟨?_, τ, hτ, hval⟩, hred⟩
  exact isCuspidal_of_not_isAffineGeomPlace_reduceFst P c (by rw [hred]; exact hv)

theorem zeroSide (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    ∃ C : Place 𝕂 (modularFunctionFieldBar (N * q)), IsZeroSide P C ∧ P.reduceSnd C = v := by
  obtain ⟨C₁, h₁, hr⟩ := inftySide hqN P v hv
  refine ⟨atkinLehnerBar N q • C₁, (isZeroSide_atkinLehnerBar_smul_iff P hqN C₁).mpr h₁, ?_⟩
  rw [reduceSnd_atkinLehnerBar_smul P hqN C₁, hr]

end Clauses

end B69E4

end

open B69E4 in

theorem solution {q : ℕ}
    [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    (∃ C : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        ProlongationTuple.IsInftySide P C ∧ P.reduceFst C = v) ∧
      (∃ C : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        ProlongationTuple.IsZeroSide P C ∧ P.reduceSnd C = v) :=
  ⟨inftySide hqN P v hv, zeroSide hqN P v hv⟩

end S_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace (solution)
