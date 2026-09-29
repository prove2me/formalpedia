-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2915327a-deb5-5bfb-b78a-4b9eedc49fef

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace InftySideExistence

private theorem _root_.InftySideExistence.exists_inftySide_place
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : ∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, IsInftySide P W := by

  haveI hprime : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  haveI : CharP (A ⧸ RingHom.ker red) q :=
    ⟨fun x => by
      rw [← map_eq_zero_iff (RingHom.kerLift red) (RingHom.kerLift_injective red), map_natCast]
      exact CharP.cast_eq_zero_iff k q x⟩
  haveI : CharP (FractionRing (A ⧸ RingHom.ker red)) q :=
    charP_of_injective_algebraMap
      (IsFractionRing.injective (A ⧸ RingHom.ker red) (FractionRing (A ⧸ RingHom.ker red))) q
  have hw := hb
  obtain ⟨c, hc, τ, hτ, hval⟩ :=
    exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty q A N
      (FractionRing (A ⧸ RingHom.ker red))
      ((algebraMap (A ⧸ RingHom.ker red) (FractionRing (A ⧸ RingHom.ker red))).comp
        (Ideal.Quotient.mk (RingHom.ker red)))
      data hKr hα hqN b hw
  refine ⟨c, Place.mem_fiberAlong.mpr hc, ?_, τ, ?_, hval⟩
  ·
    intro a
    have hJ : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = jFun N q :=
      Subtype.ext (coe_heckeAlphaBar _ _ _)
    have h := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα c
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, AlgHom.commutes, hJ, hc] at h
    rw [h]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hw a)
  ·
    have h1 : (Ideal.Quotient.mk (RingHom.ker red) τ : A ⧸ RingHom.ker red) = 1 := by
      apply IsFractionRing.injective (A ⧸ RingHom.ker red) (FractionRing (A ⧸ RingHom.ker red))
      rw [map_one]
      rw [RingHom.comp_apply] at hτ
      exact hτ
    have h2 : τ - 1 ∈ RingHom.ker red := by
      rw [← Ideal.Quotient.eq, h1, map_one]
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h2
    exact h2

p2m_export "InftySideExistence" "exists_inftySide_place"
end InftySideExistence

namespace FibreDegree

private theorem finrankAlong_heckeAlphaBar (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) :
    finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  obtain ⟨τ, hτα, hτβ⟩ :=
    exists_algEquiv_comp_heckeAlphaBar_eq_heckeBetaBar (AlgebraicClosure ℚ) N q σ hσ
  have hβ : finrankAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) = q + 1 := by
    rw [finrankAlong_heckeBetaBar, if_neg hqN]
  have h1 := finrankAlong_comp (heckeAlphaBar (AlgebraicClosure ℚ) N q) τ.toAlgHom
  have h2 := finrankAlong_comp (heckeBetaBar (AlgebraicClosure ℚ) N q) τ.toAlgHom
  rw [hτα] at h1
  rw [hτβ] at h2

  have htt : (q + 1) * 1 = (q + 1) * (finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom *
      finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom) := by
    rw [mul_one, ← mul_assoc, ← hβ, ← h2, ← h1]
  have ht1 : finrankAlong (AlgebraicClosure ℚ) τ.toAlgHom = 1 :=
    Nat.eq_one_of_mul_eq_one_right (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos q) htt).symm
  rw [h2, hβ, ht1, mul_one]

private theorem sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N) (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = q + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hfin := finiteAlong_heckeAlphaBar_of_prime (AlgebraicClosure ℚ) N q
  have hsep := separableAlong_of_charZero (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
  have hsum := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong
    (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hfin hsep b
  rw [finrankAlong_heckeAlphaBar N q hqN] at hsum
  have hsum' : (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = ((q + 1 : ℕ) : ℤ) := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun W _ => ?_
    rw [inertiaDegAlong_eq_one_laurentBaseChange (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W,
      Nat.cast_one, mul_one]
  rw [hsum', Nat.cast_add, Nat.cast_one]

end FibreDegree

namespace CuspSheetInputs

private theorem _root_.CuspSheetInputs.exists_inftySide_place
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : ∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0)
    :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, IsInftySide P W := by
  exact InftySideExistence.exists_inftySide_place hqN P b hb

p2m_export "CuspSheetInputs" "exists_inftySide_place"

private theorem sum_fiber_eq
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : ∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0)
    :
    (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = (q : ℤ) + 1 := by
  have _ := P
  have _ := hb
  exact FibreDegree.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN b

end CuspSheetInputs

open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : ∀ a : A, b.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 := by
  obtain ⟨W₀, hW₀, hinf₀⟩ := CuspSheetInputs.exists_inftySide_place hqN P b hb
  have htot := CuspSheetInputs.sum_fiber_eq hqN P b hb
  have hnn : ∀ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
      (0 : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := fun W _ => by positivity
  have hone : (1 : ℤ) ≤ (W₀.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    exact_mod_cast Place.one_le_ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W₀

  have hlow : (1 : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
    hone.trans (Finset.single_le_sum (fun W hW => hnn W (Finset.mem_filter.mp hW).1)
      (Finset.mem_filter.mpr ⟨hW₀, hinf₀⟩))

  have hcomp := le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong hqN P b

  have hsplit : (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      + (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (fun W => ¬ IsInftySide P W),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      = ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    convert Finset.sum_filter_add_sum_filter_not (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b) (IsInftySide P)
      (fun W => (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
  rw [htot] at hsplit
  omega

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_jq_sub_nonpos (solution)
