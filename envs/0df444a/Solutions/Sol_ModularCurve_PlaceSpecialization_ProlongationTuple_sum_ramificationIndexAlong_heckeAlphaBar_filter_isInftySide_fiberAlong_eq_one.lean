-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/26405901-4d99-5dc3-a056-42abbe7fc30a

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
import Theorems.Thm_ModularCurve_exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization.ProlongationTuple

namespace JacJ9SLeg1

private theorem ord_sub_algebraMap_nonpos {N : ℕ} [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (J : modularFunctionFieldBar N) (hb : b.ord J < 0) (a : A) :
    b.ord (J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ)) ≤ 0 := by
  rw [← not_lt]
  intro hlt
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hb
    exact lt_irrefl _ hb
  have hxmem : J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a : AlgebraicClosure ℚ) ∈ b.toValuationSubring := by
    by_cases hx0 : J - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (a : AlgebraicClosure ℚ) = 0
    · rw [hx0]
      exact zero_mem _
    · exact (b.mem_iff_ord_nonneg hx0).mpr hlt.le
  have hJmem : J ∈ b.toValuationSubring := by
    have h := add_mem hxmem (b.algebraMap_mem' (a : AlgebraicClosure ℚ))
    rwa [sub_add_cancel] at h
  have h0 := (b.mem_iff_ord_nonneg hJ0).mp hJmem
  omega

private theorem _root_.JacJ9SLeg1.leg1_exists_inftySide
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, IsInftySide P W := by

  haveI hprime : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  haveI : CharP (A ⧸ RingHom.ker red) q :=
    ⟨fun x => by
      rw [← map_eq_zero_iff (RingHom.kerLift red) (RingHom.kerLift_injective red), map_natCast]
      exact CharP.cast_eq_zero_iff k q x⟩
  haveI : CharP (FractionRing (A ⧸ RingHom.ker red)) q :=
    charP_of_injective_algebraMap
      (IsFractionRing.injective (A ⧸ RingHom.ker red) (FractionRing (A ⧸ RingHom.ker red))) q
  have hw := ord_sub_algebraMap_nonpos A b _ hb
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

p2m_export "JacJ9SLeg1" "leg1_exists_inftySide"
end JacJ9SLeg1

namespace J3LegS

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

end J3LegS

namespace JacJ9SLeg3

private theorem exists_algEquiv_apply_eq_pow_of_pow_eq_one (N q : ℕ) [NeZero N] [Fact q.Prime]
    (hqN : ¬ q ∣ N) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ q := by
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  have hcop : q.Coprime N := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hqN
  have hζq : IsPrimitiveRoot (ζ₀ ^ q) N := hζ₀.pow_of_coprime q hcop
  have hconj : IsConjRoot ℚ (ζ₀ ^ q) ζ₀ := by
    rw [isConjRoot_def, ← Polynomial.cyclotomic_eq_minpoly_rat hζq (NeZero.pos N),
      ← Polynomial.cyclotomic_eq_minpoly_rat hζ₀ (NeZero.pos N)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ, fun μ hμ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

private theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

private theorem restrictAlong_smul_eq {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral)
    (hβ : β.toRingHom.IsIntegral) (g : F' ≃ₐ[K] F') (h : ∀ x, g (β x) = α x)
    (W : Place K F') : (g • W).restrictAlong α hα = W.restrictAlong β hβ := by
  apply Place.ext
  ext x
  rw [mem_restrictAlong_iff, mem_restrictAlong_iff, Place.smul_toValuationSubring, ← h x]
  exact ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (x := β x)

private theorem jFun_ne_zero (N q : ℕ) [NeZero N] [NeZero q] : jFun N q ≠ 0 := fun h => by
  have h0 : ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr jq_ne_zero
  rw [h, ZeroMemClass.coe_zero] at h0
  exact h0 rfl

private theorem jQFun_ne_zero (N q : ℕ) [NeZero N] [NeZero q] : jQFun N q ≠ 0 := fun h => by
  have h0 : ((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 :=
    (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr ((map_ne_zero (qExpand ℚ q)).mpr jq_ne_zero)
  rw [h, ZeroMemClass.coe_zero] at h0
  exact h0 rfl

private theorem _root_.JacJ9SLeg3.leg3_exists_not_inftySide
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, ¬ IsInftySide P W ∧
      (q : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_pow_of_pow_eq_one N q hqN
  obtain ⟨W₁, W₂, -, hW₂b, -, he₂, -, hW₂a⟩ :=
    exists_pair_fiberAlong_heckeBetaBar_of_ord_neg N q hqN hα hβ σ hσ b hb

  have hAL : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull (N := N) (ℓ := q)
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨-, hβα⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hAL
  have hβα' : ∀ x, atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q x)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q x :=
    fun x => AlgHom.congr_fun hβα x
  refine ⟨atkinLehnerBar N q • W₂, ?_, ?_, ?_⟩
  ·
    rw [Place.mem_fiberAlong, restrictAlong_smul_eq _ _ hα hβ _ hβα', hW₂b]
  ·
    rw [isInftySide_atkinLehnerBar_smul_iff P hqN W₂]
    rintro ⟨-, τ, hτ, hval⟩
    have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      rw [ZeroMemClass.coe_eq_zero] at h0
      rw [h0, map_zero] at hτ
      exact zero_ne_one hτ
    have hord0 : W₂.ord (tZero N q) = 0 := hval.ord_eq_zero hτ0
    have hj0 := jFun_ne_zero N q
    have hjQ0 := jQFun_ne_zero N q

    have htZ : W₂.ord (tZero N q) = W₂.ord (jFun N q) - q * W₂.ord (jQFun N q) := by
      change W₂.ord (jFun N q / jQFun N q ^ q) = _
      rw [div_eq_mul_inv, W₂.ord_mul hj0 (inv_ne_zero (pow_ne_zero _ hjQ0)), Place.ord_inv,
        ← zpow_natCast, Place.ord_zpow]
      ring

    have hJQ : heckeBetaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = jQFun N q :=
      Subtype.ext (coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm
    have hJ : heckeAlphaBar (AlgebraicClosure ℚ) N q
        ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = jFun N q :=
      Subtype.ext (coe_heckeAlphaBar _ _ _)

    have hsJ : arithmeticGalois (modularFunctionFieldFull N) σ •
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ jq)
    have hbJ : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        = (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
          ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      have h := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull N) σ)
        (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
      rw [hsJ, hW₂a] at h
      exact h
    have hordQ : W₂.ord (jQFun N q) = q * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      rw [← hJQ, Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ W₂, hW₂b, he₂]
    have hordJ : W₂.ord (jFun N q)
        = (W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ := by
      rw [← hJ, Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W₂, ← hbJ]

    have hle : (W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) ≤ q + 1 := by
      rw [← J3LegS.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN
        (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)]
      exact Finset.single_le_sum (f := fun W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) =>
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
        (fun W _ => Nat.cast_nonneg _) (Place.mem_fiberAlong.mpr rfl)
    have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
    rw [htZ, hordJ, hordQ] at hord0
    have he' : ((W₂.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) - q * q)
        * b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩ = 0 := by
      rw [sub_mul, mul_assoc]
      exact hord0
    rcases mul_eq_zero.mp he' with h | h
    · have h2q : 2 * (q : ℤ) ≤ q * q := mul_le_mul_of_nonneg_right hq2 (by linarith)
      linarith
    · exact hb.ne h
  ·
    rw [Place.ramificationIndexAlong_smul (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      (heckeBetaBar (AlgebraicClosure ℚ) N q) (atkinLehnerBar N q) AlgEquiv.refl
      (fun x => (hβα' x).symm) W₂, he₂]

p2m_export "JacJ9SLeg3" "leg3_exists_not_inftySide"
end JacJ9SLeg3

namespace JacJ9S

private theorem _root_.JacJ9S.leg1_exists_inftySide
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, IsInftySide P W := by
  exact JacJ9SLeg1.leg1_exists_inftySide hqN P b hb

p2m_export "JacJ9S" "leg1_exists_inftySide"

private theorem leg2_sum_fiber
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    :
    (∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = (q : ℤ) + 1 := by
  have _ := P
  have _ := hb
  exact J3LegS.sum_ramificationIndexAlong_heckeAlphaBar_fiberAlong hα hqN b

private theorem _root_.JacJ9S.leg3_exists_not_inftySide
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0)
    :
    ∃ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, ¬ IsInftySide P W ∧
      (q : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
  exact JacJ9SLeg3.leg3_exists_not_inftySide hqN P b hb

p2m_export "JacJ9S" "leg3_exists_not_inftySide"
end JacJ9S

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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 := by
  obtain ⟨W₀, hW₀, hinf₀⟩ := JacJ9S.leg1_exists_inftySide hqN P b hb
  obtain ⟨W₁, hW₁, hnot₁, hq₁⟩ := JacJ9S.leg3_exists_not_inftySide hqN P b hb
  have htot := JacJ9S.leg2_sum_fiber hqN P b hb
  have hnn : ∀ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b,
      (0 : ℤ) ≤ (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := fun W _ => by positivity
  have hone : (1 : ℤ) ≤ (W₀.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    exact_mod_cast Place.one_le_ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W₀

  have hlow : (1 : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
    hone.trans (Finset.single_le_sum (fun W hW => hnn W (Finset.mem_filter.mp hW).1)
      (Finset.mem_filter.mpr ⟨hW₀, hinf₀⟩))

  have hcomp : (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) :=
    hq₁.trans (Finset.single_le_sum (fun W hW => hnn W (Finset.mem_filter.mp hW).1)
      (Finset.mem_filter.mpr ⟨hW₁, hnot₁⟩))

  have hsplit : (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      + (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (fun W => ¬ IsInftySide P W),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
      = ∑ W ∈ Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b, (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by
    convert Finset.sum_filter_add_sum_filter_not (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b) (IsInftySide P)
      (fun W => (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ))
  rw [htot] at hsplit
  omega

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one (solution)
