-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/08f65e84-62f6-5025-9f92-d3db1c93eadd

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

open ModularCurve.DRModelPackageLevel in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (W : Fin 2 → ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))

    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 0 ↔
      ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y = ModularCurve.coeffMap (Int.castRingHom ℚ) x)

    (hW₁ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W 1 ↔ ModularCurve.atkinLehnerInvolutionFull N₀ q f ∈ W 0)
    (hne : W 0 ≠ W 1)

    (habove : ∀ i, ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits ∧
      (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P ∈ W i ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P)⁻¹ ∈ W i) ∧
      (∀ f ∈ (W i).nonunits, f * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ∈ W i))

    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)),
      ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ V.nonunits →
      (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q)))
            ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ P)⁻¹ ∈ V) →
      V = W 0 ∨ V = W 1) :
    ∃ P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      (∀ (i : Fin 2) (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)), a ∈ P i ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits)) ∧
      (∀ i, (P i).IsPrime) ∧ P 0 ≠ P 1 ∧
      (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes = {P 0, P 1} := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqprime : q.Prime := Fact.out
  have hqℤ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime

  have hjeq : (⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N₀ * q) (ModularCurve.jq_mem (N₀ * q))⟩ : ↥(modularFunctionFieldFull (N₀ * q))) =
      IgusaScheme.jFull (N₀ * q) := rfl

  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  have hϖ : Prime ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) := (GaloisRep.irreducible_natCast_ratLocalizedAt q hqprime).prime

  have hL : ∀ c : ℤ, ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) ∣ (c : ↥(GaloisRep.ratLocalizedAt q)) → (q : ℤ) ∣ c := by
    intro c hdvd
    by_contra hnd
    obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hqℤ).mpr hnd
    have h1 : (s : ↥(GaloisRep.ratLocalizedAt q)) * ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) + (t : ↥(GaloisRep.ratLocalizedAt q)) * (c : ↥(GaloisRep.ratLocalizedAt q)) = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ↥(GaloisRep.ratLocalizedAt q))) hst
    apply hϖ.not_unit
    refine isUnit_of_dvd_one ?_
    rw [← h1]
    exact dvd_add (dvd_mul_left _ _) (hdvd.mul_left _)

  have hbridge : ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod q)) ≠ 0 →
      ¬ (Polynomial.C ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) ∣ P.map (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt q))) := by
    intro P hP hdvd
    apply hP
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd n
    rw [Polynomial.coeff_map, eq_intCast] at this
    exact_mod_cast hL _ this
  have haevalZ : ∀ P : Polynomial ℤ,
      Polynomial.aeval (IgusaScheme.jFull (N₀ * q)) (P.map (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt q))) =
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull (N₀ * q))) (IgusaScheme.jFull (N₀ * q)) P := by
    intro P
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]

  have hqW : ∀ i, (W i).valuation (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))) < 1 := fun i =>
    (ValuationSubring.mem_nonunits_iff _).mp (habove i).1
  have hjW : ∀ i, (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W i := by
    intro i
    have := ((habove i).2.1 Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    simp only [Polynomial.eval₂_X] at this
    exact this

  have hinvW : ∀ (V : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q))), V.valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) < 1 →
      ∀ b : ℤ, ¬ ((q : ℤ) ∣ b) → ((b : ↥(modularFunctionFieldFull (N₀ * q))))⁻¹ ∈ V := by
    intro V hqV b hb
    obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hqℤ).mpr hb
    have hb0 : (b : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by
      have : b ≠ 0 := fun h => hb (h ▸ dvd_zero _)
      exact_mod_cast this
    have hge : ¬ V.valuation ((b : ↥(modularFunctionFieldFull (N₀ * q)))) < 1 := by
      intro hlt
      have h1 : (s : ↥(modularFunctionFieldFull (N₀ * q))) * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) + (t : ↥(modularFunctionFieldFull (N₀ * q))) * (b : ↥(modularFunctionFieldFull (N₀ * q))) = 1 := by
        have := congrArg (fun z : ℤ => (z : ↥(modularFunctionFieldFull (N₀ * q)))) hst
        push_cast at this
        exact this
      have hv1 : V.valuation ((s : ↥(modularFunctionFieldFull (N₀ * q))) * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) + (t : ↥(modularFunctionFieldFull (N₀ * q))) * (b : ↥(modularFunctionFieldFull (N₀ * q)))) < 1 := by
        refine lt_of_le_of_lt (V.valuation.map_add _ _) (max_lt ?_ ?_)
        · rw [map_mul]
          calc V.valuation (s : ↥(modularFunctionFieldFull (N₀ * q))) * V.valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q)))
              ≤ 1 * V.valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) := mul_le_mul_left ((V.valuation_le_one_iff _).mpr (intCast_mem V s)) _
            _ < 1 := by rw [one_mul]; exact hqV
        · rw [map_mul]
          calc V.valuation (t : ↥(modularFunctionFieldFull (N₀ * q))) * V.valuation (b : ↥(modularFunctionFieldFull (N₀ * q)))
              ≤ 1 * V.valuation (b : ↥(modularFunctionFieldFull (N₀ * q))) := mul_le_mul_left ((V.valuation_le_one_iff _).mpr (intCast_mem V t)) _
            _ < 1 := by rw [one_mul]; exact hlt
      rw [h1, map_one] at hv1
      exact lt_irrefl _ hv1
    refine (V.valuation_le_one_iff _).mp ?_
    rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hb0)]
    exact not_lt.mp hge

  have hZW : ∀ i (x : ↥(GaloisRep.ratLocalizedAt q)), algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (N₀ * q)) x ∈ W i := by
    intro i x
    have hx : algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(modularFunctionFieldFull (N₀ * q)) x = algebraMap ℚ ↥(modularFunctionFieldFull (N₀ * q)) (x : ℚ) := rfl
    have hden : ¬ q ∣ (x : ℚ).den := (GaloisRep.mem_ratLocalizedAt_iff hqprime (x : ℚ)).mp x.2
    have hden' : ¬ ((q : ℤ) ∣ ((x : ℚ).den : ℤ)) := by exact_mod_cast hden
    rw [hx, ← Rat.num_div_den (x : ℚ), map_div₀, map_intCast, map_natCast, div_eq_mul_inv]
    refine mul_mem (intCast_mem (W i) _) ?_
    have := hinvW (W i) (hqW i) ((x : ℚ).den : ℤ) hden'
    simpa using this

  have hadjW : ∀ i, ∀ y ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q))), y ∈ W i := by
    intro i y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff.mp hz]; exact hjW i
    | algebraMap r => exact hZW i r
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

  have hAW : ∀ i (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)), (a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W i := by
    intro i a
    have ha : IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q)))) (a : ↥(modularFunctionFieldFull (N₀ * q))) := a.2
    let φ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q)))) →+* ↥(W i) :=
      (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt q) ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q)))).val.toRingHom.codRestrict (W i).toSubring
        fun y => hadjW i y y.2
    have ha' : IsIntegral ↥(W i) (a : ↥(modularFunctionFieldFull (N₀ * q))) := ha.map_of_comp_eq φ (RingHom.id ↥(modularFunctionFieldFull (N₀ * q))) (by ext; rfl)
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥(W i)) (K := ↥(modularFunctionFieldFull (N₀ * q)))).mp ha'
    rw [← hy]
    exact y.2

  let toW : ∀ i, ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →+* ↥(W i) := fun i =>
    (IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom.codRestrict (W i).toSubring fun a => hAW i a
  let P : Fin 2 → Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := fun i => (IsLocalRing.maximalIdeal ↥(W i)).comap (toW i)
  have hPmem : ∀ (i : Fin 2) (a : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)), a ∈ P i ↔ ((a : ↥(modularFunctionFieldFull (N₀ * q))) ∈ (W i).nonunits) := by
    intro i a
    show toW i a ∈ IsLocalRing.maximalIdeal ↥(W i) ↔ _
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hPprime : ∀ i, (P i).IsPrime := fun i => Ideal.IsPrime.comap _

  have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
    apply IntermediateField.adjoin.mono
    rintro x ⟨d, hd, hdq, rfl⟩
    exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
  have hmem : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) :=
    hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
  obtain ⟨huA, hvA⟩ := modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmem
  set uF : ↥(modularFunctionFieldFull (N₀ * q)) := ⟨modularUnitSeries q, hmem⟩ with huF
  let uA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨uF, huA⟩
  let vA : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨(q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹, hvA⟩
  obtain ⟨-, -, ⟨huW0, huinvW0⟩, ⟨hu'W1, hu'invW1⟩⟩ :=
    ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd N₀ q hqN hmem (W 0) (W 1) hW₀ hW₁
  have huF0 : uF ≠ 0 := by
    intro h
    have := congrArg (fun x : ↥(modularFunctionFieldFull (N₀ * q)) => (x : LaurentSeries ℚ)) h
    simp only [huF] at this
    exact (ModularCurve.modularUnitSeries_ne_zero q) (by simpa using this)
  have hq0 : ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ≠ 0 := by exact_mod_cast hqprime.ne_zero
  have hu0 : uA ∉ P 0 := by
    intro h
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 0 uA).mp h)
    have hle1 : (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact huF0)] at hle1
    exact not_lt.mpr hle1 hlt
  have hu1 : uA ∈ P 1 := by
    refine (hPmem 1 uA).mpr ((ValuationSubring.mem_nonunits_iff _).mpr ?_)
    have hfac : (uF : ↥(modularFunctionFieldFull (N₀ * q))) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) * ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := by
      rw [inv_mul_cancel_right₀ (pow_ne_zero _ hq0)]
    change (W 1).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q))) < 1
    rw [hfac, map_mul, map_pow]
    have h1 : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) ≤ 1 := ((W 1).valuation_le_one_iff _).mpr hu'W1
    calc (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) * (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12
        ≤ 1 * (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := mul_le_mul_left h1 _
      _ = (W 1).valuation ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le' (hqW 1) (by norm_num)
  have hv0 : vA ∈ P 0 := by
    refine (hPmem 0 vA).mpr ((ValuationSubring.mem_nonunits_iff _).mpr ?_)
    show (W 0).valuation ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹) < 1
    rw [map_mul, map_pow]
    have h1 : (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
    have hqq : (q : ↥(modularFunctionFieldFull (N₀ * q))) = ((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) := rfl
    calc (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * (W 0).valuation (uF : ↥(modularFunctionFieldFull (N₀ * q)))⁻¹
        ≤ (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * 1 := mul_le_mul_right h1 _
      _ = (W 0).valuation (q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 := mul_one _
      _ < 1 := by rw [hqq]; exact pow_lt_one₀ zero_le' (hqW 0) (by norm_num)
  have hv1 : vA ∉ P 1 := by
    intro h
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 1 vA).mp h)
    have hv : ((q : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12 * uF⁻¹) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ := by
      rw [mul_inv, inv_inv]; exact mul_comm _ _
    have hle1 : (W 1).valuation (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹) ≤ 1 := ((W 1).valuation_le_one_iff _).mpr hu'W1
    have hlt' : (W 1).valuation ((uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹) < 1 := by
      have : (vA : ↥(modularFunctionFieldFull (N₀ * q))) = (uF * (((q : ℕ) : ↥(modularFunctionFieldFull (N₀ * q))) ^ 12)⁻¹)⁻¹ := hv
      rw [← this]; exact hlt
    rw [map_inv₀, inv_lt_one₀ (by
      rw [Valuation.pos_iff]; exact mul_ne_zero huF0 (inv_ne_zero (pow_ne_zero _ hq0)))] at hlt'
    exact not_lt.mpr hle1 hlt'
  have hne : P 0 ≠ P 1 := fun h => hu0 (h ▸ hu1)
  have hn10 : ¬ P 1 ≤ P 0 := fun h => hu0 (h hu1)
  have hn01 : ¬ P 0 ≤ P 1 := fun h => hv1 (h hv0)

  have htjℚ : Transcendental ℚ (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) := by
    intro halg
    obtain ⟨r, hr, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨r, hr, ?_⟩
    have h0 : (algebraMap ↥(modularFunctionFieldFull (N₀ * q)) (LaurentSeries ℚ)) ((Polynomial.aeval (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q)))) r) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull (N₀ * q)) (LaurentSeries ℚ)) (IgusaScheme.jFull (N₀ * q)) = jq from
          IgusaScheme.coe_jFull (N₀ * q)] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  have htj : Transcendental ↥(GaloisRep.ratLocalizedAt q) (IgusaScheme.jFull (N₀ * q) : ↥(modularFunctionFieldFull (N₀ * q))) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff ↥(GaloisRep.ratLocalizedAt q) ℚ ↥(modularFunctionFieldFull (N₀ * q))).mp h)
  have hFD := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull (N₀ * q)
  haveI := hFD
  have hsep : Algebra.IsSeparable
      ↥(IntermediateField.adjoin ℚ ({IgusaScheme.jFull (N₀ * q)} : Set ↥(modularFunctionFieldFull (N₀ * q)))) ↥(modularFunctionFieldFull (N₀ * q)) := inferInstance
  have hspan : Ideal.span {algebraMap ↥(GaloisRep.ratLocalizedAt q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q) ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q))} = Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))} := by
    rw [map_natCast]
  have hS0 : ∀ 𝔮 : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q), 𝔮 ∈ (Ideal.span {((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))}).minimalPrimes → 𝔮 = P 0 ∨ 𝔮 = P 1 := by
    intro 𝔮 h𝔮
    rw [← hspan] at h𝔮
    obtain ⟨V, -, -, hcen, hqV, hgenV⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin ↥(GaloisRep.ratLocalizedAt q) ℚ ↥(modularFunctionFieldFull (N₀ * q))
        (IgusaScheme.jFull (N₀ * q)) htj hFD hsep ((q : ℕ) : ↥(GaloisRep.ratLocalizedAt q)) hϖ 𝔮 h𝔮
    have hV : V = W 0 ∨ V = W 1 := by
      apply hcomplete V
      · simpa [map_natCast] using hqV
      · intro Q hQ
        have := hgenV (Q.map (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt q))) (hbridge Q hQ)
        rwa [haevalZ] at this
    rcases hV with rfl | rfl
    · left; ext a; exact (hcen a).trans (hPmem 0 a).symm
    · right; ext a; exact (hcen a).trans (hPmem 1 a).symm

  refine ⟨P, hPmem, hPprime, hne, ?_⟩
  have hqP : ∀ i, ((q : ℕ) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ∈ P i := fun i =>
    (hPmem i _).mpr (by simpa using (habove i).1)
  ext 𝔮
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact hS0 𝔮
  · rintro (rfl | rfl)
    · obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (hqP 0))
      rcases hS0 𝔮 h𝔮min with rfl | rfl
      · exact h𝔮min
      · exact (hn10 h𝔮le).elim
    · obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr (hqP 1))
      rcases hS0 𝔮 h𝔮min with rfl | rfl
      · exact (hn01 h𝔮le).elim
      · exact h𝔮min

end S_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair (solution)
