-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/34563b4f-c799-56fd-90a3-ec878b6733c8

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq
import Theorems.Thm_LaurentSeries_exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite
import Theorems.Thm_ModularCurve_forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open AlgebraicCurve ModularCurve IsLocalRing

namespace CuspRegComb

section IntCoeff

variable {L : Type*} [Field L]

def liftSub (S : Subring L) (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ S) : LaurentSeries S where
  coeff k := ⟨x.coeff k, hx k⟩
  isPWO_support' := by
    refine x.isPWO_support.mono ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h
    exact hk (Subtype.ext h)

@[scoped simp] theorem coeff_liftSub (S : Subring L) (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ S) (k : ℤ) :
    ((liftSub S x hx).coeff k : L) = x.coeff k := rfl

theorem coeffMap_subtype_liftSub (S : Subring L) (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ S) :
    coeffMap S.subtype (liftSub S x hx) = x := by
  ext k
  rfl

theorem forall_coeff_mem_of_eq_coeffMap (S : Subring L) (y : LaurentSeries S) (k : ℤ) :
    (coeffMap S.subtype y).coeff k ∈ S := by
  rw [coeffMap_coeff]
  exact (y.coeff k).2

theorem forall_coeff_mul_mem (S : Subring L) {x y : LaurentSeries L}
    (hx : ∀ k, x.coeff k ∈ S) (hy : ∀ k, y.coeff k ∈ S) (k : ℤ) : (x * y).coeff k ∈ S := by
  have := forall_coeff_mem_of_eq_coeffMap S (liftSub S x hx * liftSub S y hy) k
  rwa [map_mul, coeffMap_subtype_liftSub, coeffMap_subtype_liftSub] at this

theorem forall_coeff_pow_mem (S : Subring L) {x : LaurentSeries L}
    (hx : ∀ k, x.coeff k ∈ S) (n : ℕ) (k : ℤ) : (x ^ n).coeff k ∈ S := by
  have := forall_coeff_mem_of_eq_coeffMap S (liftSub S x hx ^ n) k
  rwa [map_pow, coeffMap_subtype_liftSub] at this

end IntCoeff

section RatCoeff

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem exists_coeffEmb_eq_of_forall_mem_range {x : LaurentSeries L}
    (hx : ∀ k, x.coeff k ∈ Set.range (algebraMap ℚ L)) : ∃ g : LaurentSeries ℚ, coeffEmb L g = x := by
  classical
  choose r hr using hx
  refine ⟨⟨r, ?_⟩, ?_⟩
  · refine x.isPWO_support.mono ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h
    apply hk
    exact (algebraMap ℚ L).injective (by rw [hr k, h, map_zero])
  · ext k
    rw [coeffEmb_coeff]
    exact hr k

end RatCoeff

section RatDVR

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) [hq : Fact q.Prime]

abbrev ratPart : ValuationSubring ℚ := A.comap (algebraMap ℚ (AlgebraicClosure ℚ))

theorem mem_ratPart_iff (r : ℚ) : r ∈ ratPart A ↔ algebraMap ℚ (AlgebraicClosure ℚ) r ∈ A :=
  ValuationSubring.mem_comap

variable {A q}

theorem isUnit_intCast_of_not_dvd (hA : A.LiesOverPrime q) (n : ℤ) (hn : ¬ (q : ℤ) ∣ n) :
    ∃ u : A, (u : AlgebraicClosure ℚ) * (n : AlgebraicClosure ℚ) = 1 := by

  have hcop : IsCoprime n (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_dvd_right n q
    have hp : Nat.Prime q := hq.out
    rcases (Nat.dvd_prime hp).mp (by exact_mod_cast this : Int.gcd n q ∣ q) with h | h
    · exact h
    · exfalso; apply hn
      have h2 := Int.gcd_dvd_left n q
      rw [h] at h2
      exact h2
  obtain ⟨a, b, hab⟩ := hcop

  have hnA : (n : AlgebraicClosure ℚ) ∈ A := intCast_mem A n
  have hval : ¬ A.valuation (n : AlgebraicClosure ℚ) < 1 := by
    intro hlt
    have hq1 : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
    have h1 : A.valuation ((a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ)) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A a))).trans_lt hlt
      · rw [Valuation.map_mul]
        exact (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).mpr (intCast_mem A b))).trans_lt hq1
    have h2 : (a : AlgebraicClosure ℚ) * n + (b : AlgebraicClosure ℚ) * (q : ℕ) = 1 := by
      exact_mod_cast hab
    rw [h2, Valuation.map_one] at h1
    exact lt_irrefl _ h1
  have hv1 : A.valuation (n : AlgebraicClosure ℚ) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr hnA) (not_lt.mp hval)
  have hunit : IsUnit (⟨(n : AlgebraicClosure ℚ), hnA⟩ : A) := (A.valuation_eq_one_iff _).mpr hv1
  obtain ⟨u, hu⟩ := hunit
  refine ⟨↑u⁻¹, ?_⟩
  have := congrArg (fun z : A => ((↑u⁻¹ : A) : AlgebraicClosure ℚ) * (z : AlgebraicClosure ℚ)) hu
  simp only at this
  rw [← this, ← Subring.coe_mul]
  simp

end RatDVR

section RatDVR2

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} [hq : Fact q.Prime]

local notation "Qb" => AlgebraicClosure ℚ

theorem inv_natCast_q_not_mem (hA : A.LiesOverPrime q) : ((q : Qb))⁻¹ ∉ A := by
  intro h
  have hq1 : A.valuation ((q : ℕ) : Qb) < 1 := (A.mem_nonunits_iff).mp hA
  have hqA : ((q : ℕ) : Qb) ∈ A := natCast_mem A q
  have hq0 : ((q : ℕ) : Qb) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hunit : IsUnit (⟨(q : Qb), hqA⟩ : A) :=
    ⟨⟨⟨(q : Qb), hqA⟩, ⟨((q : Qb))⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hq0),
      Subtype.ext (inv_mul_cancel₀ hq0)⟩, rfl⟩
  have := (A.valuation_eq_one_iff _).mp hunit
  simp only at this
  rw [this] at hq1
  exact lt_irrefl _ hq1

theorem natCast_mem_and_inv_mem (hA : A.LiesOverPrime q) (n : ℕ) (hn : ¬ q ∣ n) :
    (n : ℚ) ∈ ratPart A ∧ ((n : ℚ))⁻¹ ∈ ratPart A := by
  refine ⟨(mem_ratPart_iff A _).mpr (by simpa using natCast_mem A n), ?_⟩
  obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd hA (n : ℤ) (by exact_mod_cast hn)
  rw [mem_ratPart_iff, map_inv₀, map_natCast]
  have hn0 : (n : Qb) ≠ 0 := by
    intro h0
    rw [Int.cast_natCast, h0, mul_zero] at hu
    exact zero_ne_one hu
  have : ((n : Qb))⁻¹ = (u : Qb) := by
    rw [Int.cast_natCast] at hu
    exact (eq_inv_of_mul_eq_one_left hu).symm
  rw [this]; exact u.2

theorem exists_unit_mul_pow_div_pow (hA : A.LiesOverPrime q) (r : ℚ) (hr : r ≠ 0) :
    ∃ (u : ℚ) (a b : ℕ), u ∈ ratPart A ∧ u⁻¹ ∈ ratPart A ∧ u ≠ 0 ∧
      r = u * (q : ℚ) ^ a / (q : ℚ) ^ b := by
  have hq1 : q ≠ 1 := hq.out.ne_one
  have hnum0 : r.num.natAbs ≠ 0 := by
    rw [ne_eq, Int.natAbs_eq_zero]; exact Rat.num_ne_zero.mpr hr
  obtain ⟨a, n', hn', hnum⟩ := Nat.exists_eq_pow_mul_and_not_dvd hnum0 q hq1
  obtain ⟨b, d', hd', hden⟩ := Nat.exists_eq_pow_mul_and_not_dvd r.den_nz q hq1
  obtain ⟨hn'mem, hn'inv⟩ := natCast_mem_and_inv_mem hA n' hn'
  obtain ⟨hd'mem, hd'inv⟩ := natCast_mem_and_inv_mem hA d' hd'
  have hn'0 : (n' : ℚ) ≠ 0 := by
    intro h0; apply hnum0; rw [hnum]
    have : n' = 0 := by exact_mod_cast h0
    rw [this, mul_zero]
  have hd'0 : (d' : ℚ) ≠ 0 := by
    intro h0; apply r.den_nz; rw [hden]
    have : d' = 0 := by exact_mod_cast h0
    rw [this, mul_zero]
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdenZ : (r.den : ℚ) = (d' : ℚ) * (q : ℚ) ^ b := by
    rw [hden]; push_cast; ring

  obtain ⟨ε, hε, hnumZ⟩ : ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ (r.num : ℚ) = ε * n' * (q : ℚ) ^ a := by
    rcases Int.natAbs_eq r.num with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [h, hnum]; push_cast; ring
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [h, hnum]; push_cast; ring
  have hεmem : ε ∈ ratPart A ∧ ε⁻¹ ∈ ratPart A ∧ ε ≠ 0 := by
    rcases hε with rfl | rfl
    · exact ⟨one_mem _, by rw [inv_one]; exact one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), by rw [inv_neg, inv_one]; exact neg_mem (one_mem _),
        neg_ne_zero.mpr one_ne_zero⟩
  refine ⟨ε * n' / d', a, b, ?_, ?_, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact mul_mem (mul_mem hεmem.1 hn'mem) hd'inv
  · rw [inv_div, div_eq_mul_inv, mul_inv]
    exact mul_mem hd'mem (mul_mem hεmem.2.1 hn'inv)
  · exact div_ne_zero (mul_ne_zero hεmem.2.2 hn'0) hd'0
  · conv_lhs => rw [← Rat.num_div_den r]
    rw [hnumZ, hdenZ]
    field_simp

theorem inv_q_not_mem_ratPart (hA : A.LiesOverPrime q) : ((q : ℚ))⁻¹ ∉ ratPart A := by
  rw [mem_ratPart_iff, map_inv₀, map_natCast]
  exact inv_natCast_q_not_mem hA

theorem q_mem_ratPart : (q : ℚ) ∈ ratPart A := by
  rw [mem_ratPart_iff, map_natCast]; exact natCast_mem A q

theorem le_of_mem_ratPart (hA : A.LiesOverPrime q) {u : ℚ} {a b : ℕ}
    (hu : u⁻¹ ∈ ratPart A) (hu0 : u ≠ 0)
    (hmem : u * (q : ℚ) ^ a / (q : ℚ) ^ b ∈ ratPart A) : b ≤ a := by
  by_contra hlt
  push Not at hlt
  apply inv_q_not_mem_ratPart hA
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero

  have key : ((q : ℚ))⁻¹ = (u * (q : ℚ) ^ a / (q : ℚ) ^ b) * u⁻¹ * (q : ℚ) ^ (b - a - 1) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt hlt
    rw [hc, show a + c + 1 - a - 1 = c by omega]
    field_simp
    ring
  rw [key]
  exact mul_mem (mul_mem hmem hu) (pow_mem q_mem_ratPart _)

theorem isDiscreteValuationRing_ratPart (hA : A.LiesOverPrime q) :
    IsDiscreteValuationRing (ratPart A) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  let p : ratPart A := ⟨(q : ℚ), q_mem_ratPart⟩
  have hp_not_unit : ¬ IsUnit p := by
    rintro ⟨w, hw⟩
    apply inv_q_not_mem_ratPart hA
    have h1 : ((w⁻¹ : (ratPart A)ˣ) : ratPart A) * p = 1 := by rw [← hw]; exact w.inv_mul
    have h2 : (((w⁻¹ : (ratPart A)ˣ) : ratPart A) : ℚ) * (q : ℚ) = 1 := by
      have := congrArg (fun z : ratPart A => (z : ℚ)) h1
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((w⁻¹ : (ratPart A)ˣ) : ratPart A).2

  have mkUnit : ∀ (u : ℚ) (hu : u ∈ ratPart A), u⁻¹ ∈ ratPart A → u ≠ 0 → IsUnit (⟨u, hu⟩ : ratPart A) := by
    intro u hu hui hu0
    exact ⟨⟨⟨u, hu⟩, ⟨u⁻¹, hui⟩, Subtype.ext (mul_inv_cancel₀ hu0), Subtype.ext (inv_mul_cancel₀ hu0)⟩, rfl⟩
  have factor : ∀ x : ratPart A, x ≠ 0 →
      ∃ (n : ℕ) (v : (ratPart A)ˣ), (x : ℚ) = ((v : ratPart A) : ℚ) * ((q : ℚ) ^ n) := by
    intro x hx
    have hx0 : (x : ℚ) ≠ 0 := fun h => hx (Subtype.ext h)
    obtain ⟨u, a, b, hu, hui, hu0, hxeq⟩ := exists_unit_mul_pow_div_pow hA (x : ℚ) hx0
    have hba : b ≤ a := le_of_mem_ratPart hA hui hu0 (hxeq ▸ x.2)
    refine ⟨a - b, (mkUnit u hu hui hu0).unit, ?_⟩
    rw [IsUnit.unit_spec, hxeq]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hba
    rw [Nat.add_sub_cancel_left, pow_add]
    field_simp
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨p, ?_, ?_⟩
  · refine ⟨hp_not_unit, ?_⟩
    intro x y hxy
    have hpq : (p : ℚ) = q := rfl
    have hx : x ≠ 0 := by
      rintro rfl; apply hq0; rw [← hpq, hxy]; simp
    have hy : y ≠ 0 := by
      rintro rfl; apply hq0; rw [← hpq, hxy]; simp
    obtain ⟨i, vx, hvx⟩ := factor x hx
    obtain ⟨j, vy, hvy⟩ := factor y hy
    have hq_eq : (q : ℚ) = ((vx : ratPart A) : ℚ) * ((vy : ratPart A) : ℚ) * ((q : ℚ) ^ (i + j)) := by
      have : (q : ℚ) = (x : ℚ) * (y : ℚ) := by rw [← hpq, hxy]; rfl
      calc (q : ℚ) = (x : ℚ) * (y : ℚ) := this
        _ = _ := by rw [hvx, hvy]; ring

    have hij : i + j = 1 := by
      rcases Nat.lt_trichotomy (i + j) 1 with h | h | h
      · exfalso
        have h0 : i + j = 0 := by omega
        rw [h0, pow_zero, mul_one] at hq_eq
        apply hp_not_unit
        have : p = (vx * vy : (ratPart A)ˣ) := Subtype.ext (by simpa using hq_eq)
        rw [this]; exact Units.isUnit _
      · exact h
      · exfalso
        apply inv_q_not_mem_ratPart hA
        obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
        have hc' : i + j = c + 2 := by omega
        set w : ℚ := ((vx : ratPart A) : ℚ) * ((vy : ratPart A) : ℚ) with hw
        have hwmem : w ∈ ratPart A := mul_mem (vx : ratPart A).2 (vy : ratPart A).2
        have hq_eq' : (q : ℚ) = w * ((q : ℚ) ^ (c + 1) * (q : ℚ)) := by
          conv_lhs => rw [hq_eq]
          rw [hc']; ring
        have h1 : (1 : ℚ) = w * (q : ℚ) ^ (c + 1) := by
          have := hq_eq'
          rw [← mul_assoc] at this
          conv_lhs at this => rw [← one_mul (q : ℚ)]
          exact mul_right_cancel₀ hq0 this
        have key : ((q : ℚ))⁻¹ = w * (q : ℚ) ^ c := by
          calc ((q : ℚ))⁻¹ = ((q : ℚ))⁻¹ * 1 := by ring
            _ = ((q : ℚ))⁻¹ * (w * (q : ℚ) ^ (c + 1)) := by rw [← h1]
            _ = w * (q : ℚ) ^ c := by field_simp; ring
        rw [key]
        exact mul_mem hwmem (pow_mem q_mem_ratPart _)
    rcases Nat.eq_zero_or_pos i with hi | hi
    · left
      rw [hi, pow_zero, mul_one] at hvx
      have : x = (vx : ratPart A) := Subtype.ext hvx
      rw [this]; exact Units.isUnit _
    · right
      have hj : j = 0 := by omega
      rw [hj, pow_zero, mul_one] at hvy
      have : y = (vy : ratPart A) := Subtype.ext hvy
      rw [this]; exact Units.isUnit _
  · intro x hx
    obtain ⟨n, v, hv⟩ := factor x hx
    refine ⟨n, ⟨v, ?_⟩⟩
    apply Subtype.ext
    change ((q : ℚ)) ^ n * ((v : ratPart A) : ℚ) = (x : ℚ)
    rw [hv, mul_comm]

end RatDVR2

section QPow
variable {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ} [hq : Fact q.Prime]
local notation "Qb" => AlgebraicClosure ℚ

theorem exists_pow_mul_mem (hA : A.LiesOverPrime q) (x : Qb) : ∃ k : ℕ, (q : Qb) ^ k * x ∈ A := by
  have halgQ : IsAlgebraic ℚ x := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x
  have halgZ : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Qb).mpr halgQ
  obtain ⟨y, hy0, hint⟩ := halgZ.exists_integral_multiple
  have hintA : IsIntegral A (y • x) := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (↥A) Qb).comp (Int.castRingHom ↥A) = algebraMap ℤ Qb :=
      RingHom.ext_int _ _
    rw [hcomp]
    exact hpx
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Qb)).mp hintA
  have hmem : (y : Qb) * x ∈ A := by
    have : (y • x : Qb) = (y : Qb) * x := zsmul_eq_mul x y
    rw [← this, ← hz]; exact z.2

  have hq1 : q ≠ 1 := hq.out.ne_one
  have hy0' : y.natAbs ≠ 0 := by rwa [ne_eq, Int.natAbs_eq_zero]
  obtain ⟨a, n', hn', hya⟩ := Nat.exists_eq_pow_mul_and_not_dvd hy0' q hq1
  obtain ⟨u, hu⟩ := isUnit_intCast_of_not_dvd hA (n' : ℤ) (by exact_mod_cast hn')
  refine ⟨a, ?_⟩

  rcases Int.natAbs_eq y with h | h
  · have : (q : Qb) ^ a * x = (u : Qb) * ((y : Qb) * x) := by
      have hy : (y : Qb) = (q : Qb) ^ a * (n' : Qb) := by
        rw [h, hya]; push_cast; ring
      rw [hy]
      rw [Int.cast_natCast] at hu
      linear_combination -((q : Qb) ^ a * x) * hu
    rw [this]; exact mul_mem u.2 hmem
  · have : (q : Qb) ^ a * x = -(u : Qb) * ((y : Qb) * x) := by
      have hy : (y : Qb) = -((q : Qb) ^ a * (n' : Qb)) := by
        rw [h, hya]; push_cast; ring
      rw [hy]
      rw [Int.cast_natCast] at hu
      linear_combination -((q : Qb) ^ a * x) * hu
    rw [this]; exact mul_mem (neg_mem u.2) hmem

end QPow

section ValLift

variable {L : Type*} [Field L] (A : ValuationSubring L)

def liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) : LaurentSeries A where
  coeff k := ⟨x.coeff k, hx k⟩
  isPWO_support' := by
    refine x.isPWO_support.mono ?_
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk ⊢
    intro h
    exact hk (Subtype.ext h)

@[scoped simp] theorem coeff_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) (k : ℤ) :
    ((liftVal A x hx).coeff k : L) = x.coeff k := rfl

theorem coeffMap_subtype_liftVal (x : LaurentSeries L) (hx : ∀ k, x.coeff k ∈ A) :
    coeffMap A.subtype (liftVal A x hx) = x := by
  ext k
  rfl

end ValLift

section FunctionField

local notation "Qb" => AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N]

abbrev jF : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

theorem coeffEmb_jq_eq_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem coeff_coeffEmb_jq_mem (A : ValuationSubring Qb) (k : ℤ) : (coeffEmb Qb jq).coeff k ∈ A := by
  rw [coeffEmb_jq_eq_jqModC, jqModC_eq_map_intCast, HahnSeries.map_coeff]
  exact intCast_mem A _

theorem coeff_jF_pow_mem (A : ValuationSubring Qb) (m : ℕ) (k : ℤ) :
    (((jF N) ^ m : ↥(modularFunctionFieldBar N)) : LaurentSeries Qb).coeff k ∈ A := by
  rw [SubmonoidClass.coe_pow]
  exact forall_coeff_pow_mem A.toSubring (coeff_coeffEmb_jq_mem A) m k

theorem jF_ne_zero : jF N ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries Qb).coeff (-1)) h
  simp only [ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at h1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  exact one_ne_zero h1

scoped instance isCurveOver_bar : IsCurveOver Qb ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N

scoped instance hasPrincipalDivisors_bar : HasPrincipalDivisors Qb ↥(modularFunctionFieldBar N) :=
  IsCurveOver.hasPrincipalDivisors

scoped instance finiteDimensional_riemannRochSpace (D : Divisor Qb ↥(modularFunctionFieldBar N)) :
    FiniteDimensional Qb ↥(riemannRochSpace D) := by
  have hC : ConstantsAreBase Qb ↥(modularFunctionFieldBar N) :=
    constantsAreBase_of_deg_eq_one (cuspInftyBar N) (deg_eq_one_modularFunctionFieldBar N _)
  haveI : FiniteDimensional Qb ↥(LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N))) := by
    rw [show LSpace (0 : Divisor Qb ↥(modularFunctionFieldBar N)) = _ from hC]
    infer_instance
  exact finiteDimensional_lSpace D

theorem exists_poleDivisor_jF : ∃ E₀ : Divisor Qb ↥(modularFunctionFieldBar N),
    ∀ v, E₀ v = max 0 (-(v.ord (jF N))) := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := Qb) (jF N) (jF_ne_zero N)
  refine ⟨Finsupp.mapRange (fun n : ℤ => max 0 (-n)) (by simp) D, fun v => ?_⟩
  rw [Finsupp.mapRange_apply, hD v]

variable {N}

theorem ord_nonneg_of_mem_riemannRochSpace {E₀ : Divisor Qb ↥(modularFunctionFieldBar N)}
    (hE₀ : ∀ v, E₀ v = max 0 (-(v.ord (jF N)))) (m : ℕ) {x : ↥(modularFunctionFieldBar N)}
    (hx : x ∈ riemannRochSpace (m • E₀)) (P : Place Qb ↥(modularFunctionFieldBar N))
    (hP : 0 ≤ P.ord (jF N)) : 0 ≤ P.ord x := by
  rcases mem_riemannRochSpace_iff.mp hx P with h | h
  · rw [h, Place.ord_zero]
  · have : (m • E₀) P = 0 := by
      rw [Finsupp.smul_apply, hE₀ P, max_eq_left (by omega), smul_zero]
    rw [this, neg_zero] at h
    exact h

theorem exists_mem_riemannRochSpace_of_cuspRegular {E₀ : Divisor Qb ↥(modularFunctionFieldBar N)}
    (hE₀ : ∀ v, E₀ v = max 0 (-(v.ord (jF N)))) {f : ↥(modularFunctionFieldBar N)} (hf : f ≠ 0)
    (hreg : ∀ P : Place Qb ↥(modularFunctionFieldBar N), 0 ≤ P.ord (jF N) → 0 ≤ P.ord f) :
    ∃ m : ℕ, f ∈ riemannRochSpace (m • E₀) := by
  classical
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := Qb) f hf
  refine ⟨Df.support.sup fun v => (-(Df v)).toNat, ?_⟩
  set m : ℕ := Df.support.sup fun v => (-(Df v)).toNat with hm
  rw [mem_riemannRochSpace_iff]
  intro P
  right
  have hbound : -(m : ℤ) ≤ P.ord f := by
    by_cases hP : P ∈ Df.support
    · have h1 : (-(Df P)).toNat ≤ m := Finset.le_sup (f := fun v => (-(Df v)).toNat) hP
      rw [← hDf P]
      omega
    · rw [Finsupp.notMem_support_iff] at hP
      rw [← hDf P, hP]
      omega
  rw [Finsupp.smul_apply, hE₀ P, nsmul_eq_mul]
  rcases le_or_gt 0 (P.ord (jF N)) with hj | hj
  · rw [max_eq_left (by omega), mul_zero, neg_zero]
    exact hreg P hj
  · rw [max_eq_right (by omega)]
    have h1 : (1 : ℤ) ≤ -(P.ord (jF N)) := by omega
    nlinarith [hbound, h1, (Nat.cast_nonneg m : (0 : ℤ) ≤ m)]

theorem arithmeticGalois_smul_jF (σ : Qb ≃ₐ[ℚ] Qb) :
    arithmeticGalois (modularFunctionFieldFull N) σ • jF N = jF N :=
  Subtype.ext (coeffMap_coeffEmb σ jq)

theorem arithmeticGalois_smul_nsmul_poleDivisor {E₀ : Divisor Qb ↥(modularFunctionFieldBar N)}
    (hE₀ : ∀ v, E₀ v = max 0 (-(v.ord (jF N)))) (m : ℕ) (σ : Qb ≃ₐ[ℚ] Qb) :
    arithmeticGalois (modularFunctionFieldFull N) σ • (m • E₀) = m • E₀ := by
  ext w
  rw [SemilinearAut.divisor_smul_apply, Finsupp.smul_apply, Finsupp.smul_apply, hE₀, hE₀]
  congr 3
  set τ := arithmeticGalois (L := Qb) (modularFunctionFieldFull N) σ with hτ
  have hfix : τ⁻¹ • jF N = jF N := by
    rw [hτ, ← map_inv]; exact arithmeticGalois_smul_jF σ⁻¹
  conv_lhs => rw [← hfix]
  exact SemilinearAut.ord_smul τ⁻¹ w (jF N)

theorem coeff_mem_range_of_forall_smul_eq (x : ↥(modularFunctionFieldBar N))
    (hx : ∀ σ : Qb ≃ₐ[ℚ] Qb, arithmeticGalois (modularFunctionFieldFull N) σ • x = x) (k : ℤ) :
    (x : LaurentSeries Qb).coeff k ∈ Set.range (algebraMap ℚ Qb) := by
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ Qb := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois ℚ Qb := IsAlgClosure.isGalois ℚ Qb
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
  intro σ
  have h := congrArg (fun z : ↥(modularFunctionFieldBar N) => (z : LaurentSeries Qb).coeff k) (hx σ)
  rw [coe_arithmeticGalois_smul, coeffMap_coeff] at h
  exact h

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single]
  exact coeffMap_single _ _ _

theorem coeffEmb_smul (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb L (r • x) = (algebraMap ℚ L r) • coeffEmb L x := by
  ext k
  rw [coeffEmb_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul, smul_eq_mul,
    map_mul]

theorem coeffEmb_smul_eq_mul (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) (x : LaurentSeries ℚ) :
    coeffEmb L (r • x) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) * coeffEmb L x := by
  rw [coeffEmb_smul, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

theorem coe_algebraMap_bar (c : Qb) :
    ((algebraMap Qb ↥(modularFunctionFieldBar N) c : ↥(modularFunctionFieldBar N)) : LaurentSeries Qb) =
      algebraMap Qb (LaurentSeries Qb) c := rfl

end FunctionField

end CuspRegComb
p2m_reactivate "P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular.CuspRegComb"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular.CuspRegComb"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open CuspRegComb

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) :
    ∃ (n : ℕ) (a : Fin n → A) (g : Fin n → LaurentSeries ℚ) (hg : ∀ i, g i ∈ modularFunctionFieldFull M'),
      (∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers) ∧
      (∀ i, ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
      (∃ hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ∀ i (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
            ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
          ∀ v : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'),
            (R₀.residue ⟨_, hj⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ v.toValuationSubring) ∧
      (f : ↥(modularFunctionFieldBar M')) =
        ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a i : AlgebraicClosure ℚ) *
          (⟨coeffEmb (AlgebraicClosure ℚ) (g i), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hg i)⟩ :
            ↥(modularFunctionFieldBar M')) := by
  classical

  have hjq : coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq :=
    (map_jqModC _).trans (coeffEmb_jq_eq_jqModC (AlgebraicClosure ℚ)).symm
  have hyj : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar M' := by
    rw [hjq]; exact (jF M').2
  have hjeq : (⟨coeffMap A.subtype (jqModC A), hyj⟩ : ↥(modularFunctionFieldBar M')) = jF M' := Subtype.ext hjq
  have hj : jF M' ∈ R₀.integers := by
    obtain ⟨h, -⟩ := hR₀ (jqModC A) hyj
    rwa [hjeq] at h

  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      ⟨hj, fun i => Fin.elim0 i⟩, ?_⟩
    simp

  obtain ⟨E₀, hE₀⟩ := exists_poleDivisor_jF M'
  obtain ⟨m, hfE⟩ := exists_mem_riemannRochSpace_of_cuspRegular hE₀ hf0 hreg
  set E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := m • E₀ with hEdef

  have hEfix : ∀ σ ∈ (Set.univ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)),
      arithmeticGalois (modularFunctionFieldFull M') σ • E = E :=
    fun σ _ => arithmeticGalois_smul_nsmul_poleDivisor hE₀ m σ
  obtain ⟨b, hb, hli, hfix⟩ :=
    exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq M' Set.univ E hEfix
  have hrat : ∀ i, ∃ g : LaurentSeries ℚ, coeffEmb (AlgebraicClosure ℚ) g = (b i : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun i => exists_coeffEmb_eq_of_forall_mem_range (AlgebraicClosure ℚ)
      (coeff_mem_range_of_forall_smul_eq (b i) (fun σ => hfix i σ (Set.mem_univ σ)))
  choose g hg using hrat
  have hgF : ∀ i, g i ∈ modularFunctionFieldFull M' := fun i =>
    mem_of_coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) _ (g i) (by rw [hg i]; exact (b i).2)

  have hbdd_b : ∀ i, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧
      ∀ k, (c • (b i : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A := by
    intro i
    have hbi0 : b i ≠ 0 := hli.ne_zero i
    have hjm0 : (jF M') ^ m ≠ 0 := pow_ne_zero _ (jF_ne_zero M')
    set h : ↥(modularFunctionFieldBar M') := b i * ((jF M') ^ m)⁻¹ with hh
    have hh0 : h ≠ 0 := mul_ne_zero hbi0 (inv_ne_zero hjm0)
    have hordpow : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        W.ord ((jF M') ^ m) = m * W.ord (jF M') := fun W => by
      rw [← zpow_natCast, Place.ord_zpow]
    have hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), W.ord h < 0 →
        ∃ a : A, 0 < W.ord (jF M' - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)) := by
      intro W hW
      refine ⟨0, ?_⟩
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
      rw [hh, W.ord_mul hbi0 (inv_ne_zero hjm0), W.ord_inv, hordpow W] at hW
      by_contra hle
      push Not at hle
      rcases lt_or_eq_of_le hle with hlt | heq
      ·
        rcases mem_riemannRochSpace_iff.mp (hb i) W with h0 | h0
        · exact hbi0 h0
        · rw [Finsupp.smul_apply, hE₀ W, max_eq_right (by omega), nsmul_eq_mul] at h0
          nlinarith [h0, hW]
      · have h0 := ord_nonneg_of_mem_riemannRochSpace hE₀ m (hb i) W (by omega)
        rw [heq] at hW
        omega
    obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A M' h hh0 hpole
    refine ⟨c, hc0, fun k => ?_⟩
    have hbeq : (b i : LaurentSeries (AlgebraicClosure ℚ)) =
        (h : LaurentSeries (AlgebraicClosure ℚ)) *
          (((jF M') ^ m : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← MulMemClass.coe_mul, hh, inv_mul_cancel_right₀ hjm0]
    rw [hbeq, ← HahnSeries.C_mul_eq_smul, ← mul_assoc, HahnSeries.C_mul_eq_smul]
    exact forall_coeff_mul_mem A.toSubring hc (coeff_jF_pow_mem M' A m) k
  have hbdd_g : ∀ i, ∃ c : ℚ, c ≠ 0 ∧ c ∈ ratPart A ∧ ∀ k, c * (g i).coeff k ∈ ratPart A := by
    intro i
    obtain ⟨c, hc0, hc⟩ := hbdd_b i
    obtain ⟨e, he⟩ := exists_pow_mul_mem hA c⁻¹
    refine ⟨(q : ℚ) ^ e, pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero),
      pow_mem q_mem_ratPart _, fun k => ?_⟩
    rw [mem_ratPart_iff, map_mul, map_pow, map_natCast]
    have h1 : algebraMap ℚ (AlgebraicClosure ℚ) ((g i).coeff k) =
        (b i : LaurentSeries (AlgebraicClosure ℚ)).coeff k := by
      rw [← hg i, coeffEmb_coeff]
    have h2 := hc k
    rw [HahnSeries.coeff_smul, smul_eq_mul] at h2
    have : (q : AlgebraicClosure ℚ) ^ e * algebraMap ℚ (AlgebraicClosure ℚ) ((g i).coeff k) =
        ((q : AlgebraicClosure ℚ) ^ e * c⁻¹) * (c * (b i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) := by
      rw [h1]; field_simp
    rw [this]
    exact mul_mem he h2

  let V : Submodule ℚ (LaurentSeries ℚ) := Submodule.span ℚ (Set.range g)
  haveI : FiniteDimensional ℚ V := FiniteDimensional.span_of_finite ℚ (Set.finite_range g)
  have hVbdd : ∀ v ∈ V, ∃ c : ℚ, c ≠ 0 ∧ c ∈ ratPart A ∧ ∀ n : ℤ, c * (v : LaurentSeries ℚ).coeff n ∈ ratPart A := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hbdd_g i
    | zero => exact ⟨1, one_ne_zero, one_mem _, fun n => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c₁, hc₁, hc₁m, h₁⟩ := hx
      obtain ⟨c₂, hc₂, hc₂m, h₂⟩ := hy
      refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, mul_mem hc₁m hc₂m, fun n => ?_⟩
      rw [HahnSeries.coeff_add, mul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm c₁, mul_assoc]; exact mul_mem hc₂m (h₁ n)
      · rw [mul_assoc]; exact mul_mem hc₁m (h₂ n)
    | smul r x _ hx =>
      obtain ⟨c, hc, hcm, h⟩ := hx
      refine ⟨c * r.den, mul_ne_zero hc (by exact_mod_cast r.den_nz), mul_mem hcm ?_, fun n => ?_⟩
      · rw [mem_ratPart_iff, map_natCast]; exact natCast_mem A _
      · rw [HahnSeries.coeff_smul, smul_eq_mul,
          show c * (r.den : ℚ) * (r * x.coeff n) = ((r.den : ℚ) * r) * (c * x.coeff n) by ring, Rat.den_mul_eq_num]
        refine mul_mem ?_ (h n)
        rw [mem_ratPart_iff, map_intCast]; exact intCast_mem A _
  haveI hDVR : IsDiscreteValuationRing (ratPart A) := isDiscreteValuationRing_ratPart hA
  obtain ⟨β, p, hβO, hpiv⟩ :=
    LaurentSeries.exists_basis_forall_coeff_mem_valuationSubring_and_coeff_eq_ite (ratPart A) V
      (fun v hv => (hVbdd v hv).imp fun c hc => ⟨hc.1, hc.2.2⟩)

  have hVle : ∀ v ∈ V, v ∈ modularFunctionFieldFull M' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hgF i
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      have : r • x = algebraMap ℚ (LaurentSeries ℚ) r * x := by
        rw [algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]
      rw [this]
      exact mul_mem (algebraMap_mem _ r) hx
  have hβF : ∀ j, ((β j : V) : LaurentSeries ℚ) ∈ modularFunctionFieldFull M' := fun j => hVle _ (β j).2
  set B : Fin (Module.finrank ℚ V) → ↥(modularFunctionFieldBar M') := fun j =>
    ⟨coeffEmb (AlgebraicClosure ℚ) ((β j : V) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hβF j)⟩ with hB
  have hBcoef : ∀ j k, ((B j : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
    intro j k
    change (coeffEmb (AlgebraicClosure ℚ) ((β j : V) : LaurentSeries ℚ)).coeff k ∈ A
    rw [coeffEmb_coeff]
    exact (mem_ratPart_iff A _).mp (hβO j k)
  set y : Fin (Module.finrank ℚ V) → LaurentSeries A := fun j => liftVal A _ (hBcoef j) with hy_def
  have hy : ∀ j, coeffMap A.subtype (y j) ∈ modularFunctionFieldBar M' := fun j => by
    rw [hy_def, coeffMap_subtype_liftVal]; exact (B j).2
  have hyB : ∀ j, (⟨coeffMap A.subtype (y j), hy j⟩ : ↥(modularFunctionFieldBar M')) = B j := fun j =>
    Subtype.ext (coeffMap_subtype_liftVal A _ _)

  have hgV : ∀ i, g i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  set r : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → Fin (Module.finrank ℚ V) → ℚ :=
    fun i j => β.repr ⟨g i, hgV i⟩ j with hr
  have hgrepr : ∀ i, g i = ∑ j, r i j • ((β j : V) : LaurentSeries ℚ) := by
    intro i
    have h1 := congrArg Subtype.val (β.sum_repr ⟨g i, hgV i⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have hbB : ∀ i, b i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')
      (algebraMap ℚ (AlgebraicClosure ℚ) (r i j)) * B j := by
    intro i
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul, coe_algebraMap_bar, hB]
    rw [← hg i, hgrepr i, map_sum]
    simp only [coeffEmb_smul_eq_mul]
  have hdpos : 0 < Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨f, hfE⟩, fun h0 => hf0 (congrArg Subtype.val h0)⟩
  haveI : Nonempty (Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E))) := ⟨⟨0, hdpos⟩⟩
  let bE : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → ↥(riemannRochSpace E) :=
    fun i => ⟨b i, hb i⟩
  have hliE : LinearIndependent (AlgebraicClosure ℚ) bE :=
    LinearIndependent.of_comp (riemannRochSpace E).subtype (by exact hli)
  let basisE := basisOfLinearIndependentOfCardEqFinrank hliE (by rw [Fintype.card_fin])
  set cf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → AlgebraicClosure ℚ :=
    fun i => basisE.repr ⟨f, hfE⟩ i with hcf
  have hfrepr : f = ∑ i, cf i • b i := by
    have h1 := congrArg Subtype.val (basisE.sum_repr ⟨f, hfE⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at h1
    simp only [Submodule.coe_smul, basisE, coe_basisOfLinearIndependentOfCardEqFinrank] at h1
    exact h1.symm
  set e : Fin (Module.finrank ℚ V) → AlgebraicClosure ℚ :=
    fun j => ∑ i, cf i * algebraMap ℚ (AlgebraicClosure ℚ) (r i j) with he_def
  have hfsum : f = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (e j) * B j := by
    rw [hfrepr]
    simp only [Algebra.smul_def, hbB, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ← map_sum, he_def]

  have hpivA : ∀ i j, (y j).coeff (p i) = if i = j then 1 else 0 := by
    intro i j
    apply Subtype.ext
    rw [hy_def, coeff_liftVal]
    change (coeffEmb (AlgebraicClosure ℚ) ((β j : V) : LaurentSeries ℚ)).coeff (p i) = _
    rw [coeffEmb_coeff, hpiv i j]
    split_ifs <;> simp
  have hsumR : (∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (e j) *
      (⟨coeffMap A.subtype (y j), hy j⟩ : ↥(modularFunctionFieldBar M'))) ∈ R₀.integers := by
    simp only [hyB]
    rw [← hfsum]
    exact hf
  have he : ∀ j, e j ∈ A :=
    forall_mem_valuationSubring_of_sum_mul_coeffMap_mem_integers_of_pivot M' A R₀ hR₀ e y hy p hpivA hsumR

  have hBint : ∀ j, B j ∈ R₀.integers := fun j => by
    obtain ⟨h, -⟩ := hR₀ (y j) (hy j)
    rwa [hyB] at h
  have hBE : ∀ j, B j ∈ riemannRochSpace E := by
    intro j
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (β j).2
    have : B j = ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')
        (algebraMap ℚ (AlgebraicClosure ℚ) (s i)) * b i := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [MulMemClass.coe_mul, coe_algebraMap_bar, hB, ← hg, ← coeffEmb_smul_eq_mul, ← map_sum, hs]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hb i)
  refine ⟨Module.finrank ℚ V, fun j => ⟨e j, he j⟩, fun j => ((β j : V) : LaurentSeries ℚ), hβF, hBint,
    fun j P hP => ord_nonneg_of_mem_riemannRochSpace hE₀ m (hBE j) P hP, ⟨hj, fun j hgj v hv => ?_⟩, ?_⟩
  · exact residue_mem_valuationSubring_of_cuspRegular_of_residue_jq_mem q M' hqM' A hA R₀ hR₀ (B j) hgj
      (fun P hP => ord_nonneg_of_mem_riemannRochSpace hE₀ m (hBE j) P hP) hj v hv
  · exact hfsum

end S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular (solution)
