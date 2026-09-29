-- Prove2me | solution 1 for ModularCurve.exists_finset_forall_coeff_mem_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8fd53b5d-f79b-5f4d-b5a1-ee262587be47

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring.ModularCurve"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd algebraMap_apply_eq_single jNumQ jq ofPowerSeries_coeff_of_neg divisorExpansions modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff mem_laurentBaseChange_iff"
namespace CoeffIntegralityAux
p2m_open "ModularCurve"

open Polynomial HahnSeries

theorem exists_int_poly_aeval_eq_zero_coeff_zero_ne (μ : AlgebraicClosure ℚ) (hμ : μ ≠ 0) :
    ∃ q : ℤ[X], aeval μ q = 0 ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic μ
  set q₀ : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p with hq₀
  have hq₀0 : q₀ ≠ 0 := fun h => hp0 ((IsFractionRing.integerNormalization_eq_zero_iff (p := p)).mp h)
  have hq₀μ : aeval μ q₀ = 0 := IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) p hp
  suffices key : ∀ (n : ℕ) (q : ℤ[X]), q.natDegree ≤ n → q ≠ 0 → aeval μ q = 0 →
      ∃ q' : ℤ[X], aeval μ q' = 0 ∧ q'.coeff 0 ≠ 0 from key _ q₀ le_rfl hq₀0 hq₀μ
  intro n
  induction n with
  | zero =>
    intro q hdeg hq0 hqμ
    refine ⟨q, hqμ, fun h0 => hq0 ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hdeg, h0, map_zero]
  | succ n ih =>
    intro q hdeg hq0 hqμ
    by_cases h0 : q.coeff 0 = 0
    · have hq : X * q.divX = q := by
        have := Polynomial.X_mul_divX_add q
        rwa [h0, map_zero, add_zero] at this
      have hdx0 : q.divX ≠ 0 := by
        intro h; apply hq0; rw [← hq, h, mul_zero]
      have hdeg' : q.divX.natDegree ≤ n := by
        have := Polynomial.natDegree_divX_eq_natDegree_tsub_one (p := q)
        omega
      have hμ' : aeval μ q.divX = 0 := by
        have : aeval μ (X * q.divX) = 0 := by rw [hq]; exact hqμ
        rw [map_mul, aeval_X] at this
        exact (mul_eq_zero.mp this).resolve_left hμ
      exact ih q.divX hdeg' hdx0 hμ'
    · exact ⟨q, hqμ, h0⟩

theorem isUnit_of_aeval_eq_zero {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hA : A.LiesOverPrime ℓ) (q : ℤ[X]) (hq0 : ¬ ℓ ∣ (q.coeff 0).natAbs)
    (μ : A) (hμ : aeval (μ : AlgebraicClosure ℚ) q = 0) : IsUnit μ := by
  by_contra hmax
  have hmax' : μ ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal μ).mpr (mem_nonunits_iff.mpr hmax)
  have hrel : μ * aeval μ q.divX + (q.coeff 0 : A) = 0 := by
    apply Subtype.ext
    have h1 := congrArg (aeval (μ : AlgebraicClosure ℚ)) (Polynomial.X_mul_divX_add q)
    rw [map_add, map_mul, aeval_X, aeval_C, hμ] at h1
    have h2 : (aeval (μ : AlgebraicClosure ℚ) q.divX) = ((aeval μ q.divX : A) : AlgebraicClosure ℚ) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def,
        show ((Polynomial.eval₂ (algebraMap ℤ A) μ q.divX : A) : AlgebraicClosure ℚ)
          = A.subtype (Polynomial.eval₂ (algebraMap ℤ A) μ q.divX) from rfl,
        Polynomial.hom_eval₂, RingHom.ext_int (A.subtype.comp (algebraMap ℤ A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
      rfl
    rw [h2] at h1
    push_cast
    simpa using h1
  have hc0 : ((q.coeff 0 : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    have : ((q.coeff 0 : ℤ) : A) = -(μ * aeval μ q.divX) := eq_neg_of_add_eq_zero_right hrel
    rw [this]
    exact neg_mem (Ideal.mul_mem_right _ _ hmax')
  have hℓA : ((ℓ : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
    have hlt : A.valuation ((ℓ : AlgebraicClosure ℚ)) < 1 := (A.mem_nonunits_iff).mp hA
    have : (((ℓ : ℤ) : A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) := by push_cast; rfl
    exact (A.valuation_lt_one_iff _).mpr (by rw [this]; exact hlt)
  have hcop : IsCoprime (q.coeff 0) (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hq0
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (1 : A) = (a : A) * ((q.coeff 0 : ℤ) : A) + (b : A) * ((ℓ : ℤ) : A) := by exact_mod_cast hab.symm
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc0) (Ideal.mul_mem_left _ _ hℓA)
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem exists_finset_forall_mem (c : AlgebraicClosure ℚ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        c ∈ A := by
  by_cases hc : c = 0
  · exact ⟨∅, by simp, fun ℓ _ _ A _ => by rw [hc]; exact zero_mem A⟩
  obtain ⟨q, hq, hq0⟩ := exists_int_poly_aeval_eq_zero_coeff_zero_ne c⁻¹ (inv_ne_zero hc)
  refine ⟨(q.coeff 0).natAbs.primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro ℓ hℓ hℓS A hA
  have hℓdvd : ¬ ℓ ∣ (q.coeff 0).natAbs := fun hd =>
    hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, hd, Int.natAbs_ne_zero.mpr hq0⟩)
  rcases A.mem_or_inv_mem c with h | h
  · exact h
  · have hu : IsUnit (⟨c⁻¹, h⟩ : A) := isUnit_of_aeval_eq_zero hℓ hA q hℓdvd ⟨c⁻¹, h⟩ hq
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : c⁻¹ * (b : AlgebraicClosure ℚ) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hbc : (b : AlgebraicClosure ℚ) = c := by
      have := (mul_eq_one_iff_eq_inv₀ (inv_ne_zero hc)).mp (by rwa [mul_comm] at hb')
      rw [this, inv_inv]
    rw [← hbc]
    exact b.2

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem forall_coeff_mem_iff (x : LaurentSeries (AlgebraicClosure ℚ)) :
    (∀ k : ℤ, x.coeff k ∈ A) ↔ x ∈ (coeffMap A.subtype).range := by
  constructor
  · intro h
    refine ⟨⟨fun k => ⟨x.coeff k, h k⟩, x.isPWO_support.mono ?_⟩, ?_⟩
    · intro k hk
      rw [HahnSeries.mem_support]
      exact fun h0 => hk (Subtype.ext h0)
    · ext k
      rfl
  · rintro ⟨y, rfl⟩ k
    rw [coeffMap_coeff]
    exact (y.coeff k).2

theorem forall_coeff_inv_mem {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : x ≠ 0)
    (h : ∀ k : ℤ, x.coeff k ∈ A) (hlead : (x.leadingCoeff)⁻¹ ∈ A) :
    ∀ k : ℤ, x⁻¹.coeff k ∈ A := by
  obtain ⟨y, hy⟩ := (forall_coeff_mem_iff A x).mp h
  have hyx : ∀ k, ((y.coeff k : A) : AlgebraicClosure ℚ) = x.coeff k := fun k => by
    rw [← hy]; rfl
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx hy.symm
  have hlc0 : x.coeff x.order ≠ 0 := fun h0 => hx (HahnSeries.coeff_order_eq_zero.mp h0)
  have hord : y.order = x.order := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero ?_) (HahnSeries.order_le_of_coeff_ne_zero ?_)
    · intro h0
      apply hlc0
      rw [← hyx, h0]
      rfl
    · rw [← hyx]
      intro h0
      exact hy0 (HahnSeries.coeff_order_eq_zero.mp ((map_eq_zero_iff A.subtype Subtype.val_injective).mp h0))
  have hunit : IsUnit y.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, hord]
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hlead⟩, Subtype.ext ?_⟩
    show ((y.coeff x.order : A) : AlgebraicClosure ℚ) * (x.leadingCoeff)⁻¹ = 1
    rw [hyx, HahnSeries.leadingCoeff_eq, mul_inv_cancel₀ hlc0]
  obtain ⟨u, hu⟩ := (HahnSeries.isUnit_iff.mpr hunit).exists_right_inv
  have hinv : x⁻¹ = coeffMap A.subtype u := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← hy, ← map_mul, hu, map_one]
  intro k
  rw [hinv, coeffMap_coeff]
  exact (u.coeff k).2

def Good (x : LaurentSeries (AlgebraicClosure ℚ)) : Prop :=
  ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
    ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ k : ℤ, x.coeff k ∈ A

variable {A}

theorem good_of_forall {x : LaurentSeries (AlgebraicClosure ℚ)}
    (h : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (k : ℤ), x.coeff k ∈ A) : Good x :=
  ⟨∅, by simp, fun _ _ _ A _ k => h A k⟩

theorem good_one : Good 1 :=
  good_of_forall fun A => (forall_coeff_mem_iff A 1).mpr (one_mem _)

theorem Good.add {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good x) (hy : Good y) :
    Good (x + y) := by
  classical
  obtain ⟨S, hS, hxS⟩ := hx
  obtain ⟨T, hT, hyT⟩ := hy
  refine ⟨S ∪ T, fun p hp => (Finset.mem_union.mp hp).elim (hS p) (hT p), ?_⟩
  intro ℓ hℓ hℓST A hA
  rw [Finset.mem_union, not_or] at hℓST
  exact (forall_coeff_mem_iff A _).mpr (add_mem ((forall_coeff_mem_iff A _).mp (hxS ℓ hℓ hℓST.1 A hA))
    ((forall_coeff_mem_iff A _).mp (hyT ℓ hℓ hℓST.2 A hA)))

theorem Good.mul {x y : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good x) (hy : Good y) :
    Good (x * y) := by
  classical
  obtain ⟨S, hS, hxS⟩ := hx
  obtain ⟨T, hT, hyT⟩ := hy
  refine ⟨S ∪ T, fun p hp => (Finset.mem_union.mp hp).elim (hS p) (hT p), ?_⟩
  intro ℓ hℓ hℓST A hA
  rw [Finset.mem_union, not_or] at hℓST
  exact (forall_coeff_mem_iff A _).mpr (mul_mem ((forall_coeff_mem_iff A _).mp (hxS ℓ hℓ hℓST.1 A hA))
    ((forall_coeff_mem_iff A _).mp (hyT ℓ hℓ hℓST.2 A hA)))

theorem Good.neg {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good x) : Good (-x) := by
  obtain ⟨S, hS, hxS⟩ := hx
  exact ⟨S, hS, fun ℓ hℓ hℓS A hA =>
    (forall_coeff_mem_iff A _).mpr (neg_mem ((forall_coeff_mem_iff A _).mp (hxS ℓ hℓ hℓS A hA)))⟩

theorem Good.inv {x : LaurentSeries (AlgebraicClosure ℚ)} (hx : Good x) : Good x⁻¹ := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [inv_zero]; exact good_of_forall fun A k => by rw [HahnSeries.coeff_zero]; exact zero_mem A
  obtain ⟨S, hS, hxS⟩ := hx
  obtain ⟨T, hT, hcT⟩ := exists_finset_forall_mem (x.leadingCoeff)⁻¹
  refine ⟨S ∪ T, fun p hp => (Finset.mem_union.mp hp).elim (hS p) (hT p), ?_⟩
  intro ℓ hℓ hℓST A hA
  rw [Finset.mem_union, not_or] at hℓST
  exact forall_coeff_inv_mem A hx0 (hxS ℓ hℓ hℓST.1 A hA) (hcT ℓ hℓ hℓST.2 A hA)

theorem good_single_zero (c : AlgebraicClosure ℚ) : Good (HahnSeries.single 0 c) := by
  obtain ⟨S, hS, hcS⟩ := exists_finset_forall_mem c
  refine ⟨S, hS, fun ℓ hℓ hℓS A hA k => ?_⟩
  rw [HahnSeries.coeff_single]
  split_ifs
  · exact hcS ℓ hℓ hℓS A hA
  · exact zero_mem A

theorem good_algebraMap (c : AlgebraicClosure ℚ) :
    Good (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) := by
  rw [algebraMap_laurentSeries_eq_single]
  exact good_single_zero c

theorem exists_int_coeff_jq (m : ℤ) : ∃ z : ℤ, jq.coeff m = z := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul]
  rcases lt_or_ge (m - -1) 0 with h | h
  · exact ⟨0, by rw [ofPowerSeries_coeff_of_neg _ h, Int.cast_zero]⟩
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [hn, HahnSeries.ofPowerSeries_apply_coeff, jNumQ, PowerSeries.coeff_map]
    exact ⟨_, rfl⟩

theorem good_coeffEmb_qExpand_jq (d : ℕ) [NeZero d] :
    Good (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)) := by
  refine good_of_forall fun A k => ?_
  rw [coeffEmb_coeff]
  by_cases hd : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hd
    obtain ⟨z, hz⟩ := exists_int_coeff_jq m
    rw [qExpand_coeff_mul, hz, map_intCast]
    exact intCast_mem A z
  · rw [qExpand_coeff_of_not_dvd d _ hd, map_zero]
    exact zero_mem A

theorem good_coeffEmb_of_mem_full (N : ℕ) {y : LaurentSeries ℚ} (hy : y ∈ modularFunctionFieldFull N) :
    Good (coeffEmb (AlgebraicClosure ℚ) y) := by
  replace hy : y ∈ Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions N) := hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨r, rfl⟩ | ⟨d, hne, _, rfl⟩
      · rw [algebraMap_apply_eq_single, coeffEmb, coeffMap_single]
        exact good_single_zero _
      · haveI := hne
        exact good_coeffEmb_qExpand_jq d
  | one => rw [map_one]; exact good_one
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | neg x _ hx => rw [map_neg]; exact hx.neg
  | inv x _ hx => rw [map_inv₀]; exact hx.inv
  | mul x y _ _ hx hy => rw [map_mul]; exact hx.mul hy

theorem good_of_mem_bar (N : ℕ) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ modularFunctionFieldBar N) : Good x := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
      · exact good_algebraMap c
      · exact good_coeffEmb_of_mem_full N hy
  | one => exact good_one
  | add x y _ _ hx hy => exact hx.add hy
  | neg x _ hx => exact hx.neg
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

end ModularCurve.CoeffIntegralityAux

open ModularCurve.CoeffIntegralityAux in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ (i : Fin r) (k : ℤ), ((s i : LaurentSeries (AlgebraicClosure ℚ)).coeff k) ∈ A := by
  classical
  choose S hS using fun i : Fin r => good_of_mem_bar N (s i).2
  refine ⟨Finset.univ.biUnion S, fun p hp => ?_, fun ℓ hℓ hℓS A hA i k => ?_⟩
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact (hS i).1 p hi
  · exact (hS i).2 ℓ hℓ (fun h => hℓS (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩)) A hA k

end S_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring
end P2MW
export P2MW.S_ModularCurve_exists_finset_forall_coeff_mem_valuationSubring (solution)
