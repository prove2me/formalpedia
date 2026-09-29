-- Prove2me | solution 1 for ModularCurve.FullLevel.Idx.smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/389208e9-1c41-5db8-86ad-e963f8d06800

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_FullLevelJacobian
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.CharP.Lemmas
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ

set_option autoImplicit false

namespace IdxTameNormEngine

open IsLocalRing Polynomial Finset

theorem valuation_eq_one_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {ζ : L} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have h : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le' hm).mp h

theorem mem_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {ζ : L} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) : ζ ∈ A :=
  (A.valuation_le_one_iff ζ).mp (valuation_eq_one_of_pow_eq_one A hm hζ).le

theorem valuation_eq_one_of_valuation_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {x : L} {m : ℕ} (hm : m ≠ 0) (hx : A.valuation (x ^ m) = 1) : A.valuation x = 1 := by
  rw [map_pow] at hx
  exact (pow_eq_one_iff_of_nonneg zero_le' hm).mp hx

theorem valuation_sub_lt_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    {x : L} (hx : x ∈ A) : ∃ _ : τ x ∈ A, A.valuation (τ x - x) < 1 := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
  have htA : ((t : L ≃ₐ[K] L) x) ∈ A := by
    have := (t • (⟨x, hx⟩ : A)).2
    exact this
  refine ⟨htA, ?_⟩
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) t = 1 :=
    (MonoidHom.mem_ker).mp ht
  have hres : residue A (t • (⟨x, hx⟩ : A)) = residue A ⟨x, hx⟩ := by
    rw [ResidueField.residue_smul]
    have := RingEquiv.congr_fun hker (residue A ⟨x, hx⟩)
    simpa using this
  have hmax : t • (⟨x, hx⟩ : A) - ⟨x, hx⟩ ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, map_sub, hres, sub_self]
  have := (ValuationSubring.valuation_lt_one_iff _ _).mp hmax
  exact this

theorem exists_residue_div_eq_one_of_mem_inertiaSubgroupIn {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K)
    {ρ : L} (hρ : A.valuation ρ = 1) :
    ∃ h : τ ρ / ρ ∈ A, residue A ⟨τ ρ / ρ, h⟩ = 1 := by
  have hρA : ρ ∈ A := (A.valuation_le_one_iff ρ).mp hρ.le
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, map_zero] at hρ
    exact zero_ne_one hρ
  obtain ⟨-, hv⟩ := valuation_sub_lt_one_of_mem_inertiaSubgroupIn A hτ hρA

  have hm : A.valuation ((τ ρ - ρ) / ρ) < 1 := by
    rw [map_div₀, hρ, div_one]; exact hv
  have hmA : (τ ρ - ρ) / ρ ∈ A := (A.valuation_le_one_iff _).mp hm.le
  have hsum : τ ρ / ρ = (τ ρ - ρ) / ρ + 1 := by
    field_simp
    ring
  have hmem : τ ρ / ρ ∈ A := by
    rw [hsum]; exact add_mem hmA (one_mem A)
  refine ⟨hmem, ?_⟩
  have hmax : (⟨(τ ρ - ρ) / ρ, hmA⟩ : A) ∈ maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    exact hm
  have hres0 : residue A ⟨(τ ρ - ρ) / ρ, hmA⟩ = 0 := (residue_eq_zero_iff _).mpr hmax
  have heq : (⟨τ ρ / ρ, hmem⟩ : A) = ⟨(τ ρ - ρ) / ρ, hmA⟩ + 1 := by
    apply Subtype.ext
    exact hsum
  rw [heq, map_add, map_one, hres0, zero_add]

theorem residue_natCast_eq_zero_of_liesOverPrime {L : Type*} [Field L] (A : ValuationSubring L)
    {q : ℕ} (hA : A.LiesOverPrime q) : ((q : ℕ) : ResidueField A) = 0 := by
  have h1 : ((q : A) : L) ∈ A.nonunits := by
    have : ((q : A) : L) = (q : L) := by simp
    rw [this]; exact hA
  have h2 : (q : A) ∈ maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp h1
  have h3 : residue A (q : A) = 0 := (residue_eq_zero_iff _).mpr h2
  simpa using h3

theorem charP_residueField_of_liesOverPrime {L : Type*} [Field L] (A : ValuationSubring L)
    {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) : CharP (ResidueField A) q :=
  (CharP.charP_iff_prime_eq_zero hq).mpr (residue_natCast_eq_zero_of_liesOverPrime A hA)

theorem residue_eq_one_of_pow_eq_one {L : Type*} [Field L] (A : ValuationSubring L)
    {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) {z : A} (hz : z ^ q = 1) :
    residue A z = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := charP_residueField_of_liesOverPrime A hq hA
  have h1 : (residue A z) ^ q = 1 := by rw [← map_pow, hz, map_one]
  have h2 : (residue A z - 1) ^ q = 0 := by
    rw [sub_pow_char, h1, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff hq.ne_zero |>.mp h2)

theorem residue_geom_sum_eq {R : Type*} [CommRing R] [IsLocalRing R] {z : R}
    (hz : residue R z = 1) (n : ℕ) :
    residue R (∑ i ∈ range n, z ^ i) = n := by
  rw [map_sum]
  simp only [map_pow, hz, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]

theorem natCast_succ_eq_prod_one_sub_pow {L : Type*} [Field L] {n : ℕ} {z : L}
    (hz : IsPrimitiveRoot z (n + 1)) :
    ((n + 1 : ℕ) : L) = ∏ i ∈ range n, (1 - z ^ (i + 1)) := by

  have hprod : (X ^ (n + 1) - C (1 : L)) = ∏ i ∈ range (n + 1), (X - C (z ^ i * 1)) :=
    X_pow_sub_C_eq_prod hz n.succ_pos (one_pow (n + 1))
  rw [prod_range_succ'] at hprod
  simp only [pow_zero, mul_one, map_one] at hprod

  rw [← geom_sum_mul] at hprod
  have hX1 : (X - 1 : L[X]) ≠ 0 := by
    have := X_sub_C_ne_zero (1 : L)
    rwa [map_one] at this
  have hcancel : (∑ i ∈ range (n + 1), (X : L[X]) ^ i) = ∏ i ∈ range n, (X - C (z ^ (i + 1))) :=
    mul_right_cancel₀ hX1 hprod
  have heval := congrArg (Polynomial.eval (1 : L)) hcancel
  rw [eval_finsetSum, eval_prod] at heval
  simpa using heval

section Main

variable (q : ℕ) [hq : Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
  (hP : P.LiesOverPrime q) (π : AlgebraicClosure ℚ)
  (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))

theorem sq_sub_one_ne_zero : q ^ 2 - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hq.out.one_lt)

theorem sq_sub_one_eq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, (Nat.sub_add_cancel hq.out.pos).symm⟩
  subst hk
  have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
  simp [this]

include hπ in
theorem pi_ne_zero : π ≠ 0 := by
  intro h
  rw [h, zero_pow (sq_sub_one_ne_zero q)] at hπ
  exact (Nat.cast_ne_zero.mpr hq.out.ne_zero) hπ.symm

include hπ in

theorem div_pow_eq_one (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (τ π / π) ^ (q ^ 2 - 1) = 1 := by
  have h0 : (π : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) ≠ 0 := by
    rw [hπ]; exact Nat.cast_ne_zero.mpr hq.out.ne_zero
  rw [div_pow, ← map_pow, hπ, map_natCast, ← hπ, div_self h0]

include hπ in
theorem div_mem (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : τ π / π ∈ P :=
  mem_of_pow_eq_one P (sq_sub_one_ne_zero q) (div_pow_eq_one q π hπ τ)

include hπ in

theorem tameCharacter_eq (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    P.tameCharacter π τ = residue P ⟨τ π / π, div_mem q P π hπ τ⟩ := by
  unfold ValuationSubring.tameCharacter
  rw [dif_pos (div_mem q P π hπ τ)]

include hP hπ in

theorem tameCharacter_pow_succ_eq_natCast_of_apply_eq_pow
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    {z : AlgebraicClosure ℚ} (hz : IsPrimitiveRoot z q) {b : ℕ} (hb : τ z = z ^ b) :
    P.tameCharacter π τ ^ (q + 1) = (b : ResidueField P) := by
  have hqp : q.Prime := hq.out
  have hq1 : 1 < q := hqp.one_lt
  have hπ0 : π ≠ 0 := pi_ne_zero q π hπ

  have hzq : z ^ q = 1 := hz.pow_eq_one
  have hzP : z ∈ P := mem_of_pow_eq_one P hqp.ne_zero hzq
  set zP : P := ⟨z, hzP⟩ with hzP_def
  have hzPq : zP ^ q = 1 := by
    apply Subtype.ext
    simp [hzP_def, hzq]
  have hres_z : residue P zP = 1 := residue_eq_one_of_pow_eq_one P hqp hP hzPq
  have hz1 : z ≠ 1 := hz.ne_one hq1
  have h1z : (1 - z : AlgebraicClosure ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)

  let eP : ℕ → P := fun n => ∑ i ∈ range n, zP ^ i
  have heP_coe : ∀ n, ((eP n : P) : AlgebraicClosure ℚ) = ∑ i ∈ range n, z ^ i := by
    intro n
    show P.subtype (eP n) = _
    simp only [eP, map_sum, map_pow]
    rfl
  have hres_e : ∀ n, residue P (eP n) = n := fun n => residue_geom_sum_eq hres_z n

  let EP : P := ∏ i ∈ range (q - 1), eP (i + 1)
  have hEP_coe : ((EP : P) : AlgebraicClosure ℚ) = ∏ i ∈ range (q - 1), ∑ j ∈ range (i + 1), z ^ j := by
    show P.subtype EP = _
    rw [map_prod]
    refine prod_congr rfl fun i _ => ?_
    exact heP_coe (i + 1)
  have hres_E : residue P EP ≠ 0 := by
    haveI : CharP (ResidueField P) q := charP_residueField_of_liesOverPrime P hqp hP
    rw [map_prod, prod_ne_zero_iff]
    intro i hi
    rw [hres_e]
    rw [mem_range] at hi
    intro h0
    have hdvd : q ∣ i + 1 := (CharP.cast_eq_zero_iff (ResidueField P) q (i + 1)).mp h0
    exact absurd (Nat.le_of_dvd i.succ_pos hdvd) (by omega)
  have hE_unit : IsUnit EP := (residue_ne_zero_iff_isUnit _).mp hres_E
  have hvE : P.valuation ((EP : P) : AlgebraicClosure ℚ) = 1 := (P.valuation_eq_one_iff EP).mp hE_unit

  have hnorm : (q : AlgebraicClosure ℚ) = (1 - z) ^ (q - 1) * ((EP : P) : AlgebraicClosure ℚ) := by
    have hz' : IsPrimitiveRoot z (q - 1 + 1) := by rwa [Nat.sub_add_cancel hqp.pos]
    have h := natCast_succ_eq_prod_one_sub_pow hz'
    rw [Nat.sub_add_cancel hqp.pos] at h
    rw [h, hEP_coe, ← card_range (q - 1), ← prod_const, card_range, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [mul_neg_geom_sum]

  set π₁ : AlgebraicClosure ℚ := π ^ (q + 1) with hπ₁_def
  have hπ₁ : π₁ ^ (q - 1) = (q : AlgebraicClosure ℚ) := by
    rw [hπ₁_def, ← pow_mul, ← sq_sub_one_eq q, hπ]
  have hq10 : q - 1 ≠ 0 := by omega

  set ρ : AlgebraicClosure ℚ := π₁ / (1 - z) with hρ_def
  have hρpow : ρ ^ (q - 1) = ((EP : P) : AlgebraicClosure ℚ) := by
    have h1zpow : (1 - z : AlgebraicClosure ℚ) ^ (q - 1) ≠ 0 := pow_ne_zero _ h1z
    rw [hρ_def, div_pow, hπ₁, hnorm, mul_div_cancel_left₀ _ h1zpow]
  have hvρ : P.valuation ρ = 1 := by
    apply valuation_eq_one_of_valuation_pow_eq_one P hq10
    rw [hρpow]; exact hvE
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h, map_zero] at hvρ; exact zero_ne_one hvρ

  obtain ⟨hwP, hres_w⟩ := exists_residue_div_eq_one_of_mem_inertiaSubgroupIn P hτ hvρ

  have hτ1z : τ (1 - z) = (1 - z) * ((eP b : P) : AlgebraicClosure ℚ) := by
    rw [map_sub, map_one, hb, heP_coe, mul_neg_geom_sum]

  have hπ₁ρ : π₁ = ρ * (1 - z) := by rw [hρ_def, div_mul_cancel₀ _ h1z]
  have hkey : (τ π / π) ^ (q + 1) = τ ρ / ρ * ((eP b : P) : AlgebraicClosure ℚ) := by
    have h1 : (τ π / π) ^ (q + 1) = τ π₁ / π₁ := by
      rw [div_pow, ← map_pow]
    rw [h1, hπ₁ρ, map_mul, hτ1z]
    field_simp

  have hkeyP : (⟨τ π / π, div_mem q P π hπ τ⟩ : P) ^ (q + 1) = ⟨τ ρ / ρ, hwP⟩ * eP b := by
    apply Subtype.ext
    show P.subtype ((⟨τ π / π, div_mem q P π hπ τ⟩ : P) ^ (q + 1)) =
      P.subtype (⟨τ ρ / ρ, hwP⟩ * eP b)
    rw [map_pow, map_mul]
    exact hkey
  rw [tameCharacter_eq q P π hπ τ, ← map_pow, hkeyP, map_mul, hres_w, hres_e, one_mul]

include hP hπ in

theorem apply_eq_pow_of_tameCharacter_pow_succ_eq_natCast
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ q = 1)
    {a : ℕ} (ha : P.tameCharacter π τ ^ (q + 1) = (a : IsLocalRing.ResidueField P)) :
    τ ζ = ζ ^ a := by
  have hqp : q.Prime := hq.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  by_cases h1 : ζ = 1
  · subst h1; simp

  have hz : IsPrimitiveRoot ζ q := by
    have hord : orderOf ζ = q := by
      have hdvd : orderOf ζ ∣ q := orderOf_dvd_of_pow_eq_one hζ
      rcases (Nat.dvd_prime hqp).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
    rw [← hord]; exact IsPrimitiveRoot.orderOf ζ

  have hτζ : (τ ζ) ^ q = 1 := by rw [← map_pow, hζ, map_one]
  obtain ⟨b, -, hb⟩ := hz.eq_pow_of_pow_eq_one hτζ
  have hnorm := tameCharacter_pow_succ_eq_natCast_of_apply_eq_pow q P hP π hπ hτ hz hb.symm

  haveI : CharP (ResidueField P) q := charP_residueField_of_liesOverPrime P hqp hP
  have hab : a ≡ b [MOD q] := (CharP.natCast_eq_natCast (ResidueField P) q).mp (ha.symm.trans hnorm)
  rw [← hb, pow_eq_pow_mod a hζ, pow_eq_pow_mod b hζ, hab]

end Main

end IdxTameNormEngine

open ModularCurve ModularCurve.FullLevel IdxTameNormEngine in
theorem solution
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ)
    (α : (GaloisField q 2)ˣ) (hα : ι (α : GaloisField q 2) = P.tameCharacter π τ)
    (d : (ZMod q)ˣ) (hd : algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1))
    (ζ : Idx q) :
    τ • ζ = ζ.pow d := by
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  have ha : P.tameCharacter π τ ^ (q + 1) = (((d : ZMod q).val : ℕ) : IsLocalRing.ResidueField P) := by
    rw [← hα, ← map_pow, ← hd, ← ZMod.natCast_zmod_val (d : ZMod q), map_natCast, map_natCast,
      ZMod.natCast_zmod_val]
  have h := apply_eq_pow_of_tameCharacter_pow_succ_eq_natCast q P hP π hπ hτ
    ζ.isPrimitiveRoot.pow_eq_one ha
  exact Idx.ext h

end S_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ
end P2MW
export P2MW.S_ModularCurve_FullLevel_Idx_smul_eq_pow_of_tameCharacter_eq_of_algebraMap_eq_pow_succ (solution)
