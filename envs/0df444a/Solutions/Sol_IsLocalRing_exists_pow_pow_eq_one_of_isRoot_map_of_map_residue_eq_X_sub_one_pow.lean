-- Prove2me | solution 1 for IsLocalRing.exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/ae87a90a-872f-5577-b95d-2165bb372b51

import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.GCD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow

set_option autoImplicit false

open Polynomial

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P : R[X]) (hP : P.map (IsLocalRing.residue R) = (X - 1) ^ P.natDegree)
    {S : Type} [CommRing S] (j : R →+* S) (ζ : S) (hζ : (P.map j).IsRoot ζ)
    {d : ℕ} (hd : 0 < d) (hζd : ζ ^ d = 1) :
    ∃ n : ℕ, ζ ^ p ^ n = 1 := by
  classical
  have hp : p.Prime := Fact.out
  letI : Algebra R S := j.toAlgebra

  have hlc : IsUnit P.leadingCoeff := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have hmon : ((X - C (1 : IsLocalRing.ResidueField R)) ^ P.natDegree).Monic := (monic_X_sub_C _).pow _
    have hdeg : ((X - C (1 : IsLocalRing.ResidueField R)) ^ P.natDegree).natDegree = P.natDegree := by
      rw [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    have h1 := hmon.coeff_natDegree
    rw [hdeg] at h1
    have hP' : P.map (IsLocalRing.residue R) = (X - C 1) ^ P.natDegree := by
      rw [C_1]
      exact hP
    have h2 : (P.map (IsLocalRing.residue R)).coeff P.natDegree = 1 := by
      rw [hP']
      exact h1
    rw [coeff_map] at h2
    rw [Polynomial.leadingCoeff, h2]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := hlc

  have hPζ : P.eval₂ (algebraMap R S) ζ = 0 := by
    have h := hζ
    rw [IsRoot.def, eval_map] at h
    exact h
  have hint : IsIntegral R ζ :=
    ⟨C (↑u⁻¹ : R) * P, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu, Units.inv_mul]),
      by rw [eval₂_mul, eval₂_C, hPζ, mul_zero]⟩
  obtain ⟨T, hT⟩ : ∃ T : Subalgebra R S, T = Algebra.adjoin R ({ζ} : Set S) := ⟨_, rfl⟩
  haveI hfin : Module.Finite R T := by
    rw [hT]
    exact Algebra.finite_adjoin_simple_of_isIntegral hint
  have hζT : ζ ∈ T := by
    rw [hT]
    exact Algebra.subset_adjoin (Set.mem_singleton ζ)
  let ζT : T := ⟨ζ, hζT⟩
  let I : Ideal T := (IsLocalRing.maximalIdeal R).map (algebraMap R T)
  let π : T →+* T ⧸ I := Ideal.Quotient.mk I

  obtain ⟨n, D, hpD, hdD⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p hp.one_lt.ne'
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hdD
    exact hd.ne' hdD
  let η : T := ζT ^ p ^ n
  have hηD : η ^ D = 1 := by
    apply Subtype.ext
    have h : ((ζT : T) : S) = ζ := rfl
    simp only [η, SubmonoidClass.coe_pow, OneMemClass.coe_one, h, ← pow_mul, ← hdD]
    exact hζd

  have hη1 : π η = 1 := by
    rcases subsingleton_or_nontrivial (T ⧸ I) with hQ | hQ
    · exact Subsingleton.elim _ _
    · have hker : ∀ a ∈ IsLocalRing.maximalIdeal R, (π.comp (algebraMap R T)) a = 0 := fun a ha =>
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
      let lift : IsLocalRing.ResidueField R →+* T ⧸ I :=
        Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) (π.comp (algebraMap R T)) hker
      haveI : CharP (T ⧸ I) p := charP_of_injective_ringHom lift.injective p
      have hcomp : lift.comp (IsLocalRing.residue R) = π.comp (algebraMap R T) :=
        RingHom.ext fun a => rfl
      have hmapf : P.map (π.comp (algebraMap R T)) = (X - 1) ^ P.natDegree := by
        rw [← hcomp, ← Polynomial.map_map, hP]
        simp
      have h2 : aeval ζT P = 0 := by
        have h3 : T.val (aeval ζT P) = 0 := by
          rw [← aeval_algHom_apply, aeval_def]
          exact hPζ
        exact (map_eq_zero_iff _ Subtype.val_injective).mp h3
      have hz : (π ζT - 1) ^ P.natDegree = 0 := by
        have h1 : (P.map (π.comp (algebraMap R T))).eval (π ζT) = 0 := by
          rw [eval_map, ← Polynomial.hom_eval₂, ← aeval_def, h2, map_zero]
        rw [hmapf] at h1
        simpa using h1
      have hmN : P.natDegree ≤ p ^ (P.natDegree + d) :=
        (Nat.lt_pow_self hp.one_lt).le.trans (Nat.pow_le_pow_right hp.pos (Nat.le_add_right _ _))
      have hzN : (π ζT) ^ p ^ (P.natDegree + d) = 1 := by
        have h := pow_eq_zero_of_le hmN hz
        rwa [sub_pow_char_pow, one_pow, sub_eq_zero] at h
      have hnN : n ≤ P.natDegree + d := by
        have h4 : n < p ^ n := Nat.lt_pow_self hp.one_lt
        have h5 : p ^ n ≤ d := by
          rw [hdD]
          exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hD0)
        omega
      have hcop : Nat.Coprime (p ^ (P.natDegree + d - n)) D :=
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpD)
      have h6 : (π η) ^ p ^ (P.natDegree + d - n) = 1 := by
        rw [map_pow, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hnN, hzN]
      have h7 : (π η) ^ D = 1 := by
        rw [← map_pow, hηD, map_one]
      have key := pow_gcd_eq_one.mpr ⟨h6, h7⟩
      rwa [hcop.gcd_eq_one, pow_one] at key

  have hDunit : IsUnit ((D : ℕ) : R) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
    exact fun h => hpD ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) p D).mp h)
  obtain ⟨uD, huD⟩ := hDunit

  let e : T := ∑ i ∈ Finset.range D, η ^ i
  have heπ : π e = (D : T ⧸ I) := by
    simp [e, map_sum, hη1]
  let a : T := algebraMap R T (↑uD⁻¹ : R)
  have heD : e - (D : T) ∈ I := Ideal.Quotient.eq.mp (by rw [heπ, map_natCast])
  have hDa : (D : T) * a = 1 := by
    simp only [a]
    rw [← map_natCast (algebraMap R T) D, ← map_mul, ← huD, Units.mul_inv, map_one]
  have h1ea : 1 - e * a ∈ I := by
    have h : 1 - e * a = -((e - D) * a) := by
      rw [sub_mul, hDa]
      ring
    rw [h]
    exact I.neg_mem (I.mul_mem_right _ heD)
  have he_unit : IsUnit e := by
    have hNN : (⊤ : Submodule R T) ≤
        LinearMap.range (LinearMap.mulLeft R e) ⊔ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R T) := by
      intro s _
      have hs : s = e * (a * s) + (1 - e * a) * s := by ring
      rw [hs]
      refine Submodule.add_mem_sup ⟨a * s, rfl⟩ ?_
      rw [Ideal.smul_top_eq_map]
      exact I.mul_mem_right _ h1ea
    have htop := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top (R := R) (M := T))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) hNN
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (htop (Submodule.mem_top : (1 : T) ∈ _))
    exact isUnit_iff_exists_inv.mpr ⟨v, hv⟩

  have hgeom : e * (η - 1) = η ^ D - 1 := geom_sum_mul η D
  rw [hηD, sub_self] at hgeom
  have hη : η = 1 := by
    rwa [he_unit.mul_right_eq_zero, sub_eq_zero] at hgeom
  refine ⟨n, ?_⟩
  have h := congrArg Subtype.val hη
  have hc : ((ζT : T) : S) = ζ := rfl
  simpa [η, hc] using h

#print axioms solution

end S_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow
end P2MW
export P2MW.S_IsLocalRing_exists_pow_pow_eq_one_of_isRoot_map_of_map_residue_eq_X_sub_one_pow (solution)
