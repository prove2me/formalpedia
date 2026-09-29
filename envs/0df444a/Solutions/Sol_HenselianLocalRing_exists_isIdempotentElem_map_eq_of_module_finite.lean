-- Prove2me | solution 1 for HenselianLocalRing.exists_isIdempotentElem_map_eq_of_module_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5741cb7a-8c56-5d82-a9f9-57f8215500e5

import Mathlib
import Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite

set_option autoImplicit false

universe u v

open Polynomial IsLocalRing

namespace F1aSol

private theorem aeval_mul_one_sub_of_isIdempotentElem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : R[X]) {ε : A} (hε : IsIdempotentElem ε) :
    aeval ε q * (1 - ε) = algebraMap R A (q.coeff 0) * (1 - ε) := by
  rw [aeval_eq_sum_range, Finset.sum_mul, Finset.sum_eq_single 0]
  · rw [pow_zero, smul_mul_assoc, one_mul, Algebra.smul_def]
  · intro i _ hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [smul_mul_assoc, pow_succ, mul_assoc, mul_sub, mul_one, hε.eq, sub_self, mul_zero, smul_zero]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0

private theorem aeval_mul_self_of_isIdempotentElem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : R[X]) {ε : A} (hε : IsIdempotentElem ε) :
    aeval ε q * ε = algebraMap R A (q.eval 1) * ε := by
  rw [aeval_eq_sum_range, eval_eq_sum_range, Finset.sum_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_pow, mul_one, smul_mul_assoc, ← pow_succ, hε.pow_succ_eq, Algebra.smul_def]

private theorem aeval_eq_zero_of_forall_coeff_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) (hI : ∀ r ∈ I, algebraMap R A r = 0) (q : R[X]) (hq : ∀ i, q.coeff i ∈ I) (x : A) :
    aeval x q = 0 := by
  rw [aeval_eq_sum_range]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Algebra.smul_def, hI _ (hq i), zero_mul]

end F1aSol

open F1aSol in
theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {B : Type v} [CommRing B] [Algebra R B] [Module.Finite R B]
    (e₀ : B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) e = e₀ := by
  classical

  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e₀
  let 𝔪 : Ideal R := maximalIdeal R
  let J : Ideal B := Ideal.map (algebraMap R B) 𝔪
  let k := ResidueField R
  have h𝔪 : 𝔪 = maximalIdeal R := rfl
  obtain ⟨p, hp, hpb⟩ : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  have hpb' : aeval b p = 0 := by rw [aeval_def]; exact hpb

  let κ := 𝔪.ResidueField
  have hpκ0 : p.map (algebraMap R κ) ≠ 0 := (hp.map _).ne_zero
  obtain ⟨h, hph, hndvd⟩ :=
    (p.map (algebraMap R κ)).exists_eq_pow_rootMultiplicity_mul_and_not_dvd hpκ0 1
  set a : ℕ := (p.map (algebraMap R κ)).rootMultiplicity 1 with ha
  have hXa : ((X - C (1 : κ)) ^ a).Monic := (monic_X_sub_C 1).pow a
  have hhm : h.Monic := by
    have := hp.map (algebraMap R κ)
    rw [hph] at this
    exact hXa.of_mul_monic_left this
  have hcop : IsCoprime ((X - C (1 : κ)) ^ a) h :=
    (((irreducible_X_sub_C (1 : κ)).coprime_iff_not_dvd).mpr hndvd).pow_left

  obtain ⟨R', _, _, _, Q, _, _, f', g', hbij, -, -, hpfg', hcop', hf'red, -⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime 𝔪 p
      ((X - C (1 : κ)) ^ a) h hp hXa hhm hph hcop

  let ι : κ ≃ₐ[R] Q.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ 𝔪 Q (Algebra.ofId R R') (Ideal.over_def Q 𝔪)) hbij
  let θ : κ →ₐ[R] k :=
    Ideal.ResidueField.liftₐ 𝔪 (Algebra.ofId R k)
      (by
        intro r hr
        rw [RingHom.mem_ker]
        exact (IsLocalRing.residue_eq_zero_iff r).mpr hr)
      (by
        intro r hr
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact (IsLocalRing.notMem_maximalIdeal.mp hr).map _)
  let φ : R' →ₐ[R] k := θ.comp ((ι.symm : Q.ResidueField →ₐ[R] κ).comp
    (IsScalarTower.toAlgHom R R' Q.ResidueField))
  obtain ⟨ψ, hψ⟩ := HenselianLocalRing.exists_algHom_lift_of_etale R' φ

  set f : R[X] := f'.map (ψ : R' →+* R) with hf
  set g : R[X] := g'.map (ψ : R' →+* R) with hg
  have hpfg : p = f * g := by
    have := congrArg (Polynomial.map (ψ : R' →+* R)) hpfg'
    rwa [Polynomial.map_map, AlgHom.comp_algebraMap, Algebra.algebraMap_self, Polynomial.map_id,
      Polynomial.map_mul] at this
  have hcopfg : IsCoprime f g := hcop'.map (mapRingHom (ψ : R' →+* R))
  have hψφ : (algebraMap R k).comp (ψ : R' →+* R) = (φ : R' →+* k) := RingHom.ext hψ
  have hfred : f.map (algebraMap R k) = (X - C (1 : k)) ^ a := by
    rw [hf, Polynomial.map_map, hψφ]
    have : (φ : R' →+* k) = ((θ : κ →+* k).comp (ι.symm : Q.ResidueField →+* κ)).comp
        (algebraMap R' Q.ResidueField) := rfl
    rw [this, ← Polynomial.map_map, ← hf'red, Polynomial.map_map]
    simp [Polynomial.map_pow, Polynomial.map_sub]
  have hf0 : IsUnit (f.coeff 0) := by
    refine IsLocalRing.notMem_maximalIdeal.mp (fun hmem => ?_)
    have hc := congrArg (fun q => Polynomial.coeff q 0) hfred
    simp only [Polynomial.coeff_map] at hc
    rw [← h𝔪, ← IsLocalRing.residue_eq_zero_iff] at hmem
    change algebraMap R k (f.coeff 0) = 0 at hmem
    rw [hmem, Polynomial.coeff_zero_eq_eval_zero, eval_pow, eval_sub, eval_X, eval_C, zero_sub] at hc
    exact ((isUnit_one.neg).pow a).ne_zero hc.symm

  obtain ⟨u, w, huw⟩ := hcopfg
  refine ⟨aeval b (w * g), ?_, ?_⟩
  ·
    have key : (w * g) * (w * g) - w * g = -(u * w) * p := by
      rw [hpfg]; linear_combination (w * g) * huw
    have := congrArg (aeval b) key
    rw [map_sub, map_mul, map_mul (aeval b) (-(u * w)) p, hpb', mul_zero] at this
    exact sub_eq_zero.mp this
  ·
    let B' := B ⧸ J
    let π : B →ₐ[R] B' := Ideal.Quotient.mkₐ R J
    have hπ' : (Ideal.Quotient.mk (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) : B → B') = π :=
      rfl
    rw [hπ'] at he₀ ⊢
    set ε : B' := π b with hε
    have hεi : IsIdempotentElem ε := he₀
    have hm0 : ∀ r ∈ 𝔪, algebraMap R B' r = 0 := by
      intro r hr
      rw [IsScalarTower.algebraMap_apply R B B']
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)

    have hpε : aeval ε p = 0 := by rw [hε, aeval_algHom_apply, hpb', map_zero]

    have hfε : aeval ε f = (ε - 1) ^ a := by
      have hdiff : ∀ i, (f - (X - C (1 : R)) ^ a).coeff i ∈ 𝔪 := by
        intro i
        have hc := congrArg (fun q => Polynomial.coeff q i) hfred
        simp only [Polynomial.coeff_map] at hc
        rw [h𝔪, ← IsLocalRing.residue_eq_zero_iff, coeff_sub, map_sub, sub_eq_zero]
        change algebraMap R k (f.coeff i) = algebraMap R k (((X - C (1:R)) ^ a).coeff i)
        rw [hc, ← Polynomial.coeff_map]
        simp
      have h0 := aeval_eq_zero_of_forall_coeff_mem 𝔪 hm0 _ hdiff ε
      rw [map_sub, sub_eq_zero] at h0
      rw [h0, map_pow, map_sub, aeval_X, aeval_C, map_one]
    show π (aeval b (w * g)) = ε
    rw [← aeval_algHom_apply, ← hε]

    have hsplit : aeval ε (w * g) = aeval ε (w * g) * ε + aeval ε (w * g) * (1 - ε) := by ring

    have hB : aeval ε (w * g) * (1 - ε) = 0 := by
      rw [aeval_mul_one_sub_of_isIdempotentElem _ hεi, mul_coeff_zero, map_mul, mul_assoc]
      have h1 : algebraMap R B' (f.coeff 0) * (algebraMap R B' (g.coeff 0) * (1 - ε)) = 0 := by
        rw [← mul_assoc, ← map_mul, ← mul_coeff_zero, ← hpfg,
          ← aeval_mul_one_sub_of_isIdempotentElem _ hεi, hpε, zero_mul]
      rw [(hf0.map (algebraMap R B')).mul_right_eq_zero] at h1
      rw [h1, mul_zero]

    have hA : aeval ε (w * g) * ε = ε := by
      by_cases ha0 : a = 0
      ·
        have hroot : ¬ (p.map (algebraMap R κ)).IsRoot 1 := by
          intro hr
          rw [ha] at ha0
          exact hpκ0 (Polynomial.rootMultiplicity_eq_zero_iff.mp ha0 hr)
        have hp1 : IsUnit (p.eval 1) := by
          refine IsLocalRing.notMem_maximalIdeal.mp (fun hmem => hroot ?_)
          rw [IsRoot, eval_one_map]
          exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
        have hε0 : ε = 0 := by
          have := aeval_mul_self_of_isIdempotentElem p hεi
          rw [hpε, zero_mul] at this
          exact ((hp1.map (algebraMap R B')).mul_right_eq_zero.mp this.symm)
        rw [hε0, mul_zero]
      · have hwg : w * g = 1 - u * f := by linear_combination huw
        obtain ⟨a', ha'⟩ := Nat.exists_eq_succ_of_ne_zero ha0
        rw [hwg, map_sub, map_one, map_mul, hfε, sub_mul, one_mul, mul_assoc, ha', pow_succ, mul_assoc,
          sub_mul, one_mul, hεi.eq, sub_self, mul_zero, mul_zero, sub_zero]
    rw [hsplit, hA, hB, add_zero]

end S_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite
end P2MW
export P2MW.S_HenselianLocalRing_exists_isIdempotentElem_map_eq_of_module_finite (solution)
