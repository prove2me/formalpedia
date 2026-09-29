-- Prove2me | solution 1 for IsDiscreteValuationRing.exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/15230c21-a2e7-5241-89c8-aa315cf5d259

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero

set_option autoImplicit false

open Polynomial IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {F : Type} [Field F] [Algebra 𝒪 F] (hinj : Function.Injective (algebraMap 𝒪 F))
    (ϖ : 𝒪) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal 𝒪) (a x : F)
    (ha : (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval a R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree))
    (hx : x * x - a * x + algebraMap 𝒪 F ϖ = 0) :
    (∃ R : Polynomial 𝒪, R.Monic ∧ Polynomial.aeval x R = 0 ∧
        R.map (IsLocalRing.residue 𝒪) = (Polynomial.X - Polynomial.C 0) ^ R.natDegree) := by
  obtain ⟨S, hSm, hSa, hSmap⟩ := ha

  have haint : IsIntegral 𝒪 a := ⟨S, hSm, by simpa [Polynomial.aeval_def] using hSa⟩

  set A : Subalgebra 𝒪 F := Algebra.adjoin 𝒪 ({a} : Set F) with hA
  haveI : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.adjoin (by simpa using haint)
  have haA : a ∈ A := Algebra.self_mem_adjoin_singleton 𝒪 a
  have hxintA : IsIntegral A x := by
    refine ⟨X ^ 2 + (C (-(⟨a, haA⟩ : A)) * X + C (algebraMap 𝒪 A ϖ)), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add ((degree_linear_le).trans_lt (by norm_num))
    · have h1 : algebraMap A F ⟨a, haA⟩ = a := rfl
      have h2 : algebraMap A F (algebraMap 𝒪 A ϖ) = algebraMap 𝒪 F ϖ :=
        (IsScalarTower.algebraMap_apply 𝒪 A F ϖ).symm
      have h3 : eval₂ (algebraMap A F) x (X ^ 2 + (C (-(⟨a, haA⟩ : A)) * X + C (algebraMap 𝒪 A ϖ)))
          = x * x - a * x + algebraMap 𝒪 F ϖ := by
        simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_neg, map_neg, h1, h2]
        ring
      rw [h3, hx]
  have hxint : IsIntegral 𝒪 x := isIntegral_trans x hxintA

  set B : Subalgebra 𝒪 F := Algebra.adjoin 𝒪 ({a, x} : Set F) with hB
  have hBfg : (Subalgebra.toSubmodule B).FG := fg_adjoin_of_finite (Set.toFinite _) (by
    rintro z hz
    rcases hz with rfl | hz
    · exact haint
    · rw [Set.mem_singleton_iff] at hz; subst hz; exact hxint)
  haveI hBfin : Module.Finite 𝒪 B := Module.Finite.iff_fg.mpr hBfg
  have haB : a ∈ B := Algebra.subset_adjoin (by simp)
  have hxB : x ∈ B := Algebra.subset_adjoin (by simp)
  set a' : B := ⟨a, haB⟩
  set x' : B := ⟨x, hxB⟩

  set I : Ideal B := Ideal.map (algebraMap 𝒪 B) (maximalIdeal 𝒪) with hI
  set π : B →+* B ⧸ I := Ideal.Quotient.mk I
  set ψ : 𝒪 →+* B ⧸ I := π.comp (algebraMap 𝒪 B)
  have hψ : ∀ c ∈ maximalIdeal 𝒪, ψ c = 0 := by
    intro c hc
    show π (algebraMap 𝒪 B c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hc)
  let ψbar : ResidueField 𝒪 →+* B ⧸ I := Ideal.Quotient.lift (maximalIdeal 𝒪) ψ hψ
  have hψbar : ψbar.comp (residue 𝒪) = ψ :=
    RingHom.ext fun c => Ideal.Quotient.lift_mk (maximalIdeal 𝒪) ψ hψ

  have hSa' : aeval a' S = 0 := by
    have h : ((aeval a' S : B) : F) = 0 := by
      rw [Polynomial.aeval_subalgebra_coe]; exact hSa
    exact_mod_cast h
  have ha_pow : (π a') ^ S.natDegree = 0 := by
    have h1 : π (aeval a' S) = 0 := by rw [hSa', map_zero]
    rw [aeval_def, hom_eval₂, ← eval_map] at h1
    change eval (π a') (S.map ψ) = 0 at h1
    rw [← hψbar, ← Polynomial.map_map, hSmap] at h1
    simpa only [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, map_zero, sub_zero, eval_pow,
      eval_X] using h1

  have hx' : x' * x' - a' * x' + algebraMap 𝒪 B ϖ = 0 := by
    apply Subtype.val_injective
    simp [x', a', hx]
  have hx_sq : π x' ^ 2 = π a' * π x' := by
    have h1 : π (x' * x' - a' * x' + algebraMap 𝒪 B ϖ) = 0 := by rw [hx', map_zero]
    have h2 : π (algebraMap 𝒪 B ϖ) = 0 := hψ ϖ hϖ
    rw [map_add, h2, add_zero, map_sub, map_mul, map_mul, sub_eq_zero] at h1
    rw [pow_two]; exact h1

  set N : ℕ := 2 * S.natDegree + 1 with hN
  have hxN : x' ^ N ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    show π (x' ^ N) = 0
    rw [map_pow, hN, pow_succ, pow_mul, hx_sq, mul_pow, ha_pow, zero_mul, zero_mul]

  set f : Module.End 𝒪 B := Algebra.lmul 𝒪 B (x' ^ N) with hf
  have hrange : LinearMap.range f ≤ maximalIdeal 𝒪 • ⊤ := by
    rintro b ⟨c, rfl⟩
    rw [Ideal.smul_top_eq_map]
    show x' ^ N * c ∈ I
    exact Ideal.mul_mem_right _ _ hxN
  obtain ⟨p, hpm, -, hpc, hpf⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero 𝒪 f
      (maximalIdeal 𝒪) hrange

  have hpB : aeval (x' ^ N) p = 0 := by
    have h1 : Algebra.lmul 𝒪 B (aeval (x' ^ N) p) = 0 := by
      rw [← aeval_algHom_apply]; exact hpf
    have h2 := LinearMap.congr_fun h1 1
    simpa using h2
  have hpF : aeval (x ^ N) p = 0 := by
    have h : ((aeval (x' ^ N) p : B) : F) = 0 := by rw [hpB]; rfl
    rwa [Polynomial.aeval_subalgebra_coe] at h

  have hpmap : p.map (residue 𝒪) = X ^ p.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy k p.natDegree with hk | rfl | hk
    · rw [if_neg hk.ne]
      have hmem : p.coeff k ∈ maximalIdeal 𝒪 :=
        Ideal.pow_le_self (by omega) (hpc k)
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    · rw [if_pos rfl, hpm.coeff_natDegree, map_one]
    · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]

  refine ⟨p.comp (X ^ N), hpm.comp (monic_X_pow N) (by rw [natDegree_X_pow]; omega), ?_, ?_⟩
  · rw [aeval_comp]; simpa using hpF
  · have hmapR : (p.comp (X ^ N)).map (residue 𝒪) = X ^ (N * p.natDegree) := by
      rw [Polynomial.map_comp, hpmap, Polynomial.map_pow, map_X, X_pow_comp, ← pow_mul]
    have hdeg : (p.comp (X ^ N)).natDegree = N * p.natDegree := by
      rw [← (hpm.comp (monic_X_pow N) (by rw [natDegree_X_pow]; omega)).natDegree_map (residue 𝒪),
        hmapR, natDegree_X_pow]
    rw [hmapR, hdeg]; simp

end S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero
end P2MW
export P2MW.S_IsDiscreteValuationRing_exists_monic_aeval_eq_zero_map_residue_eq_X_pow_of_sq_sub_mul_add_eq_zero (solution)
