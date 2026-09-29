-- Prove2me | solution 1 for IsLocalRing.exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/995ba856-c318-5f35-b631-ecf7c7065ee5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem

set_option autoImplicit false

open IsLocalRing Polynomial

theorem solution
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    (h T : S) [Module.Finite A (S ⧸ Ideal.span ({h} : Set S))]
    (hnil : ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈
      (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S)))) :
    ∃ P : Polynomial A, P.Monic ∧ (∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal A) ∧
      Polynomial.aeval T P ∈ Ideal.span ({h} : Set S) := by
  classical
  set I : Ideal S := Ideal.span ({h} : Set S) with hI
  set M := S ⧸ I
  obtain ⟨k, hk⟩ := hnil
  set t : M := Ideal.Quotient.mk I T with ht

  have hk1 : t ^ (k + 1) ∈ (maximalIdeal A).map (algebraMap A M) := by
    rw [pow_succ']
    exact Ideal.mul_mem_left _ _ hk

  let φ : Module.End A M := Algebra.lmul A M (t ^ (k + 1))
  have hφ : LinearMap.range φ ≤ (maximalIdeal A) • (⊤ : Submodule A M) := by
    rintro m ⟨m', rfl⟩
    rw [Ideal.smul_top_eq_map]
    show t ^ (k + 1) * m' ∈ (maximalIdeal A).map (algebraMap A M)
    exact Ideal.mul_mem_right _ _ hk1
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ (maximalIdeal A) hφ

  have hpt : Polynomial.aeval (t ^ (k + 1)) p = 0 := by
    have h1 : Polynomial.aeval φ p = Algebra.lmul A M (Polynomial.aeval (t ^ (k + 1)) p) := by
      rw [Polynomial.aeval_algHom_apply]
    have h2 := congrArg (fun ψ : Module.End A M => ψ 1) (h1.symm.trans hpφ)
    simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using h2
  refine ⟨Polynomial.expand A (k + 1) p, hpm.expand (Nat.succ_pos k), fun i hi => ?_, ?_⟩
  · rw [Polynomial.coeff_expand (Nat.succ_pos k)]
    split_ifs with hdvd
    · have hlt : i / (k + 1) < p.natDegree := by
        rw [Polynomial.natDegree_expand] at hi
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)
      have := hpc (i / (k + 1))
      exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) this
    · exact Submodule.zero_mem _
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk A, ← Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk, Polynomial.expand_aeval]
    exact hpt

end S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem
end P2MW
export P2MW.S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem (solution)
