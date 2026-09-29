-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/331f735b-cc11-5bad-9071-472f0684cb45

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped algebraMap in

theorem s2_exists_nonZeroDivisor_coe_mul_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical

  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2

  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)

  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  ·
    exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  ·
    have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem s2_algebraMap_adicCompletion_eq {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] (v : HeightOneSpectrum A) (d : A) :
    algebraMap A (v.adicCompletion K) d = algebraMap K (v.adicCompletion K) (algebraMap A K d) :=
  IsScalarTower.algebraMap_apply A K (v.adicCompletion K) d

theorem solution
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      algebraMap K (v.adicCompletion K) (algebraMap A K d) * a v ∈ v.adicCompletionIntegers K := by
  obtain ⟨d, hd, h⟩ := s2_exists_nonZeroDivisor_coe_mul_mem_adicCompletionIntegers K a
  refine ⟨d, hd, fun v => ?_⟩
  rw [← s2_algebraMap_adicCompletion_eq K v d]
  exact h v

end S_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_mem_nonZeroDivisors_forall_mul_apply_mem_adicCompletionIntegers (solution)
