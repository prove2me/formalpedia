-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.aeval_mem_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:12:33.256604+00:00
-- url     : https://prove2.me/submissions/b97ed9e8-e44f-4df7-98a6-fbb5953f4450

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin
import Theorems.Thm_GlobalTheory_CycSpanFin_pow_mem_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution (T : Module.End ℂ V) {Q : ℂ[X]} (hQ : Q ≠ 0) {N : Submodule ℂ V}
    (hN : ∀ v ∈ N, aeval T Q v = 0) (p : ℂ[X]) {v : V} (hv : v ∈ N) : aeval T p v ∈ ext T Q.natDegree N := by
  set Q' := Q * C Q.leadingCoeff⁻¹ with hQ'
  have hm : Q'.Monic := monic_mul_leadingCoeff_inv hQ
  have hdeg : Q'.natDegree = Q.natDegree := by
    rw [hQ', natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.2 hQ))]
  have hQ'v : aeval T Q' v = 0 := by
    rw [hQ', mul_comm, map_mul, Module.End.mul_apply, hN v hv, map_zero]
  have hsplit : p = p %ₘ Q' + (p /ₘ Q') * Q' := by
    rw [mul_comm]; exact (modByMonic_add_div p Q').symm
  rw [hsplit, map_add, LinearMap.add_apply, map_mul, Module.End.mul_apply, hQ'v, map_zero, add_zero]
  have hlt : (p %ₘ Q').natDegree < Q.natDegree + 1 := by
    have := natDegree_modByMonic_le p hm
    omega
  rw [aeval_eq_sum_range' hlt, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (pow_mem_ext T (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hv)
end GlobalTheory.CycSpanFin
