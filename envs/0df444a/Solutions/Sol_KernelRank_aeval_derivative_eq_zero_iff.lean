-- Prove2me | solution 1 for KernelRank.aeval_derivative_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:35:38.012798+00:00
-- url     : https://prove2.me/submissions/66b28051-001a-4ba7-9e7e-417911aaa8ee

import Definitions.Def_KernelRankLean_Differential
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_ComplexRank
import Theorems.Thm_KernelRank_linearIndependent_hasseDeriv
import Theorems.Thm_KernelRank_aeval_derivative_apply

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution (q : ℂ[X]) {P : ℂ[X]} (hP : P ≠ 0) :
    aeval (derivative : Module.End ℂ ℂ[X]) q P = 0 ↔
      X ^ (P.natDegree + 1) ∣ q := by
  rw [aeval_derivative_apply, X_pow_dvd_iff]
  constructor
  · intro h k hk
    have hc := Fintype.linearIndependent_iff.mp (linearIndependent_hasseDeriv hP) _ h ⟨k, hk⟩
    exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast k.factorial_ne_zero)
  · intro h
    exact Finset.sum_eq_zero fun k _ => by rw [h k k.2, zero_mul, zero_smul]
end KernelRank
