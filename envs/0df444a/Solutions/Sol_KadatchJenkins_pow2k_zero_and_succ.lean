-- Prove2me | solution 1 for KadatchJenkins.pow2k_zero_and_succ
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-22T02:59:50.172955+00:00
-- url     : https://prove2.me/submissions/260355f8-3971-4978-ac9f-a768185d10f6

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial
namespace KadatchJenkins

theorem pow2k_zero_and_succ (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) :
    pow2k P 0 = X % P ∧ ∀ k, pow2k P (k + 1) = pow2k P k ^ 2 % P := by
  refine ⟨by simp [pow2k], fun k => ?_⟩
  unfold pow2k
  rw [pow_succ, pow_mul, sq, sq]
  exact Polynomial.mul_mod _ _ _

end KadatchJenkins

theorem solution (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) :
    KadatchJenkins.pow2k P 0 = X % P ∧ ∀ k, KadatchJenkins.pow2k P (k + 1) = KadatchJenkins.pow2k P k ^ 2 % P :=
  KadatchJenkins.pow2k_zero_and_succ P hP
