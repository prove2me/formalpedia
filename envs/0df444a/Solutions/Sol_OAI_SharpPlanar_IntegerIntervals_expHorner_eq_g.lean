-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.expHorner_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:08:12.111383+00:00
-- url     : https://prove2.me/submissions/5b6e9213-33ce-46ba-a098-3b1ce6bab7d6

import Mathlib
import Definitions.Def_OAIQ098G072

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

lemma expHorner_eq_g_oai (z : ℂ) (k n : ℕ) :
    expHorner z k n = ∑ i ∈ Finset.range (n+1), z^i/((k+i).factorial:ℂ) := by
  induction n generalizing k with
  | zero => simp [expHorner]
  | succ n ih =>
    rw [expHorner,ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero,Nat.add_zero,one_div]
    rw [add_comm,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ']
    simp only [Nat.add_assoc,Nat.add_comm 1 i,mul_div_assoc]

end IntegerIntervals
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.IntegerIntervals.expHorner_eq_g_oai := @OAI.SharpPlanar.IntegerIntervals.expHorner_eq_g_oai
