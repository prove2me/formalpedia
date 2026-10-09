-- Prove2me | solution 1 for MazurProof.SexticMumford.IntegralOrientedRep.ideal_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:48:48.817373+00:00
-- url     : https://prove2.me/submissions/616a1a7a-298f-4337-9c61-dba50d0f1ae8

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRepresentative =====
section
/-!
# Integral representatives of oriented sextic Picard classes

The balanced Mumford theorem has two logically separate steps.

1. Clear the denominator of an arbitrary invertible fractional ideal.
2. Reduce the resulting integral ideal to a Mumford ideal of degree at most
   the genus.

This file proves the first step for every oriented Picard class and proves
the quadratic Hermite normal form for every primitive integral ideal.  It
uses only structural fractional-ideal and PID theorems, and therefore does
not enumerate ideal classes.  The final theorem isolates balanced reduction
as the exact remaining surjectivity criterion for `classOf`.
-/
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.SexticMumford
noncomputable section
universe u
variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)
namespace IntegralOrientedRep
theorem ideal_ne_bot (R : IntegralOrientedRep M) : R.ideal ≠ ⊥ := by
  intro h
  have hzero :
      (R.unit :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) = 0 := by
    rw [R.coe_unit, h]
    rfl
  exact R.unit.ne_zero hzero
end IntegralOrientedRep
end
end MazurProof.SexticMumford
end

end

theorem solution : type_of% @MazurProof.SexticMumford.IntegralOrientedRep.ideal_ne_bot := @MazurProof.SexticMumford.IntegralOrientedRep.ideal_ne_bot
