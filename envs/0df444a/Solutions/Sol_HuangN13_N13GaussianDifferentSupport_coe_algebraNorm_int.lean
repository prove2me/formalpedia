-- Prove2me | solution 1 for HuangN13.N13GaussianDifferentSupport.coe_algebraNorm_int
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T05:50:56.626758+00:00
-- url     : https://prove2.me/submissions/fdeba0cc-8c79-4fc4-982d-dfd9f832c28d

import Definitions.Def_MazurN13_L4

set_option autoImplicit false
attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.numberFieldL MazurProof.N13GaussianDifferentSupport.intAlgebraO


section
set_option autoImplicit false

open Algebra Module Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GaussianDifferentSupport

noncomputable section

open N13GaussianFieldEquiv
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare

open IsDedekindDomain

attribute [local instance] MazurProof.N13GaussianDifferentSupport.fieldL MazurProof.N13GaussianDifferentSupport.numberFieldL MazurProof.N13GaussianDifferentSupport.intAlgebraO

/-- Integral norms in the integral-closure presentation agree with the
field norm after embedding in `ℚ`. -/
private theorem huangN13NormTransfer (x : O) :
    (Algebra.norm ℤ x : ℚ) =
      Algebra.norm ℚ ((x : O) : L) := by
  let xstd : N13GaussianClassNumberOne.O :=
    OToClassNumberOrderAlgEquiv x
  have hcarrier :
      ((xstd : N13GaussianClassNumberOne.O) : L) =
        ((x : O) : L) := by
    rfl
  calc
    (Algebra.norm ℤ x : ℚ) =
        (Algebra.norm ℤ xstd : ℚ) := by
      rw [Algebra.norm_eq_of_algEquiv
        OToClassNumberOrderAlgEquiv x]
    _ =
        Algebra.norm ℚ
          ((xstd : N13GaussianClassNumberOne.O) : L) :=
      Algebra.coe_norm_int xstd
    _ = Algebra.norm ℚ ((x : O) : L) := by
      rw [hcarrier]
end
end MazurProof.N13GaussianDifferentSupport
end

theorem solution (x : MazurProof.N13GaussianDifferentSupport.O) :
    (Algebra.norm ℤ x : ℚ) =
      Algebra.norm ℚ ((x : MazurProof.N13GaussianDifferentSupport.O) : MazurProof.N13GaussianDifferentSupport.L) := by
  exact MazurProof.N13GaussianDifferentSupport.huangN13NormTransfer x
