-- Prove2me | solution 1 for MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:45:11.061352+00:00
-- url     : https://prove2.me/submissions/d1cfd05e-e3aa-4e66-8d0e-e896786fa5ac

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13SpecialQuotientBasis =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13SpecialQuotientBasis =====
section
/-!
# The literal basis of the fixed N13 special quotient

The selected special divisor has graph ideal `(X²+X,Y)`.  Evaluation on
that graph identifies its affine quotient with
`𝔽₂[X]/(X²+X)`.  The canonical monic power basis on the latter transports
back to the literal quotient basis `{1,x}`.

This file is only the fixed special-fibre endpoint.  It does not assert
that the contraction of an arbitrary generic Picard representative reduces
to this ideal.
-/
open Module
open Polynomial
namespace MazurProof.N13SpecialQuotientBasis
noncomputable section
@[simp] theorem specialData_u_natDegree :
    specialData.u.natDegree = 2 := by
  rw [specialData_u]
  (compute_degree; norm_num)
end
end MazurProof.N13SpecialQuotientBasis
end

end

theorem solution : type_of% @MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree := @MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree
