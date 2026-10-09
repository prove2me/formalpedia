-- Prove2me | solution 1 for MazurProof.N13GeneralizedMumfordIntegral.curvePoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:29:18.053642+00:00
-- url     : https://prove2.me/submissions/30c789da-68da-4a18-8dfe-fc6fb93b6ad0

import Mathlib
import Definitions.Def_MazurN13_L0

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GeneralizedMumfordIntegral =====
section
/-!
# Integral generalized Mumford graph quotients for N13

For the good equation

`Y² + (X³ + X + 1)Y = X⁵ + X⁴`,

evaluation on a graph `Y=v mod u` identifies the graph quotient with
`R[X]/(u)` over any nontrivial commutative base ring.  If the base is a
domain and `u` is monic, this quotient is free and hence torsion-free.
Consequently every graph ideal is saturated with respect to each nonzero
base scalar.

This is the elementary integral algebra needed before reduction modulo two;
it uses neither normality of the affine ring nor a Picard scheme.
-/
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
theorem curvePoly_natDegree [Nontrivial R] :
    (curvePoly : R[X][X]).natDegree = 2 := by
  unfold curvePoly
  compute_degree <;> norm_num
namespace TwoAdic
end TwoAdic
end
end MazurProof.N13GeneralizedMumfordIntegral
end

end

theorem solution : type_of% @MazurProof.N13GeneralizedMumfordIntegral.curvePoly_natDegree := @MazurProof.N13GeneralizedMumfordIntegral.curvePoly_natDegree
