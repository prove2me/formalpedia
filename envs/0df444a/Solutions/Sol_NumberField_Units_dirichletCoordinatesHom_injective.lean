-- Prove2me | solution 1 for NumberField.Units.dirichletCoordinatesHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:53:05.31464+00:00
-- url     : https://prove2.me/submissions/28bc467a-33dc-4a0b-8477-0191be783f53

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GaussianUnitSquareclasses =====
section
/-!
# Unit squareclasses in the N13 field

Dirichlet's theorem decomposes the unit group as finite cyclic torsion
times a free abelian group of rank two.  Squaring has index two on the
torsion factor and index `2^2` on the free factor, so the N13 unit
squareclass group has exactly eight elements.  No units are enumerated.
-/
open Finset Module
noncomputable section
namespace MazurProof.UnitSquareClass
end MazurProof.UnitSquareClass
namespace NumberField.Units
variable (K : Type*) [Field K] [NumberField K]
theorem dirichletCoordinatesHom_injective :
    Function.Injective (dirichletCoordinatesHom K) := by
  rintro ⟨ζ, a⟩ ⟨ξ, b⟩ hab
  have hcoords :
      (ζ, a.toAdd) = (ξ, b.toAdd) := by
    apply
      (exist_unique_eq_mul_prod K
        (dirichletCoordinatesHom K (ζ, a))).unique
    · rfl
    · simpa [dirichletCoordinatesHom] using hab
  refine Prod.ext (congrArg Prod.fst hcoords) ?_
  exact Multiplicative.ext
    (congrArg Prod.snd hcoords)
end NumberField.Units
namespace MazurProof.N13GaussianUnitSquareclasses
end MazurProof.N13GaussianUnitSquareclasses
end
end

end

theorem solution : type_of% @NumberField.Units.dirichletCoordinatesHom_injective := @NumberField.Units.dirichletCoordinatesHom_injective
