-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_left
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:36:45.60601+00:00
-- url     : https://prove2.me/submissions/2ecf6e81-d5d7-408e-8a1e-b70da812c292

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TensorPairing
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Skew matrix actions on the actual four tensor slots. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators

theorem matrixAction_row_sum (s : Fin 3) (M : Mat) (a b : Fin 3) :
    matrixAction s M a b = (∑ c, rotation s a c * M c b) +
      ∑ c, rotation s b c * M a c := by
  unfold matrixAction
  simp only [Finset.sum_sub_distrib]
  have h (c : Fin 3) : M a c * rotation s c b = -(rotation s b c * M a c) := by
    rw [rotation_skew s c b]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

theorem hessianPairing_add_left (X Y Z : Hessian) :
    hessianPairing (X + Y) Z = hessianPairing X Z + hessianPairing Y Z := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (X i j a b + Y i j a b) * Z i j a b) = _
  simp only [add_mul, hessianPairing, Finset.sum_add_distrib]

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestAction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The plus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- Entrywise identification with the four-slot Kronecker-sum matrix. -/
theorem totalPlus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalPlus s X) p =
      ∑ q : TensorIndex, plusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalPlus, matrixAction_row_sum, plusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]
  ring

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestMinus
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.coupledOperator_coordinates _root_.OAI.PositiveEinsteinFour.HighestHessian.vectorHessian_hessianVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The minus Casimir energy and curvature bound on actual highest Hessians. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem totalMinus_coordinates (s : Fin 3) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (totalMinus s X) p =
      ∑ q : TensorIndex, minusKernel s p q * tensorCoordinates X q := by
  rcases p with ⟨i, j, a, b⟩
  simp [tensorCoordinates, totalMinus, minusKernel,
    Fintype.sum_prod_type, add_mul, Finset.sum_add_distrib, ite_mul, ite_and]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestSquare
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted positive square on the actual highest-Hessian arrays. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

private theorem tensorCoordinates_add (X Y : Hessian) (p : TensorIndex) :
    tensorCoordinates (X + Y) p = tensorCoordinates X p + tensorCoordinates Y p := rfl

theorem totalPlus_add (s : Fin 3) (X Y : Hessian) :
    totalPlus s (X + Y) = totalPlus s X + totalPlus s Y := by
  funext i j a b
  change tensorCoordinates (totalPlus s (X + Y)) (i, j, a, b) =
    tensorCoordinates (totalPlus s X) (i, j, a, b) +
      tensorCoordinates (totalPlus s Y) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_add, mul_add,
    Finset.sum_add_distrib]

theorem totalMinus_add (s : Fin 3) (X Y : Hessian) :
    totalMinus s (X + Y) = totalMinus s X + totalMinus s Y := by
  funext i j a b
  change tensorCoordinates (totalMinus s (X + Y)) (i, j, a, b) =
    tensorCoordinates (totalMinus s X) (i, j, a, b) +
      tensorCoordinates (totalMinus s Y) (i, j, a, b)
  simp only [totalMinus_coordinates, tensorCoordinates_add, mul_add,
    Finset.sum_add_distrib]

end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The exact prescribed trace in arbitrary matrix coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem generalCurvaturePairing_add_left_oai (A U : Mat) (X Y Z : Hessian) :
    generalCurvaturePairing A U (X + Y) Z =
      generalCurvaturePairing A U X Z + generalCurvaturePairing A U Y Z := by
  simp only [generalCurvaturePairing, totalPlus_add, totalMinus_add,
    hessianPairing_add_left, mul_add, Finset.sum_add_distrib]
  ring

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_left_oai := @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_add_left_oai
