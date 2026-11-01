-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:40:10.959158+00:00
-- url     : https://prove2.me/submissions/aab5e3ba-aa64-4c2e-9b14-6c0c3ab493b1

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

theorem hessianPairing_smul_left (r : ℝ) (X Y : Hessian) :
    hessianPairing (r • X) Y = r * hessianPairing X Y := by
  change (∑ a, ∑ b, ∑ i, ∑ j, (r * X i j a b) * Y i j a b) = _
  simp only [mul_assoc, hessianPairing, ← Finset.mul_sum]

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

private theorem tensorCoordinates_smul (r : ℝ) (X : Hessian) (p : TensorIndex) :
    tensorCoordinates (r • X) p = r * tensorCoordinates X p := rfl

theorem totalPlus_smul (s : Fin 3) (r : ℝ) (X : Hessian) :
    totalPlus s (r • X) = r • totalPlus s X := by
  funext i j a b
  change tensorCoordinates (totalPlus s (r • X)) (i, j, a, b) =
    r * tensorCoordinates (totalPlus s X) (i, j, a, b)
  simp only [totalPlus_coordinates, tensorCoordinates_smul, mul_left_comm,
    ← Finset.mul_sum]

theorem totalMinus_smul (s : Fin 3) (r : ℝ) (X : Hessian) :
    totalMinus s (r • X) = r • totalMinus s X := by
  funext i j a b
  change tensorCoordinates (totalMinus s (r • X)) (i, j, a, b) =
    r * tensorCoordinates (totalMinus s X) (i, j, a, b)
  simp only [totalMinus_coordinates, tensorCoordinates_smul, mul_left_comm,
    ← Finset.mul_sum]

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

theorem generalCurvaturePairing_smul_left_oai (A U : Mat) (c : ℝ) (X Y : Hessian) :
    generalCurvaturePairing A U (c • X) Y = c * generalCurvaturePairing A U X Y := by
  have h (a b : ℝ) : a * (c * b) = c * (a * b) := by ring
  simp only [generalCurvaturePairing, totalPlus_smul, totalMinus_smul,
    hessianPairing_smul_left, h, ← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.HighestHessian
end


end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left_oai := @OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left_oai
