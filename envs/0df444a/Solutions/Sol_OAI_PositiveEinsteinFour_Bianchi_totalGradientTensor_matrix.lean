-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:31:30.671347+00:00
-- url     : https://prove2.me/submissions/cd296c48-5f5b-4b73-81d7-e24e0c3c350d

import Mathlib
import Definitions.Def_OAIQ091C013
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCoordinateModel
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed twelve real coordinates for the inner generators in the cost calculation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

/-- The fixed coordinates cover every trace-free Bianchi tensor. -/
theorem exists_costParameters (Z : Tensor) (hz : Z.traceFree) (hb : Z.bianchi) :
    ∃ v : Fin 3 → Vec, costParameters v = Z := by
  refine ⟨![radialCoordinate costShape Z, secondCoordinate costShape Z, thirdCoordinate costShape Z], ?_⟩
  exact parameters_reconstruction costShape Z hz hb


end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylLaplacian
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar contraction of the commuted Weyl equation. The compression
coefficient is derived on the actual Bianchi tensor, not taken from a
representation label or assumed as the manuscript's differential equation. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

private theorem totalGradientTensor_coordinates (s : Fin 3) (v : Fin 3 → Vec) :
    totalGradientTensor s (costParameters v) = costParameters (generatorCoordinates s v) := by
  apply Tensor.ext
  · funext a
    change rawGradientGenerator s (costParameters v).matrix a a = _
    rw [generator_coordinates]
    fin_cases a <;> rfl
  · funext a
    change rawGradientGenerator s (costParameters v).matrix (next a) (previous a) = _
    rw [generator_coordinates]
    fin_cases a <;> rfl

theorem totalGradientTensor_matrix_oai (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) :
    (totalGradientTensor s Z).matrix = rawGradientGenerator s Z.matrix := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [totalGradientTensor_coordinates, generator_coordinates]

end

end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix_oai := @OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix_oai
