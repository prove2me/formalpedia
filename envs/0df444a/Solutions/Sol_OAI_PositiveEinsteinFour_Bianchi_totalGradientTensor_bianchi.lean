-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:30:22.570732+00:00
-- url     : https://prove2.me/submissions/8c3ec04b-9cdd-42d6-aba4-667dadcf512d

import Mathlib
import Definitions.Def_OAIQ091C013
import Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.derivativeQuaternion_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawNorm_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

theorem parameters_bianchi (S : Shape) (p k l : Vec) :
    (parameters S p k l).bianchi := by
  rw [Tensor.bianchi_iff]
  intro i
  change S.s i • p - difference S.s i • k +
    (parameters S p k l).auxiliary (next i) - (parameters S p k l).auxiliary (previous i) = 0
  rw [parameters_auxiliary, parameters_auxiliary]
  calc
    _ = (S.s i + (difference S.s (next i) - difference S.s (previous i)) / 3) • p +
        (-difference S.s i + S.s (next i) - S.s (previous i)) • k := by module
    _ = 0 := by
      rw [S.difference_next_sub_previous]
      have hp : S.s i + -3 * S.s i / 3 = 0 := by ring
      have hk : -difference S.s i + S.s (next i) - S.s (previous i) = 0 := by
        unfold difference
        ring
      rw [hp, hk]
      simp

end
end PositiveEinsteinFour.Bianchi

end OAI
end

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

theorem totalGradientTensor_bianchi_oai (s : Fin 3) (Z : Tensor)
    (hz : Z.traceFree) (hb : Z.bianchi) : (totalGradientTensor s Z).bianchi := by
  obtain ⟨v, rfl⟩ := exists_costParameters Z hz hb
  rw [totalGradientTensor_coordinates]
  exact parameters_bianchi _ _ _ _

end

end PositiveEinsteinFour.Bianchi

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi_oai := @OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi_oai
