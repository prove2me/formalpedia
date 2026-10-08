-- Prove2me | solution 1 for MazurTransfer.order49_vertical_veluXHomogeneous_directional
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:37:22.722046+00:00
-- url     : https://prove2.me/submissions/48e5953d-33b0-4ec5-be84-8c52ff96267f

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Mathlib
open Polynomial
namespace MazurTransfer.Order49DifferentialCertificateHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative











/-- Directional numerator identity for a rational function `F / K²`,
where `F` is monic of degree seven and `K = X (X-b) (X-c)`. -/
theorem veluXHomogeneous_directional
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
          u v du dv * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v -
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
          (dv * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v +
            2 * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional b c u v du dv) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v *
        (du * v - u * dv) := by
  simp only [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous]
  ring





































































end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
          u v du dv * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v -
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
          (dv * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v +
            2 * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional b c u v du dv) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v *
        (du * v - u * dv) := by
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv
#print axioms solution
