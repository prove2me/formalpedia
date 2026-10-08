-- Prove2me | solution 1 for MazurTransfer.order49_vertical_kernel_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:37:38.692149+00:00
-- url     : https://prove2.me/submissions/40e05d62-e1db-46dc-8715-a8827d22f8dd

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_vertical_baseVeluDifferential_eq
open Polynomial
theorem MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial d := by
  exact @MazurTransfer.order49_vertical_baseVeluDifferential_eq d
namespace MazurTransfer.Order49DifferentialCertificateHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingSpecialization

open _root_.MazurTorsion.Kubert.OrderSevenDoublingDerivative





















/-- The cubic kernel evaluated at the source doubling forms factors as
`K * N`. -/
theorem kernel_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  rw [MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq]
  apply Polynomial.funext
  intro x
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel, MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX, MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial, MazurTorsion.Kubert.orderSevenFamily,
    MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC, MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring



end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.kernel_polynomial_identity d
#print axioms solution
