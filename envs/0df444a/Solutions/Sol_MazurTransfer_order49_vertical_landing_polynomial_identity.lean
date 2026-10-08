-- Prove2me | solution 1 for MazurTransfer.order49_vertical_landing_polynomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:37:46.64882+00:00
-- url     : https://prove2.me/submissions/b2dd816c-9b66-4b05-9fb4-73da66988853

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























/-- The completed-square cubic of the quotient image is `H * N²`. -/
theorem landing_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d)
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic (MazurTorsion.Kubert.orderSevenFamily d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) ^ 2 := by
  rw [MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq]
  apply Polynomial.funext
  intro x
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic, MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀,
    MazurTorsion.Kubert.orderSevenFamily, MazurTorsion.Kubert.orderSevenQuotient, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC,
    MazurTorsion.Kubert.tateNormalCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d)
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic (MazurTorsion.Kubert.orderSevenFamily d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) ^ 2 := by
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.landing_polynomial_identity d
#print axioms solution
