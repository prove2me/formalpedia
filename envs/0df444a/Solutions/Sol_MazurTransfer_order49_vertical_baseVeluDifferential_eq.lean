-- Prove2me | solution 1 for MazurTransfer.order49_vertical_baseVeluDifferential_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:37:30.691736+00:00
-- url     : https://prove2.me/submissions/303b89e1-75bc-4212-9083-6b3f0ff4ffc5

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib
open Polynomial
namespace MazurTransfer.Order49DifferentialCertificateHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingSpecialization

open _root_.MazurTorsion.Kubert.OrderSevenDoublingDerivative



















/-- The generic `F'K - 2FK'` polynomial specializes to the explicit
order-seven differential numerator. -/
theorem baseVeluDifferential_eq (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial d := by
  apply Polynomial.funext
  intro x
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁, MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial, MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring





end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial d := by
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq d
#print axioms solution
