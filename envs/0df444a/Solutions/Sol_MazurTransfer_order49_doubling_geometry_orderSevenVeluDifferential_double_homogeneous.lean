-- Prove2me | solution 1 for MazurTransfer.order49_doubling_geometry_orderSevenVeluDifferential_double_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:47:13.014143+00:00
-- url     : https://prove2.me/submissions/3edfcbb3-43ad-426e-bfb6-7085abf7f1e5

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DirectArithmeticData
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Definitions.Def_MazurTransfer_Order49SevenIsogenyGeometryFormulas
import Mathlib
import Theorems.Thm_MazurTransfer_order49_doubling_geometry_derivative_doubleX_certificate
import Theorems.Thm_MazurTransfer_order49_vertical_baseVeluDifferential_eq
import Theorems.Thm_MazurTransfer_order49_vertical_kernel_polynomial_identity
import Theorems.Thm_MazurTransfer_order49_vertical_landing_polynomial_identity
import Theorems.Thm_MazurTransfer_order49_vertical_vertical_at_point
open Polynomial
open _root_.WeierstrassCurve
open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.Point hiding neg_zero
theorem MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_at_point (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (W W' : WeierstrassCurve ℚ) (x : ℚ)
    (hX : MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀ W =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hkernel : MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel b c W =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c * MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c)
    (hlanding :
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c =
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic W *
          MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c ^ 2)
    (hK : (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c).eval x ≠ 0)
    (hN : (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x ≠ 0) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W).eval x *
        (MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY W).eval x =
      (MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c).eval x := by
  exact @MazurTransfer.order49_vertical_vertical_at_point a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W W' x hX hkernel hlanding hK hN

theorem MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial d := by
  exact @MazurTransfer.order49_vertical_baseVeluDifferential_eq d

theorem MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.kernel_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  exact @MazurTransfer.order49_vertical_kernel_polynomial_identity d

theorem MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.landing_polynomial_identity (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d)
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic (MazurTorsion.Kubert.orderSevenFamily d) *
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃ d)
          (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁ d) (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀ d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) ^ 2 := by
  exact @MazurTransfer.order49_vertical_landing_polynomial_identity d

theorem MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.derivative_doubleX_certificate (d : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenFamily d) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX
        (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) := by
  apply MazurTransfer.order49_doubling_geometry_derivative_doubleX_certificate <;> assumption
namespace MazurTransfer.Order49DifferentialFromExactHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Doubling

















@[simp] theorem xNumeratorHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneous W x 1 = MazurTorsion.Doubling.xNumerator W x := by
  simp only [MazurTorsion.Doubling.xNumeratorHomogeneous, MazurTorsion.Doubling.xNumerator]
  ring

@[simp] theorem completedYNumeratorHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    MazurTorsion.Doubling.completedYNumeratorHomogeneous W x 1 = MazurTorsion.Doubling.completedYNumerator W x := by
  simp only [MazurTorsion.Doubling.completedYNumeratorHomogeneous, MazurTorsion.Doubling.completedYNumerator]
  ring

@[simp] theorem completedCubicHomogeneous_at_one
    (W : WeierstrassCurve ℚ) (x : ℚ) :
    MazurTorsion.Doubling.completedCubicHomogeneous W x 1 = MazurTorsion.Doubling.completedCubic W x := by
  simp only [MazurTorsion.Doubling.completedCubicHomogeneous, MazurTorsion.Doubling.completedCubic]
  ring









end MazurTorsion.Doubling

end
end MazurTransfer.Order49DifferentialFromExactHelpers

namespace MazurTransfer.Order49DifferentialFromExactHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative



























theorem eval_completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial W u v).eval x =
      MazurTorsion.Doubling.completedCubicHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial, MazurTorsion.Doubling.completedCubicHomogeneous]



theorem eval_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial W u v).eval x =
      MazurTorsion.Doubling.xNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial, MazurTorsion.Doubling.xNumeratorHomogeneous]



theorem eval_doubleCompletedYPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleCompletedYPolynomial W u v).eval x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleCompletedYPolynomial,
    MazurTorsion.Doubling.completedYNumeratorHomogeneous]

theorem eval_veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous]



theorem eval_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c u v).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous]



theorem eval_veluDifferentialPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
        (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous]



































end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49DifferentialFromExactHelpers

namespace MazurTransfer.Order49DifferentialFromExactHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingSpecialization

open OrderSevenDoublingDerivative

















@[simp] theorem differentialPolynomial_eval (d x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial d).eval x =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingSpecialization.differentialPolynomial,
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator]







end MazurTorsion.Kubert.OrderSevenDoublingSpecialization

end MazurTransfer.Order49DifferentialFromExactHelpers

namespace MazurTransfer.Order49DifferentialFromExactHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert













@[simp] theorem orderSevenVeluXNumeratorHomogeneous_at_one
    (d x : ℚ) :
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d x 1 =
      MazurTorsion.Kubert.orderSevenVeluXNumerator d x := by
  simp only [MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluXNumerator]
  ring



private theorem derivativeVeluXHomogeneous_eq
    (d u v : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) u v =
      MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous d u v := by
  simp only [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluXNumeratorHomogeneous, MazurTorsion.Kubert.orderSevenVeluA6,
    MazurTorsion.Kubert.orderSevenVeluA5, MazurTorsion.Kubert.orderSevenVeluA4, MazurTorsion.Kubert.orderSevenVeluA3,
    MazurTorsion.Kubert.orderSevenVeluA2, MazurTorsion.Kubert.orderSevenVeluA1, MazurTorsion.Kubert.orderSevenVeluA0,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀]
  ring

private theorem derivativeVeluDifferentialHomogeneous_eq
    (d u v : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d) u v =
      MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d u v := by
  simp only [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous,
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous, MazurTorsion.Kubert.orderSevenVeluA6,
    MazurTorsion.Kubert.orderSevenVeluA5, MazurTorsion.Kubert.orderSevenVeluA4, MazurTorsion.Kubert.orderSevenVeluA3,
    MazurTorsion.Kubert.orderSevenVeluA2, MazurTorsion.Kubert.orderSevenVeluA1, MazurTorsion.Kubert.orderSevenVeluA0,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₆,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₅,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₄,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₃,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₂,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₁,
    MazurTorsion.Kubert.OrderSevenDoublingSpecialization.a₀,
    MazurTorsion.Kubert.orderSevenB, MazurTorsion.Kubert.orderSevenC]
  ring









private theorem orderSevenVeluDifferential_double_homogeneous
    (d x : ℚ)
    (hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0)
    (hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
          MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  have hK' :
      (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel
        (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d)).eval x ≠ 0 := by
    simpa [MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel,
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial,
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous,
      MazurTorsion.Kubert.orderSevenKernelPolynomial] using hK
  have hN' :
      (MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential
        (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
        (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
        (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
        (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d)).eval x ≠ 0 := by
    rw [MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.baseVeluDifferential_eq]
    simpa using hN
  have h := MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_at_point
    (MazurTorsion.Kubert.orderSevenVeluA6 d) (MazurTorsion.Kubert.orderSevenVeluA5 d)
    (MazurTorsion.Kubert.orderSevenVeluA4 d) (MazurTorsion.Kubert.orderSevenVeluA3 d)
    (MazurTorsion.Kubert.orderSevenVeluA2 d) (MazurTorsion.Kubert.orderSevenVeluA1 d)
    (MazurTorsion.Kubert.orderSevenVeluA0 d) (MazurTorsion.Kubert.orderSevenB d) (MazurTorsion.Kubert.orderSevenC d)
    (MazurTorsion.Kubert.orderSevenFamily d) (MazurTorsion.Kubert.orderSevenQuotient d) x
    (MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.derivative_doubleX_certificate d)
    (MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.kernel_polynomial_identity d)
    (MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingSpecialization.landing_polynomial_identity d)
    hK' hN'
  have h' := h
  simp only [MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluDifferentialPolynomial,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleXPolynomial,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_completedCubicPolynomial,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleCompletedYPolynomial,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluXPolynomial,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_kernelPolynomial,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_at_one,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Doubling.completedCubicHomogeneous_at_one,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Doubling.completedYNumeratorHomogeneous_at_one] at h'
  rw [MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.derivativeVeluDifferentialHomogeneous_eq,
    MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.derivativeVeluXHomogeneous_eq] at h'
  simpa [MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous,
    MazurTorsion.Kubert.orderSevenKernelPolynomial] using h'





































end MazurTorsion.Kubert

end MazurTransfer.Order49DifferentialFromExactHelpers

theorem solution (d x : ℚ)
    (hK : MazurTorsion.Kubert.orderSevenKernelPolynomial d x ≠ 0)
    (hN : MazurTorsion.Kubert.orderSevenVeluDifferentialNumerator d x ≠ 0) :
    MazurTorsion.Kubert.orderSevenVeluDifferentialNumeratorHomogeneous d
        (MazurTorsion.Doubling.xNumerator (MazurTorsion.Kubert.orderSevenFamily d) x)
        (MazurTorsion.Doubling.completedCubic (MazurTorsion.Kubert.orderSevenFamily d) x) *
          MazurTorsion.Doubling.completedYNumerator (MazurTorsion.Kubert.orderSevenFamily d) x =
      MazurTorsion.Doubling.completedYNumeratorHomogeneous (MazurTorsion.Kubert.orderSevenQuotient d)
        (MazurTorsion.Kubert.orderSevenVeluXNumerator d x)
        (MazurTorsion.Kubert.orderSevenKernelPolynomial d x ^ 2) := by
  apply MazurTransfer.Order49DifferentialFromExactHelpers.MazurTorsion.Kubert.orderSevenVeluDifferential_double_homogeneous <;> assumption
#print axioms solution
