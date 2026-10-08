-- Prove2me | solution 1 for MazurTransfer.order49_vertical_vertical_at_point
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:38:22.935486+00:00
-- url     : https://prove2.me/submissions/8a6fc517-b28c-4614-a82f-2ad551472031

import Definitions.Def_MazurTransfer_Order49DifferentialCertificateFormulas
import Definitions.Def_MazurTransfer_Order49DoublingCoordinateFormulas
import Definitions.Def_MazurTransfer_Order49SelectionEvaluationData
import Mathlib
import Theorems.Thm_MazurTransfer_order49_vertical_veluXHomogeneous_directional
import Theorems.Thm_MazurTransfer_order49_vertical_vertical_of_polynomial_certificates
import Theorems.Thm_MazurTransfer_order49_vertical_xNumeratorHomogeneous_directional
open Polynomial
theorem MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_directional (W : WeierstrassCurve ℚ) (u v du dv : ℚ) :
    MazurTorsion.Doubling.xNumeratorHomogeneousDirectional W u v du dv * v *
          MazurTorsion.Doubling.completedCubicHomogeneous W u v -
        MazurTorsion.Doubling.xNumeratorHomogeneous W u v *
          (dv * MazurTorsion.Doubling.completedCubicHomogeneous W u v +
            v * MazurTorsion.Doubling.completedCubicHomogeneousDirectional W u v du dv) =
      2 * MazurTorsion.Doubling.completedYNumeratorHomogeneous W u v * (du * v - u * dv) := by
  exact @MazurTransfer.order49_vertical_xNumeratorHomogeneous_directional W u v du dv

theorem MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous_directional (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv : ℚ) :
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
          u v du dv * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v -
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v *
          (dv * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c u v +
            2 * v * MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional b c u v du dv) =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v *
        (du * v - u * dv) := by
  exact @MazurTransfer.order49_vertical_veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v du dv

theorem MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_polynomial_certificates (A B H Kh K N Q Ht : ℚ[X]) (x Nh R Rt : ℚ)
    (hA : A = B) (hKh : Kh = K * N) (hQ : Q = K ^ 2)
    (hHt : Ht = H * N ^ 2)
    (hK : K.eval x ≠ 0) (hN : N.eval x ≠ 0)
    (hleft :
      (derivative A).eval x * H.eval x * Kh.eval x - A.eval x *
          ((derivative H).eval x * Kh.eval x +
            2 * H.eval x * (derivative Kh).eval x) =
        2 * Nh * R)
    (hright :
      (derivative B).eval x * Q.eval x * Ht.eval x - B.eval x *
          ((derivative Q).eval x * Ht.eval x +
            Q.eval x * (derivative Ht).eval x) =
        2 * Rt * K.eval x * N.eval x) :
    Nh * R = Rt := by
  exact @MazurTransfer.order49_vertical_vertical_of_polynomial_certificates A B H Kh K N Q Ht x Nh R Rt hA hKh hQ hHt hK hN hleft hright
namespace MazurTransfer.Order49DifferentialCertificateHelpers
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
end MazurTransfer.Order49DifferentialCertificateHelpers

namespace MazurTransfer.Order49DifferentialCertificateHelpers
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

theorem eval_derivative_completedCubicPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial W u v)).eval x =
      MazurTorsion.Doubling.completedCubicHomogeneousDirectional W
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.completedCubicPolynomial,
    MazurTorsion.Doubling.completedCubicHomogeneousDirectional, derivative_mul,
    derivative_pow]
  ring

theorem eval_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial W u v).eval x =
      MazurTorsion.Doubling.xNumeratorHomogeneous W (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial, MazurTorsion.Doubling.xNumeratorHomogeneous]

theorem eval_derivative_doubleXPolynomial
    (W : WeierstrassCurve ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial W u v)).eval x =
      MazurTorsion.Doubling.xNumeratorHomogeneousDirectional W
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.doubleXPolynomial, MazurTorsion.Doubling.xNumeratorHomogeneousDirectional,
    derivative_sub, derivative_mul, derivative_pow]
  ring

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

theorem eval_derivative_veluXPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ u v)).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional a₆ a₅ a₄ a₃ a₂ a₁ a₀
        (u.eval x) (v.eval x) ((derivative u).eval x)
          ((derivative v).eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneousDirectional, derivative_mul,
    derivative_pow]
  ring

theorem eval_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c u v).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous b c (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous]

theorem eval_derivative_kernelPolynomial
    (b c : ℚ) (u v : ℚ[X]) (x : ℚ) :
    (derivative (MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial b c u v)).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional b c (u.eval x) (v.eval x)
        ((derivative u).eval x) ((derivative v).eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneousDirectional, derivative_sub,
    derivative_mul]
  ring

theorem eval_veluDifferentialPolynomial
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
    (u v : ℚ[X]) (x : ℚ) :
    (MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c u v).eval x =
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
        (u.eval x) (v.eval x) := by
  simp [MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluDifferentialHomogeneous,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelPolynomial, MazurTorsion.Kubert.OrderSevenDoublingDerivative.kernelHomogeneous, MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXPolynomial,
    MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous]

































/-- The vertical homogeneous certificate obtained by differentiating the
abscissa, kernel, and landing polynomial certificates. -/
theorem vertical_at_point
    (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
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
  let p := MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX W
  let h := MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic W
  let f := MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀
  let k := MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel b c
  let n := MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let q := k ^ 2
  let A := MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX a₆ a₅ a₄ a₃ a₂ a₁ a₀ W
  let Kh := MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel b c W
  let Nh := MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W
  let B := MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let Ht := MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  let Rs := MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY W
  let Rt := MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY W' a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
  have hsource :
      (derivative p).eval x * h.eval x - p.eval x * (derivative h).eval x =
        2 * Rs.eval x := by
    have hs := MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_directional W x 1 1 0
    simp only [p, h, Rs, MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleX, MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceCompletedCubic,
      MazurTorsion.Kubert.OrderSevenDoublingDerivative.sourceDoubleCompletedY, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_doubleXPolynomial,
      MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleXPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_completedCubicPolynomial,
      MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_completedCubicPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleCompletedYPolynomial,
      eval_X, eval_one, derivative_X, derivative_one]
    simpa using hs
  have hleft :
      (derivative A).eval x * h.eval x * Kh.eval x - A.eval x *
          ((derivative h).eval x * Kh.eval x +
            2 * h.eval x * (derivative Kh).eval x) =
        2 * Nh.eval x * Rs.eval x := by
    have hv := MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c
      (p.eval x) (h.eval x) ((derivative p).eval x) ((derivative h).eval x)
    have hv' :
        (derivative A).eval x * h.eval x * Kh.eval x - A.eval x *
            ((derivative h).eval x * Kh.eval x +
              2 * h.eval x * (derivative Kh).eval x) =
          Nh.eval x *
            ((derivative p).eval x * h.eval x -
              p.eval x * (derivative h).eval x) := by
      simpa only [A, Kh, Nh, p, h, MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluX, MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedKernel,
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.composedVeluDifferential, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_veluXPolynomial,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluXPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_kernelPolynomial,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_kernelPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluDifferentialPolynomial] using hv
    rw [hv', hsource]
    ring
  have hbase :
      (derivative f).eval x * k.eval x -
          2 * f.eval x * (derivative k).eval x = n.eval x := by
    have hv := MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.veluXHomogeneous_directional a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c x 1 1 0
    simp only [f, k, n, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluX, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseKernel, MazurTorsion.Kubert.OrderSevenDoublingDerivative.baseVeluDifferential,
      MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_veluXPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluXPolynomial,
      MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_kernelPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_kernelPolynomial,
      MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_veluDifferentialPolynomial, eval_X, eval_one, derivative_X,
      derivative_one, eval_zero, mul_one, mul_zero, zero_mul,
      sub_zero] at hv ⊢
    linear_combination hv
  have hcross :
      (derivative f).eval x * q.eval x - f.eval x * (derivative q).eval x =
        k.eval x * n.eval x := by
    simp [q, derivative_pow]
    linear_combination k.eval x * hbase
  have hright :
      (derivative B).eval x * q.eval x * Ht.eval x - B.eval x *
          ((derivative q).eval x * Ht.eval x +
            q.eval x * (derivative Ht).eval x) =
        2 * Rt.eval x * k.eval x * n.eval x := by
    have ht := MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Doubling.xNumeratorHomogeneous_directional W'
      (f.eval x) (q.eval x) ((derivative f).eval x) ((derivative q).eval x)
    have ht' :
        (derivative B).eval x * q.eval x * Ht.eval x - B.eval x *
            ((derivative q).eval x * Ht.eval x +
              q.eval x * (derivative Ht).eval x) =
          2 * Rt.eval x *
            ((derivative f).eval x * q.eval x -
              f.eval x * (derivative q).eval x) := by
      simpa only [B, Ht, Rt, f, q, MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleX,
        MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetCompletedCubic, MazurTorsion.Kubert.OrderSevenDoublingDerivative.targetDoubleCompletedY,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_doubleXPolynomial, MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleXPolynomial,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_derivative_completedCubicPolynomial,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_completedCubicPolynomial,
        MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.eval_doubleCompletedYPolynomial] using ht
    rw [ht', hcross]
    ring
  apply MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_polynomial_certificates A B h Kh k n q Ht x
    (Nh.eval x) (Rs.eval x) (Rt.eval x)
  · simpa only [A, B] using hX
  · simpa only [Kh, k, n] using hkernel
  · rfl
  · simpa only [Ht, h, n] using hlanding
  · simpa only [k] using hK
  · simpa only [n] using hN
  · exact hleft
  · exact hright

end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49DifferentialCertificateHelpers

theorem solution (a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c : ℚ)
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
  exact @MazurTransfer.Order49DifferentialCertificateHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_at_point a₆ a₅ a₄ a₃ a₂ a₁ a₀ b c W W' x hX hkernel hlanding hK hN
#print axioms solution
