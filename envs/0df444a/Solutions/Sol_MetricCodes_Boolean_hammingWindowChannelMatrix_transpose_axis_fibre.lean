-- Prove2me | solution 1 for MetricCodes.Boolean.hammingWindowChannelMatrix_transpose_axis_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/dde2d0cf-f5f3-4cf7-89f4-6669cfba919d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentBlockCoefficient_amplitude_sum
import Theorems.Thm_MetricCodes_Boolean_isLevel_hammingWindowBasis
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_axis_inner
import Theorems.Thm_MetricCodes_Boolean_dot_hammingWindowBasis_apply
import Theorems.Thm_MetricCodes_Boolean_hammingAdjacentChannel_restricted_axisDot

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution
    {n k L : ℕ} (hn : 0 < n) (hk : 2 * k ≤ n)
    (hkL : k ≤ L) (hLn : L + k ≤ n)
    (v : EuclideanSpace ℝ (Fin (L - k + 1)))
    (hunit : ‖v‖ = 1)
    (hv : ∀ i : Fin (L - k + 1), 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen :
      Matrix.toEuclideanLin (MetricCodes.hammingJacobiMatrix n k L) v =
        lam • v)
    (x : BinaryWord n) :
    (hammingWindowChannelMatrix n k L v lam)ᵀ *
      matrixAxisLift (fun a : Fin n => hammingAxis x a)
        (hammingWindowFibreMatrix n k L hk v x) =
      Real.sqrt lam • hammingWindowFibreMatrix n k L hk v x := by
  classical
  ext Q p
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ z : Fin n × HammingWindowIndex n k L,
      (hammingAdjacentBlockCoefficient n k L v lam z.2.1 Q.1 *
        hammingAdjacentChannel n k L z.2.1 Q.1
          (hammingWindowBasis n k L Q) z.1 z.2.2.val) *
      (hammingAxis x z.1 *
        (hammingFibreAmplitude n k L v z.2.1 *
          wordHarmonicEmbedding x k z.2.1.val
            (harmonicBasisFunction n k hk p) z.2.2.val))) =
      Real.sqrt lam *
        (hammingFibreAmplitude n k L v Q.1 *
          wordHarmonicEmbedding x k Q.1.val
            (harmonicBasisFunction n k hk p) Q.2.val)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  let h : Function n := harmonicBasisFunction n k hk p
  have hh : IsHarmonic k h :=
    harmonicBasisFunction_isHarmonic n k hk p
  calc
    (∑ target : Fin (L - k + 1),
      ∑ S : Level n (k + target.val),
      ∑ a : Fin n,
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q) a S.val) *
        (hammingAxis x a *
          (hammingFibreAmplitude n k L v target *
            wordHarmonicEmbedding x k target.val h S.val))) =
      ∑ target : Fin (L - k + 1),
        (hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
          hammingFibreAmplitude n k L v target) *
        coordinateDot
          (hammingAdjacentChannel n k L target Q.1
            (hammingWindowBasis n k L Q))
          (hammingAxisTensor x
            (wordHarmonicEmbedding x k target.val h)) := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm, ←
            hammingAdjacentChannel_restricted_axisDot
              n k L x target Q.1
              (hammingWindowBasis n k L Q)
              (wordHarmonicEmbedding x k target.val h)
              (isLevel_hammingWindowBasis n k L Q)
              (IsLevel.wordHarmonicEmbedding hh.1 x target.val),
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S _
          ring
    _ = (∑ target : Fin (L - k + 1),
          hammingAdjacentBlockCoefficient n k L v lam target Q.1 *
            hammingFibreAmplitude n k L v target *
              Real.sqrt
                (hammingSourceChannelCoefficient n k L Q.1 target)) *
          dot (hammingWindowBasis n k L Q)
            (wordHarmonicEmbedding x k Q.1.val h) := by
          simp_rw [hammingAdjacentChannel_axis_inner
            hn hkL hLn x _ Q.1
            (hammingWindowBasis n k L Q) h hh]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro target _
          ring
    _ = Real.sqrt lam *
          (hammingFibreAmplitude n k L v Q.1 *
            wordHarmonicEmbedding x k Q.1.val h Q.2.val) := by
          rw [hammingAdjacentBlockCoefficient_amplitude_sum
            hn hkL hLn v hunit hv lam hlam heigen Q.1,
            dot_hammingWindowBasis_apply]
          ring
end MetricCodes.Boolean
