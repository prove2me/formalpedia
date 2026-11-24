-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.norm_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:55.860252+00:00
-- url     : https://prove2.me/submissions/e5b9a33d-822e-4b6a-936b-eb77a4e7d552

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] {z : ι → ℂ} {B : ℝ} (hz : ∀ i, |(z i).re| ≤ B)
    (t : ι → ℝ) : ‖ker z t‖ ≤ Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) := by
  rw [ker, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have h1 : (2 * (Real.pi : ℂ) * ∑ i, z i * t i).re = 2 * Real.pi * ∑ i, (z i).re * t i := by
    have : (2 * (Real.pi : ℂ) * ∑ i, z i * t i) = ((2 * Real.pi : ℝ) : ℂ) * ∑ i, z i * t i := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul, Complex.re_sum]
    simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (z i).re * t i ≤ |(z i).re * t i| := le_abs_self _
    _ = |(z i).re| * |t i| := abs_mul _ _
    _ ≤ B * |t i| := mul_le_mul_of_nonneg_right (hz i) (abs_nonneg _)
end GlobalTheory.CompanionTheory.EisTube
