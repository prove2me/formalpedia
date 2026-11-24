-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:16.232239+00:00
-- url     : https://prove2.me/submissions/8ccde97e-6ff0-4540-9125-16144f02dc10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (y v : ι → ℝ) (s T : ℝ) (hs : |s| ≤ T) :
    Real.exp (-(∑ i, (y i + s * v i) ^ 2) / 2) ≤
      Real.exp (T ^ 2 * (∑ i, v i ^ 2) / 2) * Real.exp (-(∑ i, y i ^ 2) / 4) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (∑ i, y i ^ 2) / 2 - s ^ 2 * ∑ i, v i ^ 2 ≤ ∑ i, (y i + s * v i) ^ 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (y i + 2 * (s * v i))]
  have h2 : s ^ 2 ≤ T ^ 2 := by
    have := abs_nonneg s
    rw [← sq_abs s]
    exact pow_le_pow_left₀ this hs 2
  have h3 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]
end GlobalTheory.CompanionTheory.EisTube
