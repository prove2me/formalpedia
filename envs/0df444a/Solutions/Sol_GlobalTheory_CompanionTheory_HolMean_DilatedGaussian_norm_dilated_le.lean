-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.norm_dilated_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:14.161101+00:00
-- url     : https://prove2.me/submissions/94962de4-0321-4351-8f8d-1755108fb073

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedDerivIntegralGaussianExponential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
namespace GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
theorem _root_.solution (m n : ℕ) (X : Fin n → ℝ) (z : ℂ)
    (h1 : ∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re)
    (h2 : ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2) (v : Fin m → Fin n → ℂ) :
    ‖dilated m n X v z‖ ≤ 2 * Real.exp (-Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  unfold dilated
  rw [norm_mul]
  have hre : (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)).re
      = -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 := by
    have e : (-(2 * Real.pi : ℂ)) = ((-(2 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul, Complex.re_sum]
    simp only [Complex.re_sum, Complex.re_mul_ofReal]
  have hS : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 ≤
      ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (h1 j) (sq_nonneg _)
  have hT : ∑ a, ∑ j, (1 / 2 : ℝ) * ‖v a j‖ ^ 2 = (1 / 2) * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    simp only [Finset.mul_sum]
  have key : -(2 * Real.pi) * ∑ a, ∑ j, (Complex.exp (2 * z * X j)).re * ‖v a j‖ ^ 2 ≤
      -Real.pi * ∑ a, ∑ j, ‖v a j‖ ^ 2 := by
    rw [hT] at hS
    nlinarith [Real.pi_pos]
  refine mul_le_mul h2 ?_ (norm_nonneg _) (by norm_num)
  rw [Complex.norm_exp, hre]
  exact Real.exp_le_exp.2 key
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
