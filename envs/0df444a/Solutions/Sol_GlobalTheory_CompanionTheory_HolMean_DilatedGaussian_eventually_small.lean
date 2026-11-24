-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.eventually_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:04.010677+00:00
-- url     : https://prove2.me/submissions/54862c2b-3fb8-4cd5-8b19-e0f0e092592e

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
theorem _root_.solution (m n : ℕ) (X : Fin n → ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, (∀ j, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re) ∧
      ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
  have hre : ∀ j, ∀ᶠ z : ℂ in 𝓝 0, 1 / 2 ≤ (Complex.exp (2 * z * X j)).re := by
    intro j
    have hc : Continuous fun z : ℂ => (Complex.exp (2 * z * X j)).re := by fun_prop
    have h0 : (1 / 2 : ℝ) < (Complex.exp (2 * 0 * X j)).re := by norm_num
    exact ((hc.tendsto 0).eventually (lt_mem_nhds h0)).mono fun z hz => hz.le
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ ≤ 2 := by
    have hc : Continuous fun z : ℂ => ‖Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ))‖ := by fun_prop
    have h0 : ‖Complex.exp ((m : ℂ) * 0 * ∑ j, (X j : ℂ))‖ < 2 := by norm_num
    exact ((hc.tendsto 0).eventually (gt_mem_nhds h0)).mono fun z hz => hz.le
  exact (Filter.eventually_all.2 hre).and hn
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
