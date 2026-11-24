-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.differentiable_dilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:17.362911+00:00
-- url     : https://prove2.me/submissions/5146a398-5875-44f3-b4cf-f9e882cc23c4

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
theorem _root_.solution (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ) :
    Differentiable ℂ (dilated m n X v) := by
  unfold dilated
  fun_prop
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
