-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.DilatedGaussian.continuous_dilated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:38:16.424438+00:00
-- url     : https://prove2.me/submissions/bcaa7b72-daa3-4416-a456-229a33057e68

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
theorem _root_.solution (m n : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    Continuous (fun v : Fin m → Fin n → ℂ => dilated m n X v z) := by
  unfold dilated
  first
  | fun_prop
  | exact continuous_const.mul (Continuous.cexp (continuous_const.mul
      (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun j _ => continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_norm.comp ((continuous_apply j).comp (continuous_apply a))).pow 2)))))
end GlobalTheory.CompanionTheory.HolMean.DilatedGaussian
