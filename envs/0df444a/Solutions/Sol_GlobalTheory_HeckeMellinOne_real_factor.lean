-- Prove2me | solution 1 for GlobalTheory.HeckeMellinOne.real_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:41.303604+00:00
-- url     : https://prove2.me/submissions/603f3bfa-0ac7-4093-89e6-6626f4c8b7ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellinOne
namespace GlobalTheory.HeckeMellinOne
theorem _root_.solution (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key
end GlobalTheory.HeckeMellinOne
