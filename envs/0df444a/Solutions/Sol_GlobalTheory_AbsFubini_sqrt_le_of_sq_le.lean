-- Prove2me | solution 1 for GlobalTheory.AbsFubini.sqrt_le_of_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:03.732659+00:00
-- url     : https://prove2.me/submissions/89935edd-a1e3-48b6-8103-545ef164cc37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralKernelLiftsFubiniSigmaFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
open GlobalTheory GlobalTheory.AbsFubini
variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
namespace GlobalTheory.AbsFubini
theorem _root_.solution {I N : ℝ≥0∞} (h : I ≤ N ^ 2) : I ^ (1 / (2:ℝ)) ≤ N := by
  calc I ^ (1 / (2:ℝ)) ≤ (N ^ 2) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = N := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
end GlobalTheory.AbsFubini
