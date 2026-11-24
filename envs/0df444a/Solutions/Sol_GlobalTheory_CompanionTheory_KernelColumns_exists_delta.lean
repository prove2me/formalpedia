-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:40:45.020574+00:00
-- url     : https://prove2.me/submissions/3eb2091f-d8bf-4446-adc8-78694f356c1e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecLimOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith
end GlobalTheory.CompanionTheory.KernelColumns
