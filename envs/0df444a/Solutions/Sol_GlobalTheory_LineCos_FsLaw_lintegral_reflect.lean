-- Prove2me | solution 1 for GlobalTheory.LineCos.FsLaw.lintegral_reflect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:45:06.825973+00:00
-- url     : https://prove2.me/submissions/aaa4dd5d-4c6b-4921-af32-f9bfe4d777e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StereographicMeasureChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LineCos GlobalTheory.LineCos.FsLaw
open GlobalTheory.LineCos
namespace GlobalTheory.LineCos.FsLaw
theorem _root_.solution (g : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, g (1 - t) = ∫⁻ t in Set.Ioo (0 : ℝ) 1, g t := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo,
    ← lintegral_sub_left_eq_self ((Set.Ioo (0 : ℝ) 1).indicator g) 1]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · have : 1 - t ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : 1 - t ∉ Set.Ioo (0 : ℝ) 1 := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]
end GlobalTheory.LineCos.FsLaw
