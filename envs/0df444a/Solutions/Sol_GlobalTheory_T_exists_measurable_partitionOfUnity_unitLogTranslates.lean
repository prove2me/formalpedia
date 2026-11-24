-- Prove2me | solution 1 for GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:33.602091+00:00
-- url     : https://prove2.me/submissions/b0b32e08-7591-4f50-8c1d-775177d05747

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
import Theorems.Thm_GlobalTheory_exists_measurable_nonneg_hasSum_ulog_translates


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  first | exact @GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | exact GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | (intros; apply GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates <;> assumption)
end _root_.GlobalTheory.T
