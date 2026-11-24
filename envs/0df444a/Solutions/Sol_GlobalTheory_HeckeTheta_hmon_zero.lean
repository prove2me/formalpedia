-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.hmon_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:20:34.183102+00:00
-- url     : https://prove2.me/submissions/0c198e8e-5f6d-46be-b6f6-32c3313ec94d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
namespace GlobalTheory.HeckeTheta
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) : hmon n 0 = 0 := by
  unfold hmon
  split_ifs with h
  · rw [map_zero]; exact zero_pow (by omega)
  · exact zero_pow (by omega)
end GlobalTheory.HeckeTheta
