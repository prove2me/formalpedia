-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.norm_hmon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:36.858683+00:00
-- url     : https://prove2.me/submissions/cfaab69a-1660-4958-bf7a-9576f61ccedf

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
theorem _root_.solution (n : ℤ) (z : ℂ) : ‖hmon n z‖ = ‖z‖ ^ n.natAbs := by
  unfold hmon
  split_ifs with h
  · rw [norm_pow, Complex.norm_conj]; congr 1; omega
  · rw [norm_pow]; congr 1; omega
end GlobalTheory.HeckeTheta
