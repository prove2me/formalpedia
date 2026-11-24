-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.mem_dInv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.592172+00:00
-- url     : https://prove2.me/submissions/326535dc-8721-411e-b749-58310b547c9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (x : E) : x ∈ dInv E 0 ↔ x ∈ Int' E := by
  simp only [dInv, pow_zero, FractionalIdeal.mem_one_iff]
  rfl
end GlobalTheory.SgGlob.Inhab
