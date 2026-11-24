-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.gq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:22.323395+00:00
-- url     : https://prove2.me/submissions/967559dc-74a9-40a8-a941-5fc2b2b69b4a

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
omit [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution (σ : E →+* E) (g : ℕ) :
    Gq (r := 0) σ 1 (1 + 2 * g) !![-1 - (g : E)] = (g : E) ^ 2 := by
  simp [Gq, lead]
  ring
end GlobalTheory.SgGlob.Inhab
