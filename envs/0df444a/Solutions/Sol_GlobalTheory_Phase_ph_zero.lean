-- Prove2me | solution 1 for GlobalTheory.Phase.ph_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:48.102281+00:00
-- url     : https://prove2.me/submissions/45dbd158-ec9c-4706-a140-dcbb29f44bc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}
namespace GlobalTheory.Phase
theorem _root_.solution : Ph 0 := ⟨1, one_pos, by simp⟩
end GlobalTheory.Phase
