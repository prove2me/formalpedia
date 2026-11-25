-- Prove2me | solution 1 for GlobalTheory.Phase.ph_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:45.109118+00:00
-- url     : https://prove2.me/submissions/275bf59a-b9af-4e15-8bfe-f4e840ade5db

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
theorem _root_.solution : Ph I := ⟨4, by norm_num, by simp [Complex.I_pow_four]⟩
end GlobalTheory.Phase
