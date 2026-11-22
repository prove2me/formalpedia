-- Prove2me | solution 1 for Log.label_mem_labelLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:14.89379+00:00
-- url     : https://prove2.me/submissions/f2f940a6-be51-47fd-ab12-0f970270ed77

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R
namespace Log
theorem _root_.solution {l : Set F.Event} {e : F.Event} (h : e ∈ l) :
    F.label e ∈ labelLog F l := ⟨e, h, rfl⟩
end Log
