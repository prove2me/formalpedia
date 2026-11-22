-- Prove2me | solution 1 for Log.compatibleWithLog_log_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:41.716077+00:00
-- url     : https://prove2.me/submissions/77397155-29e8-4f4b-a807-7f1572255752

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R
namespace Log
theorem _root_.solution {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) : l ⊆ σ.1.1 := h.1
end Log
