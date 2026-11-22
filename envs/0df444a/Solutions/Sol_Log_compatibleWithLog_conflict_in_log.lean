-- Prove2me | solution 1 for Log.compatibleWithLog_conflict_in_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:35.387832+00:00
-- url     : https://prove2.me/submissions/5b8c5de3-2bf5-4e1d-b78f-bfa568e00d9b

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R
namespace Log
theorem _root_.solution {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (hconf : R e e') : e ∈ l :=
  h.2.2 e he e' hconf
end Log
