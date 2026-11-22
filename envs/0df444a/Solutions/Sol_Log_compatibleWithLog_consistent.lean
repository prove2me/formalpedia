-- Prove2me | solution 1 for Log.compatibleWithLog_consistent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:16:55.490372+00:00
-- url     : https://prove2.me/submissions/0174efda-1c6f-4ff2-9b00-6dfd3c88b901

import Definitions.Def_EventStructures_Family_Computation
import Definitions.Def_EventStructures_Family_Log

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Log
local infixl:50 " ⊨ " => compatibleWithLog F R
namespace Log
theorem _root_.solution {σ : Computations F} {l : Set F.Event}
    (h : σ ⊨ l) {e e' : F.Event} (he : e ∈ σ.1.1) (he' : e' ∈ l) : ¬ R e e' :=
  h.2.1 e he e' he'
end Log
