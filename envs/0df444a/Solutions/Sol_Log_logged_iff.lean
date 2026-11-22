-- Prove2me | solution 1 for Log.logged_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:14.475067+00:00
-- url     : https://prove2.me/submissions/d1c5ead7-efa5-404d-8871-af02c9d90e42

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log
namespace Log
theorem _root_.solution {e : es.Event} : logged es e ↔ ∃ e', e ## e' :=
  Iff.rfl
end Log
