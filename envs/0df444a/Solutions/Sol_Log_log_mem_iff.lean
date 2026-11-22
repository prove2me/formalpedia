-- Prove2me | solution 1 for Log.log_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:12.972612+00:00
-- url     : https://prove2.me/submissions/83765310-0aa5-4c2a-b3a2-95409b7e5156

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
theorem _root_.solution {c : Conf es} {e : es.Event} :
    e ∈ log es c ↔ e ∈ c.1 ∧ ∃ e' ∉ c.1, e ## e' :=
  Iff.rfl
end Log
