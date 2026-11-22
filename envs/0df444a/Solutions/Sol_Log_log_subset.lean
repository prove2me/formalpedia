-- Prove2me | solution 1 for Log.log_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:06.207197+00:00
-- url     : https://prove2.me/submissions/5235572a-37e7-452d-813d-6e8ddb3c85f9

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
theorem _root_.solution {c : Conf es} : log es c ⊆ c.1 := fun _ ⟨h, _⟩ => h
end Log
