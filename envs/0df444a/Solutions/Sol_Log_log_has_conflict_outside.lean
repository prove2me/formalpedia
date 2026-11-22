-- Prove2me | solution 1 for Log.log_has_conflict_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:19:24.99614+00:00
-- url     : https://prove2.me/submissions/b8659a8f-725e-49b7-a611-71d66b5a6ba9

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_PES_toFamily_Config
import Theorems.Thm_PES_toFamily_Event
attribute [local simp] PES.enables_iff
attribute [local simp] PES.toFamily_Config
attribute [local simp] PES.toFamily_Event



set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log
namespace Log
theorem _root_.solution {c : Conf es} {e : es.Event} (he : e ∈ log es c) :
    ∃ e' ∉ c.1, e ## e' := by
  simp only [log, Set.mem_ofPred_eq] at he
  exact he.2
end Log
