-- Prove2me | solution 1 for Log.log_logged
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:10.038837+00:00
-- url     : https://prove2.me/submissions/bc46dc82-c081-45bb-abdd-47cfa30d9c70

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
theorem _root_.solution {c : Conf es} {e : es.Event} (h : e ∈ log es c) : logged es e := by
  simp only [log, Set.mem_ofPred_eq] at h
  exact ⟨h.2.choose, h.2.choose_spec.2⟩
end Log
