-- Prove2me | solution 1 for Log.logged_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:18:17.196291+00:00
-- url     : https://prove2.me/submissions/742307b9-3a97-4114-a3e2-b7c6b24de121

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_ConfFamily_TraceEquivFrom_symm


set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open Log
namespace Log
theorem _root_.solution {e e' : es.Event} (h : e ## e') : logged es e' :=
  ⟨e, (minimalConflict_symm es).symm _ _ h⟩
end Log
