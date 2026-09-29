-- Prove2me | solution 1 for GeneralCK.mostInformativeBooleanFunction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:33:01.370211+00:00
-- url     : https://prove2.me/submissions/4ec01787-e458-4985-921f-052c39f9d64c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_generalCourtadeKumar_of_finiteHybridBellman
import Theorems.Thm_GeneralCK_finiteHybridBellman

set_option autoImplicit false

theorem solution : GeneralCK.GeneralCourtadeKumar :=
  GeneralCK.generalCourtadeKumar_of_finiteHybridBellman GeneralCK.finiteHybridBellman
