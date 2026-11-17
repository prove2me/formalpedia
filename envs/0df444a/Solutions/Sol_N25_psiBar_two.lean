-- Prove2me | solution 1 for N25.psiBar_two
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:11.36438+00:00
-- url     : https://prove2.me/submissions/4ccb516f-f8ac-49ee-9e26-4e3b4768c0f3

import Mathlib
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25

namespace N25

/-- The generator two maps to the quintic character value 57. -/
theorem _root_.solution : psiBar (ZMod.unitOfCoprime 2 (by decide)) =
    ZMod.unitOfCoprime 57 (by decide) := rfl

end N25
