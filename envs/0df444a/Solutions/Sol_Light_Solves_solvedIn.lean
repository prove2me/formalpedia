-- Prove2me | solution 1 for Light.Solves.solvedIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:52:13.191186+00:00
-- url     : https://prove2.me/submissions/29b5a7a8-b61e-4d79-82e5-c9c022994eb3

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_Light_le_timeUpTo

set_option autoImplicit false
section
open Light
open ThreeSumApsp
namespace Light
namespace Solves
theorem _root_.solution {task : Task} {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hs : Solves task P p Tn need) (hp : PolyNeed need) : SolvedIn task (timeUpTo Tn) :=
  ⟨P, p, Tn, need, hp, hs, fun n _ _ _ _ hu => le_timeUpTo Tn n hu⟩
end Solves
end Light
