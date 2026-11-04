-- Prove2me | solution 1 for Light.sameFrame_cons_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:13.657992+00:00
-- url     : https://prove2.me/submissions/56b85116-6104-4072-9588-c64bc7d98cba

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {a : ℤ} {l : List ℤ} :
    SameFrame (a :: l) [] ↔ a = 0 ∧ SameFrame l [] :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩
end Light
