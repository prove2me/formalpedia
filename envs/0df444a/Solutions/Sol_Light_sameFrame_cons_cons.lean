-- Prove2me | solution 1 for Light.sameFrame_cons_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:12.621328+00:00
-- url     : https://prove2.me/submissions/809244e4-e2b6-4e9c-9d11-46f98b226dab

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {a b : ℤ} {l m : List ℤ} :
    SameFrame (a :: l) (b :: m) ↔ a = b ∧ SameFrame l m :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩
end Light
