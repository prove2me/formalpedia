-- Prove2me | solution 1 for Light.sameFrame_nil_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:14.707173+00:00
-- url     : https://prove2.me/submissions/2731c8c1-b645-4238-82f9-ec5c80e4bcbd

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution {b : ℤ} {m : List ℤ} :
    SameFrame [] (b :: m) ↔ b = 0 ∧ SameFrame [] m :=
  ⟨fun h => ⟨(congrFun h 0).symm, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1.symm
    | succ i => exact congrFun h.2 i⟩
end Light
