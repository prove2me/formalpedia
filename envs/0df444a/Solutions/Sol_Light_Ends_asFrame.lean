-- Prove2me | solution 1 for Light.Ends.asFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:32.221886+00:00
-- url     : https://prove2.me/submissions/599ce752-5c09-4e78-8327-6fe747953b4f

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_LocalsBut_eq_frame

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}
namespace Light
namespace Ends
theorem _root_.solution (h : LocalsBut xs l loc)
    (hs : Ends lim P d s ⟨frame (refreshLocals l loc xs), μ⟩ T Q) :
    Ends lim P d s ⟨loc, μ⟩ T Q := by
  rw [h.eq_frame]
  exact hs
end Ends
end Light
