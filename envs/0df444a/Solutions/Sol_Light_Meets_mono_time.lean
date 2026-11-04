-- Prove2me | solution 1 for Light.Meets.mono_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:34:32.613107+00:00
-- url     : https://prove2.me/submissions/f028bdce-4c7a-41d4-aaf8-cd277ae01448

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
public import Theorems.Thm_Light_Meets_mono
public import Theorems.Thm_Light_Ends_mono


set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
namespace Light
namespace Meets
theorem _root_.solution (h : Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR
end Meets
end Light
