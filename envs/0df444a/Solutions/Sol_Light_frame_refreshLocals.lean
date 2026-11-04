-- Prove2me | solution 1 for Light.frame_refreshLocals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:10.466429+00:00
-- url     : https://prove2.me/submissions/4a3f8d4a-f3dc-4003-a20e-7d13c2429b1b

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution (loc : ℕ → ℤ) (y : ℕ) : ∀ (xs : List ℕ) (l : List ℤ),
    frame (refreshLocals l loc xs) y = if y ∈ xs then loc y else frame l y
  | [], l => by simp
  | x :: xs, l => by
    rw [refreshLocals, solution loc y xs, frame_setLocal]
    by_cases hx : y = x
    · subst hx
      simp
    · simp [hx]
end Light
