-- Prove2me | solution 1 for Light.Meets.mono_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:11.868732+00:00
-- url     : https://prove2.me/submissions/b944644f-cb43-465d-8297-095c095b8711

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
public import Theorems.Thm_Light_Meets_mono_time

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
namespace Light
namespace Meets
theorem _root_.solution {c c' S : ℕ} (h : Meets lim P p d vals μ (c * S) R) (hc : c ≤ c') :
    Meets lim P p d vals μ (c' * S) R :=
  h.mono_time (Nat.mul_le_mul_right _ hc)
end Meets
end Light
