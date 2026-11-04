-- Prove2me | solution 1 for Light.Meets.of_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:33:37.873882+00:00
-- url     : https://prove2.me/submissions/fd90c9c9-4f69-4e32-870e-9b7deeef5327

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}
namespace Light
namespace Meets
theorem _root_.solution {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : Stmt}
    (hp : P[p]? = some body)
    (h : Ends lim P d body ⟨frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩
end Meets
end Light
