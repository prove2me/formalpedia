-- Prove2me | solution 1 for MatchingPolytope.Multi.inHull_of_mem_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:53.904994+00:00
-- url     : https://prove2.me/submissions/d8b86c9e-477b-4746-88af-c8191a8bfef6

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_inHull_step

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E] (ends : E → Sym2 V) (W : Finset V) (F : Finset E)
    (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F) :
    InHull (IsPM ends W F) x := by
  suffices h : ∀ n : ℕ, ∀ (ends : E → Sym2 V) (W : Finset V) (F : Finset E),
      W.card + F.card = n → Valid ends W F → ∀ x ∈ Poly ends W F, InHull (IsPM ends W F) x from
    h _ ends W F rfl hV x hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ends W F hn hV x hx
    exact inHull_step (fun ends' W' F' hlt hV' y hy => ih _ (hn ▸ hlt) ends' W' F' rfl hV' y hy)
      hV hx
end MatchingPolytope.Multi
