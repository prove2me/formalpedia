-- Prove2me | solution 1 for MatchingPolytope.Multi.Valid.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:20:51.57059+00:00
-- url     : https://prove2.me/submissions/5be36c41-9556-45ef-a1b2-daf0a4fe033f

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
namespace Valid
theorem _root_.solution {F' : Finset E} (hV : Valid ends W F) (h : F' ⊆ F) : Valid ends W F' :=
  ⟨fun e he => hV.sub e (h he), fun e he => hV.nodiag e (h he)⟩
end Valid
end MatchingPolytope.Multi
