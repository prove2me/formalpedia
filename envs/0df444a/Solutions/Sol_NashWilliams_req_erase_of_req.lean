-- Prove2me | solution 1 for NashWilliams.req_erase_of_req
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:28:29.681805+00:00
-- url     : https://prove2.me/submissions/44232093-b127-4727-999f-207d04a49828

module
public import Definitions.Def_NashWilliamsLib_Mader
public import Definitions.Def_NashWilliamsLib_Splitting
public import Definitions.Def_NashWilliamsLib_Orientation

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]
omit [DecidableEq ι]
namespace NashWilliams
theorem _root_.solution {K : ℕ} {T : Finset V} {ends : ι → V × V} {F : Finset ι}
    (hreq : Req K T ends F) (s : V) : Req K (T.erase s) ends F := by
  intro S hS hne hneT
  refine hreq S (hS.trans (erase_subset _ _)) hne ?_
  rintro rfl
  by_cases hs : s ∈ S
  · simpa using hS hs
  · exact hneT (erase_eq_of_notMem hs).symm
end NashWilliams
