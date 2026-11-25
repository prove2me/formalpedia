-- Prove2me | solution 1 for NashWilliams.cr_of_joins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:19:27.696262+00:00
-- url     : https://prove2.me/submissions/5a9ceb6e-809b-4c82-ba3c-b65cabbf42ef

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution {s u : V} {p : V × V} (hJ : Joins s u p) {S : Finset V} (hs : s ∉ S) :
    cr p S = if u ∈ S then 1 else 0 := by
  obtain ⟨h | h, -⟩ := hJ <;> subst h <;> by_cases hu : u ∈ S <;> simp [cr, hs, hu]
end NashWilliams
