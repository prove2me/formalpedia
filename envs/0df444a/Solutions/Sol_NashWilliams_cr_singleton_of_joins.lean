-- Prove2me | solution 1 for NashWilliams.cr_singleton_of_joins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:21:24.520886+00:00
-- url     : https://prove2.me/submissions/c6b70ddb-8db8-41d0-a3fa-6176d42d23fa

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
theorem _root_.solution {s u : V} {p : V × V} (hJ : Joins s u p) : cr p {s} = 1 := by
  obtain ⟨h | h, hu⟩ := hJ <;> subst h <;> simp [cr, hu]
end NashWilliams
