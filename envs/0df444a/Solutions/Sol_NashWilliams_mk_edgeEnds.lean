-- Prove2me | solution 1 for NashWilliams.mk_edgeEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:05:07.598047+00:00
-- url     : https://prove2.me/submissions/365c18b2-4717-470d-b050-42c05c587e7f

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Orientation
public import Definitions.Def_NashWilliamsLib_Defs

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V : Type*} (G : SimpleGraph V)
namespace NashWilliams
theorem _root_.solution (e : G.edgeSet) : s((edgeEnds G e).1, (edgeEnds G e).2) = (e : Sym2 V) :=
  Quot.out_eq _
end NashWilliams
