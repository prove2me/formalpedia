-- Prove2me | solution 1 for GridHam.pnext_mem_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:31:25.379195+00:00
-- url     : https://prove2.me/submissions/09309b94-1c42-435e-ae10-fc11f459eb88

module
public import Definitions.Def_GridHam_StripSplit
public import Definitions.Def_GridHam_F3

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution {p : List Coord} {x y : Coord} (h : PNext p x y) : y ∈ p := by
  obtain ⟨l1, l2, e⟩ := h
  rw [e]
  simp
end GridHam
