-- Prove2me | solution 1 for MatrixTree.mk_tl_hd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:35.651933+00:00
-- url     : https://prove2.me/submissions/5fb5003b-c38b-41f4-b821-7f130643296d

module
public import Mathlib
public import Definitions.Def_MatrixTreeLib_MatrixTree

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open MatrixTree
variable {V : Type*}
namespace MatrixTree
theorem _root_.solution (e : Sym2 V) : s(tl e, hd e) = e := Quot.out_eq e
end MatrixTree
