-- Prove2me | solution 1 for Kirkman.z3_succ_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:19.456837+00:00
-- url     : https://prove2.me/submissions/077a176a-40cf-483e-8648-326834b7bbc9

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Definitions.Def_KirkmanLib_Constructions

set_option autoImplicit true
@[expose] public section
public section
open Kirkman
namespace Kirkman
theorem _root_.solution (i : ZMod 3) : i + 1 - 1 = i := by ring
end Kirkman
