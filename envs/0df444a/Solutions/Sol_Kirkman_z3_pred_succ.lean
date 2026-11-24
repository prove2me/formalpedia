-- Prove2me | solution 1 for Kirkman.z3_pred_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:07.50188+00:00
-- url     : https://prove2.me/submissions/b1c9f380-7aa5-4c20-8de4-4e002f090b8a

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Definitions.Def_KirkmanLib_Constructions

set_option autoImplicit true
@[expose] public section
public section
open Kirkman
namespace Kirkman
theorem _root_.solution (i : ZMod 3) : i - 1 + 1 = i := by ring
end Kirkman
