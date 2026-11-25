-- Prove2me | solution 1 for Konigsberg.card_odd_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:39:18.10468+00:00
-- url     : https://prove2.me/submissions/483bf129-b96e-4f98-9b61-47a507e7e1ae

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg

set_option autoImplicit true
@[expose] public section
public section
open Konigsberg
namespace Konigsberg
theorem _root_.solution : Fintype.card {v : Fin 11 | Odd (graph.degree v)} = 4 := by
  decide
end Konigsberg
