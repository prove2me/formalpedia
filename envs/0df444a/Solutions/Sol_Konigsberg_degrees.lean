-- Prove2me | solution 1 for Konigsberg.degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:44:07.751268+00:00
-- url     : https://prove2.me/submissions/a03f1f19-e770-40d9-b0d4-a73451b73a38

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg

set_option autoImplicit true
@[expose] public section
public section
open Konigsberg
namespace Konigsberg
theorem _root_.solution :
    graph.degree 0 = 5 ∧ graph.degree 1 = 3 ∧ graph.degree 2 = 3 ∧ graph.degree 3 = 3 := by
  decide
end Konigsberg
