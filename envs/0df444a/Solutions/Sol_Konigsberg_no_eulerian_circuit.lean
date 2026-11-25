-- Prove2me | solution 1 for Konigsberg.no_eulerian_circuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:48:59.392553+00:00
-- url     : https://prove2.me/submissions/38471948-e3a0-49aa-88c0-9c0394def1fd

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg
public import Theorems.Thm_Konigsberg_no_eulerian_walk

set_option autoImplicit true
@[expose] public section
public section
open Konigsberg
namespace Konigsberg
theorem _root_.solution : ¬ ∃ u, ∃ p : graph.Walk u u, p.IsEulerian :=
  fun ⟨u, p, hp⟩ => no_eulerian_walk ⟨u, u, p, hp⟩
end Konigsberg
