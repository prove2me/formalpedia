-- Prove2me | solution 1 for Konigsberg.no_eulerian_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:44:19.130547+00:00
-- url     : https://prove2.me/submissions/07b365bc-c2e0-4501-9aa9-9bf214bb470d

module
public import Definitions.Def_Euler_Basic
public import Mathlib.Tactic.FinCases
public import Definitions.Def_Euler_Konigsberg
public import Theorems.Thm_Konigsberg_card_odd_degree

set_option autoImplicit true
@[expose] public section
public section
open Konigsberg
namespace Konigsberg
theorem _root_.solution : ¬ ∃ u v, ∃ p : graph.Walk u v, p.IsEulerian := by
  rintro ⟨u, v, p, hp⟩
  have := hp.card_odd_degree
  rw [card_odd_degree] at this
  omega
end Konigsberg
