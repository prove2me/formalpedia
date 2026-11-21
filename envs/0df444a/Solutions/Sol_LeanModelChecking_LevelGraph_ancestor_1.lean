-- Prove2me | solution 1 for LeanModelChecking.LevelGraph.ancestor_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:08.220797+00:00
-- url     : https://prove2.me/submissions/718264c8-2ea9-4e0b-ae01-dc73eb24ffb4

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LevelGraph
variable {G : LevelGraph}
namespace LeanModelChecking.LevelGraph
theorem _root_.solution {i j} (hij : i ≤ j) (v : G.level (j + 1)) :
    ancestor hij (G.ex_parent j v).choose = ancestor (show i ≤ j + 1 by omega) v := by
  rewrite (occs := .pos [2]) [ancestor.eq_def]
  by_cases eq : i = j
  · subst eq; simp
  · simp [show i ≠ j + 1 by omega]
end LeanModelChecking.LevelGraph
