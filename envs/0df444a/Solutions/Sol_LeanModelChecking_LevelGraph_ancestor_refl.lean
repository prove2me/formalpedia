-- Prove2me | solution 1 for LeanModelChecking.LevelGraph.ancestor_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:44:07.124166+00:00
-- url     : https://prove2.me/submissions/16150bf4-e235-49a1-81df-3600cd34af3a

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
theorem _root_.solution {i} (v : G.level i) : ancestor rfl.le v = v := by simp [ancestor]
end LeanModelChecking.LevelGraph
