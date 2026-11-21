-- Prove2me | solution 1 for LeanModelChecking.LevelGraph.ancestor_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:59.983176+00:00
-- url     : https://prove2.me/submissions/68b01756-5e41-49c1-8b74-d44666dd6dfb

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_refl
public import Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_1

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LevelGraph
variable {G : LevelGraph}
namespace LeanModelChecking.LevelGraph
theorem _root_.solution {i j k} (hij : i ≤ j) (hjk : j ≤ k) (v : G.level k) :
    ancestor hij (ancestor hjk v) = ancestor (hij.trans hjk) v := by
  induction k
  · obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    simp [ancestor]
  next k IH =>
    by_cases jeq : j = k + 1
    · subst jeq
      rw [ancestor_refl]
    · specialize IH (by omega) (G.ex_parent k v).choose
      rwa [ancestor_1, ancestor_1] at IH
end LeanModelChecking.LevelGraph
