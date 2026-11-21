-- Prove2me | solution 1 for LeanModelChecking.LevelGraph.ex_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:36.011397+00:00
-- url     : https://prove2.me/submissions/98d4b92e-67f6-4882-a2c4-ba425240a71f

module
public import Definitions.Def_LeanPool_LeanModelChecking_LTLNBWStatement
public import Definitions.Def_LeanPool_LeanModelChecking_ABW
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Order.KonigLemma
public import Definitions.Def_LeanPool_LeanModelChecking_ABWNBW
public import Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_refl
public import Theorems.Thm_LeanModelChecking_LevelGraph_ancestor_trans
public import Theorems.Thm_LeanModelChecking_LevelGraph_choose_eq

set_option autoImplicit true
@[expose] public section
public section
open LeanModelChecking
open LeanModelChecking.LevelGraph
namespace LeanModelChecking.LevelGraph
theorem _root_.solution (G : LevelGraph) : Nonempty (Path G) := by
  have := G.fin
  have := G.nonempty
  obtain ⟨f, pf⟩ := exists_seq_forall_proj_of_forall_finite
    (@ancestor G)
    (@ancestor_refl G)
    (@ancestor_trans G)
    (by intros; apply Subtype.finite)
  exists ?_
  intros i
  specialize pf (show i ≤ i + 1 by omega)
  unfold ancestor at pf
  simp only [Nat.left_eq_add, one_ne_zero, ↓reduceDIte, Nat.add_one_sub_one] at pf
  rw [ancestor_refl] at pf
  have := choose_eq _ pf
  assumption
end LeanModelChecking.LevelGraph
