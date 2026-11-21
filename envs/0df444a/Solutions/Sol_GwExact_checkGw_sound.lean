-- Prove2me | solution 1 for GwExact.checkGw_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:03.899784+00:00
-- url     : https://prove2.me/submissions/34e6b400-d918-41f3-83ee-17cdd8253711

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses
public import Theorems.Thm_GwExact_descCls_holds
public import Theorems.Thm_GwExact_good_leaf
public import Theorems.Thm_GwExact_run_sound


set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {n R l : Nat} (steps : List Nat) (h : checkGw n R l steps = true)
    {col : Nat → Nat} (hcol : GoodPos n R l col) : False := by
  refine run_sound (σ := asg R col) ?_ steps .leaf 0 (good_leaf _) h
  intro db hdb hint c hc
  unfold gwSrc at hc
  cases hb : Nat.beq (Nat.land hint 1) 1
  · rw [hb, Bool.cond_false] at hc
    exact descCls_holds hcol _ hc
  · rw [hb, Bool.cond_true] at hc
    exact hdb _ _ hc
end GwExact
