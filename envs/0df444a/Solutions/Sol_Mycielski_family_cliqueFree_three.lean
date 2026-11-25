-- Prove2me | solution 1 for Mycielski.family_cliqueFree_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:36.754825+00:00
-- url     : https://prove2.me/submissions/28d66f0f-d241-4cb3-9846-cef5a1a17a1f

module
public import Definitions.Def_Mycielski_Coloring
public import Definitions.Def_Mycielski_Family
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_cliqueFree_three
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_shadow_adj_original
attribute [local simp] Mycielski.apex_adj_shadow
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.shadow_adj_original



set_option autoImplicit true
@[expose] public section
public section
open Mycielski
open SimpleGraph
namespace Mycielski
theorem _root_.solution (n : ℕ) : (family n).CliqueFree 3 := by
  induction n with
  | zero =>
    intro s hs
    have hcard := hs.card_eq
    have hle := Finset.card_le_univ s
    change s.card ≤ Fintype.card (Fin 2) at hle
    simp only [Fintype.card_fin] at hle
    omega
  | succ n ih => exact cliqueFree_three ih
end Mycielski
