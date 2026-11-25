-- Prove2me | solution 1 for Mycielski.chromaticNumber_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:27:25.581087+00:00
-- url     : https://prove2.me/submissions/66de6f19-2be5-4ab3-9cc2-38c12c43e307

module
public import Definitions.Def_Mycielski_Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Definitions.Def_Mycielski_Coloring
public import Theorems.Thm_Mycielski_colorable_succ
public import Theorems.Thm_Mycielski_colorable_succ_iff
public import Theorems.Thm_Mycielski_apex_adj_shadow
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
universe u v
namespace Mycielski
theorem _root_.solution {V : Type u} [Finite V] (G : SimpleGraph V) :
    (graph G).chromaticNumber = G.chromaticNumber + 1 := by
  let k := G.chromaticNumber.toNat
  have hk : G.chromaticNumber = (k : ℕ∞) :=
    (ENat.natCast_toNat
      ((chromaticNumber_ne_top_iff_exists).mpr
        ⟨_, colorable_chromaticNumber_of_fintype G⟩)).symm
  have hupper : (graph G).chromaticNumber ≤ ((k + 1 : ℕ) : ℕ∞) :=
    (colorable_succ (colorable_chromaticNumber_of_fintype G)).chromaticNumber_le
  have hlower : ((k + 1 : ℕ) : ℕ∞) ≤ (graph G).chromaticNumber := by
    apply le_chromaticNumber_iff_colorable.mpr
    intro m hm
    cases m with
    | zero =>
      have := hm.isEmpty
      exact isEmptyElim (none : Vertex V)
    | succ m =>
      have hgm := (colorable_succ_iff G m).mp hm
      have hkm : k ≤ m := by
        have := hgm.chromaticNumber_le
        rw [hk] at this
        exact_mod_cast this
      exact Nat.succ_le_succ hkm
  apply le_antisymm
  · simpa only [hk, Nat.cast_add, Nat.cast_one] using hupper
  · simpa only [hk, Nat.cast_add, Nat.cast_one] using hlower
end Mycielski
