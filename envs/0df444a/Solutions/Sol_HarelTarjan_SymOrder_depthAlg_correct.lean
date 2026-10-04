-- Prove2me | solution 1 for HarelTarjan.SymOrder.depthAlg_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:08:44.166613+00:00
-- url     : https://prove2.me/submissions/1ecd5de3-c2a5-45ff-94f5-7666001f94fd

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms
import Theorems.Thm_HarelTarjan_SymOrder_lemma2_descendants_range
import Theorems.Thm_HarelTarjan_SymOrder_lemma3_ancestor_number

open HarelTarjan.SymOrder

private theorem sym_injective {d : ℕ} : Function.Injective (@sym d) := by
  intro u v huv
  have hp : IsAncestor u v := (lemma2_descendants_range u v).mpr (by
    rw [huv]
    have h : 1 ≤ 2 ^ height u := Nat.one_le_two_pow
    omega)
  have hq : IsAncestor v u := (lemma2_descendants_range v u).mpr (by
    rw [huv]
    have h : 1 ≤ 2 ^ height v := Nat.one_le_two_pow
    omega)
  exact Subtype.ext (hp.eq_of_length (le_antisymm hp.length_le hq.length_le))

theorem solution {d : ℕ} (v : Vertex d) (d₂ : ℕ) (hd₂ : d₂ ≤ depth v) :
    IsAncestor (ancestorAtDepth v d₂) v ∧ depth (ancestorAtDepth v d₂) = d₂ ∧
      ∀ u : Vertex d, sym u = depthAlgNum v d₂ ↔ u = ancestorAtDepth v d₂ := by
  have hanc : IsAncestor (ancestorAtDepth v d₂) v := List.take_prefix _ _
  have hdep : depth (ancestorAtDepth v d₂) = d₂ := by
    change (v.1.take d₂).length = d₂
    rw [List.length_take]
    exact Nat.min_eq_left hd₂
  refine ⟨hanc, hdep, ?_⟩
  have hheight : height (ancestorAtDepth v d₂) = d - d₂ := by
    change d - depth (ancestorAtDepth v d₂) = d - d₂
    rw [hdep]
  have hnum := (lemma3_ancestor_number v (d - d₂)
    (by unfold height depth at *; omega) (Nat.sub_le _ _)).2
    (ancestorAtDepth v d₂) hanc hheight
  change sym (ancestorAtDepth v d₂) = depthAlgNum v d₂ at hnum
  intro u
  rw [← hnum]
  exact sym_injective.eq_iff
