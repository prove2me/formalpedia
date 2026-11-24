-- Prove2me | solution 1 for Kirkman.two_mul_card_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:45.108182+00:00
-- url     : https://prove2.me/submissions/1ab5d386-fec3-459f-8c9a-b57c459ebd0e

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Instances
public import Definitions.Def_KirkmanLib_Kirkman

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
namespace Kirkman
theorem _root_.solution {v : ℕ} {𝒯 : Finset (Finset (Fin v))} (h : IsSTS 𝒯) (x : Fin v) :
    2 * #(𝒯.filter (fun T => x ∈ T)) = v - 1 := by
  have hU : (univ : Finset (Fin v)).erase x = (𝒯.filter (fun T => x ∈ T)).biUnion
      (fun T => T.erase x) := by
    ext y
    simp only [mem_erase, mem_univ, and_true, mem_biUnion, mem_filter]
    constructor
    · intro hyx
      obtain ⟨T, ⟨hT, hxT, hyT⟩, -⟩ := h.2 x y (Ne.symm hyx)
      exact ⟨T, ⟨hT, hxT⟩, hyx, hyT⟩
    · rintro ⟨T, -, hyx, -⟩; exact hyx
  have hdisj : (↑(𝒯.filter (fun T => x ∈ T)) : Set (Finset (Fin v))).PairwiseDisjoint
      (fun T => T.erase x) := by
    intro T hT T' hT' hne
    simp only [coe_filter, Set.mem_ofPred_eq] at hT hT'
    rw [Function.onFun, disjoint_left]
    intro y hy hy'
    rw [mem_erase] at hy hy'
    obtain ⟨S, -, hS⟩ := h.2 x y (Ne.symm hy.1)
    exact hne ((hS T ⟨hT.1, hT.2, hy.2⟩).trans (hS T' ⟨hT'.1, hT'.2, hy'.2⟩).symm)
  have := congrArg Finset.card hU
  rw [card_biUnion hdisj, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
  rw [this, sum_congr rfl (g := fun _ => 2), sum_const, smul_eq_mul, mul_comm]
  intro T hT
  rw [mem_filter] at hT
  rw [card_erase_of_mem hT.2, h.1 T hT.1]
end Kirkman
