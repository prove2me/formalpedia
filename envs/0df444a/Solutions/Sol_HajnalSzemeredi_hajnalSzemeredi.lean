-- Prove2me | solution 1 for HajnalSzemeredi.hajnalSzemeredi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:08.560267+00:00
-- url     : https://prove2.me/submissions/dc5c304f-3930-4f0b-b108-1e251cf7cbcf

module
public import Definitions.Def_HajnalSzemeredi_Main
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_HajnalSzemeredi_Final
public import Theorems.Thm_HajnalSzemeredi_hajnalSzemeredi_exact
public import Theorems.Thm_HajnalSzemeredi_card_classes_split
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} [Fintype V]
namespace HajnalSzemeredi
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : ∀ v, G.degree v ≤ r) :
    ∃ C : G.Coloring (Fin (r + 1)), ∀ i j : Fin (r + 1),
      (univ.filter fun v => C v = i).card ≤ (univ.filter fun v => C v = j).card + 1 := by
  -- `n + p = s (r + 1)` con `p ≤ r`
  obtain ⟨s, p, hsp, hp⟩ : ∃ s p : ℕ, Fintype.card V + p = s * (r + 1) ∧ p ≤ r := by
    have e := Nat.div_add_mod (Fintype.card V + r) (r + 1)
    have hm := Nat.mod_lt (Fintype.card V + r) (by omega : 0 < r + 1)
    refine ⟨(Fintype.card V + r) / (r + 1),
      (r + 1) * ((Fintype.card V + r) / (r + 1)) - Fintype.card V, ?_, ?_⟩
    · have e' : (r + 1) * ((Fintype.card V + r) / (r + 1)) =
          (Fintype.card V + r) / (r + 1) * (r + 1) := Nat.mul_comm _ _
      omega
    · omega
  have hdeg : ∀ w, (pad G p).degree w ≤ r := by
    intro w
    rw [← (pad G p).card_neighborFinset_eq_degree]
    cases w with
    | inl u =>
      refine le_trans (card_le_card (t := (G.neighborFinset u).map Function.Embedding.inl)
        fun x hx => ?_) ?_
      · rw [SimpleGraph.mem_neighborFinset] at hx
        cases x with
        | inl v =>
          exact mem_map_of_mem _ ((G.mem_neighborFinset u v).mpr hx)
        | inr j => exact absurd hx (by simp [pad, padAdj])
      · rw [card_map, G.card_neighborFinset_eq_degree]; exact h u
    | inr i =>
      refine le_trans (card_le_card (t := (univ.erase i).map Function.Embedding.inr)
        fun x hx => ?_) ?_
      · rw [SimpleGraph.mem_neighborFinset] at hx
        cases x with
        | inl v => exact absurd hx (by simp [pad, padAdj])
        | inr j =>
          have : i ≠ j := hx
          exact mem_map_of_mem _ (mem_erase.mpr ⟨Ne.symm this, mem_univ _⟩)
      · rw [card_map, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; omega
  obtain ⟨C', hC'⟩ := hajnalSzemeredi_exact (pad G p) r s
    (by rw [Fintype.card_sum, Fintype.card_fin, hsp]) hdeg
  -- restricción a `V`
  refine ⟨SimpleGraph.Coloring.mk (fun v => C' (.inl v)) fun {u v} huv =>
    C'.valid (show (pad G p).Adj (.inl u) (.inl v) from huv), fun i j => ?_⟩
  -- cada clase tiene a lo más un vértice agregado
  have hb : ∀ i, (univ.filter fun t : Fin p => C' (.inr t) = i).card ≤ 1 := by
    intro i
    refine card_le_one.mpr fun a ha b hb => ?_
    by_contra hab
    have hadj : (pad G p).Adj (.inr a) (.inr b) := hab
    exact C'.valid hadj (by rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2])
  have ai : ∀ i, (univ.filter fun v : V => C' (.inl v) = i).card +
      (univ.filter fun t : Fin p => C' (.inr t) = i).card = s := by
    intro i
    rw [← hC' i]
    convert (card_classes_split C' i).symm
  have key : (univ.filter fun v : V => C' (.inl v) = i).card ≤
      (univ.filter fun v : V => C' (.inl v) = j).card + 1 := by
    have := ai i; have := ai j; have := hb i; have := hb j
    omega
  convert key using 3 <;> rfl
end HajnalSzemeredi
