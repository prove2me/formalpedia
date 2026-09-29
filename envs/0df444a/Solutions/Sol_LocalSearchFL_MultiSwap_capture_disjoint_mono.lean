-- Prove2me | solution 1 for LocalSearchFL.MultiSwap.capture_disjoint_mono
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:46:29.450537+00:00
-- url     : https://prove2.me/submissions/46a75341-7f4c-4286-8cec-71986b1393ad

import Mathlib
import Definitions.Def_LocalSearchFL_MultiSwap_capture

namespace LocalSearchFL.MultiSwap

theorem aux_cdm_nbhdSet_disjoint {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS : Cl → Fa) (X Y : Finset Fa) (h : Disjoint X Y) :
    Disjoint (nbhdSet σS X) (nbhdSet σS Y) := by
  rw [Finset.disjoint_left]
  intro j hjX hjY
  simp only [nbhdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hjX hjY
  exact Finset.disjoint_left.mp h hjX hjY

theorem aux_cdm_nbhdSet_mono {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS : Cl → Fa) (X Y : Finset Fa) (h : X ⊆ Y) :
    nbhdSet σS X ⊆ nbhdSet σS Y := by
  intro j hj
  simp only [nbhdSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact h hj

end LocalSearchFL.MultiSwap

open LocalSearchFL.MultiSwap

theorem solution {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (S O X Y : Finset Fa) (hX : X ⊆ S) (hY : Y ⊆ S) :
    (Disjoint X Y → Disjoint (capture σS σO O X) (capture σS σO O Y)) ∧
      (X ⊆ Y → capture σS σO O X ⊆ capture σS σO O Y) := by
  constructor
  · intro hXY
    rw [Finset.disjoint_left]
    intro o hoX hoY
    simp only [capture, Finset.mem_filter] at hoX hoY
    have hd := aux_cdm_nbhdSet_disjoint σS X Y hXY
    have hd' : Disjoint (nbhdSet σS X ∩ nbhd σO o) (nbhdSet σS Y ∩ nbhd σO o) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hd)
    have hsub : (nbhdSet σS X ∩ nbhd σO o) ∪ (nbhdSet σS Y ∩ nbhd σO o) ⊆ nbhd σO o :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd'] at hc
    omega
  · intro hXY o ho
    simp only [capture, Finset.mem_filter] at ho ⊢
    refine ⟨ho.1, lt_of_lt_of_le ho.2 ?_⟩
    have := Finset.card_le_card
      (Finset.inter_subset_inter (aux_cdm_nbhdSet_mono σS X Y hXY) (Finset.Subset.refl (nbhd σO o)))
    omega
