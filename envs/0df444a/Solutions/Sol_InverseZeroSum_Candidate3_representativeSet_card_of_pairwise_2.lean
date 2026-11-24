-- Prove2me | solution 2 for InverseZeroSum.Candidate3.representativeSet_card_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T05:26:45.39734+00:00
-- url     : https://prove2.me/submissions/1eb760e6-9f51-40b6-b5dc-e9f99858ae85

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution {s : ℕ}
    {blocks : Fin s → Finset (Fin 24)} {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j) :
    (representativeSet rep).card = s := by
  have hinj : Function.Injective rep := by
    intro i j hij; by_contra hne
    exact (Finset.disjoint_left.mp (hBlocks i j hne)) (hRep i) (hij.symm ▸ hRep j)
  simp [representativeSet,Finset.card_image_of_injective _ hinj]
