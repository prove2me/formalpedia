-- Prove2me | solution 1 for InverseZeroSum.Candidate3.posSum_representativeSet_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:33.269726+00:00
-- url     : https://prove2.me/submissions/ca971d85-9d3a-4e42-9374-087d60ab47d2

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {s : ℕ} (S : PosSeq 24)
    {blocks : Fin s → Finset (Fin 24)} {rep : Fin s → Fin 24}
    (hBlocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hRep : ∀ j, rep j ∈ blocks j) :
    posSum S (representativeSet rep) =
      ∑ j : Fin s, (S (rep j) : G) := by
  classical
  have hInj : Function.Injective rep := by
    intro i j hij
    by_contra hne
    have hDisj := hBlocks i j hne
    have hmemj : rep i ∈ blocks j := by
      rw [hij]
      exact hRep j
    exact (Finset.disjoint_left.mp hDisj) (hRep i) hmemj
  unfold posSum representativeSet
  rw [Finset.sum_image]
  intro i _hi j _hj hij
  exact hInj hij
end InverseZeroSum.Candidate3
