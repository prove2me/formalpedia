-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_canonical_shortZero_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:46:49.203816+00:00
-- url     : https://prove2.me/submissions/65731198-2462-44a7-aec7-72ccb137a95f

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_card_two_or_three
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_base_pair_nonzero
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_base_triple_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_baseIndex_fibre_card
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (U : PosSeq 8) (hInj : Squarefree U) (hFree : ShortFree U)
    {I : Finset (Fin 24)}
    (hShort : ShortZero (tripleRep U) I) :
    ∃ a : Fin 8,
      I = (Finset.univ : Finset (Fin 24)).filter
        (fun i => baseIndex i = a) := by
  classical
  rcases shortZero_card_two_or_three hShort with hTwo | hThree
  · obtain ⟨x, y, hxy, hIeq⟩ := Finset.card_eq_two.mp hTwo
    have hZero :
        (U (baseIndex x) : G) + (U (baseIndex y) : G) = 0 := by
      simpa [hIeq, posSum, tripleRep, hxy, add_comm] using hShort.2.2
    exact False.elim (s057_base_pair_nonzero U hFree _ _ hZero)
  · obtain ⟨x, y, z, hxy, hxz, hyz, hIeq⟩ := Finset.card_eq_three.mp hThree
    have hZero :
        (U (baseIndex x) : G) + (U (baseIndex y) : G) +
          (U (baseIndex z) : G) = 0 := by
      simpa [hIeq, posSum, tripleRep, hxy, hxz, hyz,
        add_comm, add_left_comm, add_assoc] using hShort.2.2
    obtain ⟨hxyBase, hyzBase⟩ :=
      s057_base_triple_zero U hInj hFree _ _ _ hZero
    have hSame : ∀ i ∈ I, baseIndex i = baseIndex x := by
      intro i hi
      rw [hIeq] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · rfl
      · exact hxyBase.symm
      · exact (hxyBase.trans hyzBase).symm
    let A : Finset (Fin 24) :=
      Finset.univ.filter (fun i => baseIndex i = baseIndex x)
    have hSub : I ⊆ A := by
      intro i hi
      simpa [A] using hSame i hi
    have hACard : A.card = 3 := s057_baseIndex_fibre_card _
    have hEq : I = A := by
      apply Finset.eq_of_subset_of_card_le hSub
      omega
    exact ⟨baseIndex x, hEq⟩
end InverseZeroSum.Candidate3
