-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s057_base_triple_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:45:03.216823+00:00
-- url     : https://prove2.me/submissions/83eccc9c-8541-4b92-8e6d-0ef3288917dd

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_s057_base_double_plus_zero
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
    (a b c : Fin 8)
    (hZero : (U a : G) + (U b : G) + (U c : G) = 0) :
    a = b ∧ b = c := by
  classical
  have hab : a = b := by
    by_contra hne
    by_cases hac : a = c
    · have h : (U a : G) + (U a : G) + (U b : G) = 0 := by
        simpa [hac, add_comm, add_left_comm, add_assoc] using hZero
      exact hne (s057_base_double_plus_zero U hInj a b h)
    · by_cases hbc : b = c
      · have h : (U b : G) + (U b : G) + (U a : G) = 0 := by
          simpa [hbc, add_comm, add_left_comm, add_assoc] using hZero
        exact hne (s057_base_double_plus_zero U hInj b a h).symm
      · have hShort : ShortZero U ({a, b, c} : Finset (Fin 8)) := by
          refine ⟨by simp, by simp [hne, hac, hbc], ?_⟩
          simpa [posSum, hne, hac, hbc,
            add_comm, add_left_comm, add_assoc] using hZero
        exact hFree _ hShort
  subst b
  have hac : a = c := s057_base_double_plus_zero U hInj a c hZero
  exact ⟨rfl, hac⟩
end InverseZeroSum.Candidate3
