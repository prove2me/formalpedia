-- Prove2me | solution 1 for InverseZeroSum.Candidate3.constant_shortZero_block_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:21.434499+00:00
-- url     : https://prove2.me/submissions/c134e85f-e494-437e-859f-1cefba18822c

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_f3t_self_add_ne_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {S : PosSeq 24}
    {B : Finset (Fin 24)} (hShort : ShortZero S B)
    (hConst : ∀ x ∈ B, ∀ y ∈ B, S x = S y) :
    B.card ≠ 2 := by
  classical
  intro hCard
  obtain ⟨x, hx⟩ := hShort.1
  have hConstSum :
      posSum S B = B.card • (S x : G) := by
    unfold posSum
    calc
      (∑ i ∈ B, (S i : G)) =
          ∑ _i ∈ B, (S x : G) := by
            exact Finset.sum_congr rfl
              (fun i hi => congrArg Subtype.val (hConst i hi x hx))
      _ = B.card • (S x : G) := by simp
  have hTwoG : (2 : ℕ) • (S x : G) = 0 := by
    have hZero := hShort.2.2
    rw [hConstSum, hCard] at hZero
    exact hZero
  have hTwoTn :
      (2 : ℕ) • finiteModelEquiv (S x : G) = 0 := by
    calc
      (2 : ℕ) • finiteModelEquiv (S x : G) =
          finiteModelEquiv ((2 : ℕ) • (S x : G)) :=
        (map_nsmul finiteModelEquiv 2 (S x : G)).symm
      _ = finiteModelEquiv 0 := congrArg finiteModelEquiv hTwoG
      _ = 0 := map_zero finiteModelEquiv
  have hTwoT :
      finiteModelEquiv (S x : G) + finiteModelEquiv (S x : G) = 0 := by
    rw [← two_nsmul]
    exact hTwoTn
  have hNonzeroT : finiteModelEquiv (S x : G) ≠ 0 := by
    intro hZero
    apply (S x).property
    apply finiteModelEquiv.injective
    simpa using hZero
  exact (f3t_self_add_ne_zero (finiteModelEquiv (S x : G)) hNonzeroT) hTwoT
end InverseZeroSum.Candidate3
