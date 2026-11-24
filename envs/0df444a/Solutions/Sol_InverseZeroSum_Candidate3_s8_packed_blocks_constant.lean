-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s8_packed_blocks_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:23.172001+00:00
-- url     : https://prove2.me/submissions/4997e912-d634-4c47-b0bf-902c20e6baad

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_representativeSet_card_of_pairwise
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_shortFreeOn_card_sixteen_sum_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_representative_sum_eq_total_of_residual_zero
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (h16 : Length16SumZeroInput) {S : PosSeq 24}
    (c : S039PackingCertificate S) (hs : c.s = 8) :
    ∀ j : Fin c.s, ∀ x ∈ c.blocks j, ∀ y ∈ c.blocks j, S x = S y := by
  classical
  intro j x hx y hy
  let base : Fin c.s → Fin 24 :=
    fun k => Classical.choose (c.block_shortZero k).1
  have hBase : ∀ k, base k ∈ c.blocks k := by
    intro k
    exact Classical.choose_spec (c.block_shortZero k).1
  let repX : Fin c.s → Fin 24 := Function.update base j x
  let repY : Fin c.s → Fin 24 := Function.update base j y
  have hRepX : ∀ k, repX k ∈ c.blocks k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [repX] using hx
    · simpa [repX, hkj] using hBase k
  have hRepY : ∀ k, repY k ∈ c.blocks k := by
    intro k
    by_cases hkj : k = j
    · subst k
      simpa [repY] using hy
    · simpa [repY, hkj] using hBase k
  have hRepXCard : (representativeSet repX).card = c.s :=
    representativeSet_card_of_pairwise c.pairwise_disjoint hRepX
  have hRepYCard : (representativeSet repY).card = c.s :=
    representativeSet_card_of_pairwise c.pairwise_disjoint hRepY
  have hResidualXCard :
      (Finset.univ \ representativeSet repX).card = 16 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hRepXCard, hs]
    decide
  have hResidualYCard :
      (Finset.univ \ representativeSet repY).card = 16 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hRepYCard, hs]
    decide
  have hResidualXFree :=
    c.every_representative_residual_shortFree repX hRepX
  have hResidualYFree :=
    c.every_representative_residual_shortFree repY hRepY
  have hResidualXZero :
      posSum S (Finset.univ \ representativeSet repX) = 0 :=
    shortFreeOn_card_sixteen_sum_zero h16 S hResidualXCard hResidualXFree
  have hResidualYZero :
      posSum S (Finset.univ \ representativeSet repY) = 0 :=
    shortFreeOn_card_sixteen_sum_zero h16 S hResidualYCard hResidualYFree
  have hSumX :
      (∑ k : Fin c.s, (S (repX k) : G)) = totalSum S :=
    representative_sum_eq_total_of_residual_zero S
      c.pairwise_disjoint hRepX hResidualXZero
  have hSumY :
      (∑ k : Fin c.s, (S (repY k) : G)) = totalSum S :=
    representative_sum_eq_total_of_residual_zero S
      c.pairwise_disjoint hRepY hResidualYZero
  have hOther :
      (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
          (S (repX k) : G)) =
        ∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
          (S (repY k) : G) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp [repX, repY, hkj]
  have hSplitX :
      (∑ k : Fin c.s, (S (repX k) : G)) =
        (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
          (S (repX k) : G)) + (S x : G) := by
    calc
      (∑ k : Fin c.s, (S (repX k) : G)) =
          (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
            (S (repX k) : G)) + (S (repX j) : G) :=
        (Finset.sum_erase_add (Finset.univ : Finset (Fin c.s))
          (fun k => (S (repX k) : G)) (Finset.mem_univ j)).symm
      _ = _ := by simp [repX]
  have hSplitY :
      (∑ k : Fin c.s, (S (repY k) : G)) =
        (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
          (S (repY k) : G)) + (S y : G) := by
    calc
      (∑ k : Fin c.s, (S (repY k) : G)) =
          (∑ k ∈ (Finset.univ : Finset (Fin c.s)).erase j,
            (S (repY k) : G)) + (S (repY j) : G) :=
        (Finset.sum_erase_add (Finset.univ : Finset (Fin c.s))
          (fun k => (S (repY k) : G)) (Finset.mem_univ j)).symm
      _ = _ := by simp [repY]
  have hEq :
      (∑ k : Fin c.s, (S (repX k) : G)) =
        ∑ k : Fin c.s, (S (repY k) : G) :=
    hSumX.trans hSumY.symm
  rw [hSplitX, hSplitY, hOther] at hEq
  exact Subtype.ext (add_left_cancel hEq)
end InverseZeroSum.Candidate3
