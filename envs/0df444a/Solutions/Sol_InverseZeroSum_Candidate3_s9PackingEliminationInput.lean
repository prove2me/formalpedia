-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9PackingEliminationInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:57:31.342164+00:00
-- url     : https://prove2.me/submissions/b20b01bf-d208-469a-9886-1425aaafceae

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
public import Theorems.Thm_InverseZeroSum_Candidate3_mem_s039AllBlocks
public import Theorems.Thm_InverseZeroSum_Candidate3_planeSetT_card
public import Theorems.Thm_InverseZeroSum_Candidate3_shortZero_two_block_has_distinct_values
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_swap_fixed_complement_zero
public import Theorems.Thm_InverseZeroSum_Candidate3_s9_certificate_update_representative_mem
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.mem_s039AllBlocks
attribute [local simp] InverseZeroSum.Candidate3.planeSetT_card

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution : S9PackingEliminationInput := by
  classical
  intro S c hs
  have hl : c.l = 6 := by
    rcases c.signature with h | h | h | h <;> omega
  let j : Fin c.s := ⟨6, by omega⟩
  let k : Fin c.s := ⟨7, by omega⟩
  have hjk : j ≠ k := by
    intro heq
    have hval := congrArg Fin.val heq
    norm_num [j, k] at hval
  have hkj : k ≠ j := Ne.symm hjk
  have hjTwo : (c.blocks j).card = 2 := by
    simpa [j, hl] using c.block_card j
  have hkTwo : (c.blocks k).card = 2 := by
    simpa [k, hl] using c.block_card k
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    shortZero_two_block_has_distinct_values (c.block_shortZero j) hjTwo
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    shortZero_two_block_has_distinct_values (c.block_shortZero k) hkTwo
  let base : Fin c.s → Fin 24 :=
    fun i => Classical.choose (c.block_shortZero i).1
  have hBase : ∀ i, base i ∈ c.blocks i := by
    intro i
    exact Classical.choose_spec (c.block_shortZero i).1
  let repJ : Fin c.s → Fin 24 := Function.update base j x
  let repX : Fin c.s → Fin 24 := Function.update repJ k v
  let repY : Fin c.s → Fin 24 := Function.update repJ k w
  have hRepJ : ∀ i, repJ i ∈ c.blocks i :=
    s9_certificate_update_representative_mem c base hBase j hx
  have hRepX : ∀ i, repX i ∈ c.blocks i :=
    s9_certificate_update_representative_mem c repJ hRepJ k hv
  have hRepY : ∀ i, repY i ∈ c.blocks i :=
    s9_certificate_update_representative_mem c repJ hRepJ k hw
  have hRepXJ : repX j = x := by
    simp [repX, repJ, Function.update, hjk]
  have hRepYJ : repY j = x := by
    simp [repY, repJ, Function.update, hjk]
  have hValX : S (repX j) ≠ S y := by
    simpa [hRepXJ] using hxy
  have hValY : S (repY j) ≠ S y := by
    simpa [hRepYJ] using hxy
  have hZeroX :=
    s9_certificate_swap_fixed_complement_zero
      c hs repX hRepX j hy hValX
  have hZeroY :=
    s9_certificate_swap_fixed_complement_zero
      c hs repY hRepY j hy hValY
  let f : Fin 24 → F3T := fun i => finiteModelEquiv (S i : G)
  let E : Finset (Fin c.s) := (Finset.univ : Finset (Fin c.s)).erase j
  have hEq :
      (∑ i ∈ E, f (repX i)) = ∑ i ∈ E, f (repY i) := by
    exact hZeroX.trans hZeroY.symm
  have hkE : k ∈ E :=
    Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
  have hRepXK : repX k = v := by
    simp [repX]
  have hRepYK : repY k = w := by
    simp [repY]
  have hOther :
      (∑ i ∈ E.erase k, f (repX i)) =
      ∑ i ∈ E.erase k, f (repY i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    simp [repX, repY, Function.update, hik]
  have hSplitX :
      (∑ i ∈ E, f (repX i)) =
        (∑ i ∈ E.erase k, f (repX i)) + f v := by
    calc
      _ = (∑ i ∈ E.erase k, f (repX i)) + f (repX k) :=
        (Finset.sum_erase_add E (fun i => f (repX i)) hkE).symm
      _ = _ := by rw [hRepXK]
  have hSplitY :
      (∑ i ∈ E, f (repY i)) =
        (∑ i ∈ E.erase k, f (repY i)) + f w := by
    calc
      _ = (∑ i ∈ E.erase k, f (repY i)) + f (repY k) :=
        (Finset.sum_erase_add E (fun i => f (repY i)) hkE).symm
      _ = _ := by rw [hRepYK]
  rw [hSplitX, hSplitY, hOther] at hEq
  have hValues : f v = f w := add_left_cancel hEq
  exact hvw (Subtype.ext (finiteModelEquiv.injective hValues))
end InverseZeroSum.Candidate3
