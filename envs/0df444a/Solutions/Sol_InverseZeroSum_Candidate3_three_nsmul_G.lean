-- Prove2me | solution 1 for InverseZeroSum.Candidate3.three_nsmul_G
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:24:04.476091+00:00
-- url     : https://prove2.me/submissions/4877059c-86c4-4159-ab75-6b9f5c7b5ad0

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
public import Theorems.Thm_InverseZeroSum_Candidate3_baseIndex_val
attribute [local simp] InverseZeroSum.Candidate3.baseIndex_val

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution (x : G) : (3 : ℕ) • x = 0 := by
  ext i
  change (3 : ℕ) • x i = 0
  have hZModTorsion : ∀ z : ZMod 3, (3 : ℕ) • z = 0 := by
    intro z
    fin_cases z <;> decide
  exact hZModTorsion (x i)
end InverseZeroSum.Candidate3
