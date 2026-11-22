-- Prove2me | solution 1 for LatinQuarter.Textbook.scs_eq_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:05.336318+00:00
-- url     : https://prove2.me/submissions/de6bd04b-890a-42f8-95d2-97608927c47f

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
public import Theorems.Thm_LatinQuarter_Textbook_quarter_le_scsOf
public import Theorems.Thm_LatinQuarter_Textbook_cyclic_criticalSet

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook
namespace LatinQuarter.Textbook
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    scs n = n * n / 4 ∧ scsOf (cyclicSquare n) = n * n / 4 := by
  obtain ⟨T, hT, hcard⟩ := cyclic_criticalSet n hn
  have hlat : Latin (cyclicSquare n) := hT.1.1.1
  have hcyc : scsOf (cyclicSquare n) = n * n / 4 := by
    apply le_antisymm _ (quarter_le_scsOf hlat)
    rw [← hcard]
    unfold scsOf
    exact Nat.sInf_le ⟨T, hT, rfl⟩
  refine ⟨le_antisymm ?_ ?_, hcyc⟩
  · rw [← hcyc]
    unfold scs
    exact Nat.sInf_le ⟨cyclicSquare n, hlat, rfl⟩
  · unfold scs
    exact le_csInf ⟨_, cyclicSquare n, hlat, rfl⟩ (by
      rintro m ⟨L, hL, rfl⟩
      exact quarter_le_scsOf hL)
end LatinQuarter.Textbook
