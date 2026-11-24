-- Prove2me | solution 1 for MomentComparison.cubeAverage_walsh_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:06.634074+00:00
-- url     : https://prove2.me/submissions/146288d2-c833-482a-932d-1024b70d702c

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_walsh_symmDiff
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_walsh
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.cubeAverage_const

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (s t : Finset (Fin n)) :
    cubeAverage (fun x => walsh s x * walsh t x) = if s = t then 1 else 0 := by
  simp_rw [← walsh_symmDiff]
  simp only [cubeAverage_walsh, Finset.symmDiff_eq_empty]
end MomentComparison
