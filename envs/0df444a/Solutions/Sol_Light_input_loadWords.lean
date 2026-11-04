-- Prove2me | solution 1 for Light.input_loadWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:59.479715+00:00
-- url     : https://prove2.me/submissions/db89244c-59b2-4eb5-8d9f-9b4ec3807e0a

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_loadWords_mem_nat
import Theorems.Thm_ThreeSumApsp_WordRam_loadWords_mem_neg
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil



set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
namespace Light
theorem _root_.solution (W : ℕ) {ws : List ℤ} (h0 : 0 ≤ lim.word) (h : ∀ v ∈ ws, |v| ≤ lim.word) :
    Input lim (memOf ws) 0 0 (loadWords W ws) where
  rep := loadWords_mem_nat W ws
  bounded := AbsLe.abs_getD_le h0 h
  arg1 := loadWords_mem_neg W ws (by decide)
  arg2 := loadWords_mem_neg W ws (by decide)
  arg1_le := by simpa using h0
  arg2_le := by simpa using h0
end Light
