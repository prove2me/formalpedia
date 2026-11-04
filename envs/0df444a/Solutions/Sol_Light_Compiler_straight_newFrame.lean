-- Prove2me | solution 1 for Light.Compiler.straight_newFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:13:31.093998+00:00
-- url     : https://prove2.me/submissions/0dff1df6-6c35-4b9f-b45b-10d18b3069b2

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
private theorem frameInit_succ (F' n : ℕ) : frameInit (F' + 1) n = frameInit F' n ++
    [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] := by
  simp [frameInit, List.range_succ, List.flatMap_append]
private theorem straight_frameInit (n : ℕ) : ∀ F' : ℕ, ∀ i ∈ frameInit F' n, Straight i
  | 0 => by simp [frameInit]
  | F' + 1 => by
    rw [frameInit_succ]
    exact List.forall_mem_append.2 ⟨straight_frameInit n F', by simp [Straight]⟩
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (F n ret : ℕ) : ∀ i ∈ newFrame F n ret, Straight i :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨by simp [Straight], straight_frameInit n F⟩,
    by simp [Straight]⟩
end Light.Compiler
