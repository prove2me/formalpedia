-- Prove2me | solution 1 for Light.Compiler.steps_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:03.843856+00:00
-- url     : https://prove2.me/submissions/b34979da-d1a5-4f36-80c5-f0e5c47cd075

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_codeAt_headCode
import Theorems.Thm_Light_Compiler_codeAt_startCode
import Theorems.Thm_Light_Compiler_steps_jump
import Theorems.Thm_Light_Compiler_three_le_frameSize
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_count
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_agreeOutside_effects
import Theorems.Thm_ThreeSumApsp_WordRam_effect_one
import Theorems.Thm_ThreeSumApsp_WordRam_effect_sub
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_steps_straight
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
private theorem effects_headStraight (m : ℤ → BitVec W) :
    effects headStraight m =
      Function.update (Function.update (Function.update m cONE (wd W 1)) cZERO (wd W 0)) cNEG (wd W (-1)) :=
  by
  simp only [headStraight, effects_cons, effects_nil]
  rw [effect_one,
    effect_sub cZERO
      (by
        repeat
          (first
            | rw [_root_.Function.update_self]
            |
              rw [_root_.Function.update_of_ne
                  (by
                    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                            _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                            _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                            _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                            _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                            _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                            _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                            _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                            _root_.false_or, _root_.or_false] <;>
                          intros <;>
                        omega))]))
      (by
        repeat
          (first
            | rw [_root_.Function.update_self]
            |
              rw [_root_.Function.update_of_ne
                  (by
                    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                            _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                            _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                            _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                            _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                            _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                            _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                            _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                            _root_.false_or, _root_.or_false] <;>
                          intros <;>
                        omega))])),
    effect_sub cNEG
      (by
        repeat
          (first
            | rw [_root_.Function.update_self]
            |
              rw [_root_.Function.update_of_ne
                  (by
                    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                            _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                            _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                            _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                            _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                            _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                            _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                            _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                            _root_.false_or, _root_.or_false] <;>
                          intros <;>
                        omega))]))
      (by
        repeat
          (first
            | rw [_root_.Function.update_self]
            |
              rw [_root_.Function.update_of_ne
                  (by
                    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                            _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                            _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                            _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                            _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                            _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                            _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                            _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                            _root_.false_or, _root_.or_false] <;>
                          intros <;>
                        omega))]))]
  rfl
private theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧
      effects headStraight m cZERO = wd W 0 ∧ effects headStraight m cNEG = wd W (-1) :=
  by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;>
    repeat
      (first
        | rw [_root_.Function.update_self]
        |
          rw [_root_.Function.update_of_ne
              (by
                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                        _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                        _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                        _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                        _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
                        _root_.or_false] <;>
                      intros <;>
                    omega))])
private theorem agreeOutside_poolCode (N : ℕ) (m : ℤ → BitVec W) : AgreeOutside (Pool N) m (effects (poolCode N) m) :=
  by
  refine agreeOutside_effects (l := poolCode N) (List.forall_mem_cons.2 ⟨?_, List.forall_mem_map.2 fun n hn => ?_⟩) m
  · show cPool 0 ∈ Pool N
    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
            _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
            _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
            _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
            _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
            _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
            _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
            _root_.or_false] <;>
          intros <;>
        omega)
  · have := List.mem_range.1 hn
    show cPool (n + 1) ∈ Pool N
    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
            _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
            _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
            _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
            _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
            _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
            _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
            _root_.or_false] <;>
          intros <;>
        omega)
private theorem poolMem_consts (N : ℕ) (m : ℤ → BitVec W) :
    poolMem N m cONE = wd W 1 ∧ poolMem N m cZERO = wd W 0 ∧ poolMem N m cNEG = wd W (-1) :=
  by
  obtain ⟨one, zero, neg⟩ := effects_headStraight_consts m
  have keep := agreeOutside_poolCode N (effects headStraight m)
  exact
    ⟨keep.read
        (by
          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                  _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                  _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                  _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                  _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                  _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                  _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                  _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega))
        one,
      keep.read
        (by
          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                  _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                  _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                  _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                  _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                  _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                  _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                  _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega))
        zero,
      keep.read
        (by
          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                  _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                  _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                  _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                  _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                  _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                  _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                  _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega))
        neg⟩
private theorem writesIn_zeroCode (F : ℕ) : ∀ i ∈ zeroCode F, WritesIn (MainFrame F) i :=
  List.forall_mem_map.2 fun x hx => by
    have := List.mem_range.1 hx
    show cStack (mainFrame + x) ∈ MainFrame F
    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
            _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
            _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
            _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
            _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
            _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
            _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
            _root_.or_false] <;>
          intros <;>
        omega)
private theorem agreeOutside_frameCode (h3 : 3 ≤ F) (m : ℤ → BitVec W) :
    AgreeOutside ({ cFP } ∪ MainFrame F) m (effects (frameCode F) m) :=
  by
  refine
    agreeOutside_effects (l := frameCode F)
      (List.forall_mem_cons.2
        ⟨?_, List.forall_mem_append.2 ⟨fun i hi => ?_, List.forall_mem_cons.2 ⟨?_, List.forall_mem_singleton.2 ?_⟩⟩⟩)
      m
  · -- FP := 0 - 2 mainFrame
    exact Or.inl rfl
  · -- the zeros
    exact (writesIn_zeroCode F i hi).mono Set.subset_union_right
  · -- local variable 1 := the first argument
    
    show cStack (mainFrame + 1) ∈ _
    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
            _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
            _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
            _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
            _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
            _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
            _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
            _root_.or_false] <;>
          intros <;>
        omega)
  · -- local variable 2 := the second argument
    
    show cStack (mainFrame + 2) ∈ _
    (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
            _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
            _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
            _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
            _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
            _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
            _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
            _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
            _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
            _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true, _root_.false_or,
            _root_.or_false] <;>
          intros <;>
        omega)
private theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) : startMem F N m = effects (frameCode F) (poolMem N m) :=
  effects_append _ _ _
private theorem straight_headStraight : ∀ i ∈ headStraight, Straight i := by simp [headStraight, Straight]
private theorem straight_startStraight (F N : ℕ) : ∀ i ∈ startStraight F N, Straight i := by
  simp [startStraight, poolCode, frameCode, zeroCode, Straight, or_imp, forall_and]
private theorem length_startStraight (F N : ℕ) : (startStraight F N).length = N + F + 4 := by
  simp +arith [startStraight, poolCode, frameCode, zeroCode]
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (P : Program) (p0 : ℕ) (dec : Bool) (hneg : InRange W (-1)) (m : ℤ → BitVec W) :
    Steps (compileProgram P p0 dec) (dispPos P dec + frameSize P + 9) ⟨0, m⟩
      ⟨mainPos, startMem (frameSize P) (dispPos P dec) m⟩ :=
  by
  have head := codeAt_headCode P p0 dec
  have start := codeAt_startCode P p0 dec
  obtain ⟨-, -, neg₀⟩ := effects_headStraight_consts m
  obtain ⟨-, -, neg⟩ := poolMem_consts (dispPos P dec) m
  have neg₁ : startMem (frameSize P) (dispPos P dec) m cNEG = wd W (-1) := by
    rw [startMem_eq,
      (agreeOutside_frameCode (three_le_frameSize P) _).cell
        (by
          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                  _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                  _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                  _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                  _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                  _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                  _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                  _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega)),
      neg]
      -- 1, 0, -1; jump to the start-up code; the start-up code; jump back
      
  refine
    ((((steps_straight _ 0 m head.left straight_headStraight).trans (steps_jump head.right neg₀ hneg)).trans
              (steps_straight _ _ _ start.left (straight_startStraight _ _))).trans
          (steps_jump start.right neg₁ hneg)).cast_count
      ?_
  rw [length_startStraight, show headStraight.length = 3 from rfl]
  omega
end Light.Compiler
