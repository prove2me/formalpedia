-- Prove2me | solution 1 for Light.Compiler.rel_startMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:17.305618+00:00
-- url     : https://prove2.me/submissions/a2856d42-2121-43d7-bc4d-64303a94e5c8

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_ProgramCode
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans_union
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_agreeOutside_effects
import Theorems.Thm_ThreeSumApsp_WordRam_effect_add
import Theorems.Thm_ThreeSumApsp_WordRam_effect_one
import Theorems.Thm_ThreeSumApsp_WordRam_effect_sub
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
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
        (repeat
            (first
              | rw [_root_.Function.update_self]
              |
                rw [_root_.Function.update_of_ne
                    (by
                      (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                              _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                              _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                              _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                              _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                              _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                              _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                              _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                              _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                              _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                              _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                              _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                              _root_.false_or, _root_.or_false] <;> intros <;> omega))])))
      (by
        (repeat
            (first
              | rw [_root_.Function.update_self]
              |
                rw [_root_.Function.update_of_ne
                    (by
                      (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                              _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                              _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                              _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                              _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                              _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                              _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                              _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                              _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                              _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                              _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                              _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                              _root_.false_or, _root_.or_false] <;> intros <;> omega))]))),
    effect_sub cNEG
      (by
        (repeat
            (first
              | rw [_root_.Function.update_self]
              |
                rw [_root_.Function.update_of_ne
                    (by
                      (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                              _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                              _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                              _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                              _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                              _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                              _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                              _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                              _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                              _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                              _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                              _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                              _root_.false_or, _root_.or_false] <;> intros <;> omega))])))
      (by
        (repeat
            (first
              | rw [_root_.Function.update_self]
              |
                rw [_root_.Function.update_of_ne
                    (by
                      (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                              _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                              _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                              _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                              _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                              _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                              _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                              _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                              _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                              _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                              _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                              _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                              _root_.false_or, _root_.or_false] <;> intros <;> omega))])))]
  rfl
private theorem effects_headStraight_consts (m : ℤ → BitVec W) :
    effects headStraight m cONE = wd W 1 ∧
      effects headStraight m cZERO = wd W 0 ∧ effects headStraight m cNEG = wd W (-1) :=
  by
  rw [effects_headStraight]
  refine ⟨?_, ?_, ?_⟩ <;> (repeat
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
                          _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
private theorem poolCode_succ (N : ℕ) : poolCode (N + 1) = poolCode N ++ [.add (cPool (N + 1)) (cPool N) cONE] := by
  simp [poolCode, List.range_succ]
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
            _root_.or_false] <;> intros <;> omega)
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
            _root_.or_false] <;> intros <;> omega)
private theorem effects_poolCode (hone : m cONE = wd W 1) (N : ℕ) :
    ∀ n ≤ N, effects (poolCode N) m (cPool n) = wd W n := by
  induction N with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp only [poolCode, List.range_zero, List.map_nil, effects_cons, effects_nil]
    rw [effect_sub _ hone hone, Function.update_self]
    rfl
  | succ N ih =>
    intro n hn
    rw [poolCode_succ, effects_append, effects_cons, effects_nil,
      effect_add _ (ih N le_rfl)
        ((agreeOutside_poolCode N m).read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          hone)]
    obtain rfl | hlt := hn.eq_or_lt
    · rw [Function.update_self]
      push_cast
      rfl
    ·
      rw [Function.update_of_ne
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)),
        ih n (by omega)]
private theorem agreeOutside_poolMem (N : ℕ) (m : ℤ → BitVec W) : AgreeOutside (Constants N) m (poolMem N m) :=
  by
  refine AgreeOutside.trans_union ?_ (agreeOutside_poolCode N _)
  rw [effects_headStraight]
  exact (((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _).update (by simp) _
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
        neg⟩
private theorem poolMem_pool (m : ℤ → BitVec W) {n : ℕ} (hn : n ≤ N) : poolMem N m (cPool n) = wd W n :=
  effects_poolCode (effects_headStraight_consts m).1 N n hn
private theorem zeroCode_succ (F : ℕ) : zeroCode (F + 1) = zeroCode F ++ [.sub (cStack (mainFrame + F)) cONE cONE] := by
  simp [zeroCode, List.range_succ]
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
            _root_.or_false] <;> intros <;> omega)
private theorem effects_zeroCode (hone : m cONE = wd W 1) (F : ℕ) :
    ∀ x < F, effects (zeroCode F) m (cStack (mainFrame + x)) = wd W 0 := by
  induction F with
  | zero => exact fun x hx => absurd hx x.not_lt_zero
  | succ F ih =>
    intro x hx
    have hone' :=
      (agreeOutside_effects (writesIn_zeroCode F) m).read
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
        hone
    rw [zeroCode_succ, effects_append, effects_cons, effects_nil, effect_sub _ hone' hone']
    obtain rfl | hlt := (Nat.lt_succ_iff.1 hx).eq_or_lt
    · rw [Function.update_self]
      rfl
    ·
      rw [Function.update_of_ne
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)),
        ih x hlt]
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
            _root_.or_false] <;> intros <;> omega)
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
            _root_.or_false] <;> intros <;> omega)
private theorem effects_frameCode {i j : ℤ} (hzero : m cZERO = wd W 0)
    (hpool : m (cPool (2 * mainFrame)) = wd W (2 * mainFrame : ℕ)) (hi : m cARG1 = wd W i) (hj : m cARG2 = wd W j)
    (F : ℕ) :
    effects (frameCode F) m =
      Function.update
        (Function.update (effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))))
          (cStack (mainFrame + 1)) (wd W i))
        (cStack (mainFrame + 2)) (wd W j) :=
  by
  -- what the last two instructions read has not been written since the beginning
  
  have read (a : ℤ) (ha : a ∉ MainFrame F) (hfp : a ≠ cFP) :
    effects (zeroCode F) (Function.update m cFP (wd W (cStack mainFrame))) a = m a :=
    ((agreeOutside_effects (writesIn_zeroCode F) _).cell ha).trans (Function.update_of_ne hfp _ _)
  have zero :=
    (read cZERO
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))).trans
      hzero
  have arg1 :=
    (read cARG1
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))).trans
      hi
  have arg2 :=
    (read cARG2
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))).trans
      hj
  simp only [frameCode, effects_cons, effects_append, effects_nil]
    -- FP := 0 - 2 mainFrame
    
  rw [effect_sub cFP hzero hpool, show (0 : ℤ) - (2 * mainFrame : ℕ) = cStack mainFrame from rfl]
    -- after the zeros: local variable 1 := the first argument + 0
    
  rw [effect_add _ arg1 zero, add_zero]
    -- local variable 2 := the second argument + 0
    
  rw [effect_add _
      (by
        ((repeat
              (first
                | rw [_root_.Function.update_self]
                |
                  rw [_root_.Function.update_of_ne
                      (by
                        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                                _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                                _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                                _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                                _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
          exact arg2))
      (by
        ((repeat
              (first
                | rw [_root_.Function.update_self]
                |
                  rw [_root_.Function.update_of_ne
                      (by
                        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                                _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                                _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                                _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP,
                                _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
          exact zero)),
    add_zero]
private theorem startMem_eq (F N : ℕ) (m : ℤ → BitVec W) : startMem F N m = effects (frameCode F) (poolMem N m) :=
  effects_append _ _ _
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F N : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (Z : Sizes W) (h3 : 3 ≤ Z.F) (hpool : 2 * mainFrame ≤ Z.disp) {μ : ℕ → ℤ} {i j : ℤ}
    (hm : ∀ a < Z.lim.space, m (a : ℤ) = wd W (μ a)) (hi : m cARG1 = wd W i) (hj : m cARG2 = wd W j) :
    Rel Z ⟨frame [0, i, j], μ⟩ mainFrame (startMem Z.F Z.disp m) :=
  by
  obtain ⟨one, zero, neg⟩ := poolMem_consts Z.disp m
  have keep₁ := agreeOutside_poolMem Z.disp m
  have keep₂ := agreeOutside_frameCode h3 (poolMem Z.disp m)
  have written :=
    effects_frameCode zero (poolMem_pool m hpool)
      (keep₁.read
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
        hi)
      (keep₁.read
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
        hj)
      Z.F
  have zeros (x : ℕ) (hx : x < Z.F) (h1 : x ≠ 1) (h2 : x ≠ 2) :
    effects (frameCode Z.F) (poolMem Z.disp m) (cStack (mainFrame + x)) = wd W 0 :=
    by
    rw [written,
      Function.update_of_ne
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)),
      Function.update_of_ne
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))]
    exact
      effects_zeroCode
        (by
          ((repeat
                (first
                  | rw [_root_.Function.update_self]
                  |
                    rw [_root_.Function.update_of_ne
                        (by
                          (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                                  _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable,
                                  _root_.Light.Compiler.MainFrame, _root_.Set.mem_union, _root_.Set.mem_insert_iff,
                                  _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                                  _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                                  _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1,
                                  _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
                                  _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                                  _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET,
                                  _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD,
                                  _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                  _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                  _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
            exact one))
        Z.F x hx
  rw [startMem_eq]
  exact
    { one :=
        keep₂.read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          one
      zero :=
        keep₂.read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          zero
      neg :=
        keep₂.read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          neg
      pool := fun n hn =>
        keep₂.read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          (poolMem_pool m hn)
      fp := by
        rw [written,
          Function.update_of_ne
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
                      _root_.or_false] <;> intros <;> omega)),
          Function.update_of_ne
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
                      _root_.or_false] <;> intros <;> omega)),
          (agreeOutside_effects (writesIn_zeroCode Z.F) _).cell
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
                      _root_.or_false] <;> intros <;> omega)),
          Function.update_self]
      loc := fun x hx =>
        match x with
        | 0 => zeros 0 hx (by omega) (by omega)
        | 1 => by
          rw [written,
            Function.update_of_ne
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
                        _root_.or_false] <;> intros <;> omega))];
          exact Function.update_self ..
        | 2 => by rw [written]; exact Function.update_self ..
        | x + 3 => zeros (x + 3) hx (by omega) (by omega)
      mem := fun a ha =>
        keep₂.read
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
                    _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
          (keep₁.read
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
                      _root_.or_false] <;> intros <;> omega))
            (hm a ha)) }
end Light.Compiler
