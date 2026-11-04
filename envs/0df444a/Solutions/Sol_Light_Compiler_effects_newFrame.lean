-- Prove2me | solution 1 for Light.Compiler.effects_newFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:14.86674+00:00
-- url     : https://prove2.me/submissions/3cb6fd38-876c-4b28-8a03-8a1b515d2d4f

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Theorems.Thm_Light_Compiler_Rel_beyond
import Theorems.Thm_Light_Compiler_Rel_of_agreeOutside
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Sizes_inRange_stack
import Theorems.Thm_Light_Compiler_cStack_sub
import Theorems.Thm_Light_Compiler_cStack_succ_add
import Theorems.Thm_Light_Compiler_scratch_subset_writable
import Theorems.Thm_Light_Compiler_stack_subset_writable
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_effect_add
import Theorems.Thm_ThreeSumApsp_WordRam_effect_store
import Theorems.Thm_ThreeSumApsp_WordRam_effect_sub
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
private theorem frameInit_succ (F' n : ℕ) :
    frameInit (F' + 1) n =
      frameInit F' n ++ [.sub cADDR cNFP (cPool (2 * F')), .store cADDR (if F' < n then cT F' else cZERO)] :=
  by simp [frameInit, List.range_succ, List.flatMap_append]
private theorem effects_frameInit (Z : Sizes W) (n q' F' : ℕ) (m : ℤ → BitVec W) (hNFP : m cNFP = wd W (cStack q'))
    (hpool : ∀ i < F', m (cPool (2 * i)) = wd W ((2 * i : ℕ) : ℤ)) (hQ : q' + F' ≤ Z.Q) :
    (∀ i < F', effects (frameInit F' n) m (cStack (q' + i)) = if i < n then m (cT i) else m cZERO) ∧
      AgreeOutside (insert cADDR (Stack q' Z.Q)) m (effects (frameInit F' n) m) :=
  by
  induction F' with
  | zero => exact ⟨fun i h => absurd h (by omega), AgreeOutside.refl _ m⟩
  | succ F'
    ih =>
    obtain ⟨val, A⟩ :=
      ih (fun i hi => hpool i (by omega))
        (by omega)
          -- ADDR := NFP - 2 F'; the cell at ADDR := T_{F'} or 0
          
    rw [frameInit_succ, effects_append, effects_cons, effects_cons, effects_nil,
      effect_sub cADDR
        (A.read
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
          hNFP)
        (A.read
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
          (hpool F' (by omega))),
      cStack_sub, effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine
      ⟨fun i hi => ?_,
        (A.update
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
              _).update
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
          _⟩
    obtain rfl | hne := eq_or_ne i F'
    · rw [Function.update_self]
      split_ifs <;> rw [Function.update_of_ne
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
          A.cell
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
                      _root_.or_false] <;> intros <;> omega))]
    ·
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
        exact val i (by omega))
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (I : Framed Z σ q m) (hQ : q + Z.F + 1 + Z.F ≤ Z.Q) (args : List Expr)
    (hargs : ∀ i < args.length, m (cT i) = wd W (frame (args.map (·.val σ)) i)) {ret : ℕ} (hret : ret ≤ Z.disp) :
    Rel Z ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + Z.F + 1) (effects (newFrame Z.F args.length ret) m) ∧
      effects (newFrame Z.F args.length ret) m (cStack (q + Z.F)) = wd W ret ∧
        AgreeOutside (Writable Z (q + Z.F)) m (effects (newFrame Z.F args.length ret) m) :=
  by
  have R := I.rel
  have hq := I.low
  have hN := Z.offsets_le
  simp only [newFrame, effects_append, effects_cons, effects_nil]
    -- NFP := FP - 2 (F + 1).  Up to the last instruction, only scratch cells and the stack beyond the
      -- frame q change, so the memory goes on representing σ in the frame q.
    
  rw [effect_sub cNFP R.fp (R.pool _ hN), cStack_sub, ← Nat.add_assoc]
  have A₁ :=
    (AgreeOutside.refl (Scratch Z.F ∪ Stack (q + Z.F) Z.Q) m).update (a := cNFP)
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (wd W (cStack (q + Z.F + 1)))
        -- the local variables of the new frame
        
  obtain ⟨val, A⟩ :=
    effects_frameInit Z args.length (q + Z.F + 1) Z.F _ (Function.update_self cNFP _ m)
      (fun i hi => (R.beyond hq A₁).pool _ (by omega)) hQ
  generalize effects (frameInit Z.F args.length) _ = m₂ at val A ⊢
  have hNFP : m₂ cNFP = wd W (cStack (q + Z.F + 1)) :=
    A.read
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (Function.update_self _ _ _)
  have A₂ :=
    A₁.trans
      (A.mono
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega)))
        -- ADDR := NFP + 2
        
  rw [effect_add cADDR hNFP ((R.beyond hq A₂).pool 2 (by omega)), cStack_succ_add]
  have A₃ :=
    A₂.update (a := cADDR)
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (wd W (cStack (q + Z.F)))
        -- the cell at ADDR := ret
        
  rw [effect_store _ (Function.update_self _ _ _) (Z.inRange_stack (by omega)), (R.beyond hq A₃).pool ret hret]
  have A₄ :=
    A₃.update (a := cStack (q + Z.F))
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (wd W ret)
  have R₄ := R.beyond hq A₄
  rw [effect_add cFP
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
          exact hNFP))
      R₄.zero,
    add_zero]
  refine
    ⟨?_, by
      (repeat
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
                            _root_.false_or, _root_.or_false] <;> intros <;> omega))])),
      (A₄.mono (Set.union_subset scratch_subset_writable stack_subset_writable)).update
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
        _⟩
  refine
    R₄.of_agreeOutside ((AgreeOutside.refl { cFP } _).update rfl _)
      (by
        (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
                _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
                _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff,
                _root_.Light.Compiler.mem_pool_iff, _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO,
                _root_.Light.Compiler.cNEG, _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR, _root_.Light.Compiler.cNFP,
                _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
                _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or,
                _root_.or_true, _root_.false_or, _root_.or_false] <;> intros <;> omega))
      (Function.update_self _ _ _) (fun i hi => ?_) fun a ha =>
      (Function.update_of_ne
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
            _ _).trans
        (R₄.mem a ha)
          -- local variable i of the new frame: argument i, or 0
          
  (repeat
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
                        _root_.or_false] <;> intros <;> omega))]))
  rw [val i hi]
  split_ifs with h
  ·
    ((repeat
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
                            _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
      exact hargs i h)
  · (repeat
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
    rw [R.zero]
    simp [frame, List.getElem?_eq_none (not_lt.1 h)]
end Light.Compiler
