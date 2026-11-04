-- Prove2me | solution 1 for Light.Compiler.compileProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:04.648313+00:00
-- url     : https://prove2.me/submissions/234f79bd-70ef-4bb4-aef0-4b9b06f181ad

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Theorems.Thm_Light_Compiler_Fits_inRange
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Sizes_inRange_neg_one
import Theorems.Thm_Light_Compiler_agreeOutside_startMem
import Theorems.Thm_Light_Compiler_codeAt_mainStmt
import Theorems.Thm_Light_Compiler_codeAt_tailCode
import Theorems.Thm_Light_Compiler_rel_startMem
import Theorems.Thm_Light_Compiler_sim
import Theorems.Thm_Light_Compiler_size_mainStmt
import Theorems.Thm_Light_Compiler_steps_start
import Theorems.Thm_Light_Compiler_three_le_frameSize
import Theorems.Thm_Light_Compiler_two_mul_frameSize_add_le_dispPos
import Theorems.Thm_Light_Compiler_width_mainStmt
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Definitions.Def_WeightedCache3SUM_Alias_bf7e373e88f8c7b5
import Theorems.Thm_Light_bounded_frame
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_cell
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans_union
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_exec_mono
import Theorems.Thm_ThreeSumApsp_WordRam_exec_of_steps
import Theorems.Thm_ThreeSumApsp_WordRam_step_accept
import Theorems.Thm_ThreeSumApsp_WordRam_step_reject
import Theorems.Thm_ThreeSumApsp_WordRam_steps_add
import Theorems.Thm_ThreeSumApsp_WordRam_steps_bltz
import Theorems.Thm_ThreeSumApsp_WordRam_steps_sub
import Theorems.Thm_ThreeSumApsp_WordRam_toInt_wd
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr exec)
variable {W : ℕ}
private theorem steps_tail {code : List Instr} {pos : ℕ} {dec : Bool} (hcode : CodeAt code pos (tailCode dec pos))
    {m : ℤ → BitVec W} {r : ℤ} (hres : m (cStack mainFrame) = wd W r) (hzero : m cZERO = wd W 0) (hr : InRange W (-r)) :
    ∃ (n : ℕ) (cfg : Cfg W), n ≤ 3 ∧ Steps code n ⟨pos, m⟩ cfg ∧ Verdict code dec r m cfg := by
  -- the cell for the result := the result
  
  have copy : Steps code 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m cRESULT (wd W r)⟩ :=
    add_zero r ▸ steps_add hcode hres hzero
  cases dec with
  | false =>
    -- accept
    
    have read : Function.update m cRESULT (wd W r) cRESULT = wd W r := Function.update_self ..
    exact ⟨1, _, by omega, copy, step_accept hcode.tail.head, read, (AgreeOutside.refl _ m).update (by simp) _⟩
  |
    true =>
    have rest : CodeAt code (pos + 1) [.sub cD cZERO (cStack mainFrame), .bltz cD (pos + 4), .reject, .accept] :=
      hcode.tail
    have run :=
      (copy.trans
            (steps_sub rest
              (by
                ((repeat
                      (first
                        | rw [_root_.Function.update_self]
                        |
                          rw [_root_.Function.update_of_ne
                              (by
                                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff,
                                        _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch,
                                        _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                                        _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                        _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                                        _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                        _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                        _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                        _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
                  exact hzero))
              (by
                ((repeat
                      (first
                        | rw [_root_.Function.update_self]
                        |
                          rw [_root_.Function.update_of_ne
                              (by
                                (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff,
                                        _root_.Light.Compiler.Constants, _root_.Light.Compiler.Scratch,
                                        _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
                                        _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff,
                                        _root_.Set.mem_ofPred_eq, _root_.Light.Compiler.mem_temps_iff,
                                        _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
                                        _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2,
                                        _root_.Light.Compiler.cRESULT, _root_.Light.Compiler.cONE,
                                        _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
                                        _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR,
                                        _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
                                        _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT,
                                        _root_.Light.Compiler.cPool, _root_.Light.Compiler.cStack,
                                        _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
                                        _root_.false_or, _root_.or_false] <;> intros <;> omega))]));
                  exact hres)))).trans
        (steps_bltz rest.tail (Function.update_self ..) (by rwa [zero_sub]))
    have keep :
      AgreeOutside { cRESULT, cD } m (Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r))) :=
      ((AgreeOutside.refl _ m).update (by simp) _).update (by simp) _
    have read : Function.update (Function.update m cRESULT (wd W r)) cD (wd W (0 - r)) cRESULT = wd W r := by
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
                            _root_.false_or, _root_.or_false] <;> intros <;> omega))]))
    by_cases hpos : 0 < r
    · rw [if_pos (by omega)] at run
      exact ⟨3, _, le_rfl, run, (step_accept rest.tail.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩
    · rw [if_neg (by omega)] at run
      exact ⟨3, _, le_rfl, run, (step_reject rest.tail.tail.head).trans (by simp [verdictOf, hpos]), read, keep⟩
private theorem frame_le_stackCells (P : Program) (lim : Limits) : mainFrame + frameSize P + 1 ≤ stackCells P lim :=
  by
  have := Nat.le_mul_of_pos_right (frameSize P + 1) (show 0 < lim.depth + 1 by omega)
  unfold stackCells
  omega
section setting
variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}
variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))
private theorem start_mainStmt {σ : State} {m : ℤ → BitVec W} (hσ : σ.Bounded lim)
    (R : Rel (setting P p0 dec hfit).toSizes σ mainFrame m) :
    Start (setting P p0 dec hfit) 0 (mainStmt p0) σ mainPos mainFrame m
    where
  rel := R
  low := by decide
  high := (Nat.le_succ _).trans (frame_le_stackCells P lim)
  codeAt := codeAt_mainStmt P p0 dec
  below := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [size_mainStmt, setting, codeLayout, mainPos]
    omega
  width := (width_mainStmt p0).trans_le (three_le_frameSize P)
  bounded := hσ
  room := by
    simp only [setting, codeLayout, stackCells, Nat.sub_zero, Nat.mul_succ]
    omega
private theorem not_mem_of_far {a : ℤ} (ha : a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a) :
    a ∉
      Constants (dispPos P dec) ∪ ({ cFP } ∪ MainFrame (frameSize P)) ∪
          Writable (setting P p0 dec hfit).toSizes mainFrame ∪
        { cRESULT, cD } :=
  by
  have hframe := frame_le_stackCells P lim
  have htemps := two_mul_frameSize_add_le_dispPos P dec
  have hstack : 2 * stackCells P lim ≤ lowCell P dec lim := le_max_left _ _
  have hpool : 25 + 4 * dispPos P dec ≤ lowCell P dec lim := le_max_right _ _
  simp only [Writable, setting, codeLayout]
  rcases ha with ha | ha <;> (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
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
end setting
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr exec)
variable {W : ℕ}
namespace Light.Compiler
theorem _root_.solution {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool} {μ : ℕ → ℤ} {i j : ℤ} {σ' : State} {c : ℕ}
    {m : ℤ → BitVec W} (h : Exec lim P 0 (mainStmt p0) ⟨frame [0, i, j], μ⟩ σ' c)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) (hm : Input lim μ i j m) :
    ∃ m' : ℤ → BitVec W,
      exec (compileProgram P p0 dec) (ramSteps P dec c) 0 m = some (verdictOf dec (σ'.loc 0), m') ∧
        Outcome lim P dec m σ' m' :=
  by
  have hF := three_le_frameSize P
  have hdisp := two_mul_frameSize_add_le_dispPos P dec
  have hσ : State.Bounded lim ⟨frame [0, i, j], μ⟩ :=
    bounded_frame (by simp [hm.arg1_le, hm.arg2_le, (abs_nonneg i).trans hm.arg1_le]) hm.bounded
  have hσ' := h.bounded hσ
  have run₁ := steps_start P p0 dec (setting P p0 dec hfit).inRange_neg_one m
  have keep₁ := agreeOutside_startMem hF (dispPos P dec) m
  obtain ⟨m', n, fin⟩ :=
    sim (setting P p0 dec hfit) h mainPos mainFrame _
      (start_mainStmt hfit hσ
        (rel_startMem _ hF (by simp only [setting, codeLayout, mainFrame]; omega) (fun a _ => hm.rep a) hm.arg1
          hm.arg2))
  have hn : n ≤ stepsPerStep (dispPos P dec) * c := fin.le
  have run₂ :=
    fin.run.cast_pos (p' := tailPos (frameSize P))
      (by simp only [tailPos, size_mainStmt, setting, codeLayout])
        -- the verdict
        
  obtain ⟨k, cfg, hk, run₃, tail⟩ :=
    steps_tail (codeAt_tailCode P p0 dec) (fin.rel.loc 0 (show 0 < frameSize P by omega)) fin.rel.zero
      (hfit.inRange (by rw [abs_neg]; exact hσ'.1 0))
  have run := (run₁.trans run₂).trans run₃
  have keep := (keep₁.trans_union fin.agree).trans_union tail.agree
  have far (a : ℤ) ha : cfg.mem a = m a := keep.cell (not_mem_of_far hfit ha)
  refine
    ⟨cfg.mem, exec_mono (c := ⟨0, m⟩) (exec_of_steps run tail.verdict) ?_,
      { holds := ⟨fun a => ?_, hσ'.2⟩
        result := tail.result ▸ toInt_wd (hfit.inRange (hσ'.1 0))
        arg1 :=
          keep.cell
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
        arg2 :=
          keep.cell
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
        far := far }⟩
  · simp only [ramSteps, startCost]
    omega
  · by_cases ha : a < lim.space
    ·
      exact
        tail.agree.read
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
          (fin.rel.mem a ha)
    · rw [far _ (Or.inr (by exact_mod_cast not_lt.1 ha)), h.mem_outside a (not_lt.1 ha)]
      exact hm.rep a
end Light.Compiler
