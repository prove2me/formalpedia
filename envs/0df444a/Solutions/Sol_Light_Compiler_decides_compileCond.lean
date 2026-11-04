-- Prove2me | solution 1 for Light.Compiler.decides_compileCond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:13.513544+00:00
-- url     : https://prove2.me/submissions/51a08d66-cb91-4ae6-b623-fadb3e6aabed

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Theorems.Thm_Light_Compiler_codeAt_after_pair
import Theorems.Thm_Light_Compiler_steps_pair
import Theorems.Thm_Light_Compiler_Framed_same
import Theorems.Thm_Light_Compiler_Rel_same
import Theorems.Thm_Light_Cond_width_eq_le_iff
import Theorems.Thm_Light_Cond_width_lt_le_iff
import Theorems.Thm_Light_Expr_abs_val_le
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_branch
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_steps_bltz
import Theorems.Thm_ThreeSumApsp_WordRam_steps_sub
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ} {m : ℤ → BitVec W} {a b : Expr}
private theorem inRange_sub (Z : Sizes W) {x y : ℤ} (hx : |x| ≤ Z.lim.word) (hy : |y| ≤ Z.lim.word) :
    InRange W (x - y) ∧ InRange W (x - y - 1) :=
  by
  obtain ⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩ := And.intro (abs_le.1 hx) (abs_le.1 hy)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [Z.fits.word]
private theorem decides_lt (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.lt a b) l)) (hw : (Cond.lt a b).width ≤ Z.F)
    (hs : (Cond.lt a b).Safe Z.lim σ) : Decides code Z.F pos (Cond.lt a b).size l m (a.val σ < b.val σ) :=
  by
  obtain ⟨hwa, hwb⟩ := Cond.width_lt_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  have run₂ :=
    run₁.trans
      (steps_sub restCode vb va)
        -- D := D - 1
        
  have run₃ :=
    run₂.trans
      (steps_sub restCode.tail (Function.update_self _ _ _)
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
            exact (I.rel.same A₁).one)))
        -- leave if D < 0
        
  have run₄ :=
    run₃.trans
      (steps_bltz restCode.tail.tail (Function.update_self _ _ _)
        (inRange_sub Z (Expr.abs_val_le hσ b hsb) (Expr.abs_val_le hσ a hsa)).2)
  exact
    ⟨_, _, by rw [Cond.size],
      (A₁.update
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
        _,
      run₄.branch (by omega) (by rw [Cond.size]; omega)⟩
private theorem decides_eq (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim)
    (hcode : CodeAt code pos (compileCond (.eq a b) l)) (hw : (Cond.eq a b).width ≤ Z.F)
    (hs : (Cond.eq a b).Safe Z.lim σ) : Decides code Z.F pos (Cond.eq a b).size l m (a.val σ = b.val σ) :=
  by
  obtain ⟨hwa, hwb⟩ := Cond.width_eq_le_iff.1 hw
  obtain ⟨hsa, hsb⟩ := hs
  have ha := Expr.abs_val_le hσ a hsa
  have hb := Expr.abs_val_le hσ b hsb
  obtain ⟨m₁, run₁, va, vb, A₁⟩ := steps_pair I hcode hwa hwb hsa hsb
  have restCode := codeAt_after_pair hcode
  have run₂ := run₁.trans (steps_sub restCode va vb)
  have A₂ :=
    A₁.update (a := cD)
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
      (wd W (a.val σ - b.val σ))
        -- leave if D < 0
        
  have run₃ := run₂.trans (steps_bltz restCode.tail (Function.update_self _ _ _) (inRange_sub Z ha hb).1)
  by_cases hlt : a.val σ - b.val σ < 0
  · rw [if_pos hlt] at run₃
    exact ⟨_, _, by rw [Cond.size]; omega, A₂, fun h => absurd h (by omega), fun _ => run₃⟩
  rw [if_neg hlt] at run₃
  have run₄ :=
    run₃.trans
      (steps_sub restCode.tail.tail
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
            exact (I.rel.same A₁).zero))
        (Function.update_self _ _ _))
  rw [zero_sub, neg_sub] at run₄
  have run₅ := run₄.trans (steps_bltz restCode.tail.tail.tail (Function.update_self _ _ _) (inRange_sub Z hb ha).1)
  exact
    ⟨_, _, by rw [Cond.size],
      A₂.update
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
        _,
      run₅.branch (by omega) (by rw [Cond.size]; omega)⟩
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {Z : Sizes W} {code rest : List Instr} {σ : State} {q pos l : ℕ} {m : ℤ → BitVec W} {a b : Expr}
namespace Light.Compiler
theorem _root_.solution (I : Framed Z σ q m) (hσ : σ.Bounded Z.lim) (c : Cond)
    (hcode : CodeAt code pos (compileCond c l)) (hw : c.width ≤ Z.F) (hs : c.Safe Z.lim σ) :
    Decides code Z.F pos c.size l m (c.Holds σ) := by
  cases c with
  | lt a b => exact decides_lt I hσ hcode hw hs
  | eq a b => exact decides_eq I hσ hcode hw hs
end Light.Compiler
