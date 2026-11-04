-- Prove2me | solution 1 for Light.Compiler.steps_dispatcher
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:36:16.039626+00:00
-- url     : https://prove2.me/submissions/ae14fb40-efd0-4213-a336-9ba440591b33

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Theorems.Thm_Light_Compiler_length_dispatcher
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_count
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_steps_bltz
import Theorems.Thm_ThreeSumApsp_WordRam_steps_sub
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}
private theorem dispatcher_succ (n : ℕ) : dispatcher (n + 1) = dispatcher n ++ [.sub cRR cRR cONE, .bltz cRR n] := by
  simp [dispatcher, List.range_succ, List.flatMap_append]
private theorem dispatcher_prefix {j n : ℕ} (h : j ≤ n) : dispatcher j <+: dispatcher n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (dispatcher_succ n ▸ List.prefix_append _ _)
private theorem codeAt_dispatcher {j : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) :
    CodeAt code (disp + 2 * j) [.sub cRR cRR cONE, .bltz cRR j] :=
  by
  have upToPairCode : CodeAt code disp (dispatcher j ++ [.sub cRR cRR cONE, .bltz cRR j]) :=
    dispatcher_succ j ▸ (dispatcher_prefix hj).trans hcode
  exact upToPairCode.right.cast_pos (by rw [length_dispatcher])
private theorem steps_dispatcher_pair {j : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hj : j < n) (m : ℤ → BitVec W)
    (hone : m cONE = wd W 1) {v : ℤ} (hv : InRange W (v - 1)) :
    Steps code 2 ⟨disp + 2 * j, Function.update m cRR (wd W v)⟩
      ⟨if v - 1 < 0 then j else disp + 2 * (j + 1), Function.update m cRR (wd W (v - 1))⟩ :=
  by
  have pairCode := codeAt_dispatcher hcode hj
  have run₁ :=
    steps_sub pairCode (Function.update_self cRR (wd W v) m)
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
          exact hone))
  rw [Function.update_idem] at run₁
  exact run₁.trans (steps_bltz pairCode.tail (Function.update_self _ _ _) hv)
private theorem steps_dispatcher_from (hcode : CodeAt code disp (dispatcher n)) (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (k j : ℕ) (hjk : j + k < n) :
    Steps code (2 * (k + 1)) ⟨disp + 2 * j, Function.update m cRR (wd W k)⟩
      ⟨j + k, Function.update m cRR (wd W (-1))⟩ :=
  by
  induction k generalizing j with
  | zero => simpa using steps_dispatcher_pair hcode (show j < n by omega) m hone (v := 0) (by constructor <;> omega)
  | succ k
    ih =>
    have run := steps_dispatcher_pair hcode (show j < n by omega) m hone (v := k + 1) (by constructor <;> omega)
    rw [if_neg (by omega), add_sub_cancel_right] at run
    rw [Nat.cast_succ]
      -- 2 + 2 (k + 1) steps lead to the position j + 1 + k
      
    exact ((run.trans (ih (j + 1) (by omega))).cast_count (by ring)).cast_pos (by ring)
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} {code : List Instr} {disp n : ℕ}
namespace Light.Compiler
theorem _root_.solution {r : ℕ} (hcode : CodeAt code disp (dispatcher n)) (hr : r < n) (hn : 2 * (n : ℤ) < (2 : ℤ) ^ W)
    (m : ℤ → BitVec W) (hone : m cONE = wd W 1) (hRR : m cRR = wd W r) :
    Steps code (2 * (r + 1)) ⟨disp, m⟩ ⟨r, Function.update m cRR (wd W (-1))⟩ :=
  by
  have := steps_dispatcher_from hcode hn m hone r 0 (by omega)
  rwa [Nat.mul_zero, Nat.add_zero, Nat.zero_add, ← hRR, Function.update_eq_self] at this
end Light.Compiler
