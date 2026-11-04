-- Prove2me | solution 1 for Light.Compiler.effects_argsCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:01.732468+00:00
-- url     : https://prove2.me/submissions/7b61cc0e-7d8a-439a-9ca8-109fe1cb6d27

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Conditions
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Theorems.Thm_Light_Compiler_Framed_same
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Rel_same
import Theorems.Thm_Light_Compiler_effects_compileExpr_of_width
import Theorems.Thm_Light_Compiler_temps_subset_scratch
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (I : Framed Z σ q m) (es : List Expr) (k : ℕ) (hw : ∀ e ∈ es, e.width ≤ Z.F)
    (hs : ∀ e ∈ es, e.Safe Z.lim σ) (hk : k + es.length ≤ Z.F + 1) :
    (∀ i < es.length, effects (argsCode es k) m (cT (k + i)) = wd W (frame (es.map (·.val σ)) i)) ∧
      AgreeOutside (Temps k Z.F) m (effects (argsCode es k) m) :=
  by
  induction es generalizing k m with
  | nil => exact ⟨fun i h => absurd h (by simp), AgreeOutside.refl _ m⟩
  | cons e es ih =>
    obtain ⟨hwe, hwes⟩ := List.forall_mem_cons.1 hw
    obtain ⟨hse, hses⟩ := List.forall_mem_cons.1 hs
    rw [List.length_cons] at hk
    obtain ⟨ve, Ae⟩ := effects_compileExpr_of_width I e k hwe hse (by omega)
    obtain ⟨ves, Aes⟩ := ih (I.same (Ae.mono temps_subset_scratch)) (k + 1) hwes hses (by omega)
    rw [argsCode, effects_append]
    refine
      ⟨fun i hi => ?_,
        Ae.trans
          (Aes.mono
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
                  omega)))⟩
    cases i with
    | zero =>
      exact
        Aes.read
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
          ve
    | succ i =>
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact ves i (by simpa using hi)
end Light.Compiler
