-- Prove2me | solution 1 for Light.Compiler.effects_compileExpr_of_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:15:55.623671+00:00
-- url     : https://prove2.me/submissions/9e6d4bab-8463-41b2-b545-97effefaa7ed

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Expressions
import Theorems.Thm_Light_Compiler_Framed_same
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Rel_same
import Theorems.Thm_Light_Compiler_Sizes_inRange_addr
import Theorems.Thm_Light_Compiler_Sizes_inRange_stack
import Theorems.Thm_Light_Compiler_cStack_sub
import Theorems.Thm_Light_Compiler_temps_subset_scratch
import Theorems.Thm_Light_Expr_vars_op_le_iff
import Theorems.Thm_Light_Expr_width_le_iff
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
import Theorems.Thm_ThreeSumApsp_WordRam_effect_load
import Theorems.Thm_ThreeSumApsp_WordRam_effect_mul
import Theorems.Thm_ThreeSumApsp_WordRam_effect_sub
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_wd_toInt
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
variable {W : ℕ} {F : ℕ}
private theorem _root_.Light.Expr.height_pos (e : Expr) : 0 < e.height := by
  induction e with
  | const n => simp [Expr.height]
  | var x => simp [Expr.height]
  | op o a b iha _ => exact lt_of_lt_of_le iha (le_max_left _ _)
  | load a ih => exact ih
private theorem cT_mem_temps_of_height (e : Expr) {k : ℕ} (hT : k + e.height ≤ 2 * F + 1) : cT k ∈ Temps k F :=
  by
  have := e.height_pos
  (simp only [_root_.Set.subset_def, _root_.Set.mem_compl_iff, _root_.Light.Compiler.Constants,
          _root_.Light.Compiler.Scratch, _root_.Light.Compiler.Writable, _root_.Light.Compiler.MainFrame,
          _root_.Set.mem_union, _root_.Set.mem_insert_iff, _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq,
          _root_.Light.Compiler.mem_temps_iff, _root_.Light.Compiler.mem_stack_iff, _root_.Light.Compiler.mem_pool_iff,
          _root_.Light.Compiler.cARG1, _root_.Light.Compiler.cARG2, _root_.Light.Compiler.cRESULT,
          _root_.Light.Compiler.cONE, _root_.Light.Compiler.cZERO, _root_.Light.Compiler.cNEG,
          _root_.Light.Compiler.cFP, _root_.Light.Compiler.cADDR, _root_.Light.Compiler.cRET, _root_.Light.Compiler.cRR,
          _root_.Light.Compiler.cNFP, _root_.Light.Compiler.cD, _root_.Light.Compiler.cT, _root_.Light.Compiler.cPool,
          _root_.Light.Compiler.cStack, _root_.Light.Compiler.mainFrame, _root_.ne_eq, _root_.true_or, _root_.or_true,
          _root_.false_or, _root_.or_false] <;>
        intros <;>
      omega)
private theorem effects_digitsCode {c : ℤ} (hc : cONE ≠ c) (L : List ℕ) (hL : ∀ d ∈ L, d < 2) (m : ℤ → BitVec W)
    (hone : m cONE = wd W 1) :
    effects (digitsCode c L) m c = wd W (Nat.ofDigits 2 L : ℕ) ∧ AgreeOutside { c } m (effects (digitsCode c L) m) := by
  induction L with
  | nil =>
    -- c := c - c
    
    rw [digitsCode, effects_cons, effects_nil, effect_sub c (wd_toInt (m c)).symm (wd_toInt (m c)).symm, sub_self]
    exact ⟨by simp, (AgreeOutside.refl _ m).update (Set.mem_singleton c) _⟩
  | cons d L
    ih =>
    obtain ⟨val, A⟩ :=
      ih fun x hx =>
        hL x
          (by simp [hx])
            -- c := c + c
            
    rw [digitsCode, effects_append, effects_append, effects_cons, effects_nil, effect_add c val val]
    have hd : d = 0 ∨ d = 1 := by have := hL d (by simp); omega
    obtain rfl | rfl := hd
    · refine ⟨?_, A.update (Set.mem_singleton c) _⟩
      rw [if_pos rfl, effects_nil, Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
    · -- c := c + 1
      
      rw [if_neg one_ne_zero, effects_cons, effects_nil,
        effect_add c (Function.update_self _ _ _) ((Function.update_of_ne hc _ _).trans (A.read hc hone))]
      refine ⟨?_, (A.update (Set.mem_singleton c) _).update (Set.mem_singleton c) _⟩
      rw [Function.update_self, Nat.ofDigits_cons]
      congr 1
      push_cast
      ring
private theorem effect_instr (o : Op) {m : ℤ → BitVec W} {j k a b : ℤ} (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (o.instr i j k) m = Function.update m i (wd W (o.eval a b)) :=
  by
  cases o
  exacts [effect_add i hj hk, effect_sub i hj hk, effect_mul i hj hk]
variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
private theorem effects_compileExpr (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hvars : e.vars ≤ Z.F) (hs : e.Safe Z.lim σ)
    (hT : k + e.height ≤ 2 * Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧ AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  by
  induction e generalizing k m with
  | const n =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨val, A⟩ :=
      effects_digitsCode (c := cT k)
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
        (Nat.digits 2 n) (fun d hd => Nat.digits_lt_base (by norm_num) hd) m I.rel.one
    rw [Nat.ofDigits_digits] at val
    exact ⟨val, A.mono (Set.singleton_subset_iff.2 hk)⟩
  | var x =>
    have hk := cT_mem_temps_of_height _ hT
    have hx : x < Z.F := hvars
    have hN := Z.offsets_le
    have hQ := I.high
    rw [compileExpr, effects_cons, effects_cons, effects_nil, effect_sub cADDR I.rel.fp (I.rel.pool (2 * x) (by omega)),
      cStack_sub, effect_load (cT k) (Function.update_self _ _ _) (Z.inRange_stack (by omega))]
    refine
      ⟨?_,
        ((AgreeOutside.refl _ m).update
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
                    omega))
              _).update
          hk _⟩
    rw [Function.update_self,
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
                  _root_.or_true, _root_.false_or, _root_.or_false] <;>
                intros <;>
              omega)),
      I.rel.loc x hx, Expr.val]
  | op o a b iha ihb =>
    have hk := cT_mem_temps_of_height _ hT
    have hha : a.height ≤ (Expr.op o a b).height := le_max_left _ _
    have hhb : b.height + 1 ≤ (Expr.op o a b).height := le_max_right _ _
    obtain ⟨hwa, hwb⟩ := Expr.vars_op_le_iff.1 hvars
    obtain ⟨hsa, hsb, -⟩ := hs
    obtain ⟨va, Aa⟩ := iha I k hwa hsa (by omega)
    obtain ⟨vb, Ab⟩ :=
      ihb (I.same (Aa.mono temps_subset_scratch)) (k + 1) hwb hsb
        (by omega)
          -- T_k := T_k o T_{k+1}
          
    rw [compileExpr, effects_append, effects_append, effects_cons, effects_nil,
      effect_instr o (cT k)
        (Ab.read
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
          va)
        vb]
    exact
      ⟨Function.update_self _ _ _,
        (Aa.trans
              (Ab.mono
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
                      omega)))).update
          hk _⟩
  | load a ih =>
    have hk := cT_mem_temps_of_height _ hT
    obtain ⟨hsa, haddr⟩ := hs
    obtain ⟨va, Aa⟩ := ih I k hvars hsa hT
    have hnonneg : 0 ≤ a.val σ :=
      haddr.1
        -- T_k := the cell at T_k
        
    rw [compileExpr, effects_append, effects_cons, effects_nil, effect_load (cT k) va (Z.inRange_addr haddr),
      Aa.cell
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
      I.rel.read haddr]
    exact ⟨Function.update_self _ _ _, Aa.update hk _⟩
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
variable {W : ℕ} {F : ℕ}
variable {Z : Sizes W} {σ : State} {q : ℕ} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (I : Framed Z σ q m) (e : Expr) (k : ℕ) (hw : e.width ≤ Z.F) (hs : e.Safe Z.lim σ)
    (hk : k ≤ Z.F + 1) :
    effects (compileExpr e k) m (cT k) = wd W (e.val σ) ∧ AgreeOutside (Temps k Z.F) m (effects (compileExpr e k) m) :=
  effects_compileExpr I e k (Expr.width_le_iff.1 hw).1 hs (by have := (Expr.width_le_iff.1 hw).2; omega)
end Light.Compiler
