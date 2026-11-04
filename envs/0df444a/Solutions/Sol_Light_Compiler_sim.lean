-- Prove2me | solution 1 for Light.Compiler.sim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:40:32.349562+00:00
-- url     : https://prove2.me/submissions/6c107558-661e-45d6-b756-0f332f3e9cc5

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_CallFrames
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Dispatcher
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
import Theorems.Thm_Light_Compiler_Decides_of_fails
import Theorems.Thm_Light_Compiler_Decides_of_holds
import Theorems.Thm_Light_Compiler_Framed_same
import Theorems.Thm_Light_Compiler_Rel_loc_zero
import Theorems.Thm_Light_Compiler_Rel_of_agreeOutside
import Theorems.Thm_Light_Compiler_Rel_read
import Theorems.Thm_Light_Compiler_Rel_same
import Theorems.Thm_Light_Compiler_Rel_setMem
import Theorems.Thm_Light_Compiler_Sizes_inRange_addr
import Theorems.Thm_Light_Compiler_Sizes_inRange_neg_one
import Theorems.Thm_Light_Compiler_Sizes_inRange_stack
import Theorems.Thm_Light_Compiler_cStack_add
import Theorems.Thm_Light_Compiler_cStack_succ_add
import Theorems.Thm_Light_Compiler_codeAt_after_pair
import Theorems.Thm_Light_Compiler_decides_compileCond
import Theorems.Thm_Light_Compiler_effects_argsCode
import Theorems.Thm_Light_Compiler_effects_compileExpr_of_width
import Theorems.Thm_Light_Compiler_effects_newFrame
import Theorems.Thm_Light_Compiler_length_argsCode
import Theorems.Thm_Light_Compiler_length_compileCond
import Theorems.Thm_Light_Compiler_length_compileExpr
import Theorems.Thm_Light_Compiler_length_compileStmt
import Theorems.Thm_Light_Compiler_length_newFrame
import Theorems.Thm_Light_Compiler_mem_writable_of_addr
import Theorems.Thm_Light_Compiler_scratch_subset_writable
import Theorems.Thm_Light_Compiler_steps_dispatcher
import Theorems.Thm_Light_Compiler_steps_jump
import Theorems.Thm_Light_Compiler_steps_pair
import Theorems.Thm_Light_Compiler_steps_setVar
import Theorems.Thm_Light_Compiler_straight_argsCode
import Theorems.Thm_Light_Compiler_straight_compileExpr
import Theorems.Thm_Light_Compiler_straight_newFrame
import Theorems.Thm_Light_Compiler_temps_subset_scratch
import Theorems.Thm_Light_Compiler_writable_subset_writable
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Theorems.Thm_Light_Stmt_width_call_le_iff
import Theorems.Thm_Light_Stmt_width_ite_le_iff
import Theorems.Thm_Light_Stmt_width_seq_le_iff
import Theorems.Thm_Light_Stmt_width_set_le_iff
import Theorems.Thm_Light_Stmt_width_store_le_iff
import Theorems.Thm_Light_Stmt_width_while_le_iff
import Theorems.Thm_Light_bounded_callFrame
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_read
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_left
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_count
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
import Theorems.Thm_ThreeSumApsp_WordRam_effects_append
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_steps_add
import Theorems.Thm_ThreeSumApsp_WordRam_steps_load
import Theorems.Thm_ThreeSumApsp_WordRam_steps_store
import Theorems.Thm_ThreeSumApsp_WordRam_steps_straight
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
section layout
variable {code : List Instr} {G : CodeLayout} {pos x p : ℕ} {e : Expr} {c : Cond} {s t : Stmt} {args : List Expr}
private theorem codeAt_set (h : CodeAt code pos (compileStmt G (.set x e) pos)) :
    CodeAt code pos (compileExpr e 0) ∧
      CodeAt code (pos + e.size) [.sub cADDR cFP (cPool (2 * x)), .store cADDR (cT 0)] :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileExpr])⟩
private theorem codeAt_seq (h : CodeAt code pos (compileStmt G (.seq s t) pos)) :
    CodeAt code pos (compileStmt G s pos) ∧ CodeAt code (pos + s.size G.F) (compileStmt G t (pos + s.size G.F)) :=
  ⟨h.left, h.right.cast_pos (by rw [length_compileStmt])⟩
private theorem codeAt_ite (h : CodeAt code pos (compileStmt G (.ite c s t) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
        CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG (pos + c.size + s.size G.F + 1 + t.size G.F)] ∧
          CodeAt code (pos + c.size + s.size G.F + 1) (compileStmt G t (pos + c.size + s.size G.F + 1)) :=
  by
  rw [compileStmt] at h
  refine ⟨h.left.left.left, h.left.left.right.cast_pos ?_, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]
private theorem codeAt_while (h : CodeAt code pos (compileStmt G (.while c s) pos)) :
    CodeAt code pos (compileCond c (pos + c.size + s.size G.F + 1)) ∧
      CodeAt code (pos + c.size) (compileStmt G s (pos + c.size)) ∧
        CodeAt code (pos + c.size + s.size G.F) [.bltz cNEG pos] :=
  by
  rw [compileStmt] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;> simp +arith [length_compileCond, length_compileStmt]
private theorem codeAt_call (h : CodeAt code pos (compileStmt G (.call p args x) pos)) :
    CodeAt code pos (argsCode args 0 ++ newFrame G.F args.length (pos + callSize G.F args)) ∧
      CodeAt code (pos + (argsSize args + (2 * G.F + 4))) [.bltz cNEG (G.entry.getD p 0)] ∧
        CodeAt code (pos + callSize G.F args) [.sub cADDR cFP (cPool (2 * x)), .store cADDR cRET] :=
  by
  rw [compileStmt, callCode] at h
  refine ⟨h.left.left, h.left.right.cast_pos ?_, h.right.cast_pos ?_⟩ <;> simp +arith [length_argsCode, length_newFrame, callSize]
end layout
private theorem le_stepsPerStep_mul {a c n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) : a ≤ stepsPerStep n * c :=
  calc
    a ≤ stepsPerStep n * 1 := by rw [stepsPerStep]; omega
    _ ≤ stepsPerStep n * c := Nat.mul_le_mul_left _ hc
private theorem add_le_stepsPerStep_mul {a b c k n : ℕ} (h : a ≤ n) (hc : 1 ≤ c) (hb : b ≤ stepsPerStep n * k) :
    a + b ≤ stepsPerStep n * (c + k) :=
  Nat.mul_add _ c k ▸ Nat.add_le_add (le_stepsPerStep_mul h hc) hb
private theorem call_le_stepsPerStep_mul {pos size b r a k n : ℕ} (hpos : pos + (size + 2) ≤ n) (hr : r ≤ n)
    (hb : b ≤ stepsPerStep n * k) : size + b + (r + 2 * (pos + size + 1)) + 2 ≤ stepsPerStep n * (a + 2 + k) :=
  by
  rw [Nat.mul_add (stepsPerStep n), Nat.mul_add (stepsPerStep n)]
  have hK : stepsPerStep n * 2 = 4 * n := by rw [stepsPerStep]; omega
  omega
variable {W : ℕ} (S : Setting W)
variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}
private theorem Start.sub (B : Start S d s σ pos q m) {t : Stmt} {pos' : ℕ} {m' : ℤ → BitVec W}
    (hcode : CodeAt S.code pos' (compileStmt S.toCodeLayout t pos')) (hpos : pos' + t.size S.F ≤ S.disp)
    (hw : t.width ≤ S.F) (hσ : σ'.Bounded S.lim) (R : Rel S.toSizes σ' q m') : Start S d t σ' pos' q m' :=
  { rel := R, low := B.low, high := B.high, codeAt := hcode, below := hpos, width := hw, bounded := hσ, room := B.room }
private theorem Start.room_succ (B : Start S d s σ pos q m) (hd : d < S.lim.depth) :
    q + S.F + 1 + S.F + (S.F + 1) * (S.lim.depth - (d + 1)) ≤ S.Q :=
  by
  have := B.room
  rw [show S.lim.depth - d = S.lim.depth - (d + 1) + 1 by omega, Nat.mul_succ] at this
  omega
private theorem Start.test (B : Start S d s σ pos q m) {c : Cond} {l : ℕ} (hcode : CodeAt S.code pos (compileCond c l))
    (hw : c.width ≤ S.F) (hs : c.Safe S.lim σ) : Decides S.code S.F pos c.size l m (c.Holds σ) :=
  decides_compileCond B.toFramed B.bounded c hcode hw hs
private theorem sim_skip : Simulates S d .skip σ σ 0 := fun _ _ m B =>
  ⟨m, 0, { run := Steps.refl _, le := Nat.zero_le _, rel := B.rel, agree := AgreeOutside.refl _ m }⟩
private theorem sim_set {x : ℕ} {e : Expr} (hs : e.Safe S.lim σ) :
    Simulates S d (.set x e) σ { σ with loc := Function.update σ.loc x (e.val σ) } (e.cost + 1) :=
  by
  intro pos q m B
  obtain ⟨hx, he⟩ := Stmt.width_set_le_iff.1 B.width
  obtain ⟨exprCode, setCode⟩ := codeAt_set B.codeAt
  have hpos : pos + (e.size + 2) ≤ S.disp := B.below
  obtain ⟨val, A⟩ := effects_compileExpr_of_width B.toFramed e 0 he hs (by omega)
  have A₁ := A.mono temps_subset_scratch
  have run₁ := steps_straight _ pos m exprCode (straight_compileExpr e 0)
  rw [length_compileExpr] at run₁
  obtain ⟨m₂, run₂, R₂, A₂⟩ :=
    steps_setVar (B.toFramed.same A₁) hx setCode val
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
  exact
    ⟨m₂, _,
      { run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
        le := le_stepsPerStep_mul (by omega) (by omega)
        rel := R₂
        agree := (A₁.mono scratch_subset_writable).trans A₂ }⟩
private theorem sim_store {a e : Expr} (hsa : a.Safe S.lim σ) (hse : e.Safe S.lim σ) (haddr : S.lim.Addr (a.val σ)) :
    Simulates S d (.store a e) σ { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) }
      (a.cost + e.cost + 1) :=
  by
  intro pos q m B
  obtain ⟨ha, he⟩ := Stmt.width_store_le_iff.1 B.width
  have hpos : pos + (a.size + e.size + 1) ≤ S.disp := B.below
  obtain ⟨m₁, run₁, va, ve, A₁⟩ := steps_pair B.toFramed B.codeAt ha he hsa hse
  have run₂ := run₁.trans (steps_store (codeAt_after_pair B.codeAt) va (S.inRange_addr haddr))
  rw [ve] at run₂
  exact
    ⟨_, _,
      { run := run₂.cast_pos (by rw [Stmt.size, Nat.add_assoc])
        le := le_stepsPerStep_mul (by omega) (by omega)
        rel := (B.rel.same A₁).setMem B.low haddr _
        agree := (A₁.mono scratch_subset_writable).update (mem_writable_of_addr haddr) _ }⟩
private theorem sim_seq {c₁ c₂ : ℕ} (h₁ : Exec S.lim S.P d s₁ σ σ₁ c₁) (ih₁ : Simulates S d s₁ σ σ₁ c₁)
    (ih₂ : Simulates S d s₂ σ₁ σ₂ c₂) : Simulates S d (.seq s₁ s₂) σ σ₂ (c₁ + c₂) :=
  by
  intro pos q m B
  obtain ⟨hw₁, hw₂⟩ := Stmt.width_seq_le_iff.1 B.width
  obtain ⟨firstCode, secondCode⟩ := codeAt_seq B.codeAt
  have hpos : pos + (s₁.size S.F + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih₁ _ _ _ (B.sub firstCode (by omega) hw₁ B.bounded B.rel)
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ := ih₂ _ _ _ (B.sub secondCode (by omega) hw₂ (h₁.bounded B.bounded) R₁)
  exact
    ⟨m₂, n₁ + n₂,
      { run := (run₁.trans run₂).cast_pos (by rw [Stmt.size, Nat.add_assoc])
        le := Nat.mul_add _ c₁ c₂ ▸ Nat.add_le_add le₁ le₂
        rel := R₂
        agree := A₁.trans A₂ }⟩
private theorem sim_iteTrue {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (ih : Simulates S d s₁ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) :=
  by
  intro pos q m B
  obtain ⟨hwc, hw₁, -⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, thenCode, jumpCode, -⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ :=
    ih _ _ _
      (B.sub thenCode (by omega) hw₁ B.bounded (B.rel.same A₀))
        -- the jump over the second branch
        
  have run₂ := (run₀.trans run₁).trans (steps_jump jumpCode R₁.neg S.inRange_neg_one)
  exact
    ⟨m₁, n₀ + 1 + n₁,
      { run := (run₂.cast_count (by omega)).cast_pos (by rw [Stmt.size]; omega)
        le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
        rel := R₁
        agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩
private theorem sim_iteFalse {c : Cond} {k : ℕ} (hs : c.Safe S.lim σ) (fails : ¬c.Holds σ)
    (ih : Simulates S d s₂ σ σ' k) : Simulates S d (.ite c s₁ s₂) σ σ' (c.cost + 1 + k) :=
  by
  intro pos q m B
  obtain ⟨hwc, -, hw₂⟩ := Stmt.width_ite_le_iff.1 B.width
  obtain ⟨testCode, -, -, elseCode⟩ := codeAt_ite B.codeAt
  have hpos : pos + (c.size + s₁.size S.F + 1 + s₂.size S.F) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ := ih _ _ _ (B.sub elseCode (by omega) hw₂ B.bounded (B.rel.same A₀))
  exact
    ⟨m₁, n₀ + n₁,
      { run := (run₀.trans run₁).cast_pos (by rw [Stmt.size]; omega)
        le := add_le_stepsPerStep_mul (by omega) (by omega) le₁
        rel := R₁
        agree := (A₀.mono scratch_subset_writable).trans A₁ }⟩
private theorem sim_whileFalse {c : Cond} (hs : c.Safe S.lim σ) (fails : ¬c.Holds σ) :
    Simulates S d (.while c s) σ σ (c.cost + 1) := by
  intro pos q m B
  obtain ⟨hwc, -⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, -, -⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_fails fails
  exact
    ⟨m₀, n₀,
      { run := run₀.cast_pos (by rw [Stmt.size]; omega)
        le := le_stepsPerStep_mul (by omega) (by omega)
        rel := B.rel.same A₀
        agree := A₀.mono scratch_subset_writable }⟩
private theorem sim_whileTrue {c : Cond} {k₁ k₂ : ℕ} (hs : c.Safe S.lim σ) (holds : c.Holds σ)
    (h₁ : Exec S.lim S.P d s σ σ₁ k₁) (ih₁ : Simulates S d s σ σ₁ k₁) (ih₂ : Simulates S d (.while c s) σ₁ σ₂ k₂) :
    Simulates S d (.while c s) σ σ₂ (c.cost + 1 + k₁ + k₂) :=
  by
  intro pos q m B
  obtain ⟨hwc, hw⟩ := Stmt.width_while_le_iff.1 B.width
  obtain ⟨testCode, bodyCode, jumpCode⟩ := codeAt_while B.codeAt
  have hpos : pos + (c.size + s.size S.F + 1) ≤ S.disp := B.below
  obtain ⟨m₀, n₀, le₀, A₀, run₀⟩ := (B.test testCode hwc hs).of_holds holds
  obtain ⟨m₁, n₁, run₁, le₁, R₁, A₁⟩ :=
    ih₁ _ _ _
      (B.sub bodyCode (by omega) hw B.bounded (B.rel.same A₀))
        -- the jump back
        
  have run₂ :=
    (run₀.trans run₁).trans
      (steps_jump jumpCode R₁.neg S.inRange_neg_one)
        -- the loop again
        
  obtain ⟨m₃, n₃, run₃, le₃, R₃, A₃⟩ := ih₂ _ _ _ (B.sub B.codeAt B.below B.width (h₁.bounded B.bounded) R₁)
  exact
    ⟨m₃, n₀ + 1 + n₁ + n₃,
      { run := (run₂.trans run₃).cast_count (by omega)
        le := Nat.mul_add _ _ k₂ ▸ Nat.add_le_add (add_le_stepsPerStep_mul (by omega) (by omega) le₁) le₃
        rel := R₃
        agree := ((A₀.mono scratch_subset_writable).trans A₁).trans A₃ }⟩
section call
variable {p x : ℕ} {args : List Expr}
private theorem steps_callEnter (B : Start S d (.call p args x) σ pos q m) (hsa : ∀ e ∈ args, e.Safe S.lim σ)
    (hd : d < S.lim.depth) {e : ℕ} (he : S.entry[p]? = some e) :
    ∃ m₂,
      Steps S.code (callSize S.F args) ⟨pos, m⟩ ⟨e, m₂⟩ ∧
        Rel S.toSizes ⟨frame (args.map (·.val σ)), σ.mem⟩ (q + S.F + 1) m₂ ∧
          m₂ (cStack (q + S.F)) = wd W ((pos + callSize S.F args : ℕ) : ℤ) ∧
            AgreeOutside (Writable S.toSizes (q + S.F)) m m₂ :=
  by
  obtain ⟨-, hlen, hwa⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨frameCode, jumpCode, -⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  rw [List.getD_eq_getElem?_getD, he, Option.getD_some] at jumpCode
  obtain ⟨vals, A⟩ := effects_argsCode B.toFramed args 0 hwa hsa (by omega)
  have A₁ := A.mono temps_subset_scratch
  obtain ⟨R₂, hret, A₂⟩ :=
    effects_newFrame (B.toFramed.same A₁) ((Nat.le_add_right _ _).trans (B.room_succ hd)) args (by simpa using vals)
      (ret := pos + callSize S.F args) (by omega)
  have run₂ :=
    steps_straight _ pos m frameCode (List.forall_mem_append.2 ⟨straight_argsCode _ _, straight_newFrame _ _ _⟩)
  rw [effects_append, List.length_append, length_argsCode, length_newFrame] at run₂
  exact
    ⟨_, (run₂.trans (steps_jump jumpCode R₂.neg S.inRange_neg_one)).cast_count (by rw [callSize]; omega), R₂, hret,
      (A₁.mono scratch_subset_writable).trans A₂⟩
private theorem steps_callLeave (S : Setting W) {ret : ℕ} (R : Rel S.toSizes σ (q + S.F + 1) m)
    (hcode : CodeAt S.code pos (epilogue S.toCodeLayout)) (hret : m (cStack (q + S.F)) = wd W ret) (hlt : ret < S.disp)
    (hQ : q + S.F + 1 ≤ S.Q) (hF : 0 < S.F) :
    ∃ m',
      Steps S.code (epilogueSize + 2 * (ret + 1)) ⟨pos, m⟩ ⟨ret, m'⟩ ∧
        m' cFP = wd W (cStack q) ∧ m' cRET = wd W (σ.loc 0) ∧ AgreeOutside (insert cFP (Scratch S.F)) m m' :=
  by
  have hN := S.offsets_le
  have run₁ := steps_load (i := cRET) hcode R.fp (S.inRange_stack hQ)
  rw [R.loc_zero hF] at run₁
  have A₁ :=
    (AgreeOutside.refl (Scratch S.F) m).update (a := cRET)
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
      (wd W (σ.loc 0))
        -- ADDR := FP + 2, the address of the stack cell before the frame
        
  have run₂ := run₁.trans (steps_add hcode.tail (R.same A₁).fp ((R.same A₁).pool 2 (by omega)))
  rw [cStack_succ_add] at run₂
  have A₂ :=
    A₁.update (a := cADDR)
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
      (wd W (cStack (q + S.F)))
        -- RR := the cell at ADDR, which holds ret
        
  have run₃ := run₂.trans (steps_load hcode.tail.tail (Function.update_self _ _ _) (S.inRange_stack (by omega)))
  rw [A₂.read
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
      hret] at run₃
  have A₃ :=
    A₂.update (a := cRR)
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
        -- FP := FP + 2 (F + 1), the frame of the caller
        
  have run₄ := run₃.trans (steps_add hcode.tail.tail.tail (R.same A₃).fp ((R.same A₃).pool _ hN))
  rw [Nat.add_assoc q, cStack_add] at run₄
  have run₅ :=
    run₄.trans
      (steps_jump hcode.tail.tail.tail.tail
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
            exact (R.same A₃).neg))
        S.inRange_neg_one)
        -- the dispatcher, which leaves -1 in RR
        
  have run₆ :=
    run₅.trans
      (steps_dispatcher S.dispatcherAt hlt S.fits.pool_lt _
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
            exact (R.same A₃).one))
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
                                _root_.false_or, _root_.or_false] <;> intros <;> omega))]))))
  exact
    ⟨_, run₆, by
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
      by
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
      ((A₃.mono
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
                          _root_.false_or, _root_.or_false] <;> intros <;> omega))).update
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
private theorem sim_call {body : Stmt} {k : ℕ} (hsa : ∀ e ∈ args, e.Safe S.lim σ) (hp : S.P[p]? = some body)
    (hd : d < S.lim.depth) (ih : Simulates S (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ σ' k) :
    Simulates S d (.call p args x) σ ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩ ((args.map Expr.cost).sum + 2 + k) :=
  by
  intro pos q m B
  obtain ⟨hx, -, -⟩ := Stmt.width_call_le_iff.1 B.width
  obtain ⟨e, he, procCode, hend⟩ := S.bodyAt p body hp
  obtain ⟨-, -, resultCode⟩ := codeAt_call B.codeAt
  have hpos : pos + (callSize S.F args + 2) ≤ S.disp := B.below
  have hq := B.low
  have hroom := B.room_succ hd
  obtain ⟨m₁, run₁, R₁, hret, A₁⟩ := steps_callEnter B hsa hd he
  obtain ⟨m₂, n₂, run₂, le₂, R₂, A₂⟩ :=
    ih e (q + S.F + 1) m₁
      { rel := R₁, low := by omega, high := by omega, codeAt := procCode.left, below := by omega,
        width := S.width body (List.mem_of_getElem? hp), bounded := bounded_callFrame B.bounded args hsa,
        room := hroom }
        -- the body writes the stack only from its frame on, so the position to return to is still there
        
  have hret₂ :=
    A₂.read (a := cStack (q + S.F))
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
      hret
  obtain ⟨m₃, run₃, hfp, hres, A₃⟩ :=
    steps_callLeave S R₂ (procCode.right.cast_pos (by rw [length_compileStmt])) hret₂ (by omega) (by omega)
      (Nat.zero_lt_of_lt hx)
        -- since the call began, the stack has changed only from cell q + F on: the local variables of the
          -- caller are as before, and the memory is as the procedure left it
        
  have A : AgreeOutside (Writable S.toSizes (q + S.F)) m m₃ :=
    (A₁.trans (A₂.mono (writable_subset_writable (by omega)))).trans
      (A₃.mono
        (Set.insert_subset
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
          scratch_subset_writable))
  have I₃ : Framed S.toSizes ⟨σ.loc, σ'.mem⟩ q m₃ :=
    ⟨R₂.of_agreeOutside A₃
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
        hfp
        (fun y hy =>
          A.read
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
            (B.rel.loc y hy))
        fun a ha =>
        A₃.read
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
          (R₂.mem a ha),
      hq, B.high⟩
      -- store the result
      
  obtain ⟨m₄, run₄, R₄, A₄⟩ :=
    steps_setVar I₃ hx resultCode hres
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
  exact
    ⟨m₄, _,
      { run := (((run₁.trans run₂).trans run₃).trans run₄).cast_pos (by rw [Stmt.size, Nat.add_assoc])
        le := call_le_stepsPerStep_mul hpos (by omega) le₂
        rel := R₄
        agree := (A.mono (writable_subset_writable (by omega))).trans A₄ }⟩
end call
end Light.Compiler
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light Light.Compiler
open EndStatement (Instr)
variable {W : ℕ} (S : Setting W)
variable {S} {d pos q : ℕ} {s s₁ s₂ : Stmt} {σ σ' σ₁ σ₂ : State} {m : ℤ → BitVec W}
namespace Light.Compiler
theorem _root_.solution (S : Setting W) {c : ℕ} (h : Exec S.lim S.P d s σ σ' c) : Simulates S d s σ σ' c := by
  induction h with
  | skip => exact sim_skip
  | set hs => exact sim_set hs
  | store hsa hse haddr => exact sim_store hsa hse haddr
  | seq h₁ _ ih₁ ih₂ => exact sim_seq h₁ ih₁ ih₂
  | iteTrue hs holds _ ih => exact sim_iteTrue hs holds ih
  | iteFalse hs fails _ ih => exact sim_iteFalse hs fails ih
  | whileFalse hs fails => exact sim_whileFalse hs fails
  | whileTrue hs holds h₁ _ ih₁ ih₂ => exact sim_whileTrue hs holds h₁ ih₁ ih₂
  | call hsa hp hd _ ih => exact sim_call hsa hp hd ih
end Light.Compiler
