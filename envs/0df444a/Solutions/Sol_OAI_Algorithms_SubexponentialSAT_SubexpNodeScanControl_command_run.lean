-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:13:46.291273+00:00
-- url     : https://prove2.me/submissions/8d8b22f7-31b4-4b26-a1ad-4a5f63b0a07a

import Mathlib
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S081

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionIteration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

theorem test_eval (counter : Fin 256) (flag : Fin 16) (d : Data) :
    Eval (test counter flag) 1 d (testResult counter flag d) :=
  .base (.atom _ _)

theorem testResult_flag (counter : Fin 256) (flag : Fin 16) (d : Data) :
    (testResult counter flag d).regs flag = decide (0 < (d.stacks counter).length) := by
  cases h : d.stacks counter with
  | nil => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]
  | cons b bs => simp [testResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      readRegs, h]

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionStore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-only contracts for the concrete copies, fixed-width reads, and unary
counter updates in the convolution controller. Register values are genuine
outputs of the executed commands, but are unrestricted between these blocks. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

theorem takeCell_run (src dst : Fin 256) (s : Store) (bits rest : List Bool)
    (hdist : Function.Injective (![104, 121, 122, src, dst] : Fin 5 → Fin 256))
    (hsrc : s src = bits ++ rest) (hcounter : s 121 = []) (htmp : s 122 = [])
    (hwidth : (s 104).length = bits.length) :
    ExecutesIn (takeCell src dst) (14 * bits.length + 11) s
      (Function.update (Function.update s src rest) dst (bits ++ s dst)) := by
  intro regs
  refine ⟨_, readRegs regs 0 1 none, le_rfl, ?_⟩
  exact SubexpScanPrimitives.takeWord_eval (⟨regs, s⟩ : Data)
    104 121 122 src dst 0 1 hdist (by decide) bits rest hsrc hcounter htmp hwidth

theorem popToken_run (counter : Fin 256) (s : Store) (bit : Bool) (rest : List Bool)
    (hcounter : s counter = bit :: rest) :
    ExecutesIn (popToken counter) 1 s (Function.update s counter rest) := by
  intro regs
  refine ⟨1, readRegs regs 0 1 (some bit), le_rfl, ?_⟩
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop counter 0 1)
    (⟨regs, s⟩ : Data)
  simpa [popToken, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr, hcounter] using Eval.base h

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

local infixr:55 " ;; " => seq

theorem work_update (base : Store) (w : Fin 6 → List Bool) (i : Fin 6) (v : List Bool) :
    work base (Function.update w i v) = Function.update (work base w) (ports i) v :=
  ProgramLinking.extend_update ports.injective w base i v

theorem work_frame (base : Store) (w : Fin 6 → List Bool) (j : Fin 256)
    (hj : ¬ ∃ i, ports i = j) : work base w j = base j :=
  Function.extend_apply' _ _ _ hj

@[simp] theorem work_104 (base : Store) (w : Fin 6 → List Bool) : work base w 104 = base 104 :=
  work_frame base w 104 (by decide)
@[simp] theorem work_121 (base : Store) (w : Fin 6 → List Bool) : work base w 121 = base 121 :=
  work_frame base w 121 (by decide)
@[simp] theorem work_122 (base : Store) (w : Fin 6 → List Bool) : work base w 122 = base 122 :=
  work_frame base w 122 (by decide)

theorem branch_true (counter : Fin 256) (flag : Fin 16) (yes no : Code)
    (K : ℕ) (s t : Store) (hpos : 0 < (s counter).length)
    (h : ExecutesIn yes K s t) :
    ExecutesIn (.seq (test counter flag) (.ite flag yes no)) (K + 2) s t := by
  intro regs
  let d : Data := ⟨regs, s⟩
  obtain ⟨n, rf, hn, he⟩ := h (testResult counter flag d).regs
  have hg : (testResult counter flag d).regs flag = true := by
    rw [testResult_flag]
    exact decide_eq_true hpos
  exact ⟨1 + (n + 1), rf, by omega, (test_eval counter flag d).seq (.ite_true hg he)⟩

theorem branch_false (counter : Fin 256) (flag : Fin 16) (yes no : Code)
    (K : ℕ) (s t : Store) (hempty : s counter = [])
    (h : ExecutesIn no K s t) :
    ExecutesIn (.seq (test counter flag) (.ite flag yes no)) (K + 2) s t := by
  intro regs
  let d : Data := ⟨regs, s⟩
  obtain ⟨n, rf, hn, he⟩ := h (testResult counter flag d).regs
  have hg : (testResult counter flag d).regs flag = false := by
    rw [testResult_flag]
    simp [d, hempty]
  exact ⟨1 + (n + 1), rf, by omega, (test_eval counter flag d).seq (.ite_false hg he)⟩

variable {A C : Type*}

theorem choose_run (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K : ℕ)
    (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
    (cs : List C) (x : Cursor A) (c : C) :
    ExecutesIn (choose includeNode) (K + 9)
      (ready base encode encodeA cs x (encode c) [])
      (ready base encode encodeA cs (next f c x) (encode c) (negativeAfter negative c x)) := by
  rcases x with ⟨a, skip, pending⟩
  cases skip with
  | cons bit rest =>
    let before : Cursor A := ⟨a, bit :: rest, pending⟩
    let popped : Cursor A := ⟨a, rest, pending⟩
    have he : Function.update (ready base encode encodeA cs before (encode c) []) 217 rest =
        ready base encode encodeA cs popped (encode c) [] := by
      change Function.update (work base (words encode encodeA cs before (encode c) []))
        (ports 1) rest = work base (words encode encodeA cs popped (encode c) [])
      rw [← work_update]
      apply congrArg (work base)
      funext i
      fin_cases i <;> simp [words, before, popped]
    have hp := popToken_run 217 (ready base encode encodeA cs before (encode c) []) bit rest
      (by simp [ready, words, before])
    rw [he] at hp
    have h := branch_true 217 13 (popToken 217 ;; includeNode)
      (test 229 13 ;; .ite 13 (clear 229) includeNode) (1 + K) _ _
      (by simp [ready, words, before]) (hp.seq (hinclude cs popped c))
    exact h.mono (by omega)
  | nil =>
    cases pending with
    | false =>
      have h₁ := branch_false 229 13 (clear 229) includeNode K _ _
        (by simp [ready, words, marker]) (hinclude cs ⟨a, [], false⟩ c)
      have h₂ := branch_false 217 13 (popToken 217 ;; includeNode)
        (test 229 13 ;; .ite 13 (clear 229) includeNode) (K + 2) _ _
        (by simp [ready, words]) h₁
      exact h₂.mono (by omega)
    | true =>
      let s := ready base encode encodeA cs (⟨a, [], true⟩ : Cursor A) (encode c) []
      have he : Function.update s 229 [] =
          ready base encode encodeA cs (⟨a, [], false⟩ : Cursor A) (encode c) [] := by
        change Function.update
          (work base (words encode encodeA cs ⟨a, [], true⟩ (encode c) [])) (ports 2) [] =
          work base (words encode encodeA cs ⟨a, [], false⟩ (encode c) [])
        rw [← work_update]
        apply congrArg (work base)
        funext i
        fin_cases i <;> simp [words, marker]
      have hc : ExecutesIn (clear 229) 5 s
          (ready base encode encodeA cs (⟨a, [], false⟩ : Cursor A) (encode c) []) := by
        have h := clear_run 229 s
        rw [he] at h
        simpa [s, ready, words, marker] using h
      have h₁ := branch_true 229 13 (clear 229) includeNode 5 _ _
        (by simp [s, ready, words, marker]) hc
      have h₂ := branch_false 217 13 (popToken 217 ;; includeNode)
        (test 229 13 ;; .ite 13 (clear 229) includeNode) 7 _ _
        (by simp [s, ready, words]) h₁
      exact h₂.mono (by omega)

theorem step_run (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K W : ℕ)
    (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
    (hencode : ∀ c, (encode c).length = W)
    (hnegative : ∀ c, (negative c).length ≤ W)
    (hwidth : (base 104).length = W) (h121 : base 121 = []) (h122 : base 122 = [])
    (cs : List C) (x : Cursor A) (c : C) :
    ExecutesIn (step includeNode) (K + 18 * W + 26)
      (ready base encode encodeA (c :: cs) x [] [])
      (ready base encode encodeA cs (next f c x) [] []) := by
  let s := ready base encode encodeA (c :: cs) x [] []
  let middle := ready base encode encodeA cs x (encode c) []
  let chosen := ready base encode encodeA cs (next f c x) (encode c) (negativeAfter negative c x)
  let cleaned := ready base encode encodeA cs (next f c x) [] (negativeAfter negative c x)
  have he₁ : Function.update (Function.update s 215 (cs.flatMap encode)) 218 (encode c ++ s 218) =
      middle := by
    have hs218 : s 218 = [] := by simp [s, ready, words]
    rw [hs218, List.append_nil]
    change Function.update (Function.update
      (work base (words encode encodeA (c :: cs) x [] []))
      (ports 0) (cs.flatMap encode)) (ports 4) (encode c) =
      work base (words encode encodeA cs x (encode c) [])
    rw [← work_update, ← work_update]
    apply congrArg (work base)
    funext i
    fin_cases i <;> simp [ words ]
  have h₁ : ExecutesIn (takeCell 215 218) (14 * W + 11) s middle := by
    have h := takeCell_run 215 218 s (encode c) (cs.flatMap encode) (by decide)
      (by simp [s, ready, words]) (by simp [s, ready, h121])
      (by simp [s, ready, h122]) (by simp [s, ready, hwidth, hencode])
    rw [he₁] at h
    simpa [hencode] using h
  have h₂ := choose_run includeNode base encode encodeA negative f K hinclude cs x c
  have he₃ : Function.update chosen 218 [] = cleaned := by
    change Function.update
      (work base (words encode encodeA cs (next f c x) (encode c) (negativeAfter negative c x)))
        (ports 4) [] =
      work base (words encode encodeA cs (next f c x) [] (negativeAfter negative c x))
    rw [← work_update]
    apply congrArg (work base)
    funext i
    fin_cases i <;> simp [words ]
  have h₃ : ExecutesIn (clear 218) (2 * W + 3) chosen cleaned := by
    have h := clear_run 218 chosen
    rw [he₃] at h
    simpa [chosen, ready, words, hencode] using h
  have he₄ : Function.update cleaned 219 [] = ready base encode encodeA cs (next f c x) [] [] := by
    change Function.update
      (work base (words encode encodeA cs (next f c x) [] (negativeAfter negative c x)))
        (ports 5) [] = work base (words encode encodeA cs (next f c x) [] [])
    rw [← work_update]
    apply congrArg (work base)
    funext i
    fin_cases i <;> simp [words]
  have hn : (negativeAfter negative c x).length ≤ W := by
    rcases x with ⟨a, skip, pending⟩
    cases skip <;> cases pending <;> simp [negativeAfter, hnegative]
  have h₄ : ExecutesIn (clear 219) (2 * W + 3) cleaned
      (ready base encode encodeA cs (next f c x) [] []) := by
    have h := clear_run 219 cleaned
    rw [he₄] at h
    apply h.mono
    simpa [cleaned, ready, words] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 hn) 3
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  convert h using 1
  · rfl
  · ring

theorem loop_eval (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K W : ℕ)
    (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
    (hencode : ∀ c, (encode c).length = W) (hW : 0 < W)
    (hnegative : ∀ c, (negative c).length ≤ W)
    (hwidth : (base 104).length = W) (h121 : base 121 = []) (h122 : base 122 = [])
    (cs : List C) : ∀ (x : Cursor A) (regs : Fin 16 → Bool),
    regs 15 = decide (0 < cs.length) →
    ∃ n rf, n ≤ cs.length * (K + 18 * W + 28) + 1 ∧
      Eval (.while 15 (step includeNode ;; test 215 15)) n
        ⟨regs, ready base encode encodeA cs x [] []⟩
        ⟨rf, ready base encode encodeA [] (run f cs x) [] []⟩ := by
  induction cs with
  | nil =>
    intro x regs hg
    exact ⟨1, regs, by simp, .while_false (by simpa using hg)⟩
  | cons c cs ih =>
    intro x regs hg
    obtain ⟨n, r₁, hn, he⟩ := step_run includeNode base encode encodeA negative f K W
      hinclude hencode hnegative hwidth h121 h122 cs x c regs
    let d : Data := ⟨r₁, ready base encode encodeA cs (next f c x) [] []⟩
    have hflag : (testResult 215 15 d).regs 15 = decide (0 < cs.length) := by
      rw [testResult_flag]
      cases cs with
      | nil => simp [d, ready, words]
      | cons y ys => simp [d, ready, words, hencode, hW]
    obtain ⟨m, rf, hm, ht⟩ := ih (next f c x) (testResult 215 15 d).regs hflag
    refine ⟨(n + 1) + m + 1, rf, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · exact .while_true (by simpa using hg) (he.seq (test_eval 215 15 d)) ht

theorem command_run_oai (includeNode : Code) (base : Store)
    (encode : C → List Bool) (encodeA : A → List Bool)
    (negative : C → List Bool) (f : A → C → A) (K W : ℕ)
    (hinclude : IncludeSpec includeNode base encode encodeA negative f K)
    (hencode : ∀ c, (encode c).length = W) (hW : 0 < W)
    (hnegative : ∀ c, (negative c).length ≤ W)
    (hwidth : (base 104).length = W) (h121 : base 121 = []) (h122 : base 122 = [])
    (cs : List C) (x : Cursor A) :
    ExecutesIn (command includeNode) (cs.length * (K + 18 * W + 28) + 2)
      (ready base encode encodeA cs x [] [])
      (ready base encode encodeA [] (run f cs x) [] []) := by
  intro regs
  let d : Data := ⟨regs, ready base encode encodeA cs x [] []⟩
  have hflag : (testResult 215 15 d).regs 15 = decide (0 < cs.length) := by
    rw [testResult_flag]
    cases cs with
    | nil => simp [d, ready, words]
    | cons y ys => simp [d, ready, words, hencode, hW]
  obtain ⟨n, rf, hn, he⟩ := loop_eval includeNode base encode encodeA negative f K W
    hinclude hencode hW hnegative hwidth h121 h122 cs x (testResult 215 15 d).regs hflag
  exact ⟨1 + n, rf, by omega, (test_eval 215 15 d).seq he⟩

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl.command_run_oai.{u_1, u_2}
