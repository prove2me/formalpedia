-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:30:19.948991+00:00
-- url     : https://prove2.me/submissions/00b5279d-5bba-4e68-afdf-8c3928435401

import Mathlib
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_correctionCommand_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_includeNodeCommand_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_initializeLocal_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_prepareLocalInverse_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNodeScanControl_command_run

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

theorem run_after_skip (f : A → C → A) (cs : List C) (a : A) :
    (run f cs ⟨a, [], false⟩).value = cs.foldl f a := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih => simpa [run, next] using ih (f a c)

/-- The physical index/marker traversal includes exactly all nodes except the
indexed one. An out-of-range index simply includes all nodes. -/
theorem run_skip_index (f : A → C → A) (cs : List C) (skip : List Bool) (a : A) :
    (run f cs ⟨a, skip, true⟩).value = (cs.eraseIdx skip.length).foldl f a := by
  induction cs generalizing skip a with
  | nil => simp [run]
  | cons c cs ih =>
    cases skip with
    | nil => simpa [run, next] using run_after_skip f cs a
    | cons bit rest => simpa [run, next] using ih rest (f a c)

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

private theorem scan_ports_high (i : Fin 6) : 205 ≤ (SubexpNodeScanControl.ports i).val := by
  fin_cases i <;> decide

theorem scanReady_low {C P : Type*} (base : Store) (encC : C → List Bool) (encP : P → List Bool)
    (cs : List C) (x : SubexpNodeScanControl.Cursor P) (current negative : List Bool) :
    LowFrame base (SubexpNodeScanControl.ready base encC encP cs x current negative) := by
  intro i hi
  apply SubexpNodeScanControl.work_frame
  rintro ⟨j, hj⟩
  have hg := scan_ports_high j
  have hv := congrArg Fin.val hj
  omega

theorem includeNode_spec {C P : Type*} (base : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (sm sa pm : Code) (cm ca : C → C → C) (mulP : P → P → P)
    (Km Ka Kp W V J : ℕ) (theta one minusOne : C) (linear : C → P)
    (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
    (hpm : ServiceSpec base encP pm mulP Kp)
    (hcwidth : ∀ a, (encC a).length = W) (hpwidth : ∀ a, (encP a).length ≤ V)
    (hlinear : ∀ a, encP (linear a) = DensePolynomialProgram.Constructor.Counter.paddedBits
      W (encC a) (encC one) J)
    (htheta : base 213 = encC theta) (hone : base 207 = encC one)
    (hminus : base 211 = encC minusOne) (hJ : base 243 = List.replicate J true)
    (hzero : base 104 = List.replicate W false)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,205,223,241,244,245,246] : List (Fin 256)),
      base i = []) :
    SubexpNodeScanControl.IncludeSpec (includeNodeCommand sm sa pm) base encC encP
      (fun _ => []) (localUpdate cm ca mulP linear theta minusOne J)
      (includeBudget Km Ka Kp W V J) := by
  intro cs x c
  let s := SubexpNodeScanControl.ready base encC encP cs x (encC c) []
  have hout (j : Fin 256) (hj : ¬ ∃ i, SubexpNodeScanControl.ports i = j) : s j = base j :=
    SubexpNodeScanControl.work_frame base _ j hj
  have h := includeNodeCommand_run base encC encP sm sa pm cm ca mulP Km Ka Kp W V J
    one minusOne linear hsm hsa hpm hcwidth hpwidth hlinear s theta c x.value
    (scanReady_low base encC encP cs x (encC c) [])
    ((hout 213 (by decide)).trans htheta)
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 207 (by decide)).trans hone) ((hout 211 (by decide)).trans hminus)
    ((hout 243 (by decide)).trans hJ) ((hout 104 (by decide)).trans hzero)
    ((hout 100 (by decide)).trans (hclean 100 (by simp)))
    ((hout 101 (by decide)).trans (hclean 101 (by simp)))
    ((hout 102 (by decide)).trans (hclean 102 (by simp)))
    ((hout 107 (by decide)).trans (hclean 107 (by simp)))
    ((hout 108 (by decide)).trans (hclean 108 (by simp)))
    ((hout 120 (by decide)).trans (hclean 120 (by simp)))
    ((hout 205 (by decide)).trans (hclean 205 (by simp)))
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 223 (by decide)).trans (hclean 223 (by simp)))
    (by simp [s, SubexpNodeScanControl.ready, SubexpNodeScanControl.words])
    ((hout 241 (by decide)).trans (hclean 241 (by simp)))
    ((hout 244 (by decide)).trans (hclean 244 (by simp)))
    ((hout 245 (by decide)).trans (hclean 245 (by simp)))
    ((hout 246 (by decide)).trans (hclean 246 (by simp)))
  have he : Function.update s 240
      (encP (localUpdate cm ca mulP linear theta minusOne J x.value c)) =
      SubexpNodeScanControl.ready base encC encP cs
        {x with value := localUpdate cm ca mulP linear theta minusOne J x.value c} (encC c) [] := by
    change Function.update (SubexpNodeScanControl.work base
      (SubexpNodeScanControl.words encC encP cs x (encC c) []))
      (SubexpNodeScanControl.ports 3) _ = _
    rw [← SubexpNodeScanControl.work_update]
    apply congrArg (SubexpNodeScanControl.work base)
    funext i
    fin_cases i <;> simp [SubexpNodeScanControl.words]
  change ExecutesIn _ _ s (Function.update s 240
    (encP (localUpdate cm ca mulP linear theta minusOne J x.value c))) at h
  rw [he] at h
  exact h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact initialization and scan-state bridges for the native local CRT
controller. Only finite stack programs occur in these statements. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem initializedLocal_eq_ready {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool) (cs : List C) (one : P)
    (hcs : s 214 = cs.flatMap encC) (h218 : s 218 = []) (h219 : s 219 = []) :
    initializedLocal s (encP one) = SubexpNodeScanControl.ready s encC encP cs
      ⟨one, s 216, true⟩ [] [] := by
  funext i
  by_cases hi : ∃ j, SubexpNodeScanControl.ports j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j <;> simp [initializedLocal, SubexpNodeScanControl.ready,
      SubexpNodeScanControl.words, SubexpNodeScanControl.ports, SubexpNodeScanControl.marker,
      hcs, h218, h219]
  · have hout := SubexpNodeScanControl.work_frame s
      (SubexpNodeScanControl.words encC encP cs ⟨one, s 216, true⟩ [] []) i hi
    have hneq (j : Fin 6) : i ≠ SubexpNodeScanControl.ports j := by
      intro h; exact hi ⟨j, h.symm⟩
    have h215 : i ≠ (215 : Fin 256) := hneq 0
    have h217 : i ≠ (217 : Fin 256) := hneq 1
    have h229 : i ≠ (229 : Fin 256) := hneq 2
    have h240 : i ≠ (240 : Fin 256) := hneq 3
    simpa [initializedLocal, SubexpNodeScanControl.ready, Function.update_apply,
      h215, h217, h229, h240] using hout.symm

theorem scan_skip_length_le {C P : Type*} (f : P → C → P) (cs : List C)
    (x : SubexpNodeScanControl.Cursor P) :
    (SubexpNodeScanControl.run f cs x).skip.length ≤ x.skip.length := by
  induction cs generalizing x with
  | nil => exact le_rfl
  | cons c cs ih =>
    apply (ih (SubexpNodeScanControl.next f c x)).trans
    rcases x with ⟨value, skip, pending⟩
    cases skip <;> cases pending <;> simp [SubexpNodeScanControl.next]

theorem cleared_scan_eq_factor {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool) (x : SubexpNodeScanControl.Cursor P)
    (hclean : ∀ i ∈ ([215,217,218,219,229] : List (Fin 256)), s i = []) :
    SubexpLocalCRTSetup.cleared [217,229]
      (SubexpNodeScanControl.ready s encC encP [] x [] []) = Function.update s 240 (encP x.value) := by
  funext i
  by_cases hi : ∃ j, SubexpNodeScanControl.ports j = i
  · obtain ⟨j, rfl⟩ := hi
    fin_cases j <;> simp [SubexpLocalCRTSetup.cleared_apply, SubexpNodeScanControl.ready,
      SubexpNodeScanControl.words, SubexpNodeScanControl.ports, hclean 215 (by simp),
      hclean 217 (by simp), hclean 218 (by simp), hclean 219 (by simp), hclean 229 (by simp)]
  · have hout := SubexpNodeScanControl.work_frame s
      (SubexpNodeScanControl.words encC encP [] x [] []) i hi
    have hneq (j : Fin 6) : i ≠ SubexpNodeScanControl.ports j := by
      intro h; exact hi ⟨j, h.symm⟩
    have h217 : i ≠ (217 : Fin 256) := hneq 1
    have h229 : i ≠ (229 : Fin 256) := hneq 2
    have h240 : i ≠ (240 : Fin 256) := hneq 3
    simpa [SubexpLocalCRTSetup.cleared_apply, SubexpNodeScanControl.ready,
      Function.update_apply, h217, h229, h240] using hout

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition of the native local CRT scan, scalar inversion, and
polynomial correction. Service hypotheses refer to fixed finite commands;
they are instantiated by the concrete scalar and array service modules. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem executionPreparation_eq (sm sa : Code) :
    executionPreparation sm sa = prepareLocalInverse sm sa := rfl

theorem localClean_subset {s : Store} (hclean : ∀ i ∈ localWork, s i = [])
    (slots : List (Fin 256)) (hsub : slots ⊆ localWork) : ∀ i ∈ slots, s i = [] :=
  fun i hi => hclean i (hsub hi)

theorem positiveLocal_run {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (constant linear : C → P) (sm sa pm pa : Code)
    (cm ca : C → C → C) (mulP addP : P → P → P)
    (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
    (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
    (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hlinear : ∀ a, encP (linear a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
    (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
    (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
    (hpolyZero : s 192 = encP (constant zero))
    (hclean : ∀ i ∈ localWork, s i = [])
    (hhead : encP ((cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)
    let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (positiveLocal sm sa pm pa)
      (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V - 2)
      s (Function.update s 244 (encP (correctionValue mulP addP (constant zero) (constant one)
        (constant (cm inv minusOne)) (constant inv) factor jet J))) := by
  dsimp only
  let update := localUpdate cm ca mulP linear theta minusOne J
  let factor := (cs.eraseIdx (s 216).length).foldl update (constant one)
  let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
  let x := SubexpNodeScanControl.run update cs ⟨constant one, s 216, true⟩
  let start := SubexpNodeScanControl.ready s encC encP cs ⟨constant one, s 216, true⟩ [] []
  let scanned := SubexpNodeScanControl.ready s encC encP [] x [] []
  let prepared := preparedLocal s (encP factor) (encP (constant one))
    (encP (constant inv)) (encP (constant (cm inv minusOne))) (encP (constant zero))
  let value := correctionValue mulP addP (constant zero) (constant one)
    (constant (cm inv minusOne)) (constant inv) factor jet J
  let corrected := Function.update prepared 244 (encP value)
  have hx : x.value = factor := SubexpNodeScanControl.run_skip_index update cs (s 216) (constant one)
  have hinit : ExecutesIn initializeLocal
      (initializationBudget J W (cs.length * W) (s 216).length) s start := by
    have h := initializeLocal_run s J W hJ (by simp [hone, hcwidth])
      (hzero.trans hzeroBits) (localClean_subset hclean _ (by decide))
    have hlen : (s 214).length = cs.length * W := by
      rw [hcs, List.length_flatMap]
      simp [hcwidth]
    rw [hlen] at h
    have hb : DensePolynomialProgram.Constructor.Counter.paddedBits W (s 207) (s 104) J =
        encP (constant one) := by simp [hone, hzero, hconstant]
    rw [hb, initializedLocal_eq_ready s encC encP cs (constant one) hcs
      (hclean 218 (by simp [localWork])) (hclean 219 (by simp [localWork]))] at h
    exact h
  have hinclude := includeNode_spec s encC encP sm sa pm cm ca mulP Km Ka Kp W V J
    theta one minusOne linear hsm hsa hpm hcwidth hpwidth hlinear htheta hone hminus hJ
    (hzero.trans hzeroBits) (localClean_subset hclean _ (by decide))
  have hscan : ExecutesIn (scanCommand sm sa pm)
      (cs.length * (includeBudget Km Ka Kp W V J + 18 * W + 28) + 2) start scanned :=
    SubexpNodeScanControl.command_run (includeNodeCommand sm sa pm) s encC encP
      (fun _ => []) update (includeBudget Km Ka Kp W V J) W hinclude hcwidth hW
      (by intro c; simp) (by simp [hzero, hcwidth])
      (hclean 121 (by simp [localWork])) (hclean 122 (by simp [localWork])) cs
      ⟨constant one, s 216, true⟩
  have scanframe (i : Fin 256) (hi : ¬ ∃ j, SubexpNodeScanControl.ports j = i) :
      scanned i = s i := SubexpNodeScanControl.work_frame s _ i hi
  have hprep : ExecutesIn (prepareLocalInverse sm sa)
      (preparationBudget (s 209).length (s 212).length J Km Ka W V ((s 216).length + 1)) scanned prepared := by
    have h := prepareLocalInverse_run s encC encP constant sm sa cm ca Km Ka W V J
      ((s 216).length + 1) hsm hsa hcwidth hpwidth zero one minusOne c factor rest hconstant hhead
      scanned (scanReady_low s encC encP [] x [] [])
      (by simp [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words, hx])
      ((scanframe 104 (by decide)).trans hzero) hzeroBits
      ((scanframe 207 (by decide)).trans hone) ((scanframe 211 (by decide)).trans hminus)
      ((scanframe 243 (by decide)).trans hJ) ((scanframe 192 (by decide)).trans hpolyZero)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have hh := scan_skip_length_le update cs (⟨constant one, s 216, true⟩ : SubexpNodeScanControl.Cursor P)
          simpa [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words] using
            hh.trans (Nat.le_succ _)
        · cases hp : x.pending <;>
            simp [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words,
              SubexpNodeScanControl.marker, hp])
      (by
        intro i hi
        have hiport : ¬ ∃ j, SubexpNodeScanControl.ports j = i := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hsub : ([100,101,102,107,108,120,121,122,205,208,220,222,223,
          227,228,241,242,244,245,246,247] : List (Fin 256)) ⊆ localWork := by decide
        exact (scanframe i hiport).trans (hclean i (hsub hi)))
    have hclear : SubexpLocalCRTSetup.cleared [217,229] scanned =
        Function.update s 240 (encP factor) := by
      simpa only [scanned, hx] using cleared_scan_eq_factor s encC encP x
        (localClean_subset hclean _ (by decide))
    have h240 : Function.update s 240 [] = s := by
      apply Function.update_eq_self_iff.mpr
      exact (hclean 240 (by simp [localWork])).symm
    rw [← executionPreparation_eq]
    simpa only [scanframe 209 (by decide), scanframe 212 (by decide),
      hclear, prepared, inv, preparedLocal, Function.update_idem, h240] using h
  have hpreparedLow : LowFrame s prepared := by
    unfold prepared preparedLocal
    repeat' apply lowFrame_update _ _ (by decide) _
    exact lowFrame_refl s
  have hc : ExecutesIn (correctionCommand pm pa) (correctionBudget J Kp Kap V)
      prepared corrected := by
    have h := correctionCommand_run s encP pm pa mulP addP Kp Kap V hpm hpa hpwidth
      prepared (constant zero) (constant one) (constant (cm inv minusOne)) (constant inv)
      factor jet hpreparedLow
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal, hjet])
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
    simpa [corrected, value, prepared, preparedLocal, hJ] using h
  have hcleanup : ExecutesIn (SubexpLocalCRTSetup.clearMany [220,223,227,228,242])
      (5 * (2 * V + 3)) corrected (Function.update s 244 (encP value)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [220,223,227,228,242] corrected V (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simpa [corrected, prepared, preparedLocal] using hpwidth _)
    have he : SubexpLocalCRTSetup.cleared [220,223,227,228,242] corrected =
        Function.update s 244 (encP value) := by
      funext i
      by_cases hi : i ∈ ([220,223,227,228,242] : List (Fin 256))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;>
          simp [SubexpLocalCRTSetup.cleared_apply] <;>
          exact hclean _ (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        rcases hi with ⟨h220,h223,h227,h228,h242⟩
        by_cases h240 : i = 240
        · subst i
          simp [SubexpLocalCRTSetup.cleared_apply, corrected, prepared, preparedLocal] ;
            exact hclean _ (by decide)
        · simp [SubexpLocalCRTSetup.cleared_apply, corrected, prepared, preparedLocal,
            Function.update_apply, h220,h223,h227,h228,h242,h240]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (hinit.seq (hscan.seq (hprep.seq (hc.seq hcleanup)))).mono
  simp only [localBudget]
  omega

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem localCommand_run_oai {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (constant linear : C → P) (sm sa pm pa : Code)
    (cm ca : C → C → C) (mulP addP : P → P → P)
    (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
    (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
    (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hlinear : ∀ a, encP (linear a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
    (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
    (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
    (hpolyZero : s 192 = encP (constant zero))
    (hclean : ∀ i ∈ localWork, s i = [])
    (hhead : 0 < J → encP ((cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)
    let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    let out := if J = 0 then [] else encP (correctionValue mulP addP (constant zero) (constant one)
        (constant (cm inv minusOne)) (constant inv) factor jet J)
    ExecutesIn (localCommand sm sa pm pa)
      (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V)
      s (Function.update s 244 out) := by
  dsimp only
  have hbudget : 2 ≤ localBudget cs.length (s 216).length (s 209).length
      (s 212).length J Km Ka Kp Kap W V := by unfold localBudget; omega
  by_cases hJ0 : J = 0
  · have hskip : ExecutesIn (.base .skip) 0 s s := by
      intro regs
      exact ⟨0, regs, le_rfl, .base (.skip _)⟩
    have h := SubexpNodeScanControl.branch_false 243 15 (positiveLocal sm sa pm pa)
      (.base .skip) 0 s s (by simp [hJ, hJ0]) hskip
    have he : Function.update s 244 [] = s :=
      Function.update_eq_self_iff.mpr (hclean 244 (by simp [localWork])).symm
    change ExecutesIn (.seq (test 243 15)
      (.ite 15 (positiveLocal sm sa pm pa) (.base .skip))) _ _ _
    simpa [hJ0, he] using h.mono hbudget
  · have hpos : 0 < J := Nat.pos_of_ne_zero hJ0
    have hp := positiveLocal_run s encC encP constant linear sm sa pm pa cm ca mulP addP
      Km Ka Kp Kap W V J hW hsm hsa hpm hpa hcwidth hpwidth zero one minusOne theta c cs jet rest
      hconstant hlinear hzero hzeroBits hone hminus htheta hcs hJ hjet hpolyZero hclean (hhead hpos)
    have h := SubexpNodeScanControl.branch_true 243 15 (positiveLocal sm sa pm pa)
      (.base .skip) _ _ _ (by simp [hJ, hpos]) hp
    change ExecutesIn (.seq (test 243 15)
      (.ite 15 (positiveLocal sm sa pm pa) (.base .skip))) _ _ _
    simpa [hJ0, Nat.sub_add_cancel hbudget] using h

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.localCommand_run_oai.{u_1, u_2}
