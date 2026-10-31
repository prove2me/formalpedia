-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:28:55.506418+00:00
-- url     : https://prove2.me/submissions/46d8a732-5bbc-4940-830b-c372453cae60

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpDenseLiteralPadding_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem encode_eq_flatten_words {B d : ℕ} (P : List (Coeff B d)) :
    encode P = flatten (words P) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
      simp [encode, words, flatten, RingProgram.flat, List.map_ofFn, Function.comp_def,
        show (P.map RingProgram.flat).flatten = flatten (words P) from ih]

@[simp] theorem encode_length {B d : ℕ} (P : List (Coeff B d)) :
    (encode P).length = P.length * (d * B) := by
  rw [encode_eq_flatten_words, flatten_length, words_length, Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Small, extensional frame facts for the row interpreter. These proofs
split only its four control ports; they never enumerate the 256-stack frame. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram StructuredCalls
open SubexpPostfixGlobal (reindexCfg)
open SubexpPostfixInterpreter (cfg)

theorem physicalCfg_frame {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool)
    (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    (physicalCfg pc v p op code depth operands context).stacks i = contextStore context i := by
  obtain ⟨j, rfl⟩ := ports.surjective i
  revert h26 h28 h27
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k
    · intro h _ _; exact False.elim (h ports_zero)
    · intro _ h _; exact False.elim (h ports_one)
    · intro _ _ h; exact False.elim (h ports_two)
    · intro _ _ _
      simp [physicalCfg, contextStore, reindexCfg, cfg, Fin.addCases,
        SubexpPostfixControl.quadruple]
  · intro k _ _ _
    simp [physicalCfg, contextStore, reindexCfg, cfg]

private theorem local_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (cfg (r := 13) pc v p op code depth new context).stacks =
      Function.update (cfg (r := 13) pc v p op code depth old context).stacks
        (2 : Fin 256) new := by
  funext i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ i
  · intro j
    fin_cases j <;> rfl
  · intro j
    have hj : Fin.natAdd 4 j ≠ (2 : Fin 256) := by
      intro h
      have hv := congrArg Fin.val h
      change 4 + j.val = 2 at hv
      omega
    simp [cfg, hj]

theorem physicalCfg_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth new context).stacks =
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new := by
  funext i
  have hi : ports.symm i = (2 : Fin 256) ↔ i = 27 := by
    constructor
    · intro h
      have hh := congrArg ports h
      simpa only [Equiv.apply_symm_apply, ports_two] using hh
    · intro h
      subst i
      exact ports_symm_27
  change (cfg (r := 13) pc v p op code depth new context).stacks (ports.symm i) = _
  rw [local_update pc v p op code depth old new context]
  simp only [Function.update_apply, hi, physicalCfg, reindexCfg]

theorem physicalCfg_false_regs {l : ℕ} (pc : Option (Fin l))
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc false false false code depth operands context).regs = fun _ => false := by
  funext i
  refine Fin.addCases (m := 3) (n := 13) ?_ ?_ i
  · intro j; fin_cases j <;> rfl
  · intro j; simp [physicalCfg, reindexCfg, cfg]

/-- The framed service endpoint is exactly the interpreter's next boundary. -/
theorem physicalCfg_after {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    ((⟨fun _ => false,
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new⟩ :
      State 16 256).withPC (l := l) none) =
      physicalCfg (l := l) none false false false code depth new context := by
  have hs := physicalCfg_update pc v p op code depth old new context
  have hregs := physicalCfg_false_regs (l := l) none code depth new context
  apply congrArg₂ (Cfg.mk none)
  · exact hregs.symm
  · exact hs.symm

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stored arithmetic data for the row interpreter. Readiness is stated on
the fixed context alone, and proved invariant when source, operand, and
temporary argument ports change. No arithmetic trace is assumed here. -/

namespace SubexponentialSAT.SubexpRowPostfixContext

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Store bufferPorts)
open SubexpRowPostfixInterpreter (physicalCfg contextStore)

theorem operandStore_frame (context : Fin 252 → List Bool)
    (code depth operands : List Bool) (i : Fin 256)
    (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    operandStore context code depth operands i = contextStore context i :=
  SubexpRowPostfixInterpreter.physicalCfg_frame _ _ _ _ _ _ _ _ _ h26 h28 h27

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePaddingSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-width bit padding and dense polynomial coefficients

The literal loader pads or truncates a flat payload to a whole number of
coefficient cells. This file identifies that operation at the cell level.
Preservation of a complete polynomial requires its degree to be below the
number of retained cells; this condition is explicit before any Taylor shift.
-/

namespace SubexponentialSAT.SubexpDensePaddingSpec

open ModularArithmetic

private theorem padTo_prefix (shape front rest input : List Bool)
    (hlen : shape.length = front.length) :
    padTo (shape ++ rest) (front ++ input) = front ++ padTo rest input := by
  induction shape generalizing front with
  | nil =>
      have hp : front = [] := List.length_eq_zero_iff.mp hlen.symm
      simp [hp]
  | cons bit shape ih =>
      cases front with
      | nil => simp at hlen
      | cons head tail =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simpa only [List.cons_append, padTo] using congrArg (List.cons head) (ih tail hlen)

private theorem padTo_empty (shape : List Bool) :
    padTo shape [] = List.replicate shape.length false := by
  induction shape with
  | nil => rfl
  | cons bit rest ih => simp [padTo, ih, List.replicate_succ]

/-- The actual bit-loader operation agrees with truncation/padding of whole
coefficient cells, including zero-width and empty-input cases. -/
theorem padTo_flatten (cellCount width : ℕ) (words : List (List Bool))
    (hwidth : ∀ word ∈ words, word.length = width) :
    padTo (List.replicate (cellCount * width) false) words.flatten =
      (padCells (List.replicate width false) cellCount words).flatten := by
  induction cellCount generalizing words with
  | zero => simp [padCells, padTo]
  | succ n ih =>
      cases words with
      | nil =>
          simp only [List.flatten_nil, padTo_empty, List.length_replicate,
            padCells_nil, List.flatten_replicate_replicate]
      | cons word words =>
          have hw : word.length = width := hwidth word (by simp)
          rw [show (n + 1) * width = width + n * width by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], List.replicate_add,
            List.flatten_cons, padTo_prefix _ word _ _ (by simpa using hw.symm)]
          simpa only [padCells, List.flatten_cons] using
            congrArg (fun xs => word ++ xs)
              (ih words (fun x hx => hwidth x (by simp [hx])))

/-- Specialization to an arbitrary fixed-width coefficient encoding. -/
theorem padTo_encoded {C : Type*} (encode : C → List Bool) (zero : C)
    (cellCount width : ℕ) (xs : List C)
    (hzero : encode zero = List.replicate width false)
    (hwidth : ∀ x ∈ xs, (encode x).length = width) :
    padTo (List.replicate (cellCount * width) false) (xs.map encode).flatten =
      ((padCells zero cellCount xs).map encode).flatten := by
  rw [padTo_flatten cellCount width (xs.map encode) (by
    intro word hw
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
    exact hwidth x hx)]
  have hmap (n : ℕ) (ys : List C) :
      padCells (List.replicate width false) n (ys.map encode) =
        (padCells zero n ys).map encode := by
    induction n generalizing ys with
    | zero => rfl
    | succ n ih => cases ys <;> simp [padCells, hzero, ih, List.replicate_succ]
  exact congrArg List.flatten (hmap cellCount xs)

end SubexponentialSAT.SubexpDensePaddingSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native literal loading and padding for coefficient-array postfix source. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

theorem update_run {l : ℕ} (service : Program 16 256 l) (K : ℕ)
    (v p op : Bool) (code depth old new : List Bool) (context : Fin 252 → List Bool)
    (h : RunsIn service K
      ((⟨(physicalCfg (some service.entry) v p op code depth old context).regs,
        operandStore context code depth old⟩ : State 16 256).withPC (some service.entry))
      ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
        State 16 256).withPC none)) :
    RunsIn service K (physicalCfg (some service.entry) v p op code depth old context)
      (physicalCfg none false false false code depth new context) := by
  have he : ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
      State 16 256).withPC none) = physicalCfg none false false false code depth new context :=
    SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_after (some service.entry) v p op
      code depth old new context
  rw [he] at h
  exact h

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem load_implements_oai
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false) :
    LoadImplementsGlobal DensePolynomialProgram.encode (loadValue ops J)
      SubexpDenseLiteralPadding.program (loadBound (baseWidth p t) d J) context := by
  intro P xs code depth op
  let operands := Encoding.encodeList DensePolynomialProgram.encode (P :: xs)
  let tail := Encoding.encodeList DensePolynomialProgram.encode xs
  let s := operandStore context code depth operands
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    operandStore_frame context code depth operands i h26 h28 h27
  have hshape : s 242 = List.replicate (J*(d*baseWidth p t)) false := by
    rw [hs 242 (by decide) (by decide) (by decide),H.loaderShape]
    simp [DensePolynomialProgram.encode,hzero,List.flatten_replicate_replicate]
  have hpad : ModularArithmetic.padTo (s 242) (DensePolynomialProgram.encode P) =
      DensePolynomialProgram.encode (loadValue ops J P) := by
    rw [hshape]
    exact SubexpDensePaddingSpec.padTo_encoded RingProgram.flat ops.zeroRun.1 J
      (d*baseWidth p t) P hzero (fun x _ => RingProgram.flat_length x)
  apply update_run _ _ true false op code depth operands
    (Encoding.encodeList DensePolynomialProgram.encode (loadValue ops J P :: xs)) context
  have h := SubexpDenseLiteralPadding.program_runsIn s
    (physicalCfg (some SubexpDenseLiteralPadding.program.entry) true false op code depth operands context).regs
    (DensePolynomialProgram.encode P) tail rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 99 (by decide) (by decide) (by decide)]; exact H.empty99)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.arithmetic.scratch)
  rw [hpad] at h
  change RunsIn SubexpDenseLiteralPadding.program
    (12 * (DensePolynomialProgram.encode P).length + 16 * (s 242).length + 46) _ _ at h
  rw [hshape] at h
  simpa [hshape, loadBound, s, operands, tail, Encoding.encodeList] using h


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements_oai
