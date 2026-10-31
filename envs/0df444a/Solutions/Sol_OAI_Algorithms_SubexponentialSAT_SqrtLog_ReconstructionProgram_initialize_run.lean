-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:28.690116+00:00
-- url     : https://prove2.me/submissions/a78a93ac-60d2-4e70-a0c7-e7b0a6823130

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115
import Definitions.Def_OAIQ081S127

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

open BitProgram StructuredCalls StackRoutines

theorem lengthRegisters_injective : Function.Injective lengthRegisters := by
  intro a b h
  have hh := congrArg (fun j : Fin 8 => j.val) h
  exact Fin.ext hh

theorem lengthPorts_injective : Function.Injective lengthPorts := by decide

private theorem length_embed_input (d : Data) (h2 : d.stacks 2 = [])
    (h5 : d.stacks 5 = []) (hz : d.regs 2 = false) :
    embedState lengthRegisters lengthPorts d (lengthInput d) = d := by
  apply embedState_eq_of_ports _ _ _ _ _ lengthRegisters_injective lengthPorts_injective
  · intro i
    fin_cases i <;> simp [lengthInput, lengthRegisters, CounterPrograms.counterRegs, hz]
  · intro i hi; rfl
  · intro i
    fin_cases i <;> simp [lengthInput, lengthPorts, CounterPrograms.lengthStacks, h2, h5]
  · intro i hi; rfl

private theorem length_embed_output (d : Data) (h5 : d.stacks 5 = [])
    (exponent : List Bool) :
    embedState lengthRegisters lengthPorts d (lengthOutput exponent) =
      afterLength d exponent := by
  apply embedState_eq_of_ports _ _ _ _ _ lengthRegisters_injective lengthPorts_injective
  · intro i
    fin_cases i <;> simp [afterLength, lengthOutput, lengthRegisters]
  · intro j hj
    have hlarge : ¬ j.val < 3 := by
      intro hsmall
      apply hj
      exact ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩
    simp [afterLength, hlarge]
  · intro i
    fin_cases i <;> simp [lengthOutput, afterLength, lengthPorts, h5]
  · intro j hj
    have h4 : j ≠ 4 := fun h => hj ⟨0, by simpa [lengthPorts] using h.symm⟩
    have h2 : j ≠ 2 := fun h => hj ⟨1, by simpa [lengthPorts] using h.symm⟩
    simp [afterLength, h4, h2]

/-- The copied unary input is consumed, with the binary count in port 2. -/
theorem length_eval (d : Data) (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = [])
    (hz : d.regs 2 = false) :
    ∃ t ≤ (d.stacks 4).length * (8 * (d.stacks 4).length + 10) + 3,
      ∃ exponent : List Bool,
        Eval (.call lengthProgram) t d (afterLength d exponent) ∧
        BinaryArithmetic.toNat exponent = (d.stacks 4).length ∧
        exponent.length ≤ (d.stacks 4).length := by
  obtain ⟨exponent, hv, hl, t, ht, trace⟩ :=
    CounterPrograms.length_correct_from (d.regs 0) (d.regs 1) (d.stacks 4)
  change Trace CounterPrograms.lengthProgram t
    ((lengthInput d).withPC (some CounterPrograms.lengthProgram.entry))
    ((lengthOutput exponent).withPC none) at trace
  have run := eval_call_lifted CounterPrograms.lengthProgram lengthRegisters lengthPorts d
    lengthRegisters_injective lengthPorts_injective trace
  rw [length_embed_input d h2 h5 hz, length_embed_output d h5 exponent] at run
  exact ⟨t, ht, exponent, run, (CounterPrograms.value_eq_toNat exponent).symm.trans hv, hl⟩

/-- A reusable preserving unary-to-binary counter, with only three initially
empty assigned work/output stacks. All other caller stacks are arbitrary. -/
theorem count_eval (d : Data)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ t ≤ countBudget (d.stacks 1).length,
      ∃ (rf : Fin 8 → Bool) (exponent : List Bool),
        Eval countCommand t d ⟨rf, Function.update d.stacks 2 exponent⟩ ∧
        BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
        exponent.length ≤ (d.stacks 1).length := by
  let copied := ArithmeticCalls.afterCopy 1 4 d
  let ready : Data := ⟨Function.update copied.regs 2 false, copied.stacks⟩
  have hc : Eval (ArithmeticCalls.copyAt 1 4 5) (7 * (d.stacks 1).length + 5) d copied :=
    ArithmeticCalls.copyAt_eval 1 4 5 d (by decide) (by decide) (by decide) h4 h5
  have hr : Eval resetAccumulator 1 copied ready := .base (.atom _ _)
  have hready2 : ready.stacks 2 = [] := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using h2
  have hready5 : ready.stacks 5 = [] := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using h5
  obtain ⟨tl, htl, exponent, hl, he, hel⟩ :=
    length_eval ready hready2 hready5 (by simp [ready])
  let counted := afterLength ready exponent
  have hcounted : counted.stacks = Function.update d.stacks 2 exponent := by
    funext j
    by_cases h2 : j = 2
    · subst j; simp [counted, afterLength]
    · by_cases h4 : j = 4
      · subst j
        simp_all [counted, afterLength]
      · simp [counted, afterLength, ready, copied, ArithmeticCalls.afterCopy, h2, h4]
  have hexponent : BinaryArithmetic.toNat exponent = (d.stacks 1).length := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using he
  have hexponentLength : exponent.length ≤ (d.stacks 1).length := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using hel
  have hlengthBound : tl ≤ (d.stacks 1).length * (8 * (d.stacks 1).length + 10) + 3 := by
    simpa [ready, copied, ArithmeticCalls.afterCopy] using htl
  have hstate : counted = ⟨counted.regs, Function.update d.stacks 2 exponent⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hcounted
  refine ⟨(7 * (d.stacks 1).length + 5) + (1 + tl), ?_,
    counted.regs, exponent, ?_, hexponent, hexponentLength⟩
  · unfold countBudget
    omega
  · have run := hc.seq (hr.seq hl)
    change Eval countCommand _ d counted at run
    rwa [hstate] at run

theorem count_program_runsIn (d : Data)
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ (rf : Fin 8 → Bool) (exponent : List Bool),
      RunsIn countProgram (countBudget (d.stacks 1).length + 1)
        (d.withPC (some countProgram.entry))
        ((⟨rf, Function.update d.stacks 2 exponent⟩ : Data).withPC none) ∧
      BinaryArithmetic.toNat exponent = (d.stacks 1).length ∧
      exponent.length ≤ (d.stacks 1).length := by
  obtain ⟨t, ht, rf, exponent, heval, he, hel⟩ := count_eval d h2 h4 h5
  exact ⟨rf, exponent, ⟨t + 1, Nat.add_le_add_right ht 1,
    compiled_halt_trace heval 1 2⟩, he, hel⟩

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem copy_run (d : Data) (src dst : Fin 320)
    (hsd : src ≠ dst) (hs : src ≠ 318) (hd : (318 : Fin 320) ≠ dst)
    (ht : d.stacks 318 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 318 0 1 hsd hs hd (by decide) ht

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual initialization for the outer CRT tape controller. Widths and the
binary dimension are computed by fixed programs from the retained runtime
inputs. In particular, neither a binary exponent nor a jet-width word is
provided for free. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem countDimension_run (d : Data)
    (ho : d.stacks 268 = []) (hc : d.stacks 316 = []) (ht : d.stacks 317 = []) :
    ∃ n ≤ SubexpFactorCountSetup.countBudget (d.stacks 243).length + 1,
      ∃ (rf : Fin 16 → Bool) (exponent : List Bool),
        Eval countDimension n d ⟨rf, Function.update d.stacks 268 exponent⟩ ∧
        BinaryArithmetic.toNat exponent = (d.stacks 243).length ∧
        exponent.length ≤ (d.stacks 243).length := by
  let localIn := projectState registers countPorts d
  obtain ⟨rf, exponent, ⟨n, hn, htrace⟩, he, hl⟩ :=
    SubexpFactorCountSetup.count_program_runsIn localIn ho hc ht
  let localOut : State 8 13 := ⟨rf, Function.update localIn.stacks 2 exponent⟩
  have hrun := eval_call_from_state SubexpFactorCountSetup.countProgram registers countPorts d
    registers.injective countPorts.injective (b := localOut) htrace
  have hagree : Function.extend countPorts localIn.stacks d.stacks = d.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers countPorts d registers.injective countPorts.injective)
  have hfinal : embedState registers countPorts d localOut =
      (⟨Function.extend registers rf d.regs, Function.update d.stacks 268 exponent⟩ : Data) := by
    apply state_ext
    · rfl
    · change Function.extend countPorts (Function.update localIn.stacks 2 exponent) d.stacks = _
      rw [ProgramLinking.extend_update countPorts.injective, hagree]
      rfl
  refine ⟨n, hn, Function.extend registers rf d.regs, exponent, ?_, he, hl⟩
  simpa only [countDimension, hfinal] using hrun

theorem resetThree_run (d : Data) : Eval resetThreeRegisters 3 d (threeReset d) := by
  have h0 := StructuredProgram.Eval.atom (.set (0 : Fin 16) false) d
  have h1 := StructuredProgram.Eval.atom (.set (1 : Fin 16) false)
    ((StructuredProgram.Atom.set 0 false).eval d)
  have h2 := StructuredProgram.Eval.atom (.set (2 : Fin 16) false)
    ((StructuredProgram.Atom.set 1 false).eval ((StructuredProgram.Atom.set 0 false).eval d))
  have h := Eval.base (h0.seq (h1.seq h2))
  simpa [resetThreeRegisters, threeReset, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem blockCopy_run (d : Data) (D : ℕ)
    (hr : ∀ i : Fin 3, d.regs (threeRegisters i) = false)
    (hc : d.stacks 279 = List.replicate D true) (ht : d.stacks 278 = []) :
    Eval (.call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
      threeRegisters blockCopyPorts))
      (D * (7 * (d.stacks 104).length + 7) + 3) d
      ⟨d.regs, Function.update (Function.update d.stacks 277
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 279 []⟩ := by
  let localIn := Subexp.BlockCopyProgram.initialState D (d.stacks 104) (d.stacks 277)
  let localOut := Subexp.BlockCopyProgram.data false false (d.stacks 104)
    (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277) []
  have hin : projectState threeRegisters blockCopyPorts d = localIn := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [projectState, localIn, Subexp.BlockCopyProgram.initialState,
        Subexp.BlockCopyProgram.data, hr]
    · funext i
      fin_cases i <;> simp [projectState, blockCopyPorts, localIn,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data, hc, ht]
  have htrace := Subexp.BlockCopyProgram.program_trace D (d.stacks 104) (d.stacks 277)
  have hrun := eval_call_from_state Subexp.BlockCopyProgram.program
    threeRegisters blockCopyPorts d threeRegisters.injective blockCopyPorts.injective
    (b := localOut) (by simpa only [hin] using htrace)
  have hlocalOut : localOut =
      {localIn with «stacks» := Function.update (Function.update localIn.stacks 1
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 3 []} := by
    apply state_ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [localOut, localIn, Subexp.BlockCopyProgram.data,
        Subexp.BlockCopyProgram.initialState]
  have hagree := embedState_project threeRegisters blockCopyPorts d
    threeRegisters.injective blockCopyPorts.injective
  rw [hin] at hagree
  have hfinal : embedState threeRegisters blockCopyPorts d localOut =
      (⟨d.regs, Function.update (Function.update d.stacks 277
        (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)) 279 []⟩ : Data) := by
    apply state_ext
    · change Function.extend threeRegisters localOut.regs d.regs = d.regs
      change Function.extend threeRegisters localIn.regs d.regs = d.regs
      exact congrArg StructuredProgram.State.regs hagree
    · have hstack := congrArg StructuredProgram.State.stacks hlocalOut
      have hsame := congrArg StructuredProgram.State.stacks hagree
      change Function.extend blockCopyPorts localIn.stacks d.stacks = d.stacks at hsame
      change Function.extend blockCopyPorts localOut.stacks d.stacks = _
      rw [hstack, ProgramLinking.extend_update blockCopyPorts.injective,
        ProgramLinking.extend_update blockCopyPorts.injective, hsame]
      rfl
  simpa only [hfinal] using hrun

theorem buildJetWidth_run (d : Data) (D : ℕ)
    (hd : d.stacks 243 = List.replicate D true)
    (ht : d.stacks 278 = []) (hc : d.stacks 279 = []) (hu : d.stacks 318 = []) :
    Eval buildJetWidth (D * (7 * (d.stacks 104).length + 14) + 11)
      d (jetWidthState d D) := by
  have hcopy := copy_run d 243 279 (by decide) (by decide) (by decide) hu
  let copied := afterCopy d 243 279 0 1
  let ready := threeReset copied
  have hreset := resetThree_run copied
  have hregs : ∀ i : Fin 3, ready.regs (threeRegisters i) = false := by
    intro i
    fin_cases i <;> simp [ready, threeRegisters]
  have hcounter : ready.stacks 279 = List.replicate D true := by
    simp [ready, copied, afterCopy, StackRoutines.copyStacks, hd, hc]
  have htmp : ready.stacks 278 = [] := by
    simpa [ready, copied, threeReset, afterCopy, StackRoutines.copyStacks] using ht
  have hrun := blockCopy_run ready D hregs hcounter htmp
  have hfinal : (⟨ready.regs, Function.update (Function.update ready.stacks 277
      (Subexp.BlockCopyProgram.copies D (ready.stacks 104) ++ ready.stacks 277)) 279 []⟩ : Data) =
      jetWidthState d D := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 279
      · subst i; simp [ hc]
      · by_cases hj : i = 277
        · subst i
          simp [ ready, copied, afterCopy,
            StackRoutines.copyStacks]
        · simp [ ready, copied, afterCopy,
            StackRoutines.copyStacks, hi, hj]
  rw [hfinal] at hrun
  have h := hcopy.seq (hreset.seq hrun)
  have h104 : ready.stacks 104 = d.stacks 104 := by
    simp [ready, copied, afterCopy, StackRoutines.copyStacks]
  convert h using 1
  · rfl
  · rw [h104, hd]
    simp only [List.length_replicate]
    ring

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arbitrary-width physical CRT initialization. The computed ring-zero word
is passed on stack 280; all copying, width construction and unary-to-binary
conversion are charged by actual primitive traces. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

theorem initialize_run_oai (d : Data) (D : ℕ)
    (hd : d.stacks 243 = List.replicate D true)
    (hclean : ∀ j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] : List (Fin 320)),
      d.stacks j = []) :
    ∃ n ≤ initializationBudget (d.stacks 280).length D
        (d.stacks 256).length (d.stacks 265).length,
      ∃ (rf : Fin 16 → Bool) (exponent : List Bool),
        Eval initializeCode n d ⟨rf, initializedStacks d D exponent⟩ ∧
        BinaryArithmetic.toNat exponent = D ∧ exponent.length ≤ D := by
  have hz (j : Fin 320) (h : j ∈ ([104,261,268,277,278,279,316,317,318,214,257,266] :
      List (Fin 320))) : d.stacks j = [] := hclean j h
  have h1 := copy_run d 280 104 (by decide) (by decide) (by decide) (hz 318 (by simp))
  let d1 := afterCopy d 280 104 0 1
  have h2 := copy_run d1 280 261 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d2 := afterCopy d1 280 261 0 1
  obtain ⟨nc, hnc, rc, exponent, hc, he, hl⟩ := countDimension_run d2
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 268 (by simp))
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 316 (by simp))
    (by simpa [d2, d1, afterCopy, StackRoutines.copyStacks] using hz 317 (by simp))
  let d3 : Data := ⟨rc, Function.update d2.stacks 268 exponent⟩
  have h3 := buildJetWidth_run d3 D
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hd)
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 278 (by simp))
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 279 (by simp))
    (by simpa [d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d4 := jetWidthState d3 D
  have h4 := copy_run d4 256 214 (by decide) (by decide) (by decide)
    (by simpa [d4, jetWidthState, d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d5 := afterCopy d4 256 214 0 1
  have h5 := copy_run d5 256 257 (by decide) (by decide) (by decide)
    (by simpa [d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  let d6 := afterCopy d5 256 257 0 1
  have h6 := copy_run d6 265 266 (by decide) (by decide) (by decide)
    (by simpa [d6, d5, afterCopy, StackRoutines.copyStacks, d4, jetWidthState,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks] using hz 318 (by simp))
  have hfinal : (afterCopy d6 265 266 0 1).stacks = initializedStacks d D exponent := by
    simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
      d3, d2, d1, afterCopy, StackRoutines.copyStacks, initializedStacks,
      hz 104 (by simp), hz 261 (by simp), hz 214 (by simp), hz 257 (by simp), hz 266 (by simp), hz 277 (by simp)]
  have hexp : BinaryArithmetic.toNat exponent = D := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using he
  have hlength : exponent.length ≤ D := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using hl
  have hcBound : nc ≤ SubexpFactorCountSetup.countBudget D + 1 := by
    simpa [d2, d1, afterCopy, StackRoutines.copyStacks, hd] using hnc
  have hassoc {a b c : Code} {n : ℕ} {s t : Data}
      (h : Eval (.seq (.seq a b) c) n s t) : Eval (.seq a (.seq b c)) n s t := by
    cases h with
    | seq hab hc =>
      cases hab with
      | seq ha hb => simpa only [Nat.add_assoc] using ha.seq (hb.seq hc)
  have hrun' := h1.seq (h2.seq (hc.seq (h3.seq (h4.seq (h5.seq h6)))))
  have hresult : afterCopy d6 265 266 0 1 =
      (⟨(afterCopy d6 265 266 0 1).regs, initializedStacks d D exponent⟩ : Data) :=
    state_ext rfl hfinal
  change Eval initializeCode _ d _ at hrun'
  rw [hresult] at hrun'
  refine ⟨_, ?_, _, exponent, hrun', hexp, hlength⟩
  simp [d6, d5, afterCopy, StackRoutines.copyStacks, d4,
    d3, d2, d1, afterCopy, StackRoutines.copyStacks, initializationBudget, hz 104 (by simp)]
  nlinarith

end SubexponentialSAT.SqrtLog.ReconstructionProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run_oai
