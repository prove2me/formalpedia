-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:31:43.752733+00:00
-- url     : https://prove2.me/submissions/75c1c509-2966-411b-9819-63e384afea23

import Mathlib
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CRTLocalProgram_inverseConstantsCommand_run

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

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem blockRegisters_injective : Function.Injective blockRegisters :=
  by
    intro a b h
    apply Fin.ext
    exact congrArg (fun x : Fin 16 => x.val) h

theorem blockStacks_injective : Function.Injective blockStacks := by decide

theorem repeatCell_eval (d : Data) (D : ℕ) (cell output : List Bool)
    (h0 : d.regs 0 = false) (h1 : d.regs 1 = false) (h2 : d.regs 2 = false)
    (hc : d.stacks 104 = cell) (ho : d.stacks 102 = output)
    (ht : d.stacks 107 = []) (hn : d.stacks 108 = List.replicate D true) :
    Eval repeatCell (D * (7 * cell.length + 7) + 3) d (repeatOut d D cell output) := by
  have hi : embedState blockRegisters blockStacks d
      (Subexp.BlockCopyProgram.initialState D cell output) = d := by
    apply embedState_eq _ _ blockRegisters_injective blockStacks_injective
    · intro i
      fin_cases i <;>
        simp [blockRegisters, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data, h0, h1, h2]
    · intro i
      fin_cases i <;>
        simp [blockStacks, Subexp.BlockCopyProgram.initialState,
          Subexp.BlockCopyProgram.data, hc, ho, ht, hn]
    · intros; rfl
    · intros; rfl
  have hf : embedState blockRegisters blockStacks d
      (Subexp.BlockCopyProgram.data false false cell
        (Subexp.BlockCopyProgram.copies D cell ++ output) []) =
          repeatOut d D cell output := by
    apply embedState_eq _ _ blockRegisters_injective blockStacks_injective
    · intro i
      fin_cases i <;> simp [blockRegisters, repeatOut, Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [blockStacks, repeatOut, Subexp.BlockCopyProgram.data, hc, ht]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [blockRegisters] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [blockRegisters] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, by simpa [blockRegisters] using h.symm⟩
      simp [repeatOut, h0, h1, h2]
    · intro i hi
      have h102 : i ≠ 102 := fun h => hi ⟨1, by simpa [blockStacks] using h.symm⟩
      have h108 : i ≠ 108 := fun h => hi ⟨3, by simpa [blockStacks] using h.symm⟩
      simp [repeatOut, h102, h108]
  have h := eval_call_lifted Subexp.BlockCopyProgram.program blockRegisters blockStacks d
    blockRegisters_injective blockStacks_injective
    (Subexp.BlockCopyProgram.program_trace D cell output)
  simpa only [hi, hf] using h

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime construction of a padded linear polynomial. The low and high
coefficient cells occupy stacks 100 and 101. The unary dimension is on 109,
the base-word width is on 10, and the output array is on 102. -/

namespace SubexponentialSAT.SubexpLinearFactorProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem resetRegisters_eval (d : Data) :
    Eval resetRegisters 3 d (registersReset d) := by
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set 0 false) d)
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set 1 false)
    ((StructuredProgram.Atom.set 0 false).eval d))
  have h₃ := Eval.base (StructuredProgram.Eval.atom (.set 2 false)
    ((StructuredProgram.Atom.set 1 false).eval ((StructuredProgram.Atom.set 0 false).eval d)))
  exact h₁.seq (h₂.seq h₃)

theorem popDimension_eval (d : Data) :
    Eval popDimension 1 d (dimensionPopped d) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop 108 0 1) d)
  exact h

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

theorem move_run (s : Store) (src dst : Fin 256)
    (hs : src ≠ 245) (hd : dst ≠ 245) (hsd : src ≠ dst)
    (htmp : s 245 = []) (hout : s dst = []) :
    ExecutesIn (move src dst) (6 * (s src).length + 6) s
      (Function.update (Function.update s src []) dst (s src)) := by
  let middle := Function.update (Function.update s src []) 245 (s src).reverse
  have h₁ : ExecutesIn (transfer src 245) (3 * (s src).length + 3) s middle := by
    simpa [middle, htmp] using transfer_run src 245 s hs
  have he : Function.update (Function.update middle 245 []) dst
      ((middle 245).reverse ++ middle dst) =
      Function.update (Function.update s src []) dst (s src) := by
    funext j
    by_cases hj : j = 245 <;>
      simp [middle, Function.update_apply, hd, Ne.symm hs, Ne.symm hd, Ne.symm hsd, htmp, hout, hj]
  have h₂ : ExecutesIn (transfer 245 dst) (3 * (s src).length + 3) middle
      (Function.update (Function.update s src []) dst (s src)) := by
    have h := transfer_run 245 dst middle (Ne.symm hd)
    rw [he] at h
    simpa [middle] using h
  have h := h₁.seq h₂
  have hcost : (3 * (s src).length + 3) + (3 * (s src).length + 3) =
      6 * (s src).length + 6 := by omega
  simpa only [move, hcost] using h

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem constantCommand_run (s : Store) (constant rest : List Bool)
    (harray : s 223 = constant ++ rest)
    (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h247 : s 247 = []) (h205 : s 205 = []) :
    ExecutesIn constantCommand (21*constant.length+9*rest.length+19) s
      (Function.update s 205 constant) := by
  let s1 := Function.update s 247 (constant ++ rest)
  let s2 := Function.update (Function.update s 247 rest) 205 constant
  have h1 : ExecutesIn (copy 223 247) (7*(constant.length+rest.length)+5) s s1 := by
    simpa [s1, harray, h247] using copy_run 223 247 s
      (by decide) (by decide) (by decide) h120
  have h2 : ExecutesIn (takeCell 247 205) (14*constant.length+11) s1 s2 := by
    simpa [s1, s2, h205] using takeCell_run 247 205 s1 constant rest
      (by decide) (by simp [s1]) (by simp [s1, h121]) (by simp [s1, h122])
      (by simpa [s1] using hwidth)
  have he : Function.update s2 247 [] = Function.update s 205 constant := by
    funext i
    by_cases hi : i = 247 <;> simp [s2, Function.update_apply, hi, h247]
  have h3 : ExecutesIn (clear 247) (2*rest.length+3) s2 (Function.update s 205 constant) := by
    have h := clear_run 247 s2
    rw [he] at h
    simpa [s2] using h
  convert h1.seq (h2.seq h3) using 1
  · rfl
  · ring

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
namespace Counter
open SubexponentialSAT.SubexpLinearFactorProgram
private theorem copies_zero (n W : ℕ) :
    SubexponentialSAT.Subexp.BlockCopyProgram.copies n (List.replicate W false) =
      List.replicate (n * W) false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [SubexponentialSAT.Subexp.BlockCopyProgram.copies_succ, ih, ← List.replicate_add]
      congr 1
      ring

theorem fromCounter_eval (d : Data) (D W : ℕ) (low high : List Bool)
    (hlow : d.stacks 100 = low) (hhigh : d.stacks 101 = high)
    (hlength : low.length = W) (hhlength : high.length = W)
    (hcount : d.stacks 108 = List.replicate D true)
    (hcell : d.stacks 104 = List.replicate W false)
    (hout : d.stacks 102 = []) (htmp : d.stacks 107 = []) :
    ∃ n ≤ 100 * (D + 1) * (W + 1), ∃ regs,
      Eval fromCounter n d (counterResult d D W low high regs) := by
  cases D with
  | zero =>
      have hp := popDimension_eval d
      have ht : (dimensionPopped d).regs 1 = false := by
        simp [ hcount, readRegs]
      have hh := hp.seq (Eval.ite_false (yes := .seq popDimension (.ite 1 longCase copyLow))
        ht (Eval.base (StructuredProgram.Eval.skip (dimensionPopped d))))
      have he : dimensionPopped d = counterResult d 0 W low high (dimensionPopped d).regs := by
        refine state_ext rfl ?_
        funext i
        by_cases hi : i = 102
        · subst i; simp [ counterResult, paddedBits, hout]
        · simp [ counterResult, paddedBits, hi, hcount]
      have hc : Eval fromCounter 2 d (dimensionPopped d) := by
        simpa only [fromCounter] using hh
      rw [he] at hc
      exact ⟨2, by omega, _, hc⟩
  | succ D =>
      cases D with
      | zero =>
          let d₁ := dimensionPopped d
          let d₂ := dimensionPopped d₁
          have hp₁ := popDimension_eval d
          have hp₂ := popDimension_eval d₁
          have ht₁ : d₁.regs 1 = true := by simp [d₁, hcount, readRegs]
          have ht₂ : d₂.regs 1 = false := by simp [d₂, d₁, hcount, readRegs]
          have hc := copy_eval d₂ 100 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [d₂, d₁, htmp])
          let last := afterCopy d₂ 100 102 0 1
          have hh := hp₁.seq (Eval.ite_true (no := .base .skip) ht₁
            (hp₂.seq (Eval.ite_false (yes := longCase) ht₂ hc)))
          have he : last = counterResult d 1 W low high last.regs := by
            refine state_ext rfl ?_
            funext i
            by_cases hi : i = 102
            · subst i
              simp [last, d₂, d₁, afterCopy, StackRoutines.copyStacks,
                counterResult, paddedBits, hlow, hout]
            · simp [last, d₂, d₁, afterCopy, StackRoutines.copyStacks,
                counterResult, paddedBits, hi, hcount]
          refine ⟨7 * low.length + 9, ?_, last.regs, ?_⟩
          · rw [hlength]
            omega
          · have hc' : Eval fromCounter (7 * low.length + 9) d last := by
              convert hh using 1
              all_goals try with_reducible_and_instances rfl
              all_goals first
                | rfl
                | (simp [d₂, d₁, hlow, hlength]; omega)
            rw [he] at hc'
            exact hc'
      | succ n =>
          let d₁ := dimensionPopped d
          let d₂ := dimensionPopped d₁
          let dr := registersReset d₂
          let dz := SubexpJetInitProgram.repeatOut dr n (List.replicate W false) []
          let dh := afterCopy dz 101 102 0 1
          let dl := afterCopy dh 100 102 0 1
          have hp₁ := popDimension_eval d
          have hp₂ := popDimension_eval d₁
          have ht₁ : d₁.regs 1 = true := by simp [d₁, hcount, readRegs]
          have ht₂ : d₂.regs 1 = true := by simp [d₂, d₁, hcount, readRegs]
          have hr := resetRegisters_eval d₂
          have hz := SubexpJetInitProgram.repeatCell_eval dr n (List.replicate W false) []
            (by simp [dr]) (by simp [dr])
            (by simp [dr ])
            (by simp [dr, d₂, d₁, hcell])
            (by simp [dr, d₂, d₁, hout])
            (by simp [dr, d₂, d₁, htmp])
            (by simp [dr, d₂, d₁, hcount, List.replicate_succ])
          have hh := copy_eval dz 101 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [dz, SubexpJetInitProgram.repeatOut, dr,
              d₂, d₁, htmp])
          have hl := copy_eval dh 100 102 107 0 1 (by decide) (by decide) (by decide) (by decide)
            (by simp [dh, afterCopy, StackRoutines.copyStacks, dz, SubexpJetInitProgram.repeatOut,
              dr, d₂, d₁, htmp])
          have hfull := hp₁.seq (Eval.ite_true (no := .base .skip) ht₁
            (hp₂.seq (Eval.ite_true (no := copyLow) ht₂ (hr.seq (hz.seq (hh.seq hl))))))
          have he : dl = counterResult d (n + 2) W low high dl.regs := by
            refine state_ext rfl ?_
            funext i
            by_cases hi : i = 102
            · subst i
              simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                counterResult, paddedBits, hlow, hhigh, copies_zero,
                List.append_assoc]
            · by_cases hj : i = 108
              · subst i
                simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, counterResult]
              · simp [dl, dh, dz, afterCopy, StackRoutines.copyStacks,
                  SubexpJetInitProgram.repeatOut, dr, d₂, d₁,
                  counterResult, hi, hj]
          let cost := n * (7 * W + 7) + 7 * high.length + 7 * low.length + 20
          refine ⟨cost, ?_, dl.regs, ?_⟩
          · dsimp [cost]
            rw [hlength, hhlength]
            nlinarith only [Nat.zero_le n, Nat.zero_le W]
          · have hc : Eval fromCounter cost d dl := by
              have hdz101 : dz.stacks 101 = high := by
                simp [dz, SubexpJetInitProgram.repeatOut, dr,
                  d₂, d₁, hhigh]
              have hdh100 : dh.stacks 100 = low := by
                simp [dh, afterCopy, StackRoutines.copyStacks, dz,
                  SubexpJetInitProgram.repeatOut, dr,
                  d₂, d₁, hlow]
              convert hfull using 1
              · rfl
              · rw [hdz101, hdh100]
                simp only [List.length_replicate]
                dsimp [cost]
                rw [hlength, hhlength]
                ring
            rw [he] at hc
            exact hc
theorem paddedBits_length (D W : ℕ) (low high : List Bool)
    (hlow : low.length = W) (hhigh : high.length = W) :
    (paddedBits W low high D).length = D * W := by
  cases D with
  | zero => simp [paddedBits]
  | succ D =>
      cases D with
      | zero => simpa [paddedBits] using hlow
      | succ n => simp [paddedBits, hlow, hhigh]; ring

end Counter
namespace Call
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpLinearFactorCall
theorem command_run (s : Store) (D W : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = W) (hhlen : high.length = W)
    (hD : s 108 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (hout : s 102 = []) (htmp : s 107 = []) :
    ExecutesIn command (101 * (D + 1) * (W + 1)) s
      (Function.update (Function.update s 108 []) 102
        (Counter.paddedBits W low high D)) := by
  intro regs
  let d : Data := ⟨regs, s⟩
  let nativeData := projectState id ports d
  obtain ⟨n, hn, rf, he⟩ := Counter.fromCounter_eval nativeData D W low high
    hlow hhigh hllen hhlen hD hzero hout htmp
  have hc := eval_liftCommand_from_state SubexpLinearFactorProgram.fromCounter
    108 102 id ports d Function.injective_id ports.injective he
  let last := embedState id ports d
    (Counter.counterResult nativeData D W low high rf)
  have hext : Function.extend ports (s ∘ ports) s = s := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project id ports d Function.injective_id ports.injective)
    exact h
  have hs : last.stacks = Function.update (Function.update s 108 []) 102
      (Counter.paddedBits W low high D) := by
    change Function.extend ports
      (Function.update (Function.update (s ∘ ports) 108 []) 102
        (Counter.paddedBits W low high D)) s = _
    rw [ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hext]
    rfl
  have hlast : last =
      (⟨last.regs, Function.update (Function.update s 108 []) 102
        (Counter.paddedBits W low high D)⟩ : Data) := by
    exact SubexpScanPrimitives.state_ext rfl hs
  refine ⟨n + 1, last.regs, ?_, ?_⟩
  · have hp : 0 < (D + 1) * (W + 1) := Nat.mul_pos (by omega) (by omega)
    nlinarith
  · change Eval command (n + 1) d last at hc
    rw [hlast] at hc
    exact hc

end Call
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpPolynomialConstructor
theorem constructAtInputs_run (s : Store) (dst : Fin 256) (hdst : 205 ≤ dst.val)
    (hdtmp : dst ≠ 245) (D W : ℕ) (low high : List Bool)
    (hlow : s 100 = low) (hhigh : s 101 = high)
    (hllen : low.length = W) (hhlen : high.length = W)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (h102 : s 102 = []) (h107 : s 107 = []) (h108 : s 108 = [])
    (h120 : s 120 = []) (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (constructAtInputs dst) (150 * (D + 1) * (W + 1)) s
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst
        (Counter.paddedBits W low high D)) := by
  have hsmall : ∀ i : Fin 256, i.val < 205 → i ≠ dst := by
    intro i hi he
    subst i
    omega
  have h100 := hsmall 100 (by decide)
  have h101 := hsmall 101 (by decide)
  have h102d := hsmall 102 (by decide)
  let bits := Counter.paddedBits W low high D
  let s₁ := Function.update s 108 (List.replicate D true)
  let s₂ := Function.update s 102 bits
  let s₃ := Function.update s₂ 100 []
  let s₄ := Function.update s₃ 101 []
  have h₁ : ExecutesIn (copy 243 108) (7 * D + 5) s s₁ := by
    simpa [s₁, hD, h108] using copy_run 243 108 s
      (by decide) (by decide) (by decide) h120
  have he₂ : Function.update (Function.update s₁ 108 []) 102 bits = s₂ := by
    funext j
    by_cases hj : j = 108 <;> simp [s₁, s₂, Function.update_apply, h108, hj]
  have h₂ : ExecutesIn SubexpLinearFactorCall.command
      (101 * (D + 1) * (W + 1)) s₁ s₂ := by
    have h := Call.command_run s₁ D W low high
      (by simp [s₁, hlow]) (by simp [s₁, hhigh]) hllen hhlen
      (by simp [s₁]) (by simp [s₁, hzero]) (by simp [s₁, h102]) (by simp [s₁, h107])
    rw [he₂] at h
    exact h
  have h₃ : ExecutesIn (clear 100) (2 * W + 3) s₂ s₃ := by
    simpa [s₂, s₃, hlow, hllen, ← Nat.mul_assoc] using clear_run 100 s₂
  have h₄ : ExecutesIn (clear 101) (2 * W + 3) s₃ s₄ := by
    simpa [s₂, s₃, s₄, hhigh, hhlen, ← Nat.mul_assoc] using clear_run 101 s₃
  have he₅ : Function.update (Function.update s₄ 102 []) dst (s₄ 102) =
      Function.update (Function.update (Function.update s 100 []) 101 []) dst bits := by
    funext j
    by_cases hj : j = 102 <;>
      simp [s₂, s₃, s₄, Function.update_apply, hj, h102, h102d ]
  have hbits : bits.length = D * W :=
    Counter.paddedBits_length D W low high hllen hhlen
  have h₅ : ExecutesIn (move 102 dst) (6 * D * W + 6) s₄
      (Function.update (Function.update (Function.update s 100 []) 101 []) dst bits) := by
    have h := move_run s₄ 102 dst (by decide) hdtmp h102d
      (by simp [s₄, s₃, s₂, h245])
      (by simp [s₄, s₃, s₂, Ne.symm h100, Ne.symm h101, Ne.symm h102d, hout])
    rw [he₅] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp [s₄, s₃, s₂, hbits]
    ring
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  apply h.mono
  ring_nf
  omega

theorem construct_run (s : Store) (low high dst : Fin 256)
    (hl100 : low ≠ 100) (hl120 : low ≠ 120)
    (hh100 : high ≠ 100) (hh101 : high ≠ 101) (hh120 : high ≠ 120)
    (hdst : 205 ≤ dst.val) (hdtmp : dst ≠ 245) (D W : ℕ)
    (hllen : (s low).length = W) (hhlen : (s high).length = W)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h245 : s 245 = []) (hout : s dst = []) :
    ExecutesIn (construct low high dst) (220 * (D + 1) * (W + 1)) s
      (Function.update s dst (Counter.paddedBits W (s low) (s high) D)) := by
  let s₁ := Function.update s 100 (s low)
  let s₂ := Function.update s₁ 101 (s high)
  have hd100 : dst ≠ 100 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have hd101 : dst ≠ 101 := by intro h; subst dst; norm_num [Fin.coe_ofNat_eq_mod] at hdst
  have h₁ : ExecutesIn (copy low 100) (7 * (s low).length + 5) s s₁ := by
    simpa [s₁, h100] using copy_run low 100 s hl100 hl120 (by decide) h120
  have h₂ : ExecutesIn (copy high 101) (7 * (s high).length + 5) s₁ s₂ := by
    simpa [s₁, s₂, hh100, h101] using copy_run high 101 s₁ hh101 hh120
      (by decide) (by simp [s₁, h120])
  have h₃ := constructAtInputs_run s₂ dst hdst hdtmp D W (s low) (s high)
    (by simp [s₂, s₁]) (by simp [s₂]) hllen hhlen
    (by simp [s₂, s₁, hD]) (by simp [s₂, s₁, hzero])
    (by simp [s₂, s₁, h102]) (by simp [s₂, s₁, h107])
    (by simp [s₂, s₁, h108]) (by simp [s₂, s₁, h120])
    (by simp [s₂, s₁, h245]) (by simp [s₂, s₁, hd100, hd101, hout])
  have he : Function.update (Function.update (Function.update s₂ 100 []) 101 []) dst
      (Counter.paddedBits W (s low) (s high) D) =
      Function.update s dst (Counter.paddedBits W (s low) (s high) D) := by
    funext j
    by_cases h100' : j = 100 <;> by_cases h101' : j = 101 <;>
      simp [s₂, s₁, Function.update_apply, h100, h101, h100', h101']
  rw [he] at h₃
  apply (h₁.seq (h₂.seq h₃)).mono
  rw [hllen, hhlen]
  ring_nf
  omega

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramExecutionPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem lowFrame_clearMany {base s : Store} (hf : LowFrame base s)
    (slots : List (Fin 256)) (hs : ∀ i ∈ slots, 205 ≤ i.val) :
    LowFrame base (SubexpLocalCRTSetup.cleared slots s) := by
  intro i hi
  have hnot : i ∉ slots := by intro h; have := hs i h; omega
  simpa [SubexpLocalCRTSetup.cleared_apply, hnot] using hf i hi

theorem prepareLocalInverse_run_oai {C P : Type*} (base : Store)
    (encC : C → List Bool) (encP : P → List Bool) (constant : C → P)
    (sm sa : Code) (cm ca : C → C → C) (Km Ka W V J U : ℕ)
    (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne c : C) (factor : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hhead : encP factor = encC c ++ rest)
    (s : Store) (hf : LowFrame base s)
    (hfactor : s 240 = encP factor) (hzero : s 104 = encC zero)
    (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (hJ : s 243 = List.replicate J true) (hpolyZero : s 192 = encP (constant zero))
    (hcursor : ∀ i ∈ ([217,229] : List (Fin 256)), (s i).length ≤ U)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,121,122,205,208,220,222,223,
        227,228,241,242,244,245,246,247] : List (Fin 256)), s i = []) :
    let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (executionPreparation sm sa)
      (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
      (preparedLocal (SubexpLocalCRTSetup.cleared [217,229] s)
        (encP factor) (encP (constant one)) (encP (constant a))
        (encP (constant (cm a minusOne))) (encP (constant zero))) := by
  dsimp only
  let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
  let t0 := SubexpLocalCRTSetup.cleared [217,229] s
  let t1 := Function.update t0 223 (encP factor)
  let t2 := Function.update t1 240 []
  let t3 := Function.update t2 205 (encC c)
  let t4 := Function.update (Function.update t2 227 (encP (constant a))) 228
    (encP (constant (cm a minusOne)))
  let t5 := Function.update t4 220 (encP (constant one))
  let t6 := Function.update t5 242 (encP (constant zero))
  have hf0 : LowFrame base t0 := lowFrame_clearMany hf _ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide)
  have hf3 : LowFrame base t3 := lowFrame_update (lowFrame_update
    (lowFrame_update hf0 223 (by decide) _) 240 (by decide) _) 205 (by decide) _
  have hrest : rest.length ≤ V := by
    have hh := hpwidth factor
    rw [hhead, List.length_append, hcwidth] at hh
    omega
  have h0 : ExecutesIn (SubexpLocalCRTSetup.clearMany [217,229]) (2 * (2 * U + 3)) s t0 := by
    simpa [t0] using SubexpLocalCRTSetup.clearMany_run [217,229] s U hcursor
  have h1 : ExecutesIn (replace 240 223) (9 * V + 8) t0 t1 := by
    have h := replace_bounded t0 240 223 V (by decide) (by decide) (by decide)
      (by simp [t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simpa [t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using hpwidth factor)
      (by simp [t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    simpa [t1, t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using h
  have h2 : ExecutesIn (clear 240) (2 * V + 3) t1 t2 := by
    apply (clear_run 240 t1).mono
    have hh := hpwidth factor
    simpa [t1, t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) 3
  have h3 : ExecutesIn constantCommand (21 * W + 9 * V + 19) t2 t3 := by
    have h := constantCommand_run t2 (encC c) rest
      (by simp [t2, t1, hhead])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hcwidth])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    apply h.mono
    rw [hcwidth]
    omega
  have h4 : ExecutesIn (inverseConstantsCommand sm sa)
      (inverseConstantsBudget (s 209).length (s 212).length J Km Ka W) t3 t4 := by
    have h := inverseConstantsCommand_run base encC sm sa cm ca Km Ka W J hsm hsa hcwidth
      t3 c zero one minusOne hf3 (by simp [t3])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero]) hzeroBits
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hminus])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hJ])
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          <;> simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    have he : Function.update t2 205 [] = t2 := by
      apply Function.update_eq_self_iff.mpr
      simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean]
    simp only [t3, Function.update_idem, he] at h
    simpa [t4, t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, a,
      ← hconstant, hclean, Function.update_idem] using h
  have h5 : ExecutesIn (SubexpPolynomialConstructor.construct 207 104 220)
      (220 * (J + 1) * (W + 1)) t4 t5 := by
    have h := DensePolynomialProgram.Constructor.construct_run t4 207 104 220
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      J W
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone, hcwidth])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hcwidth])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hJ])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hzeroBits])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    simpa [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone, hzero, hconstant] using h
  have h6 : ExecutesIn (copy 192 242) (7 * V + 5) t5 t6 := by
    have h := copy_run 192 242 t5 (by decide) (by decide) (by decide)
      (by simp [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    have hh : (t5 192).length ≤ V := by
      simpa [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hpolyZero] using hpwidth (constant zero)
    have h' := h.mono (show 7 * (t5 192).length + 5 ≤ 7 * V + 5 by omega)
    simpa [t6, t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hpolyZero, hclean] using h'
  have he : t6 = preparedLocal t0 (encP factor) (encP (constant one))
      (encP (constant a)) (encP (constant (cm a minusOne))) (encP (constant zero)) := by
    simp only [t6, t5, t4, t2, t1, preparedLocal]
    rw [Function.update_comm (by decide : (223 : Fin 256) ≠ 240)]
  change ExecutesIn (executionPreparation sm sa)
    (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
    (preparedLocal t0 (encP factor) (encP (constant one)) (encP (constant a))
      (encP (constant (cm a minusOne))) (encP (constant zero)))
  rw [← he]
  convert h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) using 1 <;>
    simp only [executionPreparation, preparationBudget] ; ring

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run_oai.{u_1, u_2}
