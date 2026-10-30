-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:29:21.741377+00:00
-- url     : https://prove2.me/submissions/232b3f29-55a4-4bd2-b4ef-873cd3ed0fcc

import Mathlib
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S138

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem linearFactorCommand_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W J : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka) (hwidth : ∀ a, (encode a).length = W)
    (s : Store) (theta other one minusOne : C) (hf : LowFrame base s)
    (htheta : s 213 = encode theta) (hother : s 218 = encode other)
    (hone : s 207 = encode one) (hminus : s 211 = encode minusOne)
    (hJ : s 243 = List.replicate J true) (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h205 : s 205 = []) (h219 : s 219 = []) (h240 : s 240 = [])
    (h241 : s 241 = []) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn (linearFactorCommand multiply add)
      (Km+Ka+102*W+113 + 220*(J+1)*(W+1)) s
      (Function.update s 241 (DensePolynomialProgram.Constructor.Counter.paddedBits W
        (encode (differenceValue mulOp addOp theta other minusOne)) (encode one) J)) := by
  let delta := differenceValue mulOp addOp theta other minusOne
  let bits := DensePolynomialProgram.Constructor.Counter.paddedBits W (encode delta) (encode one) J
  let s1 := Function.update s 205 (encode delta)
  let s2 := Function.update s1 241 bits
  have h1 : ExecutesIn (differenceCommand multiply add) (Km+Ka+100*W+110) s s1 :=
    differenceCommand_run base encode multiply add mulOp addOp Km Ka W hm ha
      (fun a => (hwidth a).le) s theta other minusOne hf htheta hother hminus h120
      h205 h219 h240 h241 h244 h245
  have h2 : ExecutesIn (SubexpPolynomialConstructor.construct 205 207 241)
      (220*(J+1)*(W+1)) s1 s2 := by
    have h := DensePolynomialProgram.Constructor.construct_run s1 205 207 241
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) J W
      (by simp [s1, hwidth]) (by simp [s1, hone, hwidth])
      (by simp [s1, hJ]) (by simp [s1, hzero])
      (by simp [s1, h100]) (by simp [s1, h101]) (by simp [s1, h102])
      (by simp [s1, h107]) (by simp [s1, h108]) (by simp [s1, h120])
      (by simp [s1, h245]) (by simp [s1, h241])
    simpa only [s2, s1, Function.update_same,
      Function.update_of_ne (show (207 : Fin 256) ≠ 205 by decide), hone] using h
  have h3 : ExecutesIn (clear 205) (2*W+3) s2 (Function.update s 241 bits) := by
    have h := clear_run 205 s2
    have he : Function.update s2 205 [] = Function.update s 241 bits := by
      funext i
      by_cases hi : i = 205 <;> simp [s2, s1, Function.update_apply, hi, h205]
    rw [he] at h
    simpa [s2, s1, hwidth] using h
  exact (h1.seq (h2.seq h3)).mono (by omega)

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CRTLocalProgramInclude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One included-node update of the truncated local cofactor. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem includeNodeCommand_run_oai {C P : Type*} (base : Store)
    (encodeC : C → List Bool) (encodeP : P → List Bool)
    (sm sa pm : Code) (cm ca : C → C → C) (mulP : P → P → P)
    (Km Ka Kp W V J : ℕ) (one minusOne : C) (linear : C → P)
    (hsm : ServiceSpec base encodeC sm cm Km) (hsa : ServiceSpec base encodeC sa ca Ka)
    (hpm : ServiceSpec base encodeP pm mulP Kp)
    (hcwidth : ∀ a, (encodeC a).length = W) (hpwidth : ∀ a, (encodeP a).length ≤ V)
    (hlinear : ∀ a, encodeP (linear a) = DensePolynomialProgram.Constructor.Counter.paddedBits
      W (encodeC a) (encodeC one) J)
    (s : Store) (theta other : C) (acc : P) (hf : LowFrame base s)
    (htheta : s 213 = encodeC theta) (hother : s 218 = encodeC other)
    (hone : s 207 = encodeC one) (hminus : s 211 = encodeC minusOne)
    (hJ : s 243 = List.replicate J true) (hzero : s 104 = List.replicate W false)
    (h100 : s 100 = []) (h101 : s 101 = []) (h102 : s 102 = [])
    (h107 : s 107 = []) (h108 : s 108 = []) (h120 : s 120 = [])
    (h205 : s 205 = []) (h219 : s 219 = []) (h223 : s 223 = [])
    (h240 : s 240 = encodeP acc) (h241 : s 241 = [])
    (h244 : s 244 = []) (h245 : s 245 = []) (h246 : s 246 = []) :
    ExecutesIn (includeNodeCommand sm sa pm) (includeBudget Km Ka Kp W V J) s
      (Function.update s 240 (encodeP
        ((fun p => mulP p (linear (differenceValue cm ca theta other minusOne)))^[J] acc))) := by
  let factor := linear (differenceValue cm ca theta other minusOne)
  let value := (fun p => mulP p factor)^[J] acc
  let s1 := Function.update s 223 (encodeP acc)
  let s2 := Function.update s1 240 []
  let s3 := Function.update s2 241 (encodeP factor)
  let s4 := Function.update s3 240 (encodeP acc)
  let s5 := Function.update s 241 (encodeP factor)
  let s6 := Function.update s5 246 (List.replicate J true)
  let s7 := Function.update s5 240 (encodeP value)
  have hf1 : LowFrame base s1 := lowFrame_update hf 223 (by decide) _
  have hf2 : LowFrame base s2 := lowFrame_update hf1 240 (by decide) _
  have hf5 : LowFrame base s5 := lowFrame_update hf 241 (by decide) _
  have hf6 : LowFrame base s6 := lowFrame_update hf5 246 (by decide) _
  have h1 : ExecutesIn (replace 240 223) (9*V+8) s s1 := by
    simpa [s1, h240] using replace_bounded s 240 223 V (by decide) (by decide) (by decide)
      h120 (by simpa [h240] using hpwidth acc) (by simp [h223])
  have h2 : ExecutesIn (clear 240) (2*V+3) s1 s2 := by
    have h := clear_run 240 s1
    apply h.mono
    simp [s1, h240]
    have hw := hpwidth acc
    omega
  have h3 : ExecutesIn (linearFactorCommand sm sa)
      (Km+Ka+102*W+113+220*(J+1)*(W+1)) s2 s3 := by
    have h := linearFactorCommand_run base encodeC sm sa cm ca Km Ka W J hsm hsa hcwidth
      s2 theta other one minusOne hf2
      (by simp [s2, s1, htheta]) (by simp [s2, s1, hother])
      (by simp [s2, s1, hone]) (by simp [s2, s1, hminus])
      (by simp [s2, s1, hJ]) (by simp [s2, s1, hzero])
      (by simp [s2, s1, h100]) (by simp [s2, s1, h101])
      (by simp [s2, s1, h102]) (by simp [s2, s1, h107])
      (by simp [s2, s1, h108]) (by simp [s2, s1, h120])
      (by simp [s2, s1, h205]) (by simp [s2, s1, h219])
      (by simp [s2]) (by simp [s2, s1, h241])
      (by simp [s2, s1, h244]) (by simp [s2, s1, h245])
    simpa only [s3, factor, hlinear] using h
  have h4 : ExecutesIn (replace 223 240) (9*V+8) s3 s4 := by
    simpa [s4, s3, s2, s1] using replace_bounded s3 223 240 V
      (by decide) (by decide) (by decide) (by simp [s3, s2, s1, h120])
      (by simpa [s3, s2, s1] using hpwidth acc) (by simp [s3, s2])
  have h5 : ExecutesIn (clear 223) (2*V+3) s4 s5 := by
    have h := clear_run 223 s4
    have he : Function.update s4 223 [] = s5 := by
      funext i
      by_cases hi : i = 223 <;> by_cases hj : i = 240 <;>
        simp [s5, s4, s3, s2, s1, Function.update_apply, hi, hj, h223, h240]
    rw [he] at h
    apply h.mono
    simp [s4, s3, s2, s1]
    have hw := hpwidth acc
    omega
  have h6 : ExecutesIn (replace 243 246) (7*J+8) s5 s6 := by
    simpa [s6, s5, hJ, h246] using replace_run s5 243 246 (by decide) (by decide) (by decide)
      (by simp [s5, h120])
  have h7 : ExecutesIn (nativeRepeat (binaryStep pm)) (J*(Kp+8*V+11)+2) s6 s7 := by
    have h := binary_repeat_state base encodeP pm mulP Kp V hpm hpwidth s6 factor acc hf6
      (by simp [s6, s5, h240]) (by simp [s6, s5])
      (by simp [s6, s5, h244]) (by simp [s6, s5, h245])
    have hc : (s6 246).length = J := by simp [s6]
    rw [hc] at h
    have he : Function.update (Function.update s6 240 (encodeP value)) 246 [] = s7 := by
      funext i
      by_cases hi : i = 240 <;> by_cases hj : i = 246 <;>
        simp [s7, s6, s5, Function.update_apply, hi, hj, h246]
    change ExecutesIn _ _ s6 (Function.update (Function.update s6 240 (encodeP value)) 246 []) at h
    rw [he] at h
    exact h
  have h8 : ExecutesIn (clear 241) (2*V+3) s7 (Function.update s 240 (encodeP value)) := by
    have h := clear_run 241 s7
    have he : Function.update s7 241 [] = Function.update s 240 (encodeP value) := by
      funext i
      by_cases hi : i = 241 <;> simp [s7, s5, Function.update_apply, hi, h241]
    rw [he] at h
    apply h.mono
    simp [s7, s5]
    have hw := hpwidth factor
    omega
  apply (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))).mono
  dsimp [includeBudget]
  nlinarith

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
end

theorem solution.{u_1, u_2} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run_oai.{u_1, u_2} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.includeNodeCommand_run_oai.{u_1, u_2}
