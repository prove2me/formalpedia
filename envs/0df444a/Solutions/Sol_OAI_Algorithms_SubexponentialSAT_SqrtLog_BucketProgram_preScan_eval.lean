-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:16:49.12604+00:00
-- url     : https://prove2.me/submissions/f3805c43-0e24-49cc-b0a8-65b49313468b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S106

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ModularPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite Boolean-stack programs for modular arithmetic

The programs in this file use only a fixed finite collection of labels,
Boolean registers, and Boolean stacks. The operand width and modulus are data.
-/

namespace SubexponentialSAT.ModularPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularArithmetic

private theorem transfer_output (word : List Bool) :
    SubexponentialSAT.StackRoutines.transferStacks (2 : Fin 3) 0 (operandStacks [] [] word) =
      operandStacks word.reverse [] [] := by
  funext k
  fin_cases k <;> simp [SubexponentialSAT.StackRoutines.transferStacks, operandStacks]

/-- Sequentially link a proved arithmetic run to a proved transfer run.
Both runs execute inside the concrete linked finite instruction table. -/
theorem append_reverse_output {l : ℕ} (p : Program 8 3 l)
    {n : ℕ} {start : Cfg 8 3 l} (regs : Fin 8 → Bool) (word : List Bool)
    (hrun : Trace p n start ⟨none, regs, operandStacks [] [] word⟩) :
    Trace (SubexponentialSAT.ProgramLinking.link p reverseOutput)
      (n + 3 * word.length + 3)
      (SubexponentialSAT.ProgramLinking.relabelCfg (Fin.castAdd 4)
        (some (Fin.natAdd l reverseOutput.entry)) start)
      ⟨none, readRegs regs 1 3 none, operandStacks word.reverse [] []⟩ := by
  have ht := SubexponentialSAT.StackRoutines.transferProgram_trace
    (2 : Fin 3) 0 (1 : Fin 8) 3 (by decide) (by decide)
    regs (operandStacks [] [] word)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace reverseOutput ht
    (3 : Fin 4) rfl rfl
  have hlink := SubexponentialSAT.ProgramLinking.link_trace p reverseOutput hrun rfl hh
  simpa [SubexponentialSAT.ProgramLinking.relabelCfg, SubexponentialSAT.ProgramLinking.relocatePc,
    SubexponentialSAT.StackRoutines.transferResult, transfer_output, Nat.add_assoc] using hlink

/-- A reusable subtraction program returning a little-endian result.
Its exact cost includes the result-reversal routine and both return jumps. -/
theorem subtractLE_correct (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace subtractLEProgram (15 * xs.length + 6)
        ⟨some 0, regs, operandStacks xs ys []⟩
        ⟨none, finalRegs, operandStacks (subCarry (regs 0) xs ys).1 [] []⟩ ∧
      finalRegs 0 = (subCarry (regs 0) xs ys).2 := by
  obtain ⟨midRegs, hrun, hborrow⟩ := subtract_correct regs xs ys [] hlen
  have hrun' : Trace subtractProgram (12 * xs.length + 3)
      (subtractCfg (some 0) regs xs ys [])
      ⟨none, midRegs, operandStacks [] [] (subCarry (regs 0) xs ys).1.reverse⟩ := by
    simpa [subtractCfg] using hrun
  have hout := append_reverse_output subtractProgram midRegs _ hrun'
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · convert hout using 1
    · rw [List.length_reverse, subCarry_length _ _ _ hlen]
      omega
    · rfl
    · rw [List.reverse_reverse]
  · simpa [readRegs] using hborrow

theorem paddingLE_correct (regs : Fin 8 → Bool) (shape input : List Bool)
    (hlen : input.length ≤ shape.length) :
    ∃ finalRegs : Fin 8 → Bool,
      Trace paddingLEProgram (7 * shape.length + 6)
        ⟨some 0, regs, operandStacks shape input []⟩
        ⟨none, finalRegs, operandStacks (padTo shape input) [] []⟩ ∧
      finalRegs 0 = regs 0 := by
  obtain ⟨midRegs, hrun, hborrow⟩ := padding_correct regs shape input [] hlen
  have hrun' : Trace paddingProgram (4 * shape.length + 3)
      (paddingCfg (some 0) regs shape input [])
      ⟨none, midRegs, operandStacks [] [] (padTo shape input).reverse⟩ := by
    simpa [paddingCfg] using hrun
  have hout := append_reverse_output paddingProgram midRegs _ hrun'
  refine ⟨readRegs midRegs 1 3 none, ?_, ?_⟩
  · convert hout using 1
    · rw [List.length_reverse, padTo_length]
      omega
    · rfl
    · rw [List.reverse_reverse]
  · simpa [readRegs] using hborrow

/-! Preserve a candidate word while subtracting a modulus from its copy. -/

end SubexponentialSAT.ModularPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SaturatingSubtractionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving saturating binary subtraction

Eight Boolean registers and eight stacks suffice. The two operands remain
on stacks 0 and 1; stack 2 receives their natural-number difference and
stacks 3 through 7 return empty. Copied concatenations supply a common
padding shape without computing a numeric width. The final borrow bit
controls a real clear loop. Every copy, pad, subtraction, and clear is
charged in the linear instruction bound.
-/

namespace SubexponentialSAT.SaturatingSubtractionProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic

theorem copy_eval (src dst : Fin 8) (d : Data)
    (hsd : src ≠ dst) (hs6 : src ≠ 6) (h6d : (6 : Fin 8) ≠ dst)
    (h6 : d.stacks 6 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 6 0 1 hsd hs6 h6d (by decide)
    d.regs d.stacks h6

theorem embed_three (p : Fin 3 → Fin 8) (hp : Function.Injective p)
    (d : Data) (regs : Fin 8 → Bool) (a b c : List Bool) :
    embedState id p d ⟨regs, ModularPrograms.operandStacks a b c⟩ = three d regs p a b c := by
  apply embedState_eq_of_ports id p d _ _ Function.injective_id hp
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [three, ModularPrograms.operandStacks, hp.eq_iff]
  · intro i hi
    have h0 : i ≠ p 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ p 1 := fun h => hi ⟨1, h.symm⟩
    have h2 : i ≠ p 2 := fun h => hi ⟨2, h.symm⟩
    simp [three, h0, h1, h2]

theorem project_three (p : Fin 3 → Fin 8) (d : Data) (h2 : d.stacks (p 2) = []) :
    projectState id p d =
      ⟨d.regs, ModularPrograms.operandStacks (d.stacks (p 0)) (d.stacks (p 1)) []⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ ModularPrograms.operandStacks, h2]

theorem padAt_eval (p : Fin 3 → Fin 8) (hp : Function.Injective p) (d : Data)
    (h2 : d.stacks (p 2) = [])
    (hlen : (d.stacks (p 1)).length ≤ (d.stacks (p 0)).length) :
    ∃ regs, Eval (padAt p) (7 * (d.stacks (p 0)).length + 6) d
      (three d regs p (padTo (d.stacks (p 0)) (d.stacks (p 1))) [] []) := by
  obtain ⟨regs, ht, _⟩ := ModularPrograms.paddingLE_correct d.regs
    (d.stacks (p 0)) (d.stacks (p 1)) hlen
  have htrace : Trace ModularPrograms.paddingLEProgram
      (7 * (d.stacks (p 0)).length + 6)
      ((projectState id p d).withPC (some ModularPrograms.paddingLEProgram.entry))
      ((⟨regs, ModularPrograms.operandStacks
        (padTo (d.stacks (p 0)) (d.stacks (p 1))) [] []⟩ : State 8 3).withPC none) := by
    rw [project_three p d h2]
    exact ht
  have he := eval_call_from_state ModularPrograms.paddingLEProgram id p d
    Function.injective_id hp htrace
  rw [embed_three p hp] at he
  exact ⟨regs, he⟩

theorem subtractAt_eval (p : Fin 3 → Fin 8) (hp : Function.Injective p) (d : Data)
    (h2 : d.stacks (p 2) = []) (h0 : d.regs 0 = false)
    (hlen : (d.stacks (p 0)).length = (d.stacks (p 1)).length) :
    ∃ regs, Eval (subtractAt p) (15 * (d.stacks (p 0)).length + 6) d
      (three d regs p (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).1 [] []) ∧
      regs 0 = (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).2 := by
  obtain ⟨regs, ht, hb⟩ := ModularPrograms.subtractLE_correct d.regs
    (d.stacks (p 0)) (d.stacks (p 1)) hlen
  rw [h0] at ht hb
  have htrace : Trace ModularPrograms.subtractLEProgram
      (15 * (d.stacks (p 0)).length + 6)
      ((projectState id p d).withPC (some ModularPrograms.subtractLEProgram.entry))
      ((⟨regs, ModularPrograms.operandStacks
        (subCarry false (d.stacks (p 0)) (d.stacks (p 1))).1 [] []⟩ : State 8 3).withPC none) := by
    rw [project_three p d h2]
    exact ht
  have he := eval_call_from_state ModularPrograms.subtractLEProgram id p d
    Function.injective_id hp htrace
  rw [embed_three p hp] at he
  exact ⟨regs, he, hb⟩

theorem leftPorts_injective : Function.Injective leftPorts := by decide
theorem rightPorts_injective : Function.Injective rightPorts := by decide
theorem subtractPorts_injective : Function.Injective subtractPorts := by decide

theorem prepare_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Eval prepare (21 * (xs.length + ys.length) + 30) (state regs xs ys [])
      (store (readRegs regs 0 1 none) xs ys (xs ++ ys) (xs ++ ys) xs ys []) := by
  let d₀ := state regs xs ys []
  let d₁ := copied 1 2 d₀
  let d₂ := copied 0 2 d₁
  let d₃ := copied 1 3 d₂
  let d₄ := copied 0 3 d₃
  let d₅ := copied 0 4 d₄
  let d₆ := copied 1 5 d₅
  have h₁ := copy_eval 1 2 d₀ (by decide) (by decide) (by decide) (by rfl)
  have h₂ := copy_eval 0 2 d₁ (by decide) (by decide) (by decide) (by rfl)
  have h₃ := copy_eval 1 3 d₂ (by decide) (by decide) (by decide) (by rfl)
  have h₄ := copy_eval 0 3 d₃ (by decide) (by decide) (by decide) (by rfl)
  have h₅ := copy_eval 0 4 d₄ (by decide) (by decide) (by decide) (by rfl)
  have h₆ := copy_eval 1 5 d₅ (by decide) (by decide) (by decide) (by rfl)
  have hend : d₆ = store (readRegs regs 0 1 none) xs ys
      (xs ++ ys) (xs ++ ys) xs ys [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [ d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.readRegs_reset]
    · funext i
      fin_cases i <;>
        simp [ d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.copyStacks]
  have he := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  change Eval prepare _ (state regs xs ys []) d₆ at he
  rw [hend] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  simp [d₅, d₄, d₃, d₂, d₁, d₀, StackRoutines.copyStacks]
  omega

theorem finish_eval (regs : Fin 8 → Bool) (xs ys output : List Bool) :
    ∃ t ≤ 2 * output.length + 12,
      Eval finish t (state regs xs ys output)
        (state (fun _ => false) xs ys (if regs 0 then [] else output)) := by
  cases hb : regs 0 with
  | false =>
      have hs : Eval (.ite 0 clearOutput (.base .skip)) 1
          (state regs xs ys output) (state regs xs ys output) :=
        .ite_false hb (.base (.skip _))
      refine ⟨9, by omega, ?_⟩
      simpa only [finish, hb, Bool.false_eq_true, ↓reduceIte] using
        hs.seq (RegisterResetProgram.all_eval (state regs xs ys output))
  | true =>
      have hc : Eval clearOutput (2 * output.length + 3) (state regs xs ys output)
          (state (readRegs regs 0 1 none) xs ys []) := by
        apply Eval.call
        have h := ListRegisterProgram.clear_run (2 : Fin 8) (0 : Fin 8) 1
          regs (state regs xs ys output).stacks
        have hstack : StackRoutines.clearStacks (2 : Fin 8) (state regs xs ys output).stacks =
            (state (readRegs regs 0 1 none) xs ys []).stacks := by
          funext i
          fin_cases i <;> simp [ StackRoutines.clearStacks]
        unfold ListRegisterProgram.Run at h
        rw [hstack] at h
        exact h
      have hi := Eval.ite_true (no := (.base .skip : Code)) hb hc
      refine ⟨2 * output.length + 12, le_rfl, ?_⟩
      simpa only [finish, hb, ↓reduceIte, Nat.add_assoc] using
        hi.seq (RegisterResetProgram.all_eval (state (readRegs regs 0 1 none) xs ys []))

theorem saturated_value (xs ys : List Bool) (hlen : xs.length = ys.length) :
    BinaryArithmetic.toNat (saturated xs ys) = BinaryArithmetic.toNat xs - BinaryArithmetic.toNat ys := by
  have hc := subCarry_correct false xs ys hlen
  cases hb : (subCarry false xs ys).2 with
  | false =>
      simp only [hb, bitVal, Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hc
      simp only [saturated, hb, Bool.false_eq_true, ↓reduceIte]
      omega
  | true =>
      have hlt := (subCarry_borrow_iff xs ys hlen).mp hb
      simp [saturated, hb, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]

theorem saturated_length (xs ys : List Bool) (hlen : xs.length = ys.length) :
    (saturated xs ys).length ≤ xs.length := by
  cases hb : (subCarry false xs ys).2 <;>
    simp [saturated, hb, subCarry_length false xs ys hlen]

/-- Both numeric operands are preserved. The sole output is natural-number
subtraction, and its representation length is bounded by the input lengths.
The instruction allowance includes the final compiled halt. -/
theorem command_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ (t : ℕ) (word : List Bool),
      t + 1 ≤ 100 * (xs.length + ys.length + 1) ∧
      Eval command t (state regs xs ys []) (state (fun _ => false) xs ys word) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat xs - BinaryArithmetic.toNat ys ∧ word.length ≤ xs.length + ys.length := by
  let shape := xs ++ ys
  let px := padTo shape xs
  let py := padTo shape ys
  have hx : xs.length ≤ shape.length := by simp [shape]
  have hy : ys.length ≤ shape.length := by simp [shape]
  have hlen : px.length = py.length := by simp [px, py, padTo_length]
  let a := store (readRegs regs 0 1 none) xs ys shape shape xs ys []
  obtain ⟨r₁, hp₁⟩ := padAt_eval leftPorts leftPorts_injective a (by rfl) hx
  let b := store r₁ xs ys px shape [] ys []
  have eb : three a r₁ leftPorts (padTo (a.stacks (leftPorts 0))
      (a.stacks (leftPorts 1))) [] [] = b := by
    apply congrArg (StructuredProgram.State.mk r₁)
    funext i
    fin_cases i <;> simp [ a, leftPorts, px]
  rw [eb] at hp₁
  obtain ⟨r₂, hp₂⟩ := padAt_eval rightPorts rightPorts_injective b (by rfl) hy
  let c := store r₂ xs ys px py [] [] []
  have ec : three b r₂ rightPorts (padTo (b.stacks (rightPorts 0))
      (b.stacks (rightPorts 1))) [] [] = c := by
    apply congrArg (StructuredProgram.State.mk r₂)
    funext i
    fin_cases i <;> simp [ b, rightPorts, py]
  rw [ec] at hp₂
  let d := store (Function.update r₂ 0 false) xs ys px py [] [] []
  have hs : Eval setBorrow 1 c d := .base (.atom _ _)
  obtain ⟨r₃, hd, hb⟩ := subtractAt_eval subtractPorts subtractPorts_injective d
    (by rfl) (by simp [d ]) hlen
  let diff := (subCarry false px py).1
  have ee : three d r₃ subtractPorts (subCarry false (d.stacks (subtractPorts 0))
      (d.stacks (subtractPorts 1))).1 [] [] = state r₃ xs ys diff := by
    apply congrArg (StructuredProgram.State.mk r₃)
    funext i
    fin_cases i <;> simp [ d, subtractPorts, diff]
  rw [ee] at hd
  change r₃ 0 = (subCarry false px py).2 at hb
  obtain ⟨tf, htf, hf⟩ := finish_eval r₃ xs ys diff
  rw [hb] at hf
  change Eval finish tf (state r₃ xs ys diff)
    (state (fun _ => false) xs ys (saturated px py)) at hf
  have he := (prepare_eval regs xs ys).seq (hp₁.seq (hp₂.seq (hs.seq (hd.seq hf))))
  let t := (21 * (xs.length + ys.length) + 30) +
    ((7 * shape.length + 6) + ((7 * shape.length + 6) + (1 + ((15 * px.length + 6) + tf))))
  change Eval command t (state regs xs ys [])
    (state (fun _ => false) xs ys (saturated px py)) at he
  refine ⟨t, saturated px py, ?_, he, ?_, ?_⟩
  · have hdiff : diff.length = shape.length :=
      (subCarry_length false px py hlen).trans (padTo_length shape xs)
    rw [hdiff] at htf
    dsimp [t]
    rw [padTo_length]
    simp only [shape, List.length_append] at htf ⊢
    omega
  · rw [saturated_value px py hlen, padTo_correct shape xs hx, padTo_correct shape ys hy]
  · exact (saturated_length px py hlen).trans_eq (by simp [px, shape, padTo_length])

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

theorem subtractPort_injective : Function.Injective subtractPort := Fin.castAdd_injective _ _

theorem shiftCommand_eval_lengths (regs : Fin 8 → Bool) (W N P : List Bool) :
    ∃ t ≤ 300*(W.length+N.length+P.length+1)^2, ∃ rf diff out,
      Eval shiftCommand t (shiftState regs W N P [] []) (shiftState rf W N P diff out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out =
        SubexponentialSAT.BinaryArithmetic.toNat W - SubexponentialSAT.BinaryArithmetic.toNat N + SubexponentialSAT.BinaryArithmetic.toNat P ∧
      out.length ≤ W.length+N.length+P.length+1 ∧ diff.length ≤ W.length+N.length := by
  obtain ⟨ts, diff, hts, hes, hvs, hls⟩ :=
    SubexponentialSAT.SaturatingSubtractionProgram.command_eval regs W N
  have hstart : projectState id subtractPort (shiftState regs W N P [] []) =
      SubexponentialSAT.SaturatingSubtractionProgram.state regs W N [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have htrace := compiled_halt_trace hes 0 2
  rw [← hstart] at htrace
  have hcall := eval_call_from_state SubexponentialSAT.SaturatingSubtractionProgram.program id subtractPort
    (shiftState regs W N P [] []) Function.injective_id subtractPort_injective htrace
  have hend : embedState id subtractPort (shiftState regs W N P [] [])
      (SubexponentialSAT.SaturatingSubtractionProgram.state (fun _ => false) W N diff) =
      shiftState (fun _ => false) W N P diff [] := by
    apply embedState_eq_of_ports id subtractPort _ _ _ Function.injective_id subtractPort_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> try rfl
      exact (hi ⟨2,rfl⟩).elim
  rw [hend] at hcall
  let a := shiftState (fun _ => false) W N P diff []
  have ha : Valid shiftAddPorts a := by
    constructor
    · rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨ta, rf, out, hea, hva, hla, hta⟩ := addAt_eval shiftAddPorts a ha
  have hout : (⟨rf, Function.update a.stacks shiftAddPorts.out out⟩ : ShiftData) =
      shiftState rf W N P diff out := by
    apply congrArg (StructuredProgram.State.mk rf)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hout] at hea
  refine ⟨ts+1+ta, ?_, rf, diff, out, hcall.seq hea, ?_, ?_, hls⟩
  · have hl : (a.stacks shiftAddPorts.left).length + (a.stacks shiftAddPorts.right).length+1 ≤
        W.length+N.length+P.length+1 := by simpa [a,shiftState,shiftAddPorts] using Nat.add_le_add_right hls (P.length+1)
    have ht := hta.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hl 2))
    nlinarith
  · simpa [a,shiftState,shiftAddPorts,hvs] using hva
  · have hl : diff.length+P.length+1 ≤ W.length+N.length+P.length+1 := by omega
    exact (by simpa [a,shiftState,shiftAddPorts] using hla : out.length ≤ diff.length+P.length+1).trans hl

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

theorem finalRegs_after_reset {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) :
    finalRegs value present ports (readRegs regs value present none) =
      readRegs regs value present none := by
  cases ports <;> simp [finalRegs, readRegs_reset]

theorem command_eval {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (d : State r s) :
    Eval (command value present ports) (cost ports d) d (finish value present ports d) := by
  rcases d with ⟨regs, stk⟩
  induction ports generalizing regs stk with
  | nil =>
      simpa [command, cost, finish, finalRegs] using
        (Eval.base (StructuredProgram.Eval.skip (⟨regs, stk⟩ : State r s)))
  | cons port rest ih =>
      have hn := List.nodup_cons.mp hnodup
      have hmap : rest.map (fun i => (clearStacks port stk i).length) =
          rest.map (fun i => (stk i).length) := by
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ port := by
          intro h
          subst i
          exact hn.1 hi
        rw [clearStacks_frame port i stk hne]
      have hfirst := BankRoutines.clear_call_eval port value present regs stk
      have hrest := ih hn.2 (readRegs regs value present none) (clearStacks port stk)
      have hrun := Eval.seq hfirst hrest
      simpa only [command, cost, finish, finalRegs_after_reset, finalRegs_cons,
        List.map_cons, List.sum_cons, List.length_cons, hmap,
        BankRoutines.clearBankStacks_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem preStep_eval (regs : Fin 8 → Bool) (W P N : List Bool)
    (xs : List SignedWord) (out : List Bool) :
    ∃ t ≤ preStepCost W (P,N), ∃ rf word,
      Eval preStep t (preState regs W ((P,N)::xs) out)
        (preState rf W xs (Encoding.frame word++out)) ∧ shiftedWord W (P,N) word := by
  let d := preState regs W ((P,N)::xs) out
  obtain ⟨a,ha,hsa⟩ := readWord_eval (10 : Fin 14) 8 12
    (by decide) (by decide) (by decide) d P (Encoding.frame N++signedWords xs)
    (by simp [d,preState,signedWords,List.append_assoc]) rfl rfl
  obtain ⟨b,hb,hsb⟩ := readWord_eval (10 : Fin 14) 1 12
    (by decide) (by decide) (by decide) a N (signedWords xs)
    (by rw [hsa]; rfl) (by rw [hsa]; rfl) (by rw [hsa]; rfl)
  have hproj : projectState id preShiftPort b = shiftState b.regs W N P [] [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> simp [preShiftPort,hsb,hsa,d,preState]
  obtain ⟨ts,hts,rs,diff,word,hes,hvs,hls,hld⟩ := shiftCommand_eval_lengths b.regs W N P
  rw [←hproj] at hes
  have hcall := eval_call_from_state shiftProgram id preShiftPort b
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hes 0 9)
  let c : PreData := ⟨rs,Function.update (Function.update b.stacks 2 diff) 9 word⟩
  have hembed : embedState id preShiftPort b (shiftState rs W N P diff word)=c := by
    apply embedState_eq_of_ports id preShiftPort b _ _ Function.injective_id
      (Fin.castAdd_injective _ _)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [c,preShiftPort,shiftState,hsb,hsa,d,preState]
    · intro i hi
      have h2 : i≠2 := fun h => hi ⟨2,h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨9,h.symm⟩
      simp [c,h2,h9]
  change Eval preShiftCall (ts+1) b
    (embedState id preShiftPort b (shiftState rs W N P diff word)) at hcall
  rw [hembed] at hcall
  let e := WorkspaceCleanupProgram.finish (0 : Fin 8) 1 ([1,2,8] : List (Fin 14)) c
  have he := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
    ([1,2,8] : List (Fin 14)) (by decide) c
  obtain ⟨f,hf,hsf⟩ := emitFrame_eval (9 : Fin 14) 11 12
    (by decide) (by decide) (by decide) e (by simp [e,c,hsb,hsa,d,preState])
  have he9 : e.stacks 9=word := by simp [e,c]
  have hend : f=preState f.regs W xs (Encoding.frame word++out) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    rw [hsf]
    funext i; fin_cases i <;> simp [e,c,hsb,hsa,d,preState]
  have hcCost : WorkspaceCleanupProgram.cost ([1,2,8] : List (Fin 14)) c =
      2*(N.length+diff.length+P.length)+9 := by
    simp [WorkspaceCleanupProgram.cost,c,hsb,hsa,d,preState]; omega
  have hall := ha.seq (hb.seq (hcall.seq (he.seq hf)))
  rw [hend] at hall
  refine ⟨_,?_,f.regs,word,hall,hvs,hls⟩
  rw [hcCost,he9]
  dsimp [preStepCost]
  nlinarith [Nat.zero_le W.length,Nat.zero_le N.length,Nat.zero_le P.length]

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem prePeek_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (out : List Bool) : Eval prePeek 1 (preState regs W xs out)
      (preReady regs W xs out) := Eval.base (StructuredProgram.Eval.atom _ _)

theorem preLoop_eval (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord)
    (acc : List Bool) :
    ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs acc)
        (preState rf W [] (words ys.reverse++acc)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  induction xs generalizing regs acc with
  | nil =>
      refine ⟨1,by simp [preScanCost],(preReady regs W [] acc).regs,[],?_,.nil⟩
      change Eval (.while 1 preBody) 1 (preReady regs W [] acc)
        (preState (preReady regs W [] acc).regs W [] acc)
      convert (Eval.while_false
        (show (preReady regs W [] acc).regs 1=false by
          simp [preReady,preState,signedWords,readRegs]) :
        Eval (.while 1 preBody) 1 (preReady regs W [] acc) (preReady regs W [] acc)) using 1
      all_goals try with_reducible_and_instances rfl
      simp [preReady, preState, signedWords ]
  | cons a xs ih =>
      rcases a with ⟨P,N⟩
      obtain ⟨ts,hts,rs,word,hes,hword⟩ := preStep_eval
        (preReady regs W ((P,N)::xs) acc).regs W P N xs acc
      obtain ⟨tt,htt,rf,ys,het,hys⟩ := ih rs (Encoding.frame word++acc)
      have hg : (preReady regs W ((P,N)::xs) acc).regs 1=true := by
        cases P <;> simp [preReady,preState,signedWords,Encoding.frame,readRegs]
      have he := Eval.while_true hg (hes.seq (prePeek_eval rs W xs _)) het
      refine ⟨(ts+1)+tt+1,?_,rf,word::ys,?_,.cons hword hys⟩
      · simp only [preScanCost,List.map_cons,List.sum_cons] at *
        omega
      · change Eval (.while 1 preBody) _ _ _
        change Eval (.while 1 preBody) _ _ _ at he
        simpa [List.reverse_cons,words_append,words,List.append_assoc] using he

theorem preScan_eval_of_loop (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord) (t : ℕ) (rf : Fin 8 → Bool) (ys : List (List Bool))
    (ht : t ≤ preScanCost W xs)
    (he : Eval preLoop t (preReady regs W xs [])
      (preState rf W [] (words ys.reverse)))
    (hy : List.Forall₂ (shiftedWord W) xs ys) :
    ∃ t ≤ preScanCost W xs + 1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧
      List.Forall₂ (shiftedWord W) xs ys :=
  ⟨1 + t, by omega, rf, ys, (prePeek_eval regs W xs []).seq he, hy⟩

theorem preScan_eval_map (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord)
    (h : ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs [])
        (preState rf W [] (words ys.reverse ++ [])) ∧
      List.Forall₂ (shiftedWord W) xs ys) :
    ∃ t ≤ preScanCost W xs + 1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧
      List.Forall₂ (shiftedWord W) xs ys := by
  obtain ⟨t, ht, rf, ys, he, hy⟩ := h
  rw [List.append_nil] at he
  exact preScan_eval_of_loop regs W xs t rf ys ht he hy

theorem preLoop_eval_empty (regs : Fin 8 → Bool) (W : List Bool)
    (xs : List SignedWord) :
    ∃ t ≤ preScanCost W xs, ∃ rf ys,
      Eval preLoop t (preReady regs W xs [])
        (preState rf W [] (words ys.reverse ++ [])) ∧
      List.Forall₂ (shiftedWord W) xs ys :=
  preLoop_eval regs W xs []

theorem preScan_eval_oai (regs : Fin 8 → Bool) (W : List Bool) (xs : List SignedWord) :
    ∃ t ≤ preScanCost W xs+1, ∃ rf ys,
      Eval preScan t (preState regs W xs [])
        (preState rf W [] (words ys.reverse)) ∧ List.Forall₂ (shiftedWord W) xs ys := by
  exact preScan_eval_map regs W xs (preLoop_eval_empty regs W xs)

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preScan_eval_oai
