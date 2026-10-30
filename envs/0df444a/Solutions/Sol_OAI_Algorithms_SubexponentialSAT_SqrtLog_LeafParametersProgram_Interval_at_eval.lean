-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:33:30.10512+00:00
-- url     : https://prove2.me/submissions/1b4f9d48-c79a-4a93-9749-9911f4816d1a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S115

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval {S : ℕ} (src dst tmp : Fin S) (d : Data S)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    Eval (copyCmd src dst tmp) (7 * (d.stacks src).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks dst (d.stacks src)⟩ := by
  have h := ListRegisterProgram.copy_run src dst tmp (0 : Fin 8) 1
    hsd hst htd (by decide) d.regs d.stacks ht
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, hd] using h

end SubexponentialSAT.ArithmeticExpressionSupport

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem state_work (r : Regs) (w : Words) (i : Fin 32) (hi : 10 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 10 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 10) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 10
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have := congrArg Fin.val he
      simp only [] at this
      omega
    simp [state, Function.update_apply, hj, hji]

theorem width_pos (r Q R : List Bool) : 0 < width r Q R := by unfold width; omega

theorem copy_eval (regs : Regs) (w : Words) (a b : Fin 10)
    (hab : a ≠ b) (hb : w b = []) :
    Eval (copyCmd a b) (7 * (w a).length + 5) (state regs w)
      (state (readRegs regs 0 1 none) (Function.update w b (w a))) := by
  have hp (i : Fin 10) : port i ≠ (16 : Fin 32) := by
    intro he
    have := congrArg Fin.val he
    simp only [] at this
    omega
  have h := ArithmeticExpressionSupport.copy_eval (port a) (port b) 16 (state regs w)
    (by intro he; exact hab (Fin.ext (congrArg (fun j : Fin 32 => j.val) he)))
    (hp a) (hp b).symm
    (by simpa only [state_port] using hb) (state_work _ _ _ (by decide))
  simpa only [copyCmd, state_port, state_update, state_regs] using h

theorem pred_eval (regs : Regs) (w : Words) (i : Fin 10) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (predCmd i) t (state regs w) (state rf (Function.update w i word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w i) - 1 ∧ word.length ≤ (w i).length ∧
      t ≤ 20 * ((w i).length + 1) := by
  obtain ⟨t, rf, word, ht, he, hv, hl⟩ :=
    CounterPredProgram.pred_correct (predPorts i) (state regs w)
      (state_work _ _ 15 (by decide))
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [predCmd, predPorts, state_update] using he
  · simpa only [predPorts, state_port] using hv
  · simpa only [predPorts, state_port] using hl
  · simpa only [predPorts, state_port] using ht

theorem arithmetic_valid (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state regs w) := by
  constructor
  · simpa only [arithmeticPorts, state_port] using ho
  · intro i
    apply state_work
    change 10 ≤ 10 + i.val
    omega

theorem multiply_eval (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (multiplyCmd a b o hoa hob) t (state regs w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1)^2 := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state regs w)
      (arithmetic_valid regs w a b o hoa hob ho)
  exact ⟨t, rf, word,
    by simpa only [multiplyCmd, arithmeticPorts, state_update] using he,
    by simpa only [arithmeticPorts, state_port] using hv,
    by simpa only [arithmeticPorts, state_port] using hl,
    by simpa only [arithmeticPorts, state_port] using ht⟩

theorem add_eval (regs : Regs) (w : Words) (a b o : Fin 10)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval (addCmd a b o hoa hob) t (state regs w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1)^2 := by
  obtain ⟨t, rf, word, he, hv, hl, ht⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state regs w)
      (arithmetic_valid regs w a b o hoa hob ho)
  exact ⟨t, rf, word,
    by simpa only [addCmd, arithmeticPorts, state_update] using he,
    by simpa only [arithmeticPorts, state_port] using hv,
    by simpa only [arithmeticPorts, state_port] using hl,
    by simpa only [arithmeticPorts, state_port] using ht⟩

theorem command_eval (regs : Regs) (r Q R : List Bool) :
    ∃ (t : ℕ) (rf : Regs) (w : Words),
      Eval command t (state regs (inputWords r Q R)) (state rf w) ∧
      w 0 = r ∧ w 1 = Q ∧ w 2 = R ∧ w 3 = [] ∧ w 9 = [] ∧
      BinaryArithmetic.toNat (w 6) = (BinaryArithmetic.toNat Q - 1) * (BinaryArithmetic.toNat r - 1) ∧
      BinaryArithmetic.toNat (w 7) = BinaryArithmetic.toNat R * BinaryArithmetic.toNat r ∧ BinaryArithmetic.toNat (w 8) = 2 * BinaryArithmetic.toNat r ∧
      (∀ j, (w j).length ≤ 2 * width r Q R) ∧ t ≤ 1000 * (width r Q R)^2 := by
  let w0 := inputWords r Q R
  let w1 := Function.update w0 4 r
  let r1 := readRegs regs 0 1 none
  have hc1 := copy_eval regs w0 0 4 (by decide) (by rfl)
  obtain ⟨t1, r2, rp, hp1, hv1, hl1, ht1⟩ := pred_eval r1 w1 4
  let w2 := Function.update w1 4 rp
  let w3 := Function.update w2 5 Q
  let r3 := readRegs r2 0 1 none
  have hc2 := copy_eval r2 w2 1 5 (by decide) (by simp [w2, w1, w0, inputWords])
  obtain ⟨t2, r4, qp, hp2, hv2, hl2, ht2⟩ := pred_eval r3 w3 5
  let w4 := Function.update w3 5 qp
  obtain ⟨t3, r5, prod, hm1, hv3, hl3, ht3⟩ :=
    multiply_eval r4 w4 5 4 6 (by decide) (by decide) (by
      simp [w4, w3, w2, w1, w0, inputWords])
  let w5 := Function.update w4 6 prod
  obtain ⟨t4, r6, radius, hm2, hv4, hl4, ht4⟩ :=
    multiply_eval r5 w5 2 0 7 (by decide) (by decide) (by
      simp [w5, w4, w3, w2, w1, w0, inputWords])
  let w6 := Function.update w5 7 radius
  obtain ⟨t5, r7, den, ha, hv5, hl5, ht5⟩ :=
    add_eval r6 w6 0 0 8 (by decide) (by decide) (by
      simp [w6, w5, w4, w3, w2, w1, w0, inputWords])
  let w7 := Function.update w6 8 den
  simp only [w1, Function.update_self] at hv1 hl1 ht1
  simp only [w3, Function.update_self] at hv2 hl2 ht2
  simp [w6, w5, w4, w3, w2, w1, w0, inputWords] at hv3 hl3 ht3 hv4 hl4 ht4 hv5 hl5 ht5
  have he : Eval command ((7 * r.length + 5) + (t1 +
      ((7 * Q.length + 5) + (t2 + (t3 + (t4 + t5))))))
      (state regs w0) (state r7 w7) :=
    hc1.seq (hp1.seq (hc2.seq (hp2.seq (hm1.seq (hm2.seq ha)))))
  refine ⟨_, r7, w7, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
  · simpa [w7, w6, w5, hv1, hv2] using hv3
  · simpa [w7, w6] using hv4
  · simpa [w7, two_mul] using hv5
  · intro j
    fin_cases j <;> simp [w7, w6, w5, w4, w3, w2, w1, w0, inputWords]
    all_goals dsimp [width] at *; omega
  · let W := width r Q R
    have hW : 1 ≤ W := width_pos r Q R
    have hWsq : W ≤ W^2 := by nlinarith
    have h3w : qp.length + rp.length + 1 ≤ W := by dsimp [W, width]; omega
    have h4w : R.length + r.length + 1 ≤ W := by dsimp [W, width]; omega
    have h5w : r.length + r.length + 1 ≤ 2 * W := by dsimp [W, width]; omega
    have hb3 := ht3.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h3w 2))
    have hb4 := ht4.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h4w 2))
    have hb5 := ht5.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left h5w 2))
    have hlr : r.length ≤ W := by dsimp [W, width]; omega
    have hlq : Q.length ≤ W := by dsimp [W, width]; omega
    change _ ≤ 1000 * W^2
    nlinarith only [hb3, hb4, hb5, ht1, ht2, hlr, hlq, hW, hWsq]

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalFinishProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual long division and scratch cleanup for the interval initializer. -/

namespace SubexponentialSAT.SubexpIntervalFinishProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem quotientPorts_injective : Function.Injective quotientPorts := by decide

private theorem embed_quotient (frame r : Regs) (w : Words)
    (remainder numerator quotient : List Bool) :
    embedState id quotientPorts (state frame w)
      ⟨r, ModularQuotientPrograms.quotientStacks remainder (w 8) numerator quotient⟩ =
      divisionState r (Function.update w 3 quotient) remainder numerator := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · exact quotientPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [divisionState, state, quotientPorts,
      ModularQuotientPrograms.quotientStacks]
  · intro i hi
    fin_cases i <;>
      first
      | exact (hi ⟨0, rfl⟩).elim
      | exact (hi ⟨1, rfl⟩).elim
      | exact (hi ⟨2, rfl⟩).elim
      | exact (hi ⟨3, rfl⟩).elim
      | exact (hi ⟨4, rfl⟩).elim
      | exact (hi ⟨5, rfl⟩).elim
      | exact (hi ⟨6, rfl⟩).elim
      | exact (hi ⟨7, rfl⟩).elim
      | simp [divisionState, state]

private theorem divisionState_start (r : Regs) (w : Words) (numerator : List Bool) :
    divisionState r w [] numerator =
      (⟨r, Function.update (state r w).stacks 15 numerator⟩ : Data) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

private theorem divisionState_clear (r : Regs) (w : Words) (remainder : List Bool) :
    (⟨readRegs r 0 1 none,
      Function.update (divisionState r w remainder []).stacks 10 []⟩ : Data) =
      state (readRegs r 0 1 none) w := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext i
  fin_cases i <;> simp [divisionState, state]

theorem division_eval (r : Regs) (w : Words)
    (hd : 0 < BinaryArithmetic.toNat (w 8)) (ho : w 3 = []) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval divisionCmd t (state r w) (state rf (Function.update w 3 word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w 9) / BinaryArithmetic.toNat (w 8) ∧ word.length = (w 9).length ∧
      t ≤ 100 * ((w 8).length + (w 9).length + 1)^2 +
        9 * (w 9).length + 2 * (w 8).length + 8 := by
  have hc := ArithmeticExpressionSupport.copy_eval (port 9) 15 16 (state r w)
    (by decide) (by decide) (by decide)
    (state_work _ _ _ (by decide)) (state_work _ _ _ (by decide))
  let r1 := readRegs r 0 1 none
  have hc' : Eval (ArithmeticExpressionSupport.copyCmd (port 9) 15 16)
      (7 * (w 9).length + 5) (state r w) (divisionState r1 w [] (w 9)) := by
    simpa [state, state_port, divisionState_start, r1] using hc
  obtain ⟨rf, word, rem, hrun, hlen, hrlen, hval, _⟩ :=
    ModularQuotientPrograms.quotient_value r1 (w 8) (w 9) hd
  obtain ⟨t, ht, htrace⟩ := hrun
  have he := eval_call_lifted ModularQuotientPrograms.quotientProgram id quotientPorts
    (state r1 w) Function.injective_id quotientPorts_injective
    (a := ⟨r1, ModularQuotientPrograms.quotientStacks [] (w 8) (w 9) []⟩)
    (b := ⟨rf, ModularQuotientPrograms.quotientStacks rem (w 8) [] word⟩) htrace
  have hw : Function.update w 3 [] = w := by
    rw [← ho]
    exact Function.update_eq_self _ _
  simp only [embed_quotient, hw] at he
  have hclear := ArithmeticExpressionSupport.clear_eval (10 : Fin 32)
    (divisionState rf (Function.update w 3 word) rem [])
  have hclear' : Eval (ArithmeticExpressionSupport.clearCmd 10)
      (2 * rem.length + 3) (divisionState rf (Function.update w 3 word) rem [])
      (state (readRegs rf 0 1 none) (Function.update w 3 word)) := by
    simpa only [divisionState_regs, divisionState_clear, divisionState_ten] using hclear
  refine ⟨_, readRegs rf 0 1 none, word, hc'.seq (he.seq hclear'), hval, hlen, ?_⟩
  omega

theorem clearWords_eval (is : List (Fin 10)) (r : Regs) (w : Words) (B : ℕ)
    (hB : ∀ i, (w i).length ≤ B) :
    ∃ (t : ℕ) (rf : Regs), Eval (clearWords is) t (state r w)
      (state rf (clearedWords is w)) ∧ t ≤ is.length * (2 * B + 3) := by
  induction is generalizing r w with
  | nil => exact ⟨0, r, .base (.skip _), by simp⟩
  | cons i is ih =>
    have hc := ArithmeticExpressionSupport.clear_eval (port i) (state r w)
    have hc' : Eval (ArithmeticExpressionSupport.clearCmd (port i))
        (2 * (w i).length + 3) (state r w)
        (state (readRegs r 0 1 none) (Function.update w i [])) := by
      simpa only [state_port, state_update, state_regs] using hc
    have hB' : ∀ j, (Function.update w i [] j).length ≤ B := by
      intro j
      by_cases h : j = i
      · subst j
        simpa only [Function.update_self, List.length_nil] using Nat.zero_le B
      · simpa [h] using hB j
    obtain ⟨t, rf, he, ht⟩ := ih (readRegs r 0 1 none) (Function.update w i []) hB'
    refine ⟨_, rf, hc'.seq he, ?_⟩
    have := hB i
    simp only [List.length_cons]
    nlinarith

theorem cleanup_eval (regs : Regs) (w : Words) (r Q R word : List Bool)
    (h0 : w 0 = r) (h1 : w 1 = Q) (h2 : w 2 = R) (h3 : w 3 = word)
    (B : ℕ) (hB : ∀ i, (w i).length ≤ B) :
    ∃ (t : ℕ) (rf : Regs), Eval cleanup t (state regs w)
      (state rf (Function.update (inputWords r Q R) 3 word)) ∧
      t ≤ 6 * (2 * B + 3) := by
  obtain ⟨t, rf, he, ht⟩ := clearWords_eval [4, 5, 6, 7, 8, 9] regs w B hB
  have hw : clearedWords [4, 5, 6, 7, 8, 9] w =
      Function.update (inputWords r Q R) 3 word := by
    funext i
    fin_cases i <;> simp [clearedWords, inputWords, h0, h1, h2, h3]
  refine ⟨t, rf, ?_, ht⟩
  simpa only [cleanup, hw] using he

end SubexponentialSAT.SubexpIntervalFinishProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStartProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open BitProgram StructuredCalls BinaryArithmetic
open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem subtractionPorts_injective : Function.Injective subtractionPorts := by decide

private theorem embed_subtraction (frame regs : Regs) (w : Words) (word : List Bool) :
    embedState id subtractionPorts (state frame w)
      (SaturatingSubtractionProgram.state regs (w 6) (w 7) word) =
      state regs (Function.update w 9 word) := by
  apply embedState_eq_of_ports
  · exact Function.injective_id
  · exact subtractionPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> simp [ state, subtractionPorts]
  · intro i hi
    have h9 : i ≠ port 9 := by
      intro h
      exact hi ⟨2, h.symm⟩
    rw [← state_update frame regs w 9 word]
    simp only [Function.update_of_ne h9]

theorem subtraction_eval (regs : Regs) (w : Words) (ho : w 9 = []) :
    ∃ (t : ℕ) (word : List Bool),
      Eval subtractionCmd t (state regs w)
        (state (fun _ => false) (Function.update w 9 word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w 6) - BinaryArithmetic.toNat (w 7) ∧
      word.length ≤ (w 6).length + (w 7).length ∧
      t ≤ 100 * ((w 6).length + (w 7).length + 1) := by
  obtain ⟨t, word, ht, he, hv, hl⟩ :=
    SaturatingSubtractionProgram.command_eval regs (w 6) (w 7)
  have hc := eval_call_lifted SaturatingSubtractionProgram.program id subtractionPorts
    (state regs w) Function.injective_id subtractionPorts_injective
    (compiled_halt_trace he 0 2)
  have hzero : Function.update w 9 [] = w := by
    rw [← ho]
    exact Function.update_eq_self _ _
  simp only [embed_subtraction, hzero] at hc
  exact ⟨t + 1, word, hc, hv, hl, ht⟩

theorem command_eval (regs : Regs) (r Q R : List Bool) (hr : 0 < BinaryArithmetic.toNat r) :
    ∃ (t : ℕ) (rf : Regs) (word : List Bool),
      Eval command t (initialState regs r Q R) (finalState rf r Q R word) ∧
      BinaryArithmetic.toNat word = value (BinaryArithmetic.toNat r) (BinaryArithmetic.toNat Q) (BinaryArithmetic.toNat R) ∧
      word.length ≤ 4 * width r Q R ∧ t ≤ 10000 * (width r Q R)^2 := by
  obtain ⟨t1, r1, w, he1, hw0, hw1, hw2, hw3, hw9, hv6, hv7, hv8, hwidth, ht1⟩ :=
    SubexpIntervalCoreProgram.command_eval regs r Q R
  obtain ⟨t2, num, he2, hvnum, hlnum, ht2⟩ := subtraction_eval r1 w hw9
  let w1 := Function.update w 9 num
  have hd : 0 < BinaryArithmetic.toNat (w1 8) := by simpa [w1, hv8] using Nat.mul_pos (by decide : 0 < 2) hr
  have ho : w1 3 = [] := by simpa [w1] using hw3
  obtain ⟨t3, r3, word, he3, hvword, hlword, ht3⟩ :=
    SubexpIntervalFinishProgram.division_eval (fun _ => false) w1 hd ho
  let w2 := Function.update w1 3 word
  have hnum : num.length ≤ 4 * width r Q R := by
    have h6 := hwidth 6
    have h7 := hwidth 7
    omega
  have hword : word.length ≤ 4 * width r Q R := by
    simpa only [w1, Function.update_self] using hlword.le.trans hnum
  have hw2bound : ∀ i, (w2 i).length ≤ 4 * width r Q R := by
    intro i
    by_cases h3 : i = 3
    · simpa [w2, h3] using hword
    by_cases h9 : i = 9
    · simpa [w2, w1, h9] using hnum
    have hi := hwidth i
    simpa [w2, w1, h3, h9] using hi.trans (by omega : 2 * width r Q R ≤ 4 * width r Q R)
  obtain ⟨t4, r4, he4, ht4⟩ := SubexpIntervalFinishProgram.cleanup_eval r3 w2 r Q R word
    (by simpa [w2, w1] using hw0) (by simpa [w2, w1] using hw1)
    (by simpa [w2, w1] using hw2) (by simp [w2]) (4 * width r Q R) hw2bound
  have he := he1.seq (he2.seq (he3.seq he4))
  refine ⟨t1 + (t2 + (t3 + t4)), r4, word, he, ?_, hword, ?_⟩
  · simpa [value, w1, hvnum, hv6, hv7, hv8] using hvword
  · let W := width r Q R
    have hW : 1 ≤ W := width_pos r Q R
    have hWsq : W ≤ W^2 := by nlinarith
    change t1 ≤ 1000 * W^2 at ht1
    change t4 ≤ 6 * (2 * (4 * W) + 3) at ht4
    have h6 := hwidth 6
    have h7 := hwidth 7
    have h8 := hwidth 8
    change (w 6).length ≤ 2 * W at h6
    change (w 7).length ≤ 2 * W at h7
    have hs : (w1 8).length + (w1 9).length + 1 ≤ 7 * W := by
      simp only [w1, Function.update_self,
        Function.update_of_ne (by decide : (8 : Fin 10) ≠ 9)]
      omega
    have hp := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hs 2)
    have h8' : (w1 8).length ≤ 2 * W := by simpa [w1] using h8
    have h9' : (w1 9).length ≤ 4 * W := by simpa [w1] using hnum
    change _ ≤ 10000 * W^2
    nlinarith only [ht1, ht2, ht3, ht4, hp, h8', h9', h6, h7, hW, hWsq]

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ports_injective : Function.Injective ports := by decide

private theorem project_initial (r : Regs) (w : Words)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[]) :
    projectState id ports (Bank.state r w)=
      SubexpIntervalStartProgram.initialState r (w 18) (w 21) (w 29) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [ports,Bank.state,
        SubexpIntervalCoreProgram.inputWords]
    all_goals apply hc; decide

private theorem embed_final (r rf : Regs) (w : Words) (word : List Bool)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[]) :
    embedState id ports (Bank.state r w)
      (SubexpIntervalStartProgram.finalState rf (w 18) (w 21) (w 29) word)=
        Bank.state rf (Function.update w 46 word) := by
  apply embedState_eq_of_ports id ports (Bank.state r w) _ _
    Function.injective_id ports_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    fin_cases i <;>
      simp [ports,Bank.state,SubexpIntervalStartProgram.finalState,
        SubexpIntervalCoreProgram.state,SubexpIntervalCoreProgram.inputWords]
    all_goals apply hc; decide
  · intro i hi
    have ho : i≠Bank.port 46 := by
      intro he
      exact hi ⟨3,by simpa [ports,Bank.port] using he.symm⟩
    rw [← Bank.state_update r rf w 46 word]
    simp only [Function.update_of_ne ho]

theorem at_eval_oai (r : Regs) (w : Words)
    (hc : ∀ a : Fin 64, 46 ≤ a.val → w a=[])
    (hr : 0 < BinaryArithmetic.toNat (w 18)) :
    ∃ t rf word, Eval intervalAt t (Bank.state r w)
        (Bank.state rf (Function.update w 46 word)) ∧
      BinaryArithmetic.toNat word=Subexp.TailInterval.intervalStart
        (BinaryArithmetic.toNat (w 18)) (BinaryArithmetic.toNat (w 21)) (BinaryArithmetic.toNat (w 29)) ∧
      word.length ≤ 4*((w 18).length+(w 21).length+(w 29).length+1) ∧
      t ≤ 10000*((w 18).length+(w 21).length+(w 29).length+1)^2+1 := by
  obtain ⟨t,rf,word,he,hv,hl,ht⟩ := SubexpIntervalStartProgram.command_eval
    r (w 18) (w 21) (w 29) hr
  have hp := project_initial r w hc
  have htrace := compiled_halt_trace he (0 : Fin 32) 3
  rw [← hp] at htrace
  have hh := eval_call_from_state SubexpIntervalStartProgram.program id ports
    (Bank.state r w) Function.injective_id ports_injective htrace
  rw [embed_final r rf w word hc] at hh
  refine ⟨t+1,rf,word,hh,?_,hl,Nat.add_le_add_right ht 1⟩
  exact hv.trans (SubexpIntervalStart.value_eq_intervalStart _ _ _ hr)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval_oai
