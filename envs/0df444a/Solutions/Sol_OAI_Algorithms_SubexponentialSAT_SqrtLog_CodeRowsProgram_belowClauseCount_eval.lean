-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:32:40.677242+00:00
-- url     : https://prove2.me/submissions/ab4f5c1a-fe96-48e1-a8ba-3fb4c6a5890f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118

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

end SubexponentialSAT.SaturatingSubtractionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving binary comparison for filtering the shortened code's columns.
The instruction table uses padding and borrow, with no numeric comparison
primitive and no traversal of the original column universe. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic
open SubexponentialSAT.SaturatingSubtractionProgram

theorem core_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf word, Eval core (50*(xs.length+ys.length)+49)
      (state regs xs ys []) (state rf xs ys word) ∧
      (rf 0=true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) ∧ word.length=xs.length+ys.length := by
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
  refine ⟨r₃,diff,?_,?_,?_⟩
  · have he := (prepare_eval regs xs ys).seq (hp₁.seq (hp₂.seq (hs.seq hd)))
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    simp [a,b,d,px,py,shape,leftPorts,rightPorts,subtractPorts,padTo_length]
    omega
  · rw [hb,subCarry_borrow_iff px py hlen,padTo_correct shape xs hx,padTo_correct shape ys hy]
  · exact (subCarry_length false px py hlen).trans (by simp [px,shape,padTo_length])

theorem command_eval (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf, Eval command (52*(xs.length+ys.length)+53)
      (state regs xs ys []) (state rf xs ys []) ∧
      (rf 7=true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rr,word,he,hflag,hwidth⟩ := core_eval regs xs ys
  let r1 := Function.update rr 7 (rr 0)
  have hsave : Eval (.base (.atom (.copy 7 0))) 1
      (state rr xs ys word) (state r1 xs ys word) := .base (.atom _ _)
  have hclear := Subexp.TupleProgram.clear_eval (2 : Fin 8) (0 : Fin 8) 1
    (state r1 xs ys word)
  let rf := readRegs r1 0 1 none
  have hfinal : (⟨rf,StackRoutines.clearStacks 2 (state r1 xs ys word).stacks⟩ : State 8 8)=
      state rf xs ys [] := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;> simp [StackRoutines.clearStacks]
  change Eval clearOutput (2*word.length+3) (state r1 xs ys word)
    ⟨rf,StackRoutines.clearStacks 2 (state r1 xs ys word).stacks⟩ at hclear
  rw [hfinal] at hclear
  refine ⟨rf,?_,?_⟩
  · convert he.seq (hsave.seq hclear) using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · simpa [rf,r1,readRegs] using hflag

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls SubexponentialSAT.BinaryArithmetic

theorem low8_injective : Function.Injective low8 := Fin.castAdd_injective _ _

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCompareCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

theorem belowClauseCount_eval_oai (d : Data)
    (hw : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[]) :
    ∃ rf, Eval belowClauseCount (52*((d.stacks 21).length+(d.stacks 4).length)+54)
      d ⟨rf,d.stacks⟩ ∧
      (rf 7=true ↔ BinaryArithmetic.toNat (d.stacks 21) < BinaryArithmetic.toNat (d.stacks 4)) ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have h33 : d.stacks 33=[] := hw 2 (by decide)
  have h34 : d.stacks 34=[] := hw 3 (by decide)
  have h35 : d.stacks 35=[] := hw 4 (by decide)
  have h36 : d.stacks 36=[] := hw 5 (by decide)
  have h37 : d.stacks 37=[] := hw 6 (by decide)
  have h38 : d.stacks 38=[] := hw 7 (by decide)
  obtain ⟨rr,he,hflag⟩ := Compare.command_eval (d.regs ∘ low8) (d.stacks 21) (d.stacks 4)
  let a := SaturatingSubtractionProgram.state (d.regs ∘ low8) (d.stacks 21) (d.stacks 4) []
  let b := SaturatingSubtractionProgram.state rr (d.stacks 21) (d.stacks 4) []
  have hin : embedState low8 compareStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective compareStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [a,
        compareStacks,h33,h34,h35,h36,h37,h38]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d.regs
  have hout : embedState low8 compareStacks d b=(⟨rf,d.stacks⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective compareStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i
      fin_cases i <;> simp [b,
        compareStacks,h33,h34,h35,h36,h37,h38]
    · intro i hi; rfl
  have ht : Trace Compare.program (52*((d.stacks 21).length+(d.stacks 4).length)+54)
      (a.withPC (some Compare.program.entry)) (b.withPC none) := by
    convert compiled_halt_trace he 0 1 using 1
    all_goals try with_reducible_and_instances rfl
  have hl := eval_call_lifted Compare.program low8 compareStacks d
    low8_injective compareStacks_injective ht
  refine ⟨rf,by simpa only [hin,hout] using hl,?_,?_⟩
  · have h7 : rf 7=rr 7 := low8_injective.extend_apply rr d.regs 7
    simpa [h7] using hflag
  · intro i hi
    apply Function.extend_apply'
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low8] at hv
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.belowClauseCount_eval_oai
