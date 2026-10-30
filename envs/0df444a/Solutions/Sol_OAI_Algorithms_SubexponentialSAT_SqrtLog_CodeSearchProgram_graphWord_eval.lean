-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:18:47.704806+00:00
-- url     : https://prove2.me/submissions/75670cf7-c411-4e78-be49-35a9c14115b2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S089
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchProgram_graphCounts_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeSearchWalshProgram_prepare_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

open StructuredProgram

private theorem workRegister_injective : Function.Injective workRegister := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 9 => x.val) h

private theorem pairStack_injective (j : Fin 3) : Function.Injective (pairStack j) := by
  intro i k h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [pairStack] at this
  omega

private theorem accumulator_not_work : ¬ ∃ i, workRegister i = (8 : Fin 9) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  change i.val = 8 at this
  have hi := i.isLt
  omega

/-- Concrete comparison-and-accumulation contract. Pair operands are consumed;
all other stacks, including a caller's retained copies, are preserved. -/
theorem checkPair_eval (j : Fin 3) (a : State 9 6) :
    ∃ b : State 9 6, StructuredCalls.Eval (checkPair j) (pairCost j a) a b ∧
      b.regs 8 = (a.regs 8 && pairPass j a) ∧
      (∀ i, (¬ ∃ h, pairStack j h = i) → b.stacks i = a.stacks i) ∧
      (∀ h, b.stacks (pairStack j h) = []) := by
  obtain ⟨mid, hrun, hcmp, hregs, hstacks, hclear⟩ :=
    compare_call workRegister (pairStack j) workRegister_injective (pairStack_injective j) a
  let inv := (Atom.bnot (0 : Fin 9) 0).eval mid
  let b := (Atom.band (8 : Fin 9) 8 0).eval inv
  have heval : StructuredProgram.Eval
      (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))) 2 mid b :=
    .seq (.atom _ _) (.atom _ _)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.Eval.seq hrun (StructuredCalls.Eval.base heval)
    simpa only [checkPair, pairCost, Nat.add_assoc] using h
  · have hacc := hregs 8 accumulator_not_work
    have hbool : (!mid.regs 0) = pairPass j a := by
      change mid.regs 0 = true ↔ _ at hcmp
      cases hm : mid.regs 0 with
      | false =>
        have hn : BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) := by
          have hnot : ¬ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) < BinaryArithmetic.toNat (a.stacks (pairStack j 1)) := by
            simpa [hm] using hcmp.symm
          omega
        simp [ pairPass, hn]
      | true =>
        have hn : ¬ BinaryArithmetic.toNat (a.stacks (pairStack j 1)) ≤ BinaryArithmetic.toNat (a.stacks (pairStack j 0)) := by
          have hlt := hcmp.mp hm
          omega
        simp [ pairPass, hn]
    simp [b, inv, Atom.eval, Atom.instr, State.ofCfg,
      execInstr, hacc, hbool]
  · intro i hi
    exact hstacks i hi
  · exact hclear


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem checkStacks_injective : Function.Injective checkStacks := by decide

theorem check_eval (j : Fin 2) (d : Data) :
    ∃ e : Data, Eval (check j)
      (10 * max (d.stacks (pairPorts j 0)).length (d.stacks (pairPorts j 1)).length + 9) d e ∧
      e.regs 8 = (d.regs 8 && decide
        (BinaryArithmetic.toNat (d.stacks (pairPorts j 1)) ≤ BinaryArithmetic.toNat (d.stacks (pairPorts j 0)))) ∧
      (∀ i, i ≠ pairPorts j 0 → i ≠ pairPorts j 1 → e.stacks i = d.stacks i) ∧
      (∀ i, e.stacks (pairPorts j i) = []) := by
  let a := projectState id checkStacks d
  obtain ⟨b, he, ho, hf, hz⟩ := SubexpGuardProgram.checkPair_eval (Fin.castAdd 1 j) a
  let e := embedState id checkStacks d b
  have hs (i : Fin 6) : e.stacks (checkStacks i) = b.stacks i :=
    embedState_stack id checkStacks d b checkStacks_injective i
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · have h := eval_liftCommand_from_state (SubexpGuardProgram.checkPair (Fin.castAdd 1 j))
      0 0 id checkStacks d Function.injective_id checkStacks_injective he
    simpa [check, SubexpGuardProgram.pairCost, a, projectState, pairPorts, Nat.add_assoc] using h
  · rw [show e.regs 8 = b.regs 8 from embedState_register id checkStacks d b Function.injective_id 8]
    exact ho
  · intro i hi0 hi1
    by_cases hm : ∃ k, checkStacks k = i
    · obtain ⟨k, rfl⟩ := hm
      rw [hs]
      apply hf
      rintro ⟨z, hz'⟩
      have heq := congrArg checkStacks hz'
      fin_cases z
      · exact hi0 heq.symm
      · exact hi1 heq.symm
    · exact embedState_stack_frame id checkStacks d b i hm
  · intro i; rw [show e.stacks (pairPorts j i) = b.stacks (SubexpGuardProgram.pairStack (Fin.castAdd 1 j) i) from hs _]
    exact hz i

theorem clearCount_eval (d : Data) :
    Eval clearCount (2 * (d.stacks 3).length + 3) d (cleared d) :=
  .call _ (ListRegisterProgram.clear_run 3 0 1 d.regs d.stacks)

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem init_eval (d : Data) : Eval (.base (.atom (.set 8 true))) 1 d (init d) := by
  simpa [init, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (.set (8 : Fin 9) true) d)

theorem command_eval (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 700 * (2 * size d + 4)^2, ∃ z : Data,
      Eval command t d z ∧ z.regs 8 = pass d ∧ z.stacks = d.stacks := by
  obtain ⟨tp, htp, p, hp, hv3, hv4, hv5, hv6, hv7, hlen, hframe⟩ := prepare_eval d hd
  let a := init p
  have ha := init_eval p
  obtain ⟨b, hb, hbr, hbf, hbz⟩ := check_eval 0 a
  obtain ⟨c, hc, hcr, hcf, hcz⟩ := check_eval 1 b
  let z := cleared c
  have hz := clearCount_eval c
  have hb5 : b.stacks 5 = p.stacks 5 := hbf 5 (by decide) (by decide)
  have hb7 : b.stacks 7 = p.stacks 7 := hbf 7 (by decide) (by decide)
  have hc3 : c.stacks 3 = p.stacks 3 :=
    (hcf 3 (by decide) (by decide)).trans (hbf 3 (by decide) (by decide))
  have ht0 : 10 * max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length + 9 ≤
      10 * (2 * size d + 4) + 9 := by
    have h := max_le (hlen 6 (by decide) (by decide)) (hlen 4 (by decide) (by decide))
    change max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length ≤ _ at h
    omega
  have ht1 : 10 * max (b.stacks (pairPorts 1 0)).length (b.stacks (pairPorts 1 1)).length + 9 ≤
      10 * (2 * size d + 4) + 9 := by
    change 10 * max (b.stacks 7).length (b.stacks 5).length + 9 ≤ _
    rw [hb7, hb5]
    have h := max_le (hlen 7 (by decide) (by decide)) (hlen 5 (by decide) (by decide))
    omega
  have hcl : (c.stacks 3).length ≤ 2 * size d + 4 := by
    rw [hc3]; exact hlen 3 (by decide) (by decide)
  refine ⟨tp + (1 + ((10 * max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length + 9) +
    ((10 * max (b.stacks (pairPorts 1 0)).length (b.stacks (pairPorts 1 1)).length + 9) +
      (2 * (c.stacks 3).length + 3)))), ?_, z, hp.seq (ha.seq (hb.seq (hc.seq hz))), ?_, ?_⟩
  · nlinarith only [htp, ht0, ht1, hcl, Nat.zero_le (size d)]
  · have hpa : a.regs 8 = true := by simp [a, init]
    change b.regs 8 = (a.regs 8 && decide (BinaryArithmetic.toNat (a.stacks 4) ≤ BinaryArithmetic.toNat (a.stacks 6))) at hbr
    change c.regs 8 = (b.regs 8 && decide (BinaryArithmetic.toNat (b.stacks 5) ≤ BinaryArithmetic.toNat (b.stacks 7))) at hcr
    have hcv : c.regs 8 = pass d := by
      rw [hcr, hbr, hpa, hb5, hb7]
      change ((true && decide (BinaryArithmetic.toNat (p.stacks 4) ≤ BinaryArithmetic.toNat (p.stacks 6))) &&
        decide (BinaryArithmetic.toNat (p.stacks 5) ≤ BinaryArithmetic.toNat (p.stacks 7))) = pass d
      rw [hv4, hv5, hv6, hv7]
      unfold pass good
      by_cases h₁ : BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ≤
          BinaryArithmetic.toNat (d.stacks 1) +
            2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length
      · by_cases h₂ : 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ≤
            BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) +
              BinaryArithmetic.toNat (d.stacks 1) <;> simp [h₁, h₂]
      · simp [h₁]
    simpa [z, cleared, readRegs] using hcv
  · funext j
    by_cases hj3 : j = 3
    · subst j; simp [z, cleared, hd 3 (by decide)]
    have hzc : z.stacks j = c.stacks j := by simp [z, cleared, hj3]
    rw [hzc]
    by_cases hj5 : j = 5
    · subst j; exact (hcz 1).trans (hd 5 (by decide)).symm
    by_cases hj7 : j = 7
    · subst j; exact (hcz 0).trans (hd 7 (by decide)).symm
    rw [hcf j hj7 hj5]
    by_cases hj4 : j = 4
    · subst j; exact (hbz 1).trans (hd 4 (by decide)).symm
    by_cases hj6 : j = 6
    · subst j; exact (hbz 0).trans (hd 6 (by decide)).symm
    rw [hbf j hj6 hj4]
    apply hframe j
    have h3 : j.val ≠ 3 := by intro h; apply hj3; exact Fin.ext h
    have h4 : j.val ≠ 4 := by intro h; apply hj4; exact Fin.ext h
    have h5 : j.val ≠ 5 := by intro h; apply hj5; exact Fin.ext h
    have h6 : j.val ≠ 6 := by intro h; apply hj6; exact Fin.ext h
    have h7 : j.val ≠ 7 := by intro h; apply hj7; exact Fin.ext h
    omega

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- The only retained result is the designated Boolean flag. Every caller stack
and every register outside the fixed local register image are preserved. -/
theorem command_lifted {R S : ℕ} (register : Fin 9 → Fin R) (stack : Fin 14 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks (stack j) = []) :
    ∃ t ≤ 700 * (2 * size (projectState register stack d) + 4)^2 + 1,
    ∃ e : State R S,
      Eval (liftCommand command 0 0 register stack) t d e ∧
      e.regs (register 8) = pass (projectState register stack d) ∧
      e.stacks = d.stacks ∧
      (∀ j, (¬ ∃ i, register i = j) → e.regs j = d.regs j) := by
  obtain ⟨t, ht, b, he, ho, hf⟩ := command_eval (projectState register stack d) hd
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state command 0 0 register stack d hr hs he, ?_, ?_, ?_⟩
  · simpa only [embedState_register register stack d b hr 8] using ho
  · funext j
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i, hf]
      rfl
    · exact embedState_stack_frame register stack d b j hm
  · exact fun j hj => embedState_register_frame register stack d b j hj

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One complete Walsh query, executed by a fixed program. The inputs contain
an actual binary matrix, a binary character, and binary words for q and D.
No integer inequality is an instruction: the final comparison invokes the
count/arithmetic/guard routine with its measured bit trace. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

theorem graphCheckStacks_injective : Function.Injective graphCheckStacks := by decide

theorem parityWeight_le {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r) :
    WalshExistence.parityWeight s a ≤ D := by
  unfold WalshExistence.parityWeight
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- All helper scratch stacks are restored, and the two binary scalar sources
are preserved. The designated Boolean result means this character rejects
this candidate graph. -/
theorem graphWord_eval_oai {r D : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hq : BinaryArithmetic.toNat qbits = q) (hD : BinaryArithmetic.toNat Dbits = D)
    (a : GraphWordState)
    (hin : projectState graphCountRegisters graphCountStacks a =
      extendPairState (matrixInput s x (a.regs ∘ graphCountRegisters)) qbits Dbits)
    (hclean : ∀ i : Fin 29, 18 ≤ i.val → a.stacks i = []) :
    ∃ (n : ℕ) (out : GraphWordState), n + 1 ≤ graphWordBudget D r qbits.length Dbits.length ∧
      Eval graphWordCommand n a out ∧ out.regs 15 = decide (graphWordRejects s x q) ∧
      out.stacks 16 = qbits ∧ out.stacks 17 = Dbits ∧
      (∀ i : Fin 29, 18 ≤ i.val → out.stacks i = []) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 := by
  obtain ⟨nc,c,hnc,hec,hcn,hch,hcq,hcD⟩ :=
    graphCounts_eval s x (a.regs ∘ graphCountRegisters) qbits Dbits
  rw [← hin] at hec
  let b := embedState graphCountRegisters graphCountStacks a c
  have hb := eval_liftCommand_from_state graphCountsCommand 11 9
    graphCountRegisters graphCountStacks a (Fin.castAdd_injective _ _)
      (Fin.castAdd_injective _ _) hec
  have hbreg (i : Fin 16) (hi : 8 ≤ i.val) : b.regs i = a.regs i := by
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphCountRegisters] at hv
    omega
  have hbstack (i : Fin 29) (hi : 18 ≤ i.val) : b.stacks i = a.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphCountStacks] at hv
    omega
  have hbq : b.stacks 16 = qbits :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 16).trans hcq
  have hbD : b.stacks 17 = Dbits :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 17).trans hcD
  have hbh : b.stacks 9 = List.replicate (WalshExistence.parityWeight s x) true :=
    (embedState_stack graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 9).trans hch
  have hbn : b.regs 7 = decide (x ≠ 0) :=
    (embedState_register graphCountRegisters graphCountStacks a c
      (Fin.castAdd_injective _ _) 7).trans hcn
  let flagged := (Atom.copy 15 7).eval b
  have hfclean (j : Fin 14) (hj : 3 ≤ j.val) :
      flagged.stacks (graphCheckStacks j) = [] := by
    change b.stacks (graphCheckStacks j) = []
    have hidx : 18 ≤ (graphCheckStacks j).val := by
      revert hj
      fin_cases j <;> decide
    exact (hbstack _ hidx).trans (hclean _ hidx)
  obtain ⟨nh,hnh,e,he,hef,hes,her⟩ := CodeSearchWalshProgram.command_lifted
    graphCheckRegisters graphCheckStacks (Fin.castAdd_injective _ _)
      graphCheckStacks_injective flagged hfclean
  have hsize : CodeSearchWalshProgram.size
      (projectState graphCheckRegisters graphCheckStacks flagged) =
        qbits.length + Dbits.length + WalshExistence.parityWeight s x := by
    simp [CodeSearchWalshProgram.size,CodeSearchWalshProgram.inputLength,projectState,graphCheckStacks,
      flagged,Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,hbq,hbD,hbh]
  have hpass : e.regs 8 = decide (CodeSearchWalshProgram.good q D
      (WalshExistence.parityWeight s x)) := by
    simpa [CodeSearchWalshProgram.pass,projectState,graphCheckRegisters,graphCheckStacks,
      flagged,Atom.eval,Atom.instr,execInstr,StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC,hbq,hbD,hbh,hq,hD] using hef
  have her15 : e.regs 15 = decide (x ≠ 0) := by
    rw [her 15 (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [graphCheckRegisters] at hv
      omega)]
    exact hbn
  let negated := (Atom.bnot 8 8).eval e
  let out := (Atom.band 15 15 8).eval negated
  have houtst : out.stacks = b.stacks := hes
  have houtreg (i : Fin 16) (hi8 : i ≠ 8) (hi15 : i ≠ 15) (hi9 : 9 ≤ i.val) :
      out.regs i = a.regs i := by
    have hri : e.regs i = flagged.regs i := her i (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [graphCheckRegisters] at hv
      omega)
    simp [out,negated,flagged,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,hi8,hi15,hri,
      hbreg i (by omega)]
  refine ⟨nc+1+(1+(nh+(1+1))),out,?_,
    hb.seq ((Eval.base (.atom _ b)).seq (he.seq
      ((Eval.base (.atom _ e)).seq (Eval.base (.atom _ negated))))),?_,?_,?_,?_,?_,?_⟩
  · rw [hsize] at hnh
    have hp := parityWeight_le s x
    have hsquare : (2 * (qbits.length + Dbits.length + WalshExistence.parityWeight s x) + 4)^2 ≤
        (2 * (qbits.length + Dbits.length + D) + 4)^2 := Nat.pow_le_pow_left (by omega) 2
    unfold graphWordBudget
    omega
  · simp [out,negated,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,hpass,her15,graphWordRejects]
    apply Bool.eq_iff_iff.mpr
    simp
    by_cases h : x ≠ 0 ∧ ¬ CodeSearchWalshProgram.good q D
        (WalshExistence.parityWeight s x)
    · simp [h]
    · simp [h]
  · rw [congrFun houtst 16]; exact hbq
  · rw [congrFun houtst 17]; exact hbD
  · intro i hi
    rw [congrFun houtst i,hbstack i hi]
    exact hclean i hi
  · exact houtreg 13 (by decide) (by decide) (by decide)
  · exact houtreg 14 (by decide) (by decide) (by decide)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval_oai
