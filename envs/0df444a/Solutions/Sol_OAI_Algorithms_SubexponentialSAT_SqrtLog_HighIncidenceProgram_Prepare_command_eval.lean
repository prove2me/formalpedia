-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:46:53.289799+00:00
-- url     : https://prove2.me/submissions/c64ca460-8d2d-4d19-87b6-c23ab0b467be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_MassPreserve_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_Prepare_cutoff_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HighIncidenceProgram_scan_eval

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

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

theorem counterReg_injective : Function.Injective counterReg := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem counterStack_injective : Function.Injective counterStack := by decide

theorem countCall_eval (records : List (List Bool)) (d : Data)
    (hi : d.stacks 14 = Encoding.encodeList id records) (ho : d.stacks 2 = []) :
    ∃ e : Data, Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 14 []) 2 (List.replicate records.length true) := by
  let a := counterState (d.regs 0) (d.regs 1) (Encoding.encodeList id records) []
  let b := counterState false false [] (List.replicate records.length true)
  have ha : a = projectState counterReg counterStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [ counterStack, ParserProgram.pair, hi, ho]
  have ht := counter_trace records (d.regs 0) (d.regs 1)
  change Trace counterProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state counterProgram counterReg counterStack d
    counterReg_injective counterStack_injective ht
  let e := embedState counterReg counterStack d b
  have hs (i : Fin 2) : e.stacks (counterStack i) = b.stacks i :=
    embedState_stack _ _ _ _ counterStack_injective i
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h14 : i = 14
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 0
  by_cases h2 : i = 2
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 1
  · rw [embedState_stack_frame counterReg counterStack d b i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [counterStack] at hj <;> simp_all)]
    simp [h14, h2]

theorem count_eval (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = []) (h14 : d.stacks 14 = []) :
    ∃ rf : Fin 8 → Bool,
      Eval countCommand (countBudget records) d
        ⟨rf, Function.update d.stacks 2 (List.replicate records.length true)⟩ := by
  let a := ArithmeticCalls.afterCopy 1 14 d
  have ha14 : a.stacks 14 = Encoding.encodeList id records := by
    simp [a, ArithmeticCalls.afterCopy, hs]
  have ha2 : a.stacks 2 = [] := by simpa [a, ArithmeticCalls.afterCopy] using h2
  obtain ⟨e, he, hstacks⟩ := countCall_eval records a ha14 ha2
  have heq : e.stacks = Function.update d.stacks 2 (List.replicate records.length true) := by
    rw [hstacks]
    funext i
    by_cases hi2 : i = 2
    · subst i; simp
    by_cases hi14 : i = 14
    · subst i; simp [h14]
    · simp [a, ArithmeticCalls.afterCopy, hi2, hi14]
  have heq' : e = (⟨e.regs, Function.update d.stacks 2 (List.replicate records.length true)⟩ : Data) :=
    congrArg (fun stk => (⟨e.regs, stk⟩ : Data)) heq
  have hcopy := ArithmeticCalls.copyAt_eval (1 : Fin 15) 14 5 d
    (by decide) (by decide) (by decide) h14 h5
  have hrun := hcopy.seq he
  rw [heq'] at hrun
  refine ⟨e.regs, ?_⟩
  simpa only [countCommand, countBudget, hs] using hrun

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Serialized scope adapter and complete bit cost for the nested counter.
The counter counts supplied entries; the caller's normalization invariant is
what identifies this with distinct factor-variable incidence mass. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem encode_map_nat (xs : List ℕ) :
    encode (xs.map Encoding.encodeNat) = Encoding.encodeList Encoding.encodeNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, encode, Encoding.encodeList, id_eq, ih]

theorem encoded_scopeRecords (scopes : List (List ℕ)) :
    encode ((scopeRecords scopes).map encode) = SubexpIncidenceSlotProgram.scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons xs xss ih =>
      simpa only [scopeRecords, List.map_cons, encode, Encoding.encodeList,
        id_eq, encode_map_nat, SubexpIncidenceSlotProgram.scopeBits,
        SubexpIncidenceSlotProgram.scopeBytes, SubexpIncidencePlanScan.scopeBytes] using
        congrArg (fun tail => true :: (Encoding.frame
          (Encoding.encodeList Encoding.encodeNat xs) ++ tail)) ih

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareUtil
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Small framing lemma for the fixed high-incidence preparation calls. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lift_update {r s R S : ℕ} (c : Cmd r s) (input output : Fin s)
    (reg : Fin r → Fin R) (stk : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (j : Fin s) (word : List Bool) (rf : Fin r → Bool) (time : ℕ)
    (he : Eval c time (projectState reg stk d)
      ⟨rf, Function.update (projectState reg stk d).stacks j word⟩) :
    ∃ regs, Eval (liftCommand c input output reg stk) (time + 1) d
      ⟨regs, Function.update d.stacks (stk j) word⟩ := by
  have h := eval_liftCommand_from_state c input output reg stk d hr hs he
  let b := embedState reg stk d
    (⟨rf, Function.update (projectState reg stk d).stacks j word⟩ : State r s)
  have hb : b.stacks = Function.update d.stacks (stk j) word := by
    change Function.extend stk (Function.update _ j word) d.stacks = _
    rw [ProgramLinking.extend_update hs]
    have hp : Function.extend stk (projectState reg stk d).stacks d.stacks = d.stacks :=
      congrArg StructuredProgram.State.stacks (embedState_project reg stk d hr hs)
    rw [hp]
  refine ⟨b.regs, ?_⟩
  change Eval _ _ d b at h
  have hb' : b = (⟨b.regs, Function.update d.stacks (stk j) word⟩ : State R S) :=
    congrArg (fun stkOut => (⟨b.regs, stkOut⟩ : State R S)) hb
  rwa [hb'] at h

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed ports for the physical high-incidence prefix. Each operation below
is a genuine call to an already verified finite program. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem reg8_inj : Function.Injective reg8 := Fin.castAdd_injective _ _
theorem reg3_inj : Function.Injective reg3 := Fin.castAdd_injective _ _

theorem countPorts_inj : Function.Injective countPorts := by decide
theorem massPorts_inj : Function.Injective massPorts := by decide
theorem binaryPorts_inj : Function.Injective binaryPorts := by decide
theorem unaryPorts_inj : Function.Injective unaryPorts := by decide
theorem fuelPorts_inj : Function.Injective fuelPorts := by decide

theorem count_eval (d : Data) (records : List (List Bool))
    (h0 : d.stacks 0 = Encoding.encodeList id records)
    (h1 : d.stacks 1 = []) (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = []) :
    ∃ rf, Eval countCall (SubexpScopeCountSetup.countBudget records + 1) d
      ⟨rf, Function.update d.stacks 1 (List.replicate records.length true)⟩ := by
  obtain ⟨rf, he⟩ := SubexpScopeCountSetup.count_eval records (projectState reg8 countPorts d)
    h0 h1 h21 h22
  exact lift_update _ 1 2 reg8 countPorts d reg8_inj countPorts_inj 2 _ rf _ he

theorem mass_eval (d : Data) (scopes : List (List ℕ))
    (h0 : d.stacks 0 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (h18 : d.stacks 18 = []) (h21 : d.stacks 21 = [])
    (h22 : d.stacks 22 = []) (h23 : d.stacks 23 = []) :
    ∃ time rf, Eval massCall time d
      ⟨rf, Function.update d.stacks 18 (List.replicate ((scopes.map List.length).sum) true)⟩ ∧
      time ≤ MassPreserve.bound (SubexpIncidenceSlotProgram.scopeBits scopes) := by
  let a := projectState reg8 massPorts d
  have ha : a = MassPreserve.state a.regs (SubexpIncidenceSlotProgram.scopeBits scopes) [] := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;> simp [ massPorts, h0, h18, h21, h22, h23]
  obtain ⟨time, rf, he, ht⟩ := MassPreserve.command_eval a.regs scopes
  have hs : (MassPreserve.state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
      (List.replicate ((scopes.map List.length).sum) true)).stacks =
      Function.update a.stacks 2 (List.replicate ((scopes.map List.length).sum) true) := by
    rw [ha]
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [← ha] at he
  have hb : MassPreserve.state rf (SubexpIncidenceSlotProgram.scopeBits scopes)
      (List.replicate ((scopes.map List.length).sum) true) =
      (⟨rf, Function.update a.stacks 2 (List.replicate ((scopes.map List.length).sum) true)⟩ : MassPreserve.Data) :=
    congrArg (StructuredProgram.State.mk rf) hs
  rw [hb] at he
  obtain ⟨r, hr⟩ := lift_update _ 0 2 reg8 massPorts d reg8_inj massPorts_inj 2 _ rf time he
  exact ⟨time + 1, r, hr, ht⟩

theorem binary_eval (d : Data) (h19 : d.stacks 19 = [])
    (h21 : d.stacks 21 = []) (h22 : d.stacks 22 = []) :
    ∃ time rf bits, Eval binaryCall time d ⟨rf, Function.update d.stacks 19 bits⟩ ∧
      time ≤ SubexpFactorCountSetup.countBudget (d.stacks 18).length + 1 ∧
      BinaryArithmetic.toNat bits = (d.stacks 18).length ∧ bits.length ≤ (d.stacks 18).length := by
  obtain ⟨time, ht, rf, bits, he, hv, hl⟩ :=
    SubexpFactorCountSetup.count_eval (projectState reg8 binaryPorts d) h19 h21 h22
  obtain ⟨r, hr⟩ := lift_update _ 1 2 reg8 binaryPorts d reg8_inj binaryPorts_inj 2 bits rf time he
  exact ⟨time + 1, r, bits, hr, Nat.add_le_add_right ht 1, hv, hl⟩

theorem unary_eval (ports : Fin 14 → Fin 32) (hi : Function.Injective ports)
    (d : Data) (h1 : d.stacks (ports 1) = [])
    (h11 : d.stacks (ports 11) = []) (h12 : d.stacks (ports 12) = [])
    (h13 : d.stacks (ports 13) = []) :
    ∃ time rf, Eval (liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 ports)
      time d ⟨rf, Function.update d.stacks (ports 1)
        (List.replicate (BinaryArithmetic.toNat (d.stacks (ports 0))) true)⟩ ∧
      time ≤ SubexpClauseMastersProgram.unaryCopyBound (d.stacks (ports 0)) + 1 := by
  obtain ⟨time, ht, he⟩ := SubexpClauseMastersProgram.unaryCopy_eval 0 1
    (projectState reg3 ports d) (by decide) (by decide) (by decide) (by decide)
    h1 h11 h12 h13
  simp only [SubexpClauseMastersProgram.write, SubexpClauseMastersProgram.unary,
    CounterPrograms.value_eq_toNat] at he
  obtain ⟨rf, hr⟩ := lift_update _ 0 1 reg3 ports d reg3_inj hi 1 _ _ time he
  exact ⟨time + 1, rf, hr, Nat.add_le_add_right ht 1⟩

theorem bump_eval (d : Data) :
    Eval bump 2 d ⟨Function.update d.regs 0 true,
      Function.update d.stacks 13 (true :: d.stacks 13)⟩ :=
  (Eval.base (.atom _ _)).seq (Eval.base (.atom _ _))

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem scanPorts_inj : Function.Injective scanPorts := Fin.castAdd_injective _ _
theorem unaryBound_le (bits : List Bool) (value size : ℕ)
    (hv : BinaryArithmetic.toNat bits = value) (hl : bits.length ≤ size) :
    SubexpClauseMastersProgram.unaryCopyBound bits + 1 ≤ unarySized value size := by
  simp only [SubexpClauseMastersProgram.unaryCopyBound, CounterConversions.runtimeBound,
    CounterPrograms.value_eq_toNat, hv, unarySized]
  gcongr

theorem records_bits (scopes : List (List ℕ)) :
    Encoding.encodeList id (records scopes) = scopeBits scopes :=
  Mass.encoded_scopeRecords scopes
theorem records_length (scopes : List (List ℕ)) : (records scopes).length = scopes.length := by
  simp [records, Mass.scopeRecords]

/-- Full prefix trace. Persistent input words and source scopes are retained;
output14 is the mask, output2 is unary n, and output13 is unary(cut+1).
Computed E1, unary S18, binary S19 and cutoff20 remain in their work ports.
Arithmetic work24--31 may contain leftovers and is outside the scan frame. -/
theorem command_eval_oai (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    ∃ time b, Eval command time (initial regs scopes n t) b ∧
      time ≤ budget scopes n t ∧
      b.stacks 0 = scopeBits scopes ∧ b.stacks 16 = n ∧ b.stacks 17 = t ∧
      b.stacks 14 = highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ∧
      b.stacks 2 = unary (BinaryArithmetic.toNat n) ∧ b.stacks 13 = unary (cut scopes n t + 1) ∧
      b.stacks 15 = [] := by
  let a := initial regs scopes n t
  obtain ⟨re, he⟩ := count_eval a (records scopes)
    (by simpa [a, initial] using (records_bits scopes).symm) (by simp [a, initial])
    (by simp [a, initial]) (by simp [a, initial])
  let e : Data := ⟨re, Function.update a.stacks 1 (unary scopes.length)⟩
  rw [records_length] at he
  obtain ⟨tm, rm, hm, htm⟩ := mass_eval e scopes
    (by simp [e, a, initial]) (by simp [e, a, initial]) (by simp [e, a, initial])
    (by simp [e, a, initial]) (by simp [e, a, initial])
  let m : Data := ⟨rm, Function.update e.stacks 18 (unary (mass scopes))⟩
  obtain ⟨tb, rb, bits, hb, htb, hvb, hlb⟩ := binary_eval m
    (by simp [m, e, a, initial]) (by simp [m, e, a, initial]) (by simp [m, e, a, initial])
  have hvb' : BinaryArithmetic.toNat bits = mass scopes := by simpa [m] using hvb
  have hlb' : bits.length ≤ mass scopes := by simpa [m] using hlb
  let v : Data := ⟨rb, Function.update m.stacks 19 bits⟩
  have hv16 : v.stacks 16 = n := by simp [v, m, e, a, initial]
  have hv17 : v.stacks 17 = t := by simp [v, m, e, a, initial]
  have hv19 : v.stacks 19 = bits := by simp [v]
  obtain ⟨tc, c, hc, htc, hvc, hlc, hframe⟩ := cutoff_eval v (by simpa [hv16] using hn) (by
    intro i hi0 hi1 hi2
    fin_cases i <;> first | exact (hi0 rfl).elim | exact (hi1 rfl).elim |
      exact (hi2 rfl).elim | simp [cutoffPorts, v, m, e, a, initial])
  have hvc' : BinaryArithmetic.toNat (c.stacks 20) = cut scopes n t := by
    simpa only [hv16, hv17, hv19, hvb', cut] using hvc
  have hlc' : (c.stacks 20).length ≤ mass scopes + t.length + 2 := by
    rw [hv19, hv17] at hlc
    omega
  have hcsmall (i : Fin 32) (hi : i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
      i = 21 ∨ i = 22 ∨ i = 23) : c.stacks i = v.stacks i := hframe i hi
  obtain ⟨tu, ru, hu, htu⟩ := unary_eval unaryPorts unaryPorts_inj c
    (by change c.stacks 13 = []; rw [hcsmall 13 (Or.inl (by decide))]; simp [v, m, e, a, initial])
    (by change c.stacks 21 = []; rw [hcsmall 21 (by simp)]; simp [v, m, e, a, initial])
    (by change c.stacks 22 = []; rw [hcsmall 22 (by simp)]; simp [v, m, e, a, initial])
    (by change c.stacks 23 = []; rw [hcsmall 23 (by simp)]; simp [v, m, e, a, initial])
  change Eval unaryCall tu c ⟨ru, Function.update c.stacks 13 (unary (BinaryArithmetic.toNat (c.stacks 20)))⟩ at hu
  rw [hvc'] at hu
  let u : Data := ⟨ru, Function.update c.stacks 13 (unary (cut scopes n t))⟩
  let p : Data := ⟨Function.update u.regs 0 true,
    Function.update u.stacks 13 (unary (cut scopes n t + 1))⟩
  have hp : Eval bump 2 u p := by
    simpa [p, u, unary, List.replicate_succ] using bump_eval u
  obtain ⟨tf, rf, hf, htf⟩ := unary_eval fuelPorts fuelPorts_inj p
    (by change p.stacks 15 = []; simp only [p, u, Function.update_of_ne (by decide : (15 : Fin 32) ≠ 13)];
        rw [hcsmall 15 (Or.inl (by decide))]; simp [v, m, e, a, initial])
    (by change p.stacks 21 = []; simp only [p, u, Function.update_of_ne (by decide : (21 : Fin 32) ≠ 13)];
        rw [hcsmall 21 (by simp)]; simp [v, m, e, a, initial])
    (by change p.stacks 22 = []; simp only [p, u, Function.update_of_ne (by decide : (22 : Fin 32) ≠ 13)];
        rw [hcsmall 22 (by simp)]; simp [v, m, e, a, initial])
    (by change p.stacks 23 = []; simp only [p, u, Function.update_of_ne (by decide : (23 : Fin 32) ≠ 13)];
        rw [hcsmall 23 (by simp)]; simp [v, m, e, a, initial])
  have hp16 : p.stacks 16 = n := by simp [p, u, hcsmall 16 (by simp), hv16]
  change Eval fuelCall tf p ⟨rf, Function.update p.stacks 15 (unary (BinaryArithmetic.toNat (p.stacks 16)))⟩ at hf
  rw [hp16] at hf
  let f : Data := ⟨rf, Function.update p.stacks 15 (unary (BinaryArithmetic.toNat n))⟩
  have hproject : projectState id scanPorts f =
      state f.regs scopes 0 (cut scopes n t) [] (unary (BinaryArithmetic.toNat n)) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i
    have hi : (scanPorts i).val < 16 := i.isLt
    have hci := hcsmall (scanPorts i) (Or.inl hi)
    fin_cases i <;> simp [ scanPorts, f, p, u] <;>
      simpa [scanPorts, v, m, e, a, initial] using hci
  obtain ⟨ts, rs, hts, hs⟩ := scan_eval f.regs scopes (BinaryArithmetic.toNat n) (cut scopes n t) []
  rw [← hproject] at hs
  let final := embedState id scanPorts f
    (state rs scopes (BinaryArithmetic.toNat n) (cut scopes n t) (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ++ []) [])
  have hs' := eval_liftCommand_from_state scan 0 14 id scanPorts f
    Function.injective_id scanPorts_inj hs
  have hfinal (i : Fin 16) : final.stacks (scanPorts i) =
      (state rs scopes (BinaryArithmetic.toNat n) (cut scopes n t) (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) ++ []) []).stacks i :=
    embedState_stack _ _ _ _ scanPorts_inj i
  refine ⟨(SubexpScopeCountSetup.countBudget (records scopes) + 1) +
      (tm + (tb + (tc + (tu + (2 + (tf + (ts + 1))))))), final,
    he.seq (hm.seq (hb.seq (hc.seq (hu.seq (hp.seq (hf.seq hs')))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have htm' : tm ≤ MassPreserve.bound (scopeBits scopes) := by simpa [scopeBits] using htm
    have htb' : tb ≤ SubexpFactorCountSetup.countBudget (mass scopes) + 1 := by simpa [m] using htb
    have htc' : tc ≤ Cutoff.bound (List.replicate (mass scopes) false) t n := by
      rw [hv19, hv17, hv16] at htc
      apply htc.trans
      unfold Cutoff.bound
      simp only [List.length_replicate]
      gcongr
    have htu' : tu ≤ unarySized (cut scopes n t) (mass scopes + t.length + 2) :=
      htu.trans (unaryBound_le _ _ _ hvc' hlc')
    have htf' : tf ≤ unarySized (BinaryArithmetic.toNat n) n.length := by
      change tf ≤ SubexpClauseMastersProgram.unaryCopyBound (p.stacks 16) + 1 at htf
      rw [hp16] at htf
      exact htf.trans (unaryBound_le n _ _ rfl le_rfl)
    unfold budget
    omega
  · exact hfinal 0
  · rw [embedState_stack_frame id scanPorts f _ 16 (by
        rintro ⟨i, hi⟩; have := congrArg Fin.val hi; dsimp [scanPorts] at this; omega)]
    simp [f, hp16]
  · rw [embedState_stack_frame id scanPorts f _ 17 (by
        rintro ⟨i, hi⟩; have := congrArg Fin.val hi; dsimp [scanPorts] at this; omega)]
    simp [f, p, u, hcsmall 17 (by simp), hv17]
  · simpa [scanPorts, state] using hfinal (14 : Fin 16)
  · exact hfinal 2
  · exact hfinal 13
  · exact hfinal 15

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval_oai
