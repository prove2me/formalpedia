-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:20:01.098693+00:00
-- url     : https://prove2.me/submissions/0a8a83d8-3670-4011-9701-4b6187b920b5

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_insert_code_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem frameReadRegs_injective : Function.Injective frameReadRegs := Fin.castAdd_injective _ _
theorem frameReadPorts_injective {s : ℕ} (src dst : Fin s) (h : src ≠ dst) :
    Function.Injective (frameReadPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [frameReadPorts, ParserProgram.pair]

theorem readFrame8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst)
    (bits : List Bool) (rest : List Bool) (hin : d.stacks src = Encoding.frame bits ++ rest) :
    Eval (readFrame8 src dst) (6 * bits.length + 4) d (afterFrame8 d src dst bits rest) := by
  let a : State 2 2 := ⟨ParserProgram.pair (d.regs 0) (d.regs 1),
    ParserProgram.pair (Encoding.frame bits ++ rest) (d.stacks dst)⟩
  let b : State 2 2 := ⟨ParserProgram.pair false true,
    ParserProgram.pair rest (bits.reverse ++ d.stacks dst)⟩
  have ha : embedState frameReadRegs (frameReadPorts src dst) d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i
      · exact hin
      · rfl
    · intros; rfl
  have hb : embedState frameReadRegs (frameReadPorts src dst) d b = afterFrame8 d src dst bits rest := by
    apply embedState_eq_of_ports _ _ _ _ _ frameReadRegs_injective (frameReadPorts_injective src dst hsd)
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadRegs, readRegs, b, ParserProgram.pair]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [frameReadRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [frameReadRegs] using h.symm⟩
      simp [afterFrame8, readRegs, h0, h1]
    · intro i; fin_cases i <;> simp [afterFrame8, frameReadPorts, ParserProgram.pair, b, hsd]
    · intro j hj
      have hsrc : j ≠ src := fun h => hj ⟨0, by simpa [frameReadPorts] using h.symm⟩
      have hdst : j ≠ dst := fun h => hj ⟨1, by simpa [frameReadPorts] using h.symm⟩
      simp [afterFrame8, hsrc, hdst]
  have ht : Trace ParserProgram.frameProgram (6 * bits.length + 4)
      (a.withPC (some ParserProgram.frameProgram.entry)) (b.withPC none) :=
    ParserProgram.frame_trace bits rest (d.stacks dst) (d.regs 0) (d.regs 1)
  have h := eval_call_lifted ParserProgram.frameProgram frameReadRegs
    (frameReadPorts src dst) d frameReadRegs_injective (frameReadPorts_injective src dst hsd) ht
  simpa only [ha,hb,readFrame8] using h

theorem transfer8_eval {s : ℕ} (d : State 8 s) (src dst : Fin s) (hsd : src ≠ dst) :
    Eval (transfer8 src dst) (3*(d.stacks src).length+3) d (afterTransfer8 d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [afterTransfer8,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

theorem readRecord_result (d : State 8 28) (key coeff tail : List Bool)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    afterTransfer8 (afterFrame8 (afterFrame8 d 27 16 key (Encoding.frame coeff ++ tail))
      27 18 coeff tail) 18 17 = readRecordResult d key coeff tail := by
  apply congrArg₂ StructuredProgram.State.mk
  · simp [afterFrame8,StackRoutines.readRegs_reset]
  · funext i
    by_cases h27 : i = 27
    · subst i; simp [afterFrame8,StackRoutines.transferStacks]
    · by_cases h16i : i = 16
      · subst i; simp [afterFrame8,StackRoutines.transferStacks,h16]
      · by_cases h18i : i = 18
        · subst i; simp [afterFrame8,StackRoutines.transferStacks]
        · by_cases h17i : i = 17
          · subst i; simp [afterFrame8,StackRoutines.transferStacks,h17,h18]
          · simp [afterFrame8,StackRoutines.transferStacks,h27,h16i,h18i,h17i]

theorem takeDictionaryRecord_eval (d : State 8 28) (key coeff tail : List Bool)
    (hinput : d.stacks 27 = Encoding.frame key ++ Encoding.frame coeff ++ tail)
    (h16 : d.stacks 16 = []) (h17 : d.stacks 17 = []) (h18 : d.stacks 18 = []) :
    Eval takeDictionaryRecord (6*key.length+9*coeff.length+11)
      d (readRecordResult d key coeff tail) := by
  have h1 := readFrame8_eval d 27 16 (by decide) key (Encoding.frame coeff ++ tail)
    (by simpa [List.append_assoc] using hinput)
  let a := afterFrame8 d 27 16 key (Encoding.frame coeff ++ tail)
  have h2 := readFrame8_eval a 27 18 (by decide) coeff tail (by simp [a,afterFrame8])
  let b := afterFrame8 a 27 18 coeff tail
  have h3 := transfer8_eval b 18 17 (by decide)
  have h3' : Eval (transfer8 18 17) (3*coeff.length+3) b (afterTransfer8 b 18 17) := by
    simpa [b,a,afterFrame8,h18] using h3
  have he := h1.seq (h2.seq h3')
  have ht : (6*key.length+4)+((6*coeff.length+4)+(3*coeff.length+3)) =
      6*key.length+9*coeff.length+11 := by omega
  rw [ht] at he
  simpa only [takeDictionaryRecord,b,a,readRecord_result d key coeff tail h16 h17 h18] using he

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem lower_injective : Function.Injective lower := Fin.castSucc_injective _

theorem embed_lower (a b : Dictionary.Data) (source : List Bool) :
    embedState id lower (extend a source) b = extend b source := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lower_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; simp [extend,lower]
  · intro i hi
    fin_cases i <;> simp_all [lower,extend,Fin.exists_fin_succ,Fin.snoc]

theorem peek_eval (d : Data) : Eval peek 1 d (peeked d) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem insert_eval {n : ℕ} {a b : Dictionary.Data}
    (he : Eval Dictionary.insert n a b) (source : List Bool) :
    Eval insert (n+1) (extend a source) (extend b source) := by
  have h := eval_call_lifted Dictionary.insertProgram id lower (extend a source)
    Function.injective_id lower_injective (compiled_halt_trace he 15 15)
  simpa only [embed_lower] using h

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem read_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (key coeff tail : List Bool) :
    Eval Squarefree.Program.takeDictionaryRecord (6*key.length+9*coeff.length+11)
      (state regs modulus width count (Squarefree.Program.rawEntries entries)
        (Encoding.frame key ++ Encoding.frame coeff ++ tail))
      (extend (Dictionary.machine (readRegs regs 0 1 none)
        (Dictionary.inputTape modulus width count entries key coeff)) tail) := by
  have h := Squarefree.Program.takeDictionaryRecord_eval
    (state regs modulus width count (Squarefree.Program.rawEntries entries)
      (Encoding.frame key ++ Encoding.frame coeff ++ tail)) key coeff tail rfl rfl rfl rfl
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [state,extend,
      Dictionary.machine,Dictionary.inputTape,Dictionary.outputTape,Dictionary.tapes,Fin.snoc]
    all_goals rfl

theorem clearCoefficient_eval (regs : Fin 8 → Bool)
    (modulus width count dict coeff tail : List Bool) :
    Eval clearCoefficient (2*coeff.length+3)
      (extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict coeff)) tail)
      (state (readRegs regs 0 1 none) modulus width count dict tail) := by
  let d := extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict coeff)) tail
  let next : Data := ⟨readRegs d.regs 0 1 none,clearStacks 17 d.stacks⟩
  have h := clearProgram_trace (17 : Fin 28) (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  have hlen : d.stacks 17 = coeff := rfl
  have hrun : Eval clearCoefficient (2*coeff.length+3) d next := by
    apply Eval.call
    simpa only [clearResult,StructuredProgram.State.withPC,next,hlen,Nat.add_assoc] using hh
  have hs : next = state (readRegs regs 0 1 none) modulus width count dict tail := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [clearStacks,d,extend,
        Dictionary.machine,Dictionary.outputTape,Dictionary.tapes,Fin.snoc]
      all_goals first | rfl
  rwa [hs] at hrun

variable {K : Type*} [DecidableEq K]

theorem step_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (seed : List (K × RingProgram.Code (Word (baseWidth p t)) d)) (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width count tail : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ stepBudget p t M cache key seed k x, ∃ rr,
      Eval step n
        (state regs M.bits width count
          (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat seed))
          (Encoding.frame (key k) ++ Encoding.frame (RingProgram.flat x) ++ tail))
        (state rr M.bits width count
          (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
            (Dictionary.insertCode p t M cache k x seed))) tail) := by
  have hr := read_eval regs M.bits width count
    (Squarefree.Program.encodeDictionary key RingProgram.flat seed) (key k) (RingProgram.flat x) tail
  obtain ⟨n,hn,r1,hi⟩ := Dictionary.insert_code_eval p t M cache key hk seed k x
    (readRegs regs 0 1 none) width count hc hw
  have hp := insert_eval hi tail
  have hc := clearCoefficient_eval r1 M.bits width count
    (Squarefree.Program.rawEntries (Squarefree.Program.encodeDictionary key RingProgram.flat
      (Dictionary.insertCode p t M cache k x seed))) (RingProgram.flat x) tail
  have hrun := hr.seq (hp.seq hc)
  refine ⟨_,?_,readRegs r1 0 1 none,hrun⟩
  change _ ≤ 6*(key k).length+11*(RingProgram.flat x).length+15+_
  calc
    _ = (6*(key k).length+11*(RingProgram.flat x).length+15)+n := by omega
    _ ≤ _ := Nat.add_le_add_left hn _

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem peek_ready {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d)) :
    Eval peek 1 (state regs modulus width count (bytes key seed) (bytes key source))
      (ready regs modulus width count key seed source) := by
  exact peek_eval _

omit [DecidableEq K] in
theorem ready_nil {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed : List (K × RingProgram.Code (Word B) d)) :
    (ready regs modulus width count key seed []).regs 7 = false := by
  simp [ready,state,extend,Dictionary.machine,readRegs,bytes,
    Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary]

omit [DecidableEq K] in
theorem ready_cons {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d))
    (a : K × RingProgram.Code (Word B) d) :
    (ready regs modulus width count key seed (a::source)).regs 7 = true := by
  cases he : key a.1 <;>
    simp [ready,state,extend,Dictionary.machine,readRegs,bytes,
      Squarefree.Program.rawEntries,Squarefree.Program.encodeDictionary,Encoding.frame,he]

theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ n ≤ work p t M cache key source seed, ∃ rr,
      Eval loop n (ready regs M.bits width count key seed source)
        (state rr M.bits width count (bytes key (run p t M cache source seed)) []) := by
  induction source generalizing seed regs with
  | nil =>
    refine ⟨1,le_rfl,readRegs regs 0 7 none,?_⟩
    exact Eval.while_false (ready_nil regs M.bits width count key seed)
  | cons a source ih =>
    let initial := readRegs regs 0 7 (bytes key (a::source)).head?
    let next := Dictionary.insertCode p t M cache a.1 a.2 seed
    obtain ⟨n,hn,r1,hs⟩ := step_eval p t M cache key hk seed a.1 a.2 initial width count (bytes key source) hc hw
    have hp := peek_ready r1 M.bits width count key next source
    obtain ⟨m,hm,rr,ht⟩ := ih next r1
    have hrun := Eval.while_true (ready_cons regs M.bits width count key seed source a) (hs.seq hp) ht
    refine ⟨_,?_,rr,hrun⟩
    dsimp only [next] at hm
    dsimp [work]
    omega

theorem program_run_oai (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ rr, RunsIn program (work p t M cache key source seed + 2)
      ((state regs M.bits width count (bytes key seed) (bytes key source)).withPC (some program.entry))
      ((state rr M.bits width count (bytes key (run p t M cache source seed)) []).withPC none) := by
  obtain ⟨n,hn,rr,hl⟩ := loop_eval p t M cache key hk source seed regs width count hc hw
  have hr := (peek_ready regs M.bits width count key seed source).seq hl
  exact ⟨rr,1+n+1,by omega,compiled_halt_trace hr 27 15⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run_oai.{u_1}
