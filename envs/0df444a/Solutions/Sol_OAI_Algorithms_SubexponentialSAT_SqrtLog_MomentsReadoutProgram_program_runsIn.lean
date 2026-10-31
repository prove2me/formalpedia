-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:01:05.496309+00:00
-- url     : https://prove2.me/submissions/b9adcc07-6dc6-4ddf-b4e0-0242d6d05719

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S169
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsReadoutProgram_fetchAdd_code

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem transfer_eval (d : Data) (src dst : Fin 27) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred d src dst) := by
  apply Eval.call
  have h := transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := halt_after_trace _ h 3 rfl rfl
  simpa [transfer, transferred, transferResult, StructuredProgram.State.withPC,
    transferProgram, Nat.add_assoc] using hh

theorem clear_eval (d : Data) (src : Fin 27) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa [clear, cleared, clearResult, StructuredProgram.State.withPC,
    clearProgram, Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryMoves
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem transfer_machine (regs : Fin 8 → Bool) (a b : Tape) (src dst : Fin 27)
    (hsd : src ≠ dst) (hs : transferStacks src dst (tapes a) = tapes b) :
    Eval (transfer src dst) (3 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [transferred,machine,hs] using transfer_eval (machine regs a) src dst hsd

theorem clear_machine (regs : Fin 8 → Bool) (a b : Tape) (src : Fin 27)
    (hs : clearStacks src (tapes a) = tapes b) :
    Eval (clear src) (2 * (tapes a src).length + 3) (machine regs a)
      (machine (readRegs regs 0 1 none) b) := by
  simpa only [cleared,machine,hs] using clear_eval (machine regs a) src

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramAccumulate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Commit the native sum as the next accumulator, reclaiming all temporary
strings. The dictionary and query are preserved for the runtime loop. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

theorem commit_eval (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (entries : List (List Bool × List Bool)) (query acc out : List Bool) :
    ∃ rr, Eval commit (2*acc.length+6*out.length+9)
      (machine regs (fetchedTape modulus width count entries query acc out))
      (machine rr (inputTape modulus width count entries query out)) := by
  let a := fetchedTape modulus width count entries query acc out
  let a1 : Tape := { a with coeff := [] }
  let a2 : Tape := { a1 with out := [], combined := out.reverse }
  let a3 := inputTape modulus width count entries query out
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 : Eval (clear 17) (2*acc.length+3) (machine regs a) (machine r1 a1) := by
    apply clear_machine regs a a1 17
    funext i; fin_cases i <;> simp [clearStacks,tapes,a,a1,fetchedTape,inputTape]
  have h2 : Eval (transfer 0 26) (3*out.length+3) (machine r1 a1) (machine r2 a2) := by
    apply transfer_machine r1 a1 a2 0 26 (by decide)
    funext i; fin_cases i <;> simp [transferStacks,tapes,a,a1,a2,fetchedTape,inputTape]
  have h3 : Eval (transfer 26 17) (3*out.reverse.length+3) (machine r2 a2)
      (machine (readRegs r2 0 1 none) a3) := by
    apply transfer_machine r2 a2 a3 26 17 (by decide)
    funext i; fin_cases i <;> simp [transferStacks,tapes,a,a1,a2,a3,fetchedTape,inputTape]
  refine ⟨readRegs r2 0 1 none, ?_⟩
  convert h1.seq (h2.seq h3) using 1 ; simp ; omega

theorem accumulate_eval {K : Type*} [DecidableEq K]
    (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p e) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    ∃ n ≤ accumulateBudget (baseWidth p e) d encoded (key k), ∃ rr,
      Eval accumulate n (machine regs (inputTape M.bits width count encoded (key k) (RingProgram.flat acc)))
        (machine rr (inputTape M.bits width count encoded (key k)
          (RingProgram.flat (addFetched p e M cache entries k acc)))) := by
  dsimp only
  obtain ⟨n,hn,r1,h1⟩ := fetchAdd_code p e M cache key hk entries k acc regs width count hc hw
  obtain ⟨r2,h2⟩ := commit_eval r1 M.bits width count
    (Squarefree.Program.encodeDictionary key RingProgram.flat entries) (key k) (RingProgram.flat acc)
    (RingProgram.flat (addFetched p e M cache entries k acc))
  refine ⟨_, ?_, r2, h1.seq h2⟩
  simp only [RingProgram.flat_length]
  dsimp [accumulateBudget]
  omega

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem wide_project (regs : Fin 8 → Bool) (a : D) (h : High) :
    projectState id widePorts (wideState regs a h) =
      MomentsProgram.Dictionary.machine regs a := by
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  fin_cases i <;> simp [widePorts,wideState,wideTapes,MomentsProgram.Dictionary.tapes]

theorem wide_embed (regs rr : Fin 8 → Bool) (a b : D) (h : High) :
    embedState id widePorts (wideState regs a h)
      (MomentsProgram.Dictionary.machine rr b) = wideState rr b h := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (Fin.castAdd_injective _ _)
  · intros; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    fin_cases i <;> simp [wideState,wideTapes,MomentsProgram.Dictionary.machine,
      MomentsProgram.Dictionary.tapes]
  · intro i hi
    fin_cases i <;> simp_all [wideState,wideTapes,Fin.exists_fin_succ]

theorem wideAccumulate_eval {K : Type*} [DecidableEq K]
    (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (key : K → List Bool) (hk : Function.Injective key)
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool) (h : High)
    (hc : count.length=d) (hw : width.length=baseWidth p e) :
    let encoded := Squarefree.Program.encodeDictionary key RingProgram.flat entries
    ∃ n ≤ accumulateBudget (baseWidth p e) d encoded (key k)+1, ∃ rr,
      Eval wideAccumulate n
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded
          (key k) (RingProgram.flat acc)) h)
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded
          (key k) (RingProgram.flat (addFetched p e M cache entries k acc))) h) := by
  dsimp only
  obtain ⟨n,hn,rr,he⟩ := accumulate_eval p e M cache key hk entries k acc regs width count hc hw
  have hp := wide_project regs (MomentsProgram.Dictionary.inputTape M.bits width count
    (Squarefree.Program.encodeDictionary key RingProgram.flat entries)
    (key k) (RingProgram.flat acc)) h
  rw [←hp] at he
  have ht := eval_call_from_state accumulateProgram id widePorts
    (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count
      (Squarefree.Program.encodeDictionary key RingProgram.flat entries)
      (key k) (RingProgram.flat acc)) h)
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace he 15 17)
  rw [wide_embed] at ht
  exact ⟨n+1,by omega,rr,ht⟩

theorem wcopy_eval (d : WideData) (src dst tmp : Fin 40)
    (hsd : src≠dst) (hst : src≠tmp) (htd : tmp≠dst) (he : d.stacks tmp=[]) :
    Eval (wcopy src dst tmp) (7*(d.stacks src).length+5) d (wcopied d src dst) := by
  apply Eval.call
  have h := copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd (by decide)
    d.regs d.stacks he
  have hh := halt_after_trace _ h 7 rfl rfl
  simpa [wcopy,wcopied,copyResult,StructuredProgram.State.withPC,copyProgram,
    Nat.add_assoc] using hh

theorem wtransfer_eval (d : WideData) (src dst : Fin 40) (hsd : src≠dst) :
    Eval (wtransfer src dst) (3*(d.stacks src).length+3) d (wtransferred d src dst) := by
  apply Eval.call
  have h := transferProgram_trace src dst (0 : Fin 8) 1 hsd (by decide) d.regs d.stacks
  have hh := halt_after_trace _ h 3 rfl rfl
  simpa [wtransfer,wtransferred,transferResult,StructuredProgram.State.withPC,
    transferProgram,Nat.add_assoc] using hh

theorem wclear_eval (d : WideData) (src : Fin 40) :
    Eval (wclear src) (2*(d.stacks src).length+3) d (wcleared d src) := by
  apply Eval.call
  have h := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ h 2 rfl rfl
  simpa [wclear,wcleared,clearResult,StructuredProgram.State.withPC,
    clearProgram,Nat.add_assoc] using hh

theorem wpush_eval (d : WideData) (dst : Fin 40) (bit : Bool) :
    Eval (wpush dst bit) 2 d (wpushed d dst bit) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set 0 bit) d)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst 0)
      (StructuredProgram.Atom.eval (.set 0 bit) d)))
  simpa [wpush,wpushed,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using h

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem buildQuery_eval (regs : Fin 8 → Bool) (a : D) (h : High)
    (hq : a.query=[]) :
    ∃ rr, Eval buildQuery (7*(h.u.length+h.z.length+h.mask.length)+19)
      (wideState regs a h) (wideState rr {a with query:=queryBits h} h) := by
  let d := wideState regs a h
  let d1 := wcopied d 30 16
  let d2 := wpushed d1 16 false
  let d3 := wcopied d2 31 16
  let d4 := wpushed d3 16 false
  let d5 := wcopied d4 34 16
  have h1 := wcopy_eval d 30 16 23 (by decide) (by decide) (by decide) rfl
  have h2 := wpush_eval d1 16 false
  have h3 := wcopy_eval d2 31 16 23 (by decide) (by decide) (by decide)
    (by simp [d2,d1,d,wcopied,wpushed,wideState,wideTapes,copyStacks])
  have h4 := wpush_eval d3 16 false
  have h5 := wcopy_eval d4 34 16 23 (by decide) (by decide) (by decide)
    (by simp [d4,d3,d2,d1,d,wcopied,wpushed,wideState,wideTapes,copyStacks])
  have hend : d5=wideState d5.regs {a with query:=queryBits h} h := by
    apply congrArg (StructuredProgram.State.mk d5.regs)
    funext i
    fin_cases i <;> simp [d4,d3,d2,d1,d,wcopied,wpushed,wideState,wideTapes,copyStacks,queryBits,hq]
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  change Eval buildQuery _ d d5 at he
  rw [hend] at he
  refine ⟨d5.regs,?_⟩
  convert he using 1 ;
    simp [d4,d3,d2,d1,d,wcopied,wpushed,wideState,wideTapes,copyStacks] ; omega

theorem advanceU_eval (regs : Fin 8 → Bool) (a : D) (h : High) :
    ∃ rr, Eval advanceU (2*a.query.length+5)
      (wideState regs a h)
      (wideState rr {a with query:=[]} {h with u:=true::h.u}) := by
  let d := wideState regs a h
  let d1 := wcleared d 16
  let d2 := wpushed d1 30 true
  have h1 := wclear_eval d 16
  have h2 := wpush_eval d1 30 true
  have hend : d2=wideState d2.regs {a with query:=[]} {h with u:=true::h.u} := by
    apply congrArg (StructuredProgram.State.mk d2.regs)
    funext i
    fin_cases i <;> simp [d1,d,wcleared,wideState,wideTapes,clearStacks]
  have he := h1.seq h2
  change Eval advanceU _ d d2 at he
  rw [hend] at he
  exact ⟨d2.regs,by simpa [d,wideState,wideTapes,MomentsProgram.Dictionary.tapes] using he⟩

theorem emptyMask (n : ℕ) : Squarefree.encodeMask (∅ : Finset (Fin n)) =
    List.replicate n false := by
  simp [Squarefree.encodeMask,List.ofFn_const]

theorem queryBits_eq {n u z : ℕ} (h : High)
    (hu : h.u=unary u) (hz : h.z=unary z) (hm : h.mask=List.replicate n false) :
    queryBits h = (Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))).reverse := by
  simp [queryBits,hu,hz,hm,Squarefree.encodeIndex,emptyMask,Encoding.encodeNat,unary,
    List.reverse_append,List.append_assoc]

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem slot_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (u z : ℕ) (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool) (h : High)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hu : h.u=unary u) (hz : h.z=unary z) (hm : h.mask=List.replicate n false) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    ∃ cost ≤ slotBudget (baseWidth p e) d n u z encoded, ∃ rr,
      Eval slot cost
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat acc)) h)
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat (addFetched p e M cache entries ⟨u,z,∅⟩ acc)))
          {h with u:=true::h.u}) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  let key := Squarefree.encodeIndex (⟨u,z,∅⟩ : Squarefree.Index (Fin n))
  have hkey : queryBits h=key.reverse := queryBits_eq h hu hz hm
  obtain ⟨r1,h1⟩ := buildQuery_eval regs
    (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] (RingProgram.flat acc)) h rfl
  have h1' : Eval buildQuery (7*(h.u.length+h.z.length+h.mask.length)+19)
      (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] (RingProgram.flat acc)) h)
      (wideState r1 (MomentsProgram.Dictionary.inputTape M.bits width count encoded key (RingProgram.flat acc)) h) := by
    simpa [MomentsProgram.Dictionary.inputTape,hkey] using h1
  obtain ⟨c2,hc2,r2,h2⟩ := wideAccumulate_eval p e M cache Squarefree.encodeIndex
    Squarefree.encodeIndex_injective entries ⟨u,z,∅⟩ acc r1 width count h hc hw
  obtain ⟨r3,h3⟩ := advanceU_eval r2
    (MomentsProgram.Dictionary.inputTape M.bits width count encoded key
      (RingProgram.flat (addFetched p e M cache entries ⟨u,z,∅⟩ acc))) h
  have h3' : Eval advanceU (2*key.reverse.length+5)
      (wideState r2 (MomentsProgram.Dictionary.inputTape M.bits width count encoded key
        (RingProgram.flat (addFetched p e M cache entries ⟨u,z,∅⟩ acc))) h)
      (wideState r3 (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
        (RingProgram.flat (addFetched p e M cache entries ⟨u,z,∅⟩ acc))) {h with u:=true::h.u}) := by
    simpa [MomentsProgram.Dictionary.inputTape] using h3
  refine ⟨_,?_,r3,h1'.seq (h2.seq h3')⟩
  have hlu : h.u.length=u := by simp [hu,unary]
  have hlz : h.z.length=z := by simp [hz,unary]
  have hlm : h.mask.length=n := by simp [hm]
  have hlkey : key.reverse.length=u+z+n+2 := by simp [key]
  dsimp [slotBudget]
  omega

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem innerPop_state (regs : Fin 8 → Bool) (a : D) (h : High)
    (u : ℕ) (rem : List Bool) :
    UnaryForPrograms.popped innerPorts (wideState regs a (innerHigh h u rem)) =
      wideState (readRegs regs 0 1 rem.head?) a (innerHigh h u rem.tail) := by
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 rem.head?))
  funext i
  fin_cases i <;> simp [innerPorts,wideState,wideTapes,innerHigh]

theorem inner_visits {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z : ℕ) (width count : List Bool) (h : High)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hz : h.z=unary z) (hm : h.mask=List.replicate n false)
    (rem : List Bool) :
    ∀ (u : ℕ) (acc : RingProgram.Code (Word (baseWidth p e)) d) (regs : Fin 8 → Bool),
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    ∃ costs time, time ≤ innerBudget (baseWidth p e) d n z encoded u rem.length ∧ ∃ rr,
      UnaryForPrograms.Visits innerPorts slot costs time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat acc)) (innerHigh h u rem))
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat (foldU p e M cache entries z u rem.length acc)))
          (innerHigh h (u+rem.length) [])) := by
  induction rem with
  | nil =>
      intro u acc regs
      dsimp only
      let a := MomentsProgram.Dictionary.inputTape M.bits width count
        (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries)
        [] (RingProgram.flat acc)
      have hv := UnaryForPrograms.Visits.done (p:=innerPorts) (body:=slot)
        (wideState regs a (innerHigh h u [])) (by rfl)
      rw [innerPop_state] at hv
      exact ⟨[],2,by simp [innerBudget],_,by simpa [foldU] using hv⟩
  | cons bit rem ih =>
      intro u acc regs
      dsimp only
      let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
      let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] (RingProgram.flat acc)
      let acc' := addFetched p e M cache entries ⟨u,z,∅⟩ acc
      let a' := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] (RingProgram.flat acc')
      let r1 := readRegs regs 0 1 (some bit)
      obtain ⟨cb,hcb,r2,hb⟩ := slot_eval p e M cache entries u z acc r1 width count
        (innerHigh h u rem) hc hw rfl hz hm
      have hh : {innerHigh h u rem with u:=true::(innerHigh h u rem).u} =
          innerHigh h (u+1) rem := by
        simp [innerHigh,unary,List.replicate_succ]
      rw [hh] at hb
      have hb' : Eval slot cb
          (UnaryForPrograms.popped innerPorts (wideState regs a (innerHigh h u (bit::rem))))
          (wideState r2 a' (innerHigh h (u+1) rem)) := by
        rw [innerPop_state]
        exact hb
      obtain ⟨costs,ct,hct,r3,ht⟩ := ih (u+1) acc' r2
      have hv := UnaryForPrograms.Visits.step
        (p:=innerPorts) (body:=slot)
        (d:=wideState regs a (innerHigh h u (bit::rem)))
        (e:=wideState r2 a' (innerHigh h (u+1) rem))
        (nb:=cb) (nt:=ct) (costs:=costs)
        (by simp only [innerCounter_state, ne_eq, List.cons_ne_nil, not_false_eq_true]) hb'
        (by simp only [innerCounter_state, UnaryForPrograms.popped_counter, List.tail_cons]) ht
      refine ⟨cb::costs,cb+ct+2,?_,r3,?_⟩
      · simp only [List.length_cons,innerBudget]
        omega
      · simpa [foldU,acc',a,a',encoded,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv

theorem inner_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z u : ℕ) (acc : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool) (h : High) (rem : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hz : h.z=unary z) (hm : h.mask=List.replicate n false) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    ∃ time ≤ innerBudget (baseWidth p e) d n z encoded u rem.length, ∃ rr,
      Eval inner time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat acc)) (innerHigh h u rem))
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
          (RingProgram.flat (foldU p e M cache entries z u rem.length acc)))
          (innerHigh h (u+rem.length) [])) := by
  obtain ⟨costs,time,ht,rr,hv⟩ := inner_visits p e M cache entries z width count h hc hw hz hm rem u acc regs
  exact ⟨time,ht,rr,hv.eval⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem startRow_eval (regs : Fin 8 → Bool) (a : D) (h : High)
    (hc : a.coeff=[]) (hr : h.remU=[]) :
    ∃ rr, Eval startRow (7*h.zero.length+7*h.t.length+10)
      (wideState regs a h)
      (wideState rr {a with coeff:=h.zero} {h with remU:=h.t}) := by
  let d := wideState regs a h
  let d1 := wcopied d 27 17
  let d2 := wcopied d1 28 32
  have h1 := wcopy_eval d 27 17 23 (by decide) (by decide) (by decide) rfl
  have h2 := wcopy_eval d1 28 32 23 (by decide) (by decide) (by decide)
    (by simp [d1,d,wcopied,wideState,wideTapes,copyStacks])
  have hend : d2=wideState d2.regs {a with coeff:=h.zero} {h with remU:=h.t} := by
    apply congrArg (StructuredProgram.State.mk d2.regs)
    funext i
    fin_cases i <;> simp [d1,d,wcopied,wideState,wideTapes,copyStacks,hc,hr]
  have he := h1.seq h2
  change Eval startRow _ d d2 at he
  rw [hend] at he
  refine ⟨d2.regs,?_⟩
  convert he using 1 ; simp [d1,d,wcopied,wideState,wideTapes,copyStacks] ; omega

theorem finishRow_eval (regs : Fin 8 → Bool) (a : D) (h : High) :
    ∃ rr, Eval finishRow (3*a.coeff.length+2*h.u.length+8)
      (wideState regs a h)
      (wideState rr {a with coeff:=[]}
        {h with output:=a.coeff.reverse++h.output,u:=[],z:=true::h.z}) := by
  let d := wideState regs a h
  let d1 := wtransferred d 17 35
  let d2 := wcleared d1 30
  let d3 := wpushed d2 31 true
  have h1 := wtransfer_eval d 17 35 (by decide)
  have h2 := wclear_eval d1 30
  have h3 := wpush_eval d2 31 true
  have hend : d3=wideState d3.regs {a with coeff:=[]}
      {h with output:=a.coeff.reverse++h.output,u:=[],z:=true::h.z} := by
    apply congrArg (StructuredProgram.State.mk d3.regs)
    funext i
    fin_cases i <;> simp [d2,d1,d,wtransferred,wcleared,wideState,wideTapes,transferStacks,clearStacks]
  have he := h1.seq (h2.seq h3)
  change Eval finishRow _ d d3 at he
  rw [hend] at he
  refine ⟨d3.regs,?_⟩
  convert he using 1 ; simp [d1,d,wtransferred,wideState,wideTapes,transferStacks] ; omega

theorem row_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count : List Bool) (h : High)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hz : h.z=unary z) (hm : h.mask=List.replicate n false)
    (hzero : h.zero=RingProgram.flat zero) (ht : h.t.length=t)
    (hu : h.u=[]) (hr : h.remU=[]) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let value := foldU p e M cache entries z 0 t zero
    ∃ time ≤ rowBudget (baseWidth p e) d n z t encoded, ∃ rr,
      Eval row time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []) h)
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          {h with z:=true::h.z,output:=(RingProgram.flat value).reverse++h.output}) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []
  obtain ⟨r1,h1⟩ := startRow_eval regs a h rfl hr
  have h1' : Eval startRow (7*h.zero.length+7*h.t.length+10) (wideState regs a h)
      (wideState r1 (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
        (RingProgram.flat zero)) (innerHigh h 0 h.t)) := by
    simpa [a,MomentsProgram.Dictionary.inputTape,innerHigh,unary,hu,hzero] using h1
  obtain ⟨ti,hti,r2,h2⟩ := inner_eval p e M cache entries z 0 zero r1 width count h h.t hc hw hz hm
  obtain ⟨r3,h3⟩ := finishRow_eval r2
    (MomentsProgram.Dictionary.inputTape M.bits width count encoded []
      (RingProgram.flat (foldU p e M cache entries z 0 h.t.length zero)))
    (innerHigh h (0+h.t.length) [])
  have he := h1'.seq (h2.seq h3)
  refine ⟨_,?_,r3,(by simpa [row,a,MomentsProgram.Dictionary.inputTape,innerHigh,hu,hr,ht] using he)⟩
  simp only [unary,List.length_replicate,
    RingProgram.flat_length,hzero,ht] at hti ⊢
  dsimp [rowBudget]
  omega

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem outputBits_length {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) (z J : ℕ) :
    (outputBits p e M cache entries t zero z J).length=J*(d*baseWidth p e) := by
  induction J generalizing z with
  | zero => simp [outputBits,outputCodes]
  | succ J ih =>
      simp only [outputBits,outputCodes,List.map_cons,List.flatten_cons,List.length_append,
        RingProgram.flat_length] at *
      rw [ih]
      simp [Nat.succ_mul,Nat.add_comm]

theorem outerPop_state (regs : Fin 8 → Bool) (a : D) (h : High)
    (z : ℕ) (rem out : List Bool) :
    UnaryForPrograms.popped outerPorts (wideState regs a (outerHigh h z rem out)) =
      wideState (readRegs regs 0 1 rem.head?) a (outerHigh h z rem.tail out) := by
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 rem.head?))
  funext i
  fin_cases i <;> simp [outerPorts,wideState,wideTapes,outerHigh]

theorem outer_visits {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (width count : List Bool) (h : High)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hm : h.mask=List.replicate n false) (hzero : h.zero=RingProgram.flat zero)
    (ht : h.t.length=t) (rem : List Bool) :
    ∀ (z : ℕ) (out : List Bool) (regs : Fin 8 → Bool),
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    ∃ costs time, time ≤ outerBudget (baseWidth p e) d n t encoded z rem.length ∧ ∃ rr,
      UnaryForPrograms.Visits outerPorts row costs time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (outerHigh h z rem out))
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (outerHigh h (z+rem.length) [] ((outputBits p e M cache entries t zero z rem.length).reverse++out))) := by
  induction rem with
  | nil =>
      intro z out regs
      dsimp only
      let a := MomentsProgram.Dictionary.inputTape M.bits width count
        (Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries) [] []
      have hv := UnaryForPrograms.Visits.done (p:=outerPorts) (body:=row)
        (wideState regs a (outerHigh h z [] out)) (by rfl)
      rw [outerPop_state] at hv
      exact ⟨[],2,by simp [outerBudget],_,by simpa [outputBits,outputCodes] using hv⟩
  | cons bit rem ih =>
      intro z out regs
      dsimp only
      let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
      let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []
      let value := foldU p e M cache entries z 0 t zero
      let out' := (RingProgram.flat value).reverse++out
      let r1 := readRegs regs 0 1 (some bit)
      obtain ⟨cb,hcb,r2,hb⟩ := row_eval p e M cache entries z t zero r1 width count
        (outerHigh h z rem out) hc hw rfl hm hzero ht rfl rfl
      have hh : ({outerHigh h z rem out with z:=true::(outerHigh h z rem out).z, output:=(RingProgram.flat value).reverse++(outerHigh h z rem out).output} : High) =
          outerHigh h (z+1) rem out' := by
        simp [outerHigh,unary,List.replicate_succ,out']
      rw [hh] at hb
      have hb' : Eval row cb
          (UnaryForPrograms.popped outerPorts (wideState regs a (outerHigh h z (bit::rem) out)))
          (wideState r2 a (outerHigh h (z+1) rem out')) := by
        rw [outerPop_state]
        exact hb
      obtain ⟨costs,ct,hct,r3,hrest⟩ := ih (z+1) out' r2
      have hv := UnaryForPrograms.Visits.step (p:=outerPorts) (body:=row)
        (d:=wideState regs a (outerHigh h z (bit::rem) out))
        (e:=wideState r2 a (outerHigh h (z+1) rem out'))
        (nb:=cb) (nt:=ct) (costs:=costs)
        (by simp only [outerCounter_state, ne_eq, List.cons_ne_nil, not_false_eq_true]) hb'
        (by simp only [outerCounter_state, UnaryForPrograms.popped_counter, List.tail_cons]) hrest
      refine ⟨cb::costs,cb+ct+2,?_,r3,?_⟩
      · simp only [List.length_cons,outerBudget]
        omega
      · simpa [outputBits,outputCodes,value,out',a,encoded,List.reverse_append,List.append_assoc,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv

theorem outer_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (width count : List Bool) (h : High) (z : ℕ) (rem out : List Bool) (regs : Fin 8 → Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e)
    (hm : h.mask=List.replicate n false) (hzero : h.zero=RingProgram.flat zero)
    (ht : h.t.length=t) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    ∃ time ≤ outerBudget (baseWidth p e) d n t encoded z rem.length, ∃ rr,
      Eval outer time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (outerHigh h z rem out))
        (wideState rr (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (outerHigh h (z+rem.length) [] ((outputBits p e M cache entries t zero z rem.length).reverse++out))) := by
  obtain ⟨costs,time,hb,rr,hv⟩ := outer_visits p e M cache entries t zero width count h hc hw hm hzero ht rem z out regs
  exact ⟨time,hb,rr,hv.eval⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem maskPop_state (regs : Fin 8 → Bool) (a : D) (h : High) (rem acc : List Bool) :
    UnaryForPrograms.popped maskPorts (wideState regs a (maskHigh h rem acc)) =
      wideState (readRegs regs 0 1 rem.head?) a (maskHigh h rem.tail acc) := by
  apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 rem.head?))
  funext i
  fin_cases i <;> simp [maskPorts,wideState,wideTapes,maskHigh]

theorem maskPush_state (regs : Fin 8 → Bool) (a : D) (h : High) (rem acc : List Bool) :
    wpushed (wideState regs a (maskHigh h rem acc)) 34 false =
      wideState (Function.update regs 0 false) a (maskHigh h rem (false::acc)) := by
  apply congrArg (StructuredProgram.State.mk (Function.update regs 0 false))
  funext i
  fin_cases i <;> simp [wideState,wideTapes,maskHigh]

theorem replicate_snoc_false (k : ℕ) (acc : List Bool) :
    List.replicate k false ++ false::acc = List.replicate (k+1) false ++ acc := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (false::·) ih

theorem maskLoop_visits (a : D) (h : High) (rem : List Bool) :
    ∀ (regs : Fin 8 → Bool) (acc : List Bool), ∃ costs rr,
      UnaryForPrograms.Visits maskPorts (wpush 34 false) costs (4*rem.length+2)
        (wideState regs a (maskHigh h rem acc))
        (wideState rr a (maskHigh h [] (List.replicate rem.length false++acc))) := by
  induction rem with
  | nil =>
      intro regs acc
      have hv := UnaryForPrograms.Visits.done (p:=maskPorts) (body:=wpush 34 false)
        (wideState regs a (maskHigh h [] acc)) (by rfl)
      rw [maskPop_state] at hv
      exact ⟨[],_,by simpa using hv⟩
  | cons bit rem ih =>
      intro regs acc
      let r1 := readRegs regs 0 1 (some bit)
      let r2 := Function.update r1 0 false
      have hb := wpush_eval (wideState r1 a (maskHigh h rem acc)) 34 false
      rw [maskPush_state] at hb
      obtain ⟨costs,rr,ht⟩ := ih r2 (false::acc)
      have hb' : Eval (wpush 34 false) 2
          (UnaryForPrograms.popped maskPorts (wideState regs a (maskHigh h (bit::rem) acc)))
          (wideState r2 a (maskHigh h rem (false::acc))) := by
        rw [maskPop_state]
        exact hb
      have hv := UnaryForPrograms.Visits.step (p:=maskPorts) (body:=wpush 34 false)
        (d:=wideState regs a (maskHigh h (bit::rem) acc))
        (e:=wideState r2 a (maskHigh h rem (false::acc)))
        (nb:=2) (nt:=4*rem.length+2) (costs:=costs)
        (by simp only [maskCounter_state, ne_eq, List.cons_ne_nil, not_false_eq_true]) hb'
        (by simp only [maskCounter_state, UnaryForPrograms.popped_counter, List.tail_cons]) ht
      refine ⟨2::costs,rr,?_⟩
      have hcost : 2+(4*rem.length+2)+2 = 4*(bit::rem).length+2 := by simp; omega
      rw [hcost, replicate_snoc_false] at hv
      exact hv

theorem makeMask_eval (regs : Fin 8 → Bool) (a : D) (h : High)
    (hm : h.mask=[]) (hx : h.tmp2=[]) :
    ∃ rr, Eval makeMask (11*h.shape.length+7) (wideState regs a h)
      (wideState rr a {h with mask:=List.replicate h.shape.length false}) := by
  let d := wideState regs a h
  have hc := wcopy_eval d 36 38 23 (by decide) (by decide) (by decide) rfl
  have hcend : wcopied d 36 38=wideState (readRegs regs 0 1 none) a (maskHigh h h.shape []) := by
    apply congrArg (StructuredProgram.State.mk (readRegs regs 0 1 none))
    funext i
    fin_cases i <;> simp [d,wideState,wideTapes,maskHigh,copyStacks,hm,hx]
  rw [hcend] at hc
  obtain ⟨costs,rr,hl⟩ := maskLoop_visits a h h.shape (readRegs regs 0 1 none) []
  have he := hc.seq hl.eval
  change Eval makeMask (7*h.shape.length+5+(4*h.shape.length+2))
    (wideState regs a h)
    (wideState rr a (maskHigh h [] (List.replicate h.shape.length false++[]))) at he
  have hend : maskHigh h [] (List.replicate h.shape.length false++[]) =
      {h with mask:=List.replicate h.shape.length false} := by
    simp [maskHigh,hx]
  have hcost : 7*h.shape.length+5+(4*h.shape.length+2)=11*h.shape.length+7 := by omega
  rw [hend,hcost] at he
  exact ⟨rr,he⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem prepare_eval (regs : Fin 8 → Bool) (a : D) (zero t J shape : List Bool) :
    ∃ rr, Eval prepare (11*shape.length+7*J.length+12)
      (wideState regs a (inputHigh zero t J shape))
      (wideState rr a (outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false} 0 J [])) := by
  obtain ⟨r1,h1⟩ := makeMask_eval regs a (inputHigh zero t J shape) rfl rfl
  let h := {inputHigh zero t J shape with mask:=List.replicate shape.length false}
  let d := wideState r1 a h
  have h2 := wcopy_eval d 29 33 23 (by decide) (by decide) (by decide) rfl
  have hd29 : (d.stacks 29).length = J.length := by
    simp [d, h, inputHigh, wideState, wideTapes ]
  rw [hd29] at h2
  have hend : wcopied d 29 33=wideState (readRegs r1 0 1 none) a (outerHigh h 0 J []) := by
    apply congrArg (StructuredProgram.State.mk (readRegs r1 0 1 none))
    funext i
    fin_cases i <;> simp [d,h,wideState,wideTapes,copyStacks,
      outerHigh,inputHigh,unary]
  rw [hend] at h2
  refine ⟨readRegs r1 0 1 none,?_⟩
  have hcost : (11 * shape.length + 7) + (7 * J.length + 5) =
      11 * shape.length + 7 * J.length + 12 := by omega
  simpa only [prepare, hcost, d, h, inputHigh] using h1.seq h2

theorem finish_eval (regs : Fin 8 → Bool) (a : D) (zero t J shape bits : List Bool)
    (ho : a.out=[]) :
    ∃ rr, Eval finish (3*bits.length+2*J.length+2*shape.length+9)
      (wideState regs a (outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false}
        J.length [] bits.reverse))
      (wideState rr {a with out:=bits} (inputHigh zero t J shape)) := by
  let h := outerHigh {inputHigh zero t J shape with mask:=List.replicate shape.length false}
    J.length [] bits.reverse
  let d := wideState regs a h
  let d1 := wtransferred d 35 0
  let d2 := wcleared d1 31
  let d3 := wcleared d2 34
  have h1 := wtransfer_eval d 35 0 (by decide)
  have h2 := wclear_eval d1 31
  have h3 := wclear_eval d2 34
  have hend : d3=wideState d3.regs {a with out:=bits} (inputHigh zero t J shape) := by
    apply congrArg (StructuredProgram.State.mk d3.regs)
    funext i
    fin_cases i <;> simp [d2,d1,d,h,wtransferred,wcleared,wideState,wideTapes,
      outerHigh,inputHigh,unary,transferStacks,clearStacks,ho]
  have he := h1.seq (h2.seq h3)
  change Eval finish _ d d3 at he
  rw [hend] at he
  refine ⟨d3.regs,?_⟩
  convert he using 1 ;
    simp [d2,d1,d,h,wtransferred,wcleared,wideState,wideTapes,outerHigh,
      inputHigh,unary,transferStacks,clearStacks] ; omega

theorem command_eval {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ time ≤ readoutBudget (baseWidth p e) d n t.length J.length encoded, ∃ rr,
      Eval command time
        (wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
          (inputHigh (RingProgram.flat zero) t J shape))
        (wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
          (inputHigh (RingProgram.flat zero) t J shape)) := by
  dsimp only
  let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
  let a := MomentsProgram.Dictionary.inputTape M.bits width count encoded [] []
  let h := {inputHigh (RingProgram.flat zero) t J shape with mask:=List.replicate shape.length false}
  obtain ⟨r1,h1⟩ := prepare_eval regs a (RingProgram.flat zero) t J shape
  obtain ⟨tm,htm,r2,h2⟩ := outer_eval p e M cache entries t.length zero width count h 0 J [] r1
    hc hw (by simp [h,hs]) rfl rfl
  let bits := outputBits p e M cache entries t.length zero 0 J.length
  obtain ⟨r3,h3⟩ := finish_eval r2 a (RingProgram.flat zero) t J shape bits rfl
  have h2' : Eval outer tm (wideState r1 a (outerHigh h 0 J []))
      (wideState r2 a (outerHigh h J.length [] bits.reverse)) := by
    simpa [bits] using h2
  refine ⟨_,?_,r3,h1.seq (h2'.seq h3)⟩
  have hl : bits.length=J.length*(d*baseWidth p e) := outputBits_length p e M cache entries t.length zero 0 J.length
  dsimp [readoutBudget]
  omega

theorem program_runsIn_oai {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (zero : RingProgram.Code (Word (baseWidth p e)) d)
    (regs : Fin 8 → Bool) (width count t J shape : List Bool)
    (hc : count.length=d) (hw : width.length=baseWidth p e) (hs : shape.length=n) :
    let encoded := Squarefree.Program.encodeDictionary Squarefree.encodeIndex RingProgram.flat entries
    let bits := outputBits p e M cache entries t.length zero 0 J.length
    ∃ rr, RunsIn program (readoutBudget (baseWidth p e) d n t.length J.length encoded+1)
      ((wideState regs (MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [])
        (inputHigh (RingProgram.flat zero) t J shape)).withPC (some program.entry))
      ((wideState rr {MomentsProgram.Dictionary.inputTape M.bits width count encoded [] [] with out:=bits}
        (inputHigh (RingProgram.flat zero) t J shape)).withPC none) := by
  obtain ⟨time,ht,rr,he⟩ := command_eval p e M cache entries zero regs width count t J shape hc hw hs
  exact ⟨rr,⟨time+1,by omega,compiled_halt_trace he 15 0⟩⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn_oai
