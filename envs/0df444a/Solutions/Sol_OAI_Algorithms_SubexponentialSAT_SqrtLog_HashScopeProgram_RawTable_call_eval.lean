-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:44:33.073764+00:00
-- url     : https://prove2.me/submissions/50f630a2-6bee-460c-aa87-d5e422cac4dd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S119
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_loop_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashScopeProgram_Single_program_runsIn

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem scanInput_append {m : ℕ} (b : ℕ) (xs ys : List (Fin m × ZMod 3)) :
    scanInput b (xs++ys)=scanInput b xs++scanInput b ys := by
  simp [scanInput,List.flatten_append]

theorem scanInput_reverse {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) :
    scanInput b terms.reverse=rawInput b terms := by
  induction terms with
  | nil => rfl
  | cons a terms ih =>
      rw [List.reverse_cons,scanInput_append,ih]
      have ha : scanInput b [a]=(word b m a).reverse := by simp [scanInput]
      rw [ha]
      simp [rawInput]

theorem original_payload_length_le (clauses : List (List Bool)) (p : List Bool)
    (hp : p∈clauses) : p.length ≤ (Encoding.encodeList id clauses).length := by
  induction clauses with
  | nil => simp at hp
  | cons q qs ih =>
      have hq := Encoding.length_frame q
      simp only [Encoding.encodeList,id_eq,Encoding.length_frame,List.length_cons,List.length_append] at *
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have hh := ih hp
        omega

theorem loopBudget_le (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) :
    loopBudget t d b modulus.length clauses terms ≤ uniformBudget t d b modulus clauses terms.length := by
  induction terms with
  | nil => simp [loopBudget,uniformBudget]
  | cons a terms ih =>
      have hc := original_payload_length_le clauses clauses[a.1.val] (List.getElem_mem a.1.isLt)
      simp only [loopBudget,uniformBudget,List.map_cons,List.sum_cons,List.length_cons] at *
      unfold termBudget at *
      nlinarith

theorem initializeRow_eval (regs : Fin 8 → Bool) (raw width modulus master shape : List Bool) :
    Eval initializeRow 2 (data regs raw width modulus master shape [] [] [] [] [])
      (data (Function.update regs 0 false) raw width modulus master shape [false] [] [] [] []) := by
  let a := data regs raw width modulus master shape [] [] [] [] []
  let b := (StructuredProgram.Atom.set (0 : Fin 8) false).eval a
  have h1 : Eval (.base (.atom (.set 0 false))) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (16 : Fin 24) 0) b)
  convert h1.seq h2 using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

/-- The input is only the reversed raw tuple plus the original source bytes
and dynamic size data. The fully inlined payload is produced by the run. -/
theorem assemble_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ uniformBudget t d b modulus clauses terms.length+2, ∃ rf,
      Eval assemble n
        (data regs (rawInput b terms) width modulus (Encoding.encodeList id clauses)
          shape [] [] [] [] [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (Encoding.encodeList id (terms.map (payload t d clauses))) [] [] [] []) := by
  have hi := initializeRow_eval regs (rawInput b terms) width modulus (Encoding.encodeList id clauses) shape
  obtain ⟨n,hn,rf,he⟩ := loop_eval t d ht b hb clauses terms.reverse hbound
    (Function.update regs 0 false) width modulus shape [false] hw hm hshape
  rw [scanInput_reverse,List.reverse_reverse] at he
  have hh (ps : List (List Bool)) : records ps [false]=Encoding.encodeList id ps := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
        change true::(Encoding.frame p++records ps [false]) =
          true::(Encoding.frame p++Encoding.encodeList id ps)
        rw [ih]
  rw [hh] at he
  have hcost := loopBudget_le t d b modulus clauses terms.reverse
  simp only [List.length_reverse] at hcost
  exact ⟨2+n,by omega,rf,hi.seq he⟩

theorem assemble_runs (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool)
    (hw : width.length=b) (hm : SubexponentialSAT.BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn assembleProgram (uniformBudget t d b modulus clauses terms.length+3)
      ((data regs (rawInput b terms) width modulus (Encoding.encodeList id clauses)
        shape [] [] [] [] []).withPC (some assembleProgram.entry))
      ((data rf [] width modulus (Encoding.encodeList id clauses) shape
        (Encoding.encodeList id (terms.map (payload t d clauses))) [] [] [] []).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := assemble_eval t d ht b hb clauses terms hbound regs width modulus shape hw hm hshape
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 16⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace FromTuple

theorem interpreted_payload (t d : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) :
    Encoding.encodeList payload (interpretedTerms (clauses := clauses) t d codes terms)=
      Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses)) := by
  induction terms with
  | nil => rfl
  | cons a as ih =>
      simpa [interpretedTerms,Encoding.encodeList,payload,HashInputProgram.Loop.payload,hc] using
        congrArg (fun rest => true :: (Encoding.frame (HashInputProgram.Loop.payload t d clauses a) ++ rest)) ih


end FromTuple
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramReset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Reset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (command is) is.length a (result is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip _)
  | cons i is ih =>
      let b : State r s := ⟨Function.update a.regs i false,a.stacks⟩
      have hs : Eval (.base (.atom (.set i false))) 1 a b := .base (.atom _ _)
      have he : result is b = result (i::is) a := by
        apply congrArg₂ StructuredProgram.State.mk
        · funext j
          by_cases hji : j=i <;> by_cases hj : j ∈ is <;>
            simp [b,hji,hj,Function.update]
        · rfl
      have h := hs.seq (ih b)
      rw [he] at h
      simpa [command,Nat.add_comm] using h

theorem all_eval {r s : ℕ} (a : State r s) :
    Eval (all : Cmd r s) r a ⟨fun _ => false,a.stacks⟩ := by
  simpa [all,result] using command_eval (List.finRange r) a

end SubexponentialSAT.SqrtLog.HashScopeProgram.Reset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct original-source-to-scope composition. The finite program first reads
raw tuple references and looks up original clauses, then extracts their scope.
No table of precomputed scopes is supplied to this machine. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem assemblyRegisters_injective : Function.Injective assemblyRegisters :=
  Fin.castAdd_injective _ _
theorem assemblyStacks_injective : Function.Injective assemblyStacks :=
  Fin.castAdd_injective _ _
theorem scopeStacks_injective : Function.Injective scopeStacks := by decide

private theorem restrict_extend (a : State 8 24) :
    restrictState assemblyRegisters assemblyStacks (extend a)=a := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; simp [restrictState,extend,assemblyRegisters,i.isLt]
  · funext i; simp [restrictState,extend,assemblyStacks,i.isLt]

private theorem embed_extend (a b : State 8 24) :
    embedState assemblyRegisters assemblyStacks (extend a) b=extend b := by
  apply embedState_eq_of_ports _ _ _ _ _ assemblyRegisters_injective assemblyStacks_injective
  · intro i; simp [extend,assemblyRegisters,i.isLt]
  · intro i hi
    have hn : ¬i.val < 8 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    simp [extend,hn]
  · intro i; simp [extend,assemblyStacks,i.isLt]
  · intro i hi
    have hn : ¬i.val < 24 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    simp [extend,hn]


private theorem extract_eval (terms : List Term) (a : Data)
    (hr : a.regs=fun _ => false)
    (hs : a.stacks 16=Encoding.encodeList payload terms)
    (he : ∀ i : Fin 22, i≠19 → a.stacks (scopeStacks i)=[]) :
    ∃ n ≤ Single.cost terms, ∃ rf,
      Eval extract n a (scopeState rf a (Encoding.encodeList Encoding.encodeNat (scope terms))) := by
  obtain ⟨rf,ht⟩ := Single.program_runsIn terms
  let localState : State 11 22 := ⟨rf,SubexponentialSAT.SubexpChunkRecordMap.tapes [true]
    (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩
  have ha : restrictState id scopeStacks a=
      SubexponentialSAT.SubexpChunkRecordMap.data false false false [] (Encoding.encodeList payload terms) [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState,hr,SubexponentialSAT.SubexpChunkRecordMap.data,SubexponentialSAT.SubexpChunkRecordMap.regs]
    · funext i
      by_cases hi : i=19
      · subst i; simpa [restrictState,scopeStacks,SubexponentialSAT.SubexpChunkRecordMap.data,
          SubexponentialSAT.SubexpChunkRecordMap.tapes] using hs
      · simpa [restrictState,SubexponentialSAT.SubexpChunkRecordMap.data,SubexponentialSAT.SubexpChunkRecordMap.tapes,hi]
          using he i hi
  obtain ⟨n,hn,hh⟩ := lifted_call Single.program id scopeStacks Function.injective_id
    scopeStacks_injective a localState (Single.cost terms) (by simpa [ha,localState] using ht)
  have hb : embedState id scopeStacks a localState=
      scopeState rf a (Encoding.encodeList Encoding.encodeNat (scope terms)) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scopeStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      have hei := he i
      fin_cases i <;> simp_all [scopeState,scopeStacks,localState,SubexponentialSAT.SubexpChunkRecordMap.tapes]
    · intro i hi
      have h16 : i≠16 := fun h => hi ⟨19,h.symm⟩
      have h42 : i≠42 := fun h => hi ⟨18,h.symm⟩
      simp [scopeState,h16,h42]
  exact ⟨n,hn,rf,by simpa [hb] using hh⟩

private theorem clearEll_eval (rf : Fin 11 → Bool)
    (width modulus master shape oldBits bits : List Bool) :
    Eval clearEll 5
      (scopeState rf (finished (fun _ => false) width modulus master shape oldBits) bits)
      (finished (readRegs rf 8 9 none) width modulus master shape bits) := by
  have hh := SubexponentialSAT.Subexp.TupleProgram.clear_eval (42 : Fin 46) (8 : Fin 11) 9
    (scopeState rf (finished (fun _ => false) width modulus master shape oldBits) bits)
  convert hh using 1
  · simp [scopeState]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))

/-- The output is produced from raw references and the unexpanded original
clause bytes, including every zero-coefficient and repeated reference. -/
theorem state_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (cost t d b modulus clauses codes terms)
      ((extend (HashInputProgram.Loop.data regs (HashInputProgram.Loop.rawInput b terms) width modulus
        (Encoding.encodeList id clauses) shape [] [] [] [] [])).withPC (some program.entry))
      ((finished rf width modulus (Encoding.encodeList id clauses) shape
        (Encoding.encodeList Encoding.encodeNat
          (scope (interpretedTerms (clauses := clauses) t d codes terms)))).withPC none) := by
  let initial := HashInputProgram.Loop.data regs (HashInputProgram.Loop.rawInput b terms) width modulus
    (Encoding.encodeList id clauses) shape [] [] [] [] []
  obtain ⟨rf,hassemble⟩ := HashInputProgram.Loop.assemble_runs t d ht b hb clauses terms hbound regs
    width modulus shape hw hm hshape
  let middle := HashInputProgram.Loop.data rf [] width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses))) [] [] [] []
  obtain ⟨na,hna,hea⟩ := lifted_call HashInputProgram.Loop.assembleProgram assemblyRegisters assemblyStacks
    assemblyRegisters_injective assemblyStacks_injective (extend initial) middle
    (HashInputProgram.Loop.uniformBudget t d b modulus clauses terms.length+3)
    (by simpa [restrict_extend,initial,middle] using hassemble)
  rw [embed_extend] at hea
  let clean : Data := ⟨fun _ => false,(extend middle).stacks⟩
  have her : Eval (Reset.all : Cmd 11 46) 11 (extend middle) clean := Reset.all_eval _
  obtain ⟨ns,hns,rs,hes⟩ := extract_eval (interpretedTerms (clauses := clauses) t d codes terms) clean rfl
    (by simpa [clean,extend,middle,HashInputProgram.Loop.data,HashInputProgram.Loop.tapes] using
      (interpreted_payload t d clauses codes hc terms).symm)
    (by intro i hi; simp [clean,extend,scopeStacks,hi])
  have hclear := clearEll_eval rs width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses)))
    (Encoding.encodeList Encoding.encodeNat (scope (interpretedTerms (clauses := clauses) t d codes terms)))
  refine ⟨readRegs rs 8 9 none,na+(11+(ns+5))+1,?_,?_⟩
  · unfold cost; omega
  · exact compiled_halt_trace (hea.seq (her.seq (hes.seq hclear))) 0 16



end SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

theorem callStacks_injective : Function.Injective callStacks := Fin.castAdd_injective _ _

theorem call_eval_oai (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3)) (hbound : 3*clauses.length ≤ 2^b)
    (width modulus shape source out : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ n ≤ FromTuple.cost t d b modulus clauses codes terms, ∃ rf,
      Eval call n
        (data zeroRegs (rowBits b terms).reverse width modulus
          (Encoding.encodeList id clauses) shape [] source [] out [])
        (data rf [] width modulus (Encoding.encodeList id clauses) shape
          (scopeBytes (clauses := clauses) t d codes terms) source [] out []) := by
  obtain ⟨rf,h⟩ := FromTuple.state_runsIn t d ht b hb clauses codes hc terms hbound
    (fun _ => false) width modulus shape hw hm hshape
  let a := data zeroRegs (rowBits b terms).reverse width modulus
    (Encoding.encodeList id clauses) shape [] source [] out []
  let z := FromTuple.finished rf width modulus (Encoding.encodeList id clauses) shape
    (scopeBytes (clauses := clauses) t d codes terms)
  have ha : restrictState id callStacks a=FromTuple.extend
      (HashInputProgram.Loop.data (fun _ => false) (HashInputProgram.Loop.rawInput b terms)
        width modulus (Encoding.encodeList id clauses) shape [] [] [] [] []) := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨n,hn,he⟩ := lifted_call FromTuple.program id callStacks Function.injective_id
    callStacks_injective a z (FromTuple.cost t d b modulus clauses codes terms)
    (by simpa [ha,z,scopeBytes] using h)
  have hz : embedState id callStacks a z=
      data rf [] width modulus (Encoding.encodeList id clauses) shape
        (scopeBytes (clauses := clauses) t d codes terms) source [] out [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id callStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,h.symm⟩
      have h7 : i≠7 := fun h => hi ⟨7,h.symm⟩
      have h14 : i≠14 := fun h => hi ⟨14,h.symm⟩
      have h15 : i≠15 := fun h => hi ⟨15,h.symm⟩
      have h16 : i≠16 := fun h => hi ⟨16,h.symm⟩
      have h45 : i≠45 := fun h => hi ⟨45,h.symm⟩
      simp [a,data,h0,h1,h7,h14,h15,h16,h45]
  exact ⟨n,hn,rf,by simpa [call,hz] using he⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval_oai
