-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:53.874448+00:00
-- url     : https://prove2.me/submissions/87ecdb66-0116-4b82-b847-740e09c1cf6e

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S144
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Loop_loop_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact pure result functions of the fixed native hash interpreter. The
execution proofs live in HashCircuitProgramInterpreter; no alternate evaluator
or operation oracle is introduced here. -/

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)

/-- The supplied clause bytes are the original canonical literal list. -/
theorem literalList_eq {n B d : ℕ} (w : WeightedClause n B d) :
    literalList w = Encoding.encodeList Encoding.encodeNat (w.literals.map Encoding.literalCode) := by
  cases w with
  | mk scalar ls =>
    dsimp [literalList]
    induction ls with
    | nil => rfl
    | cons l ls ih =>
      simpa [Encoding.encodeList,Clause.literalBits] using
        (congrArg (fun xs => true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++ xs)) ih)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-clause provenance for a raw tuple, including repetitions.
The integer lift is taken BEFORE the tuple terms are added; its reduction, not
its value in the thickened ring, equals the combined ternary selector row. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open scoped BigOperators
open LeafProgram

/-- Original literal byte order is retained, including repeated literals. -/
theorem clausePayload_codes {n : ℕ} (ls : List (SAT.Literal (Fin n))) :
    clausePayload ls = Encoding.encodeList Encoding.encodeNat (ls.map Encoding.literalCode) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      change true :: (Encoding.frame (Encoding.encodeNat (Encoding.literalCode l)) ++
        clausePayload ls) = _
      simp only [List.map_cons,Encoding.encodeList]
      rw [ih]

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native expansion of one selected raw hash row.  The row is read from the
dispatcher result; every original clause lookup and coefficient lift is paid
by the fixed assembler.  The original formula and dynamic width words are
read in place, so they remain available for the next factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion

open SubexponentialSAT BitProgram StructuredCalls

theorem register_injective : Function.Injective register :=
  Fin.castAdd_injective 8 32

theorem stackMap_injective : Function.Injective stackMap := by decide

/-- The only inputs besides the actual row/source bytes are represented
runtime dimensions.  In particular, the theorem does not assume a supplied
inline row or a trace for a source lookup. -/
theorem command_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (a : Data)
    (hraw : a.stacks 154=HashInputProgram.Loop.rawInput b terms)
    (hsource : a.stacks 700=Encoding.encodeList id clauses)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=clauses.length)
    (hshape : (a.stacks 280).length=(d+1)*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hwork : ∀ i∈scratch, a.stacks i=[]) :
    ∃ k rf, k ≤ HashInputProgram.Loop.uniformBudget t d b (a.stacks 707)
        clauses terms.length+3 ∧
      Eval command k a (finished a rf (outputWord t d clauses terms)) := by
  obtain ⟨rf,k,hk,he⟩ := HashInputProgram.Loop.assemble_runs t d ht b hb clauses terms
    hbound (a.regs ∘ register) (a.stacks 708) (a.stacks 707) (a.stacks 280)
    hwidth hmodulus hshape
  have hi : projectState register stackMap a =
      HashInputProgram.Loop.data (a.regs ∘ register)
        (HashInputProgram.Loop.rawInput b terms) (a.stacks 708) (a.stacks 707)
        (Encoding.encodeList id clauses) (a.stacks 280) [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        first | exact hraw | exact hsource | exact houtput | rfl | exact hwork _ (by decide)
  rw [← hi] at he
  have lifted := eval_call_from_state HashInputProgram.Loop.assembleProgram
    register stackMap a register_injective stackMap_injective he
  refine ⟨k,rf,hk,?_⟩
  simpa only [command,finished,outputWord,hsource] using lifted

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramExpansionForward
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The preserved source lookup returns forward frame contents. Reverse this
actual tape before invoking the raw-tuple assembler. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem reversedInput_frame (a : Data) (i : Fin 768) (hi : i ≠ 154) :
    (reversedInput a).stacks i = a.stacks i := by
  simp [reversedInput,afterReverse,StackRoutines.reverseStacks,hi]

private theorem scratch_ne_input (i : Fin 768) (hi : i ∈ scratch) : i ≠ 154 := by
  simp only [scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> decide

theorem forward_command_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (a : Data)
    (hraw : a.stacks 154 = (HashInputProgram.Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700 = Encoding.encodeList id clauses)
    (hwidth : (a.stacks 708).length = b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707) = clauses.length)
    (hshape : (a.stacks 280).length = (d+1)*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64 = [])
    (hwork : ∀ i ∈ scratch, a.stacks i = [])
    (h358 : a.stacks 358 = []) (h359 : a.stacks 359 = []) :
    ∃ k rf, k ≤ 9*(a.stacks 154).length + 7 +
        HashInputProgram.Loop.uniformBudget t d b (a.stacks 707) clauses terms.length + 3 ∧
      Eval forwardCommand k a
        (finished (reversedInput a) rf (outputWord t d clauses terms)) := by
  let x := reversedInput a
  have hframe (i : Fin 768) (hi : i ≠ 154) : x.stacks i = a.stacks i :=
    reversedInput_frame a i hi
  have hr : x.stacks 154 = HashInputProgram.Loop.rawInput b terms := by
    simp [x,reversedInput,afterReverse,StackRoutines.reverseStacks,hraw]
  have hw : ∀ i ∈ scratch, x.stacks i = [] := by
    intro i hi
    have hn := scratch_ne_input i hi
    exact (hframe i hn).trans (hwork i hi)
  obtain ⟨k,rf,hk,he⟩ := command_eval t d ht b hb clauses terms hbound x hr
    ((hframe 700 (by decide)).trans hsource)
    (by simpa only [hframe 708 (by decide)] using hwidth)
    (by simpa only [hframe 707 (by decide)] using hmodulus)
    (by simpa only [hframe 280 (by decide)] using hshape)
    ((hframe 64 (by decide)).trans houtput) hw
  have hv := reverse_eval a 154 358 359 0 1
    (by decide) (by decide) (by decide) (by decide) h358 h359
  have hk' : k ≤ HashInputProgram.Loop.uniformBudget t d b (a.stacks 707)
      clauses terms.length + 3 := by
    simpa only [hframe 707 (by decide)] using hk
  refine ⟨9*(a.stacks 154).length+7+k,rf,by omega,?_⟩
  exact hv.seq he

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem coefficient_flat (t D : ℕ) (hD : 0 < D) (c : ZMod 3) :
    RingProgram.flat (coefficient t D c)=RingProgram.flat (constantVector t (D-1) c) := by
  cases D with
  | zero => omega
  | succ d => rfl

theorem weightedClause_payload {n : ℕ} (t D : ℕ) (hD : 0 < D)
    (source : List (List (SAT.Literal (Fin n))))
    (term : Fin (encodedClauses source).length × ZMod 3) :
    Row.payload (weightedClause t D source term)=
      Loop.payload t (D-1) (encodedClauses source) term := by
  rw [Row.payload,Row.literalList_eq]
  simp only [weightedClause,coefficient_flat t D hD]
  rw [← clausePayload_codes]
  simp [Loop.payload,encodedClauses,originalClause]

/-- Exact serialized bytes, with every zero, repeated clause, and repeated
literal retained in original tuple order. -/
theorem outputWord_eq {n : ℕ} (t D : ℕ) (hD : 0 < D)
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3)) :
    LeafProgram.Expansion.outputWord t (D-1) (encodedClauses source) terms=
      Encoding.encodeList id ((weightedRow t D source terms).map Row.payload) := by
  unfold LeafProgram.Expansion.outputWord weightedRow
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  exact (weightedClause_payload t D hD source term).symm

theorem original_source_bytes {n : ℕ} (source : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (encodedClauses source)=ExecQuantitativeSparsify.encodeRawFormula source := by
  rw [encodedClauses,ExecSparsifyEncoding.encodeList_map]
  rw [ExecQuantitativeSparsify.encodeRawFormula,ExecSparsifyEncoding.encodeList_map]
  congr 1
  funext ls
  exact clausePayload_codes ls

/-- The forward physical parser output is reversed by the paid command. Its
full shape dimension and exact original formula bytes suffice to produce the
interpreter's forward weighted-row input; no serialization premise is added. -/
theorem forward_original_eval_oai {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (b : ℕ) (hb : 0 < b) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3))
    (hbound : 3*(encodedClauses source).length ≤ 2^b) (a : LeafProgram.Expansion.Data)
    (hraw : a.stacks 154=(Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=(encodedClauses source).length)
    (hshape : (a.stacks 280).length=D*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hwork : ∀ i∈LeafProgram.Expansion.scratch,a.stacks i=[])
    (h358 : a.stacks 358=[]) (h359 : a.stacks 359=[]) :
    ∃ k rf, k ≤ 9*(a.stacks 154).length+7+
        Loop.uniformBudget t (D-1) b (a.stacks 707) (encodedClauses source) terms.length+3 ∧
      Eval LeafProgram.Expansion.forwardCommand k a
        (LeafProgram.Expansion.finished (LeafProgram.Expansion.reversedInput a) rf
          (Encoding.encodeList id ((weightedRow t D source terms).map Row.payload))) := by
  have hdim : D-1+1=D := by omega
  have hs : a.stacks 700=Encoding.encodeList id (encodedClauses source) :=
    hsource.trans (original_source_bytes source).symm
  obtain ⟨k,rf,hk,he⟩ := LeafProgram.Expansion.forward_command_eval t (D-1) ht b hb
    (encodedClauses source) terms hbound a hraw hs hwidth hmodulus
    (by simpa only [hdim] using hshape) houtput hwork h358 h359
  rw [outputWord_eq t D hD source terms] at he
  exact ⟨k,rf,hk,he⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval_oai
