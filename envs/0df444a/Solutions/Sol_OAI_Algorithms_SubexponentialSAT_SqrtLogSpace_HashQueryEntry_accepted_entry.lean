-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:06:29.950167+00:00
-- url     : https://prove2.me/submissions/2a4d1f4c-f8c7-4496-bc79-90b32419b20b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_supplied_history_raw_encoding

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

theorem width_pos (m : ℕ) : 0 < width m := by
  unfold width
  omega

theorem lt_two_pow_width (m : ℕ) : m < 2 ^ width m :=
  Nat.lt_pow_succ_log_self (by decide) m

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem literalCode_lt {n : ℕ} (l : SAT.Literal (Fin n)) : literalCode l < 2 * n := by
  have hv := l.variable.isLt
  cases hp : l.positive <;> simp [literalCode, hp] ; omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

theorem digitWidth_sufficient (m : ℕ) : 3 * m ≤ 2 ^ digitWidth m :=
  (DyadicWidth.lt_two_pow_width _).le


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem routes_frame (ps : List Route) (a : Data) (i : Fin 896)
    (hi : ∀ p ∈ ps, p.2 ≠ i) : (routesState ps a).stacks i = a.stacks i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [routesState,ih (routed p a) (fun q hq => hi q (by simp [hq]))]
    exact Function.update_of_ne (Ne.symm (hi p (by simp))) _ _

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

theorem finalStaged_sources (a : Data) :
    (finalStaged a).stacks 700=a.stacks 784 ∧
    (finalStaged a).stacks 701=a.stacks 777 ∧
    (finalStaged a).stacks 707=a.stacks 782 ∧
    (finalStaged a).stacks 708=a.stacks 783 ∧
    (finalStaged a).stacks 709=a.stacks 785 := by
  simp [finalStaged,masterRoutes,routesState,routed]

theorem finalStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (finalStaged a).stacks i=a.stacks i := by
  apply routes_frame
  intro p hp
  simp only [masterRoutes,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact Ne.symm h0
  · exact Ne.symm h7
  · exact Ne.symm h8
  · exact Ne.symm h9
  · exact Ne.symm h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

theorem temporary_frame (a : State 40 896) (i : Fin 896) (hi : i ≠ 767) :
    (temporaryCleared a).stacks i = a.stacks i := clearStacks_frame _ _ _ hi

theorem staged_sources (a : State 40 896) :
    (staged a).stacks 700 = a.stacks 784 ∧
    (staged a).stacks 701 = a.stacks 777 ∧
    (staged a).stacks 707 = a.stacks 782 ∧
    (staged a).stacks 708 = a.stacks 783 ∧
    (staged a).stacks 709 = a.stacks 785 := by
  simpa only [staged, temporary_frame _ 784 (by decide), temporary_frame _ 777 (by decide),
    temporary_frame _ 782 (by decide), temporary_frame _ 783 (by decide),
    temporary_frame _ 785 (by decide)] using LeafOuterNative.finalStaged_sources (temporaryCleared a)

theorem staged_frame (a : State 40 896) (i : Fin 896)
    (hi : i ∉ HashMassStaged.stagedPorts) (ht : i ≠ 767) :
    (staged a).stacks i = a.stacks i := by
  have hn : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [HashMassStaged.stagedPorts] using hi
  exact (LeafOuterNative.finalStaged_frame _ i hn.1 hn.2.1
    hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).trans (temporary_frame a i ht)

/-- The accepted history stage does not use the trial-prefix scratch. -/
theorem staged_702 (a : State 40 896) : (staged a).stacks 702 = a.stacks 702 :=
  (LeafOuterNative.finalStaged_frame _ 702 (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans (temporary_frame a 702 (by decide))

theorem staged_temporary (a : State 40 896) : (staged a).stacks 767 = [] := by
  change (LeafOuterNative.finalStaged (temporaryCleared a)).stacks 767 = []
  rw [LeafOuterNative.finalStaged_frame _ 767 (by decide) (by decide) (by decide)
    (by decide) (by decide)]
  simp [temporaryCleared]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
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


theorem mem_interpreted_scope (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ)
    (terms : List (Fin clauses.length × ZMod 3)) (v : ℕ) :
    v ∈ scope (interpretedTerms (clauses := clauses) t d codes terms) ↔
      ∃ a∈terms, ∃ c∈codes a.1, c/2=v := by
  rw [mem_scope]
  constructor
  · rintro ⟨term,hterm,c,hc,hv⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hterm
    exact ⟨a,ha,c,hc,hv⟩
  · rintro ⟨a,ha,c,hc,hv⟩
    exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,c,hc,hv⟩

end FromTuple
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

theorem recordCodes_word {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    (NativeTerminal.clauseRecords F)[i.val] =
      Encoding.encodeList Encoding.encodeNat (recordCodes F i) := by
  simp only [NativeTerminal.clauseRecords, List.getElem_map, recordCodes,
    List.get_eq_getElem, recordIndex, ExecSparsifyEncoding.encodeList_map]
  rfl

theorem recordCodes_lt {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    ∀ v ∈ recordCodes F i, v < 2 * n := by
  intro v hv
  obtain ⟨lit,_hmem,rfl⟩ := List.mem_map.mp hv
  exact Encoding.literalCode_lt lit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem unmarkedInput_index (a : Data) (h705 : a.stacks 705=[]) :
    (unmarkedInput a).stacks 705=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705]

theorem unmarkedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (unmarkedInput a).stacks 706=[false] := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h706]

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem cleanWork_private (a : Data) (h : CleanWork a) (i : Fin 768)
    (hlo : 340 ≤ i.val) (hhi : i.val < 680) : a.stacks i=[] := by
  apply h
  · intro hp
    simp only [Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hp
    norm_num at hp
    omega
  · intro hi
    subst i
    norm_num at hlo

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendSources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed source and empty-workspace relations follow from the actual trial
and accepted source stages. Changing the marked clause does not change the
immutable source words; its scope and high mask are recomputed by the frontend. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HighMarkedFrontend

private theorem cast_ne {i j : Fin 768} (h : i ≠ j) : stackMap i ≠ stackMap j :=
  fun he => h (Fin.castAdd_injective 768 128 he)

private theorem unprotected_ne (i : Fin 768) (hi : ¬LeafProgram.Query.Protected i)
    (j : Fin 768) (hj : LeafProgram.Query.Protected j) : i ≠ j := by
  intro h
  subst i
  exact hi hj

private theorem outside_staged (i : Fin 768) (hi : ¬LeafProgram.Query.Protected i)
    (h702 : i ≠ 702) : stackMap i ∉ HashMassStaged.stagedPorts := by
  simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨cast_ne (unprotected_ne i hi 700 (by decide)),
    cast_ne (unprotected_ne i hi 701 (by decide)), cast_ne h702,
    cast_ne (unprotected_ne i hi 707 (by decide)),
    cast_ne (unprotected_ne i hi 708 (by decide)),
    cast_ne (unprotected_ne i hi 709 (by decide))⟩

/-- The accepted stage uses the saved history literally, with no candidate
prefix and no replacement of the declared ambient count. -/
theorem accepted_sources (q : LeafQueryFrontend.Query) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784 = Encoding.encodeList id q.clauses)
    (hr : a.stacks 777 = HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (hm : a.stacks 782 = q.modulus) (hw : a.stacks 783 = q.width)
    (hn : a.stacks 785 = q.ambient) :
    LeafProgram.Query.Sources q (project (AcceptedQueryStage.staged a)) := by
  obtain ⟨h0,h1,h7,h8,h9⟩ := AcceptedQueryStage.staged_sources a
  exact ⟨h0.trans hf,h1.trans hr,h7.trans hm,h8.trans hw,h9.trans hn⟩

theorem accepted_clean (a : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a)) :
    LeafProgram.Query.CleanWork (project (AcceptedQueryStage.staged a)) := by
  intro i hi h321
  change (AcceptedQueryStage.staged a).stacks (stackMap i) = []
  by_cases h702 : i = 702
  · subst i
    exact (AcceptedQueryStage.staged_702 a).trans (hc 702 (by decide) (by decide))
  have ht : stackMap i ≠ 767 := cast_ne (unprotected_ne i hi 767 (by decide))
  rw [AcceptedQueryStage.staged_frame a _ (outside_staged i hi h702) ht]
  exact hc i hi h321

/-- Every current hashed or marked scope comes from an actual source literal.
This applies uniformly to the optional mark; no precomputed scope bound is an
input to the machine. -/
theorem scopeRows_lt (q : LeafQueryFrontend.Query) (n : ℕ)
    (hc : ∀ i, ∀ c ∈ q.codes i, c < 2*n) :
    ∀ row ∈ q.scopeRows, ∀ v ∈ row, v < n := by
  intro row hr v hv
  change row ∈ (q.rows.map (fun terms => HashScopeProgram.scope
    (HashScopeProgram.FromTuple.interpretedTerms (clauses := q.clauses) 1 0 q.codes terms)) ++
      q.mark.toList.map (fun i => HashScopeProgram.Marked.markedScope (q.codes i))) at hr
  rcases List.mem_append.mp hr with hh | hm
  · obtain ⟨terms,_ht,rfl⟩ := List.mem_map.mp hh
    obtain ⟨term,_hm,c,hc',rfl⟩ :=
      (HashScopeProgram.FromTuple.mem_interpreted_scope 1 0 q.codes terms v).mp hv
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc term.1 c hc')
  · obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hm
    obtain ⟨c,hc',he⟩ := (SubexpScopeProducer.mem_scope [true] (q.codes i) v).mp hv
    have he' : c/2=v := by simpa [BinaryArithmetic.toNat,BinaryArithmetic.bitVal] using he
    rw [← he']
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc i c hc')

theorem rawQuery_clauses {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) :
    ∀ i, (rawQuery F rows mark index width modulus ambient).clauses[i.val]=
      Encoding.encodeList Encoding.encodeNat
        ((rawQuery F rows mark index width modulus ambient).codes i) :=
  NativeLeafSemantics.recordCodes_word F

theorem rawQuery_scopeRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) (hn : BinaryArithmetic.toNat ambient=n) :
    ∀ row ∈ (rawQuery F rows mark index width modulus ambient).scopeRows,
      ∀ v ∈ row, v < BinaryArithmetic.toNat ambient := by
  rw [hn]
  exact scopeRows_lt _ n (NativeLeafSemantics.recordCodes_lt F)

theorem inputBits_cast {m m' : ℕ} (h : m=m') (rows : HashScopeProgram.RawTable.Rows m)
    (width : ℕ) : HashScopeProgram.RawTable.inputBits width (castRows h rows)=
      HashScopeProgram.RawTable.inputBits width rows := by
  subst m'
  simp [castRows]

theorem recordRows_input {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (width : ℕ) :
    HashScopeProgram.RawTable.inputBits width (recordRows F rows)=
      HashScopeProgram.RawTable.inputBits width rows := inputBits_cast _ _ _

theorem recordMark_index {n : ℕ} (F : DisjointReuse.RawCNF n)
    (mark : Option (Fin F.length)) (index : List Bool)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val) :
    ∀ i, recordMark F mark=some i → index=Encoding.encodeNat i.val := by
  intro i h
  obtain ⟨j,hj,hji⟩ := Option.map_eq_some_iff.mp h
  subst i
  exact hi j hj

theorem rawQueryFromRows_accepted_sources {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784=Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hr : a.stacks 777=HashScopeProgram.RawTable.inputBits width.length rows)
    (hm : a.stacks 782=modulus) (hw : a.stacks 783=width) (hn : a.stacks 785=ambient) :
    LeafProgram.Query.Sources (rawQueryFromRows F rows mark index width modulus ambient)
      (project (AcceptedQueryStage.staged a)) := by
  apply accepted_sources _ a hf _ hm hw hn
  exact hr.trans (recordRows_input F rows width.length).symm

/-- Concrete raw records satisfy every source-side frontend validity field.
The positive ambient case is selected by the actual terminal dispatcher. -/
theorem rawQuery_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQuery F rows mark index width modulus ambient).Valid := by
  refine ⟨hw,?_,rawQuery_clauses F rows mark index width modulus ambient,
    ?_,hi,?_,rawQuery_scopeRows F rows mark index width modulus ambient ha⟩
  · simpa only [rawQuery,ha] using hn
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hsize
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hm

theorem rawQueryFromRows_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQueryFromRows F rows mark index width modulus ambient).Valid :=
  rawQuery_valid F _ _ index width modulus ambient hn hw hsize
    (recordMark_index F mark index hi) hm ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryAccepted
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The accepted (unmarked) query uses the same immutable source masters and
explicitly writes the two false singleton fields consumed by the frontend. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem accepted_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark=none) (hi : q.index=[false]) :
    q.Ready (unmarkedInput a) := by
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (unmarkedInput_frame a 700 (by decide) (by decide)).trans hs.formula
  · exact (unmarkedInput_frame a 701 (by decide) (by decide)).trans hs.rows
  · rw [hi]
    exact unmarkedInput_index a e705
  · simpa only [hm,Option.isSome_none] using unmarkedInput_flag a e706
  · exact (unmarkedInput_frame a 707 (by decide) (by decide)).trans hs.modulus
  · exact (unmarkedInput_frame a 708 (by decide) (by decide)).trans hs.width
  · exact (unmarkedInput_frame a 709 (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    rw [unmarkedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (unmarkedInput_frame a 338 (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (unmarkedInput_frame a 718 (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (unmarkedInput_frame a 719 (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalizer, trial source stage and marked-record parser supply
the literal query sources. These proofs impose no length cap on the suspended
reference tail or mass accumulator, and execute no extra marker stage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry

open BitProgram StructuredCalls SqrtLog
open HighFrontendSources HashGreedyCode

/-- The real paid accepted stage supplies the history-only source table and
clears its routing scratch. No second unmarked-input stage is introduced. -/
theorem accepted_entry_oai {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (d : Data)
    (hformula : d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hwidth : (d.stacks 783).length = HashCandidates.digitWidth F.length)
    (hmodulus : BinaryArithmetic.toNat (d.stacks 782) = F.length)
    (hambient : BinaryArithmetic.toNat (d.stacks 785) = n)
    (hclean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project d)) :
    AcceptedEntry (acceptedQuery F hm shifts Q rounds d) (AcceptedQueryStage.staged d) := by
  let q := acceptedQuery F hm shifts Q rounds d
  have hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project (AcceptedQueryStage.staged d)) := by
    apply rawQueryFromRows_accepted_sources F _ none [false]
      (d.stacks 783) (d.stacks 782) (d.stacks 785) d hformula _ rfl rfl rfl
    rw [hhistory, hwidth]
    exact supplied_history_raw_encoding (NativeLeafSemantics.indexed F) hm shifts Q rounds
  have hc := accepted_clean d hclean
  have hm' : q.mark = none := by
    simp [q, acceptedQuery, rawQueryFromRows, rawQuery, recordMark]
  have hi : q.index = [false] := rfl
  refine ⟨?_, hs, hc, hm', hi, hc 705 (by decide) (by decide),
    hc 706 (by decide) (by decide), AcceptedQueryStage.staged_temporary d, ?_⟩
  · apply rawQueryFromRows_valid F _ none [false]
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hn
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases he
    · exact hmodulus
    · exact hambient
  · exact LeafProgram.Query.accepted_ready q _ hc hs hm' hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry_oai
