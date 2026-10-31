-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trial_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:08:59.906616+00:00
-- url     : https://prove2.me/submissions/9c63ea78-fa9c-402f-b863-b33a569a3d1b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S172
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_supplied_trial_word_raw_encoding

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

private theorem workPort_ne (i : Fin 891) (j : Fin 896) (hj : 320 ≤ j.val ∧ j.val ≤ 324) :
    workPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [workPort] at hv
  split_ifs at hv <;> simp only at hv <;> omega

@[simp] theorem workspace_recordState (a : Data) (v pr f : Bool) (src payload : List Bool) :
    workspace (RecordPrograms.state recordPorts a v pr f src payload) = workspace a := by
  funext i
  have hs := workPort_ne i 320 (by decide)
  have hp := workPort_ne i 321 (by decide)
  simp [workspace, RecordPrograms.state, recordPorts, hs, hp]

variable {X Row : Type*} [Fintype X] {m : ℕ}



/-- Equality of the retained workspace frames every port outside the five
physical collector words, including all high query and selector ports. -/
theorem workspace_frame (a b : Data) (h : workspace b = workspace a)
    (i : Fin 896) (h320 : i ≠ 320) (h321 : i ≠ 321) (h322 : i ≠ 322)
    (h323 : i ≠ 323) (h324 : i ≠ 324) : b.stacks i = a.stacks i := by
  have h320' : i.val ≠ 320 := by intro hh; exact h320 (Fin.ext hh)
  have h321' : i.val ≠ 321 := by intro hh; exact h321 (Fin.ext hh)
  have h322' : i.val ≠ 322 := by intro hh; exact h322 (Fin.ext hh)
  have h323' : i.val ≠ 323 := by intro hh; exact h323 (Fin.ext hh)
  have h324' : i.val ≠ 324 := by intro hh; exact h324 (Fin.ext hh)
  by_cases hlow : i.val < 320
  · let j : Fin 891 := ⟨i.val, by omega⟩
    have hj : workPort j = i := by simp [workPort, j, hlow]
    simpa only [workspace, hj] using congrFun h j
  · let j : Fin 891 := ⟨i.val - 5, by omega⟩
    have hj : workPort j = i := by
      apply Fin.ext
      simp [workPort, j, show ¬i.val - 5 < 320 by omega]
      omega
    simpa only [workspace, hj] using congrFun h j


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
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

theorem prefixed_rows (a : Data) :
    (prefixed a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 701) := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,
    TupleProgram.frame_eq_escaped,List.append_assoc]

theorem prefixed_scratch (a : Data) : (prefixed a).stacks 702=[] := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed]

theorem prefixed_frame (a : Data) (i : Fin 896) (h1 : i≠701) (h2 : i≠702) :
    (prefixed a).stacks i=a.stacks i := by
  simp [prefixed,trialPorts,TupleProgram.pushedState,routed,h1,h2]

theorem trialStaged_sources (a : Data) :
    (trialStaged a).stacks 700=a.stacks 784 ∧
    (trialStaged a).stacks 701=true::(Encoding.frame (a.stacks 768).reverse++a.stacks 777) ∧
    (trialStaged a).stacks 707=a.stacks 782 ∧
    (trialStaged a).stacks 708=a.stacks 783 ∧
    (trialStaged a).stacks 709=a.stacks 785 := by
  have h := finalStaged_sources a
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact (prefixed_frame _ 700 (by decide) (by decide)).trans h.1
  · rw [trialStaged,prefixed_rows,h.2.1,
      finalStaged_frame a 768 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact (prefixed_frame _ 707 (by decide) (by decide)).trans h.2.2.1
  · exact (prefixed_frame _ 708 (by decide) (by decide)).trans h.2.2.2.1
  · exact (prefixed_frame _ 709 (by decide) (by decide)).trans h.2.2.2.2

theorem trialStaged_frame (a : Data) (i : Fin 896)
    (h0 : i≠700) (h1 : i≠701) (h2 : i≠702) (h7 : i≠707) (h8 : i≠708) (h9 : i≠709) :
    (trialStaged a).stacks i=a.stacks i :=
  (prefixed_frame _ i h1 h2).trans (finalStaged_frame a i h0 h1 h7 h8 h9)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

theorem staged_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ stagedPorts) :
    (LeafOuterNative.trialStaged a).stacks i = a.stacks i := by
  have hne : i ≠ 700 ∧ i ≠ 701 ∧ i ≠ 702 ∧ i ≠ 707 ∧ i ≠ 708 ∧ i ≠ 709 := by
    simpa [stagedPorts] using hi
  exact LeafOuterNative.trialStaged_frame a i hne.1 hne.2.1 hne.2.2.1
    hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
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

theorem markedInput_index (a : Data) (h699 : a.stacks 699=[]) (h705 : a.stacks 705=[]) :
    (markedInput a).stacks 705=(a.stacks 321).reverse := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h699,h705]

theorem markedInput_flag (a : Data) (h706 : a.stacks 706=[]) :
    (markedInput a).stacks 706=[true] := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,h706]

theorem markedInput_frame (a : Data) (i : Fin 768)
    (hi : i≠699) (h705 : i≠705) (h706 : i≠706) :
    (markedInput a).stacks i=a.stacks i := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,hi,h705,h706]

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

theorem marked_ready (q : LeafQueryFrontend.Query) (a : Data)
    (hc : CleanWork a) (hs : Sources q a) (hm : q.mark.isSome=true)
    (href : a.stacks 321=q.index.reverse) : q.Ready (markedInput a) := by
  have e699 := hc 699 (by decide) (by decide)
  have e705 := hc 705 (by decide) (by decide)
  have e706 := hc 706 (by decide) (by decide)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (markedInput_frame a 700 (by decide) (by decide) (by decide)).trans hs.formula
  · exact (markedInput_frame a 701 (by decide) (by decide) (by decide)).trans hs.rows
  · simpa only [href,List.reverse_reverse] using markedInput_index a e699 e705
  · simpa only [hm] using markedInput_flag a e706
  · exact (markedInput_frame a 707 (by decide) (by decide) (by decide)).trans hs.modulus
  · exact (markedInput_frame a 708 (by decide) (by decide) (by decide)).trans hs.width
  · exact (markedInput_frame a 709 (by decide) (by decide) (by decide)).trans hs.ambient
  · intro i hlo hhi
    have hn (x : ℕ) (hx : 680 ≤ x) : i.val≠x := by omega
    rw [markedInput_frame a i
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)
      (by intro h; have hh := congrArg Fin.val h; norm_num at hh; omega)]
    exact cleanWork_private a hc i hlo hhi
  · exact (markedInput_frame a 338 (by decide) (by decide) (by decide)).trans
      (hc 338 (by decide) (by decide))
  · exact (markedInput_frame a 718 (by decide) (by decide) (by decide)).trans
      (hc 718 (by decide) (by decide))
  · exact (markedInput_frame a 719 (by decide) (by decide) (by decide)).trans
      (hc 719 (by decide) (by decide))

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

/-- The physical candidate prefix and copied history are typed as this
query's rows; no scope, layout, or evaluated query is supplied here. -/
theorem trial_sources (q : LeafQueryFrontend.Query) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784 = Encoding.encodeList id q.clauses)
    (hr : true :: (Encoding.frame (a.stacks 768).reverse ++ a.stacks 777) =
      HashScopeProgram.RawTable.inputBits q.width.length q.rows)
    (hm : a.stacks 782 = q.modulus) (hw : a.stacks 783 = q.width)
    (hn : a.stacks 785 = q.ambient) :
    LeafProgram.Query.Sources q (project (LeafOuterNative.trialStaged a)) := by
  obtain ⟨h0,h1,h7,h8,h9⟩ := LeafOuterNative.trialStaged_sources a
  exact ⟨h0.trans hf,h1.trans hr,h7.trans hm,h8.trans hw,h9.trans hn⟩

theorem trial_clean (a : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a)) :
    LeafProgram.Query.CleanWork (project (LeafOuterNative.trialStaged a)) := by
  intro i hi h321
  change (LeafOuterNative.trialStaged a).stacks (stackMap i) = []
  by_cases h702 : i = 702
  · subst i
    exact LeafOuterNative.prefixed_scratch (LeafOuterNative.finalStaged a)
  rw [HashMassStaged.staged_frame a _ (outside_staged i hi h702)]
  exact hc i hi h321

/-- The actual collector's workspace equality preserves the source words at
every marked callback boundary. -/
theorem workspace_sources (q : LeafQueryFrontend.Query) (a b : HighMarkedFrontend.Data)
    (hs : LeafProgram.Query.Sources q (project a))
    (h : HashMassAdapter.workspace b = HashMassAdapter.workspace a) :
    LeafProgram.Query.Sources q (project b) := by
  constructor
  · exact (HashMassAdapter.workspace_frame a b h 700 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.formula
  · exact (HashMassAdapter.workspace_frame a b h 701 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.rows
  · exact (HashMassAdapter.workspace_frame a b h 707 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.modulus
  · exact (HashMassAdapter.workspace_frame a b h 708 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.width
  · exact (HashMassAdapter.workspace_frame a b h 709 (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hs.ambient

theorem workspace_clean (a b : HighMarkedFrontend.Data)
    (hc : LeafProgram.Query.CleanWork (project a))
    (h : HashMassAdapter.workspace b = HashMassAdapter.workspace a)
    (h324 : b.stacks 324 = []) : LeafProgram.Query.CleanWork (project b) := by
  intro i hi h321
  change b.stacks (stackMap i) = []
  by_cases he : i = 324
  · subst i
    exact h324
  rw [HashMassAdapter.workspace_frame a b h (stackMap i)
    (cast_ne (unprotected_ne i hi 320 (by decide))) (cast_ne h321)
    (cast_ne (unprotected_ne i hi 322 (by decide)))
    (cast_ne (unprotected_ne i hi 323 (by decide))) (cast_ne he)]
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

theorem rawQueryFromRows_trial_sources {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) (a : HighMarkedFrontend.Data)
    (hf : a.stacks 784=Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hr : true :: (Encoding.frame (a.stacks 768).reverse ++ a.stacks 777)=
      HashScopeProgram.RawTable.inputBits width.length rows)
    (hm : a.stacks 782=modulus) (hw : a.stacks 783=width) (hn : a.stacks 785=ambient) :
    LeafProgram.Query.Sources (rawQueryFromRows F rows mark index width modulus ambient)
      (project (LeafOuterNative.trialStaged a)) := by
  apply trial_sources _ a hf _ hm hw hn
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashReturnBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Runtime of the actual marked-query return depends only on words that it
erases or returns. Preserved accumulator/source/caller words may be arbitrary;
source-prefix storage continues to use the separate all-word theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds

open BitProgram StructuredCalls SqrtLog
open HashMarkedQueryAdapter HashMarkedReturn

/-- The fixed cleanup/copy temporary is transported by the same actual
workspace relation even though it is a preserved caller port. -/
theorem record_entry_scratch (staged a : Data)
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a)
    (ht : staged.stacks 767 = []) (tail bits : List Bool) :
    (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks 767 = [] := by
  have hw := HashMassAdapter.workspace_recordState a false true false tail bits.reverse
  exact (HashMassAdapter.workspace_frame staged _ (hw.trans hready.workspace_ready) 767
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht

theorem staged_record_entry_scratch (d a : Data)
    (hready : HashMassAdapter.Ready
      (fun ws => ws = HashMassAdapter.workspace (LeafOuterNative.trialStaged d)) a)
    (ht : d.stacks 767 = []) (tail bits : List Bool) :
    (RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse).stacks 767 = [] := by
  apply record_entry_scratch _ a hready _ tail bits
  rw [HashMassStaged.staged_frame d 767 (by decide)]
  exact ht

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashReturnBounds
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

theorem record_ready (staged a : Data) (tail bits : List Bool)
    (h : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a) :
    HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged)
      (recordState a tail bits) := by
  refine ⟨(HashMassAdapter.workspace_recordState a false true false tail bits.reverse).trans
    h.workspace_ready, ?_, ?_⟩
  · simpa [recordState, RecordPrograms.state, HashMassAdapter.recordPorts] using h.result_empty
  · simpa [recordState, RecordPrograms.state, HashMassAdapter.recordPorts] using h.scratch_empty

/-- The actual counter word is normalized once, and its physical prefix plus
the attained history is exactly the raw-row table supplied to the frontend. -/
theorem trial_entry_oai {n B : ℕ} (F : DisjointReuse.RawCNF n) (hn : 0 < n)
    (hm : 0 < F.length) (shifts : SparseCode.SuppliedShifts F.length B)
    (Q : SparseCode.SuppliedLocal F.length B) (rounds : ℕ) (word : List Bool)
    (d a : Data) (e : Fin F.length) (tail : List Bool)
    (hword : word.length = HashCandidates.payloadWidth F.length
      (SparseCode.distanceDenom F.length B))
    (hformula : d.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F))
    (hhistory : d.stacks 777 = HashGreedyProgram.encodedHistory
      (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
        (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))
    (hwidth : (d.stacks 783).length = HashCandidates.digitWidth F.length)
    (hmodulus : BinaryArithmetic.toNat (d.stacks 782) = F.length)
    (hambient : BinaryArithmetic.toNat (d.stacks 785) = n)
    (hclean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project d))
    (hscratch : d.stacks 767 = [])
    (hready : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))) a) :
    MarkedEntry (trialQuery F hm shifts Q rounds word e d)
      (LeafOuterNative.trialStaged (HashGreedyExecution.trialState d F.length
        (SparseCode.distanceDenom F.length B) word))
      (recordState a tail (Encoding.encodeNat e.val)) := by
  let candidateState := HashGreedyExecution.trialState d F.length
    (SparseCode.distanceDenom F.length B) word
  let staged := LeafOuterNative.trialStaged candidateState
  let q := trialQuery F hm shifts Q rounds word e d
  have hc : LeafProgram.Query.CleanWork (HighMarkedFrontend.project candidateState) := by
    intro i hi h321
    have hne : HighMarkedFrontend.stackMap i ≠ 768 := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = 768 at hv
      omega
    simpa only [candidateState, HighMarkedFrontend.project, projectState,
      HashGreedyExecution.trialState, Function.comp_apply, Function.update_of_ne hne] using hclean i hi h321
  have ht : candidateState.stacks 767 = [] := by
    simpa [candidateState, HashGreedyExecution.trialState] using hscratch
  have hs : LeafProgram.Query.Sources q (HighMarkedFrontend.project staged) := by
    apply rawQueryFromRows_trial_sources F (trialRows F hm shifts Q rounds word)
      (some e) (Encoding.encodeNat e.val) (d.stacks 783) (d.stacks 782) (d.stacks 785)
      candidateState
    · simpa [candidateState, HashGreedyExecution.trialState] using hformula
    · simpa only [candidateState, HashGreedyExecution.trialState, Function.update_self,
        Function.update_of_ne (by decide : (777 : Fin 896) ≠ 768), hhistory,
        hwidth, trialRows] using
        supplied_trial_word_raw_encoding (NativeLeafSemantics.indexed F) hm shifts Q rounds word hword
    · simp [candidateState, HashGreedyExecution.trialState]
    · simp [candidateState, HashGreedyExecution.trialState]
    · simp [candidateState, HashGreedyExecution.trialState]
  have hrec := record_ready staged a tail (Encoding.encodeNat e.val) hready
  have hsrc := workspace_sources q staged (recordState a tail (Encoding.encodeNat e.val))
    hs hrec.workspace_ready
  have hcl := workspace_clean staged (recordState a tail (Encoding.encodeNat e.val))
    (trial_clean candidateState hc) hrec.workspace_ready hrec.scratch_empty
  have hmark : q.mark.isSome = true := by
    simp [q, trialQuery, rawQueryFromRows, rawQuery, recordMark]
  have hi : (recordState a tail (Encoding.encodeNat e.val)).stacks 321 = q.index.reverse := by
    simp [recordState, RecordPrograms.state, HashMassAdapter.recordPorts,
      q, trialQuery, rawQueryFromRows, rawQuery]
  refine ⟨?_, hsrc, hcl, hmark, hi, hcl 705 (by decide) (by decide),
    hcl 706 (by decide) (by decide), ?_, hrec, ?_⟩
  · apply rawQueryFromRows_valid F _ (some e) (Encoding.encodeNat e.val)
      (d.stacks 783) (d.stacks 782) (d.stacks 785) hn
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases Option.some.inj he
      rfl
    · exact hmodulus
    · exact hambient
  · exact HashReturnBounds.staged_record_entry_scratch candidateState a hready ht
      tail (Encoding.encodeNat e.val)
  · exact LeafProgram.Query.marked_ready q _ hcl hsrc hmark hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trial_entry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trial_entry_oai
