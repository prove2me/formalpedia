-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:28:13.617312+00:00
-- url     : https://prove2.me/submissions/5e7627a3-5932-4854-80bb-11f69fe560cc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds_accepted_envelope
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_accepted_replay
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_literal_accepted_count
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup_accepted_with_shadow
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds_envelope_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeQueryTimeBounds_runtime_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_EncodingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

theorem highPrefix_trueCount (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      ∑ v ∈ Finset.range n, if cut < degree scopes v then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : cut < degree scopes n
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using ih

theorem highPrefix_count_eq_card (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      (HighIncidence.high (suppliedScope n scopes) cut).card := by
  rw [highPrefix_trueCount, Finset.sum_range]
  simp only [HighIncidence.high, Finset.card_eq_sum_ones, Finset.sum_filter,
    degree_suppliedScope]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

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

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

theorem worker_empty (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] := by
  intro i hi
  have h := he ⟨i.val, hi⟩
  simpa [workerStack] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

theorem ready_low {n m B : ℕ} {initial : List (List Bool)} {a : State 40 896}
    (hr : NativeLeafPreparation.Ready n m B initial a) :
    ∀ i : Fin 896, i.val < 768 → a.stacks i = [] :=
  NativeCodeAssembly.worker_empty a hr.worker

theorem rounds_query_workspace (base out : State 40 896) (rows : List (List Bool))
    (hr : RowBoundary base rows out)
    (hb : ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      base.stacks i = []) :
    ∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
      out.stacks i = [] := by
  intro i hi
  have hn (j : Fin 896) (hj : j.val < 788) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  exact (hr.frame i (hn 777 (by decide)) (hn 781 (by decide))).trans (hb i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryEntryFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual preparation and attained-history boundary supply every discarded
word required by the complete accepted-query return. No extra entry-blank
assumption is added to the query caller. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
open BitProgram StructuredCalls HashGreedyRound

theorem accepted_entry_discarded_blank {n m B : ℕ} {initial rows : List (List Bool)}
    (base selected : State 40 896)
    (hr : NativeLeafPreparation.Ready n m B initial base)
    (hupper : ∀ i : Fin 896,
      (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) → base.stacks i = [])
    (hselected : RowBoundary base rows selected) :
    ∀ i, HashMarkedReturn.kept i = false →
      (AcceptedQueryStage.staged selected).stacks i = [] := by
  have hlow : ∀ i : Fin 896, i.val < 768 → selected.stacks i = [] := by
    intro i hi
    have hne (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact (hselected.frame i (hne 777 (by decide)) (hne 781 (by decide))).trans
      (ready_low hr i hi)
  have hu := rounds_query_workspace base selected rows hselected hupper
  intro i hk
  by_cases h702 : i = 702
  · subst i
    rw [AcceptedQueryStage.staged_702]
    exact hlow 702 (by decide)
  have hout : i ∉ HashMassStaged.stagedPorts := by
    simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [HashMarkedReturn.kept, decide_eq_false_iff_not, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hk
    simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h702 ⊢
    omega
  have ht : i ≠ 767 := by
    intro h
    subst i
    have hkeep : HashMarkedReturn.kept (767 : Fin 896) = true := by decide
    rw [hkeep] at hk
    cases hk
  rw [AcceptedQueryStage.staged_frame selected i hout ht]
  by_cases hi : i.val < 768
  · exact hlow i hi
  · apply hu i
    simp only [HashMarkedReturn.kept, decide_eq_false_iff_not, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hk
    have hib := i.isLt
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual query's ternary count is the selector's exact natural score.
Literal source occurrences and the entire ambient assignment type are retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount

open SqrtLog DisjointReuse HighFrontendSources HashGreedyCode HashQueryEntry
open LeafProgram OuterQuery.Count

/-- Native clause records are the original interpreter's literal source bytes. -/
theorem clauseRecords_eq {n : ℕ} (F : RawCNF n) :
    NativeTerminal.clauseRecords F = HashInputProgram.Expansion.encodedClauses F := by
  apply List.map_congr_left
  intro clause _
  rw [HashInputProgram.clausePayload_codes]
  simp only [ExecSparsifyEncoding.encodeList_map]
  rfl


/-- Equality of ambient dimensions changes no literal bytes. -/
theorem rawQuery_source_bytes {n N : ℕ} (F : RawCNF n) (h : n = N)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) :
    (rawQueryFromRows F rows mark index width modulus ambient).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F) := by
  cases h
  exact clauseRecords_eq F

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryCount
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact current-query mask and attained counter semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

theorem high_mask_count (q : LeafQueryFrontend.Query) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.trueCount
      (LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))=(highSet q).card := by
  exact OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix_count_eq_card _ _ _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

theorem full_count_le {n : ℕ} (hashes : List (SparseRow (Fin n) (ZMod 3)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) :
    fullCount hashes marked clause ≤ 2 ^ n := by
  classical
  calc
    _ ≤ ∑ _x : Fin n → Bool, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

open HashGreedyProgram.NativeRound


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed input-length bounds for the literal trial and accepted query
preparations. The common bound is produced before the greedy loop; none of
these caps contains a suspended caller word or a repeated-node scratch cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry LeafParametersProgram CostAssembly.Polynomial
open NativeQueryPreparation ProducedQueryResources

private theorem sourceCap_mono (Cn dn Cl dl N k L U : ℕ) (h : L ≤ U) :
    sourceCap Cn dn Cl dl N L k ≤ sourceCap Cn dn Cl dl N U k := by
  unfold sourceCap
  gcongr

private theorem frontendCap_mono (Cf df k L U : ℕ) (h : L ≤ U) :
    frontendCap Cf df L k ≤ frontendCap Cf df U k := by
  unfold frontendCap
  gcongr

private theorem preparedCap_mono (Cp dp Cn dn Cl dl Cf df N k L U : ℕ) (h : L ≤ U) :
    preparedCap Cp dp Cn dn Cl dl Cf df N L k ≤
      preparedCap Cp dp Cn dn Cl dl Cf df N U k := by
  have hs := sourceCap_mono Cn dn Cl dl N k L U h
  have hf := frontendCap_mono Cf df k L U h
  dsimp only [preparedCap, HighQuerySetup.localBound]
  have ha := Nat.add_le_add hs hf
  exact Nat.add_le_add_right (Nat.add_le_add ha
    (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) dp))) 1

/-- Substitution uses a fixed polynomial for the genuinely produced common
bound. The degree is independent of all later states, candidates and nodes. -/
theorem cap_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C d : ℕ, ∀ N L : ℕ, L ≤ C0 * (N + 1) ^ d0 →
      sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
        preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N + 6 ≤ C * (N + 1) ^ d := by
  let U := fun N => C0 * (N+1)^d0
  have hU : Ordinary U := ordinary_mul (ordinary_const C0)
    (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) d0)
  have hK := ordinary_add (ordinary_add hU (ordinary_const k)) (ordinary_const 1)
  have hS : Ordinary (fun N => sourceCap Cn dn Cl dl N (U N) k) :=
    ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 3) hU) (ordinary_const 2))
      (ordinary_mul (ordinary_const Cn) (ordinary_pow
        (ordinary_add ordinary_id (ordinary_const 1)) dn)))
      (ordinary_mul (ordinary_const Cl) (ordinary_pow hK dl))
  have hF : Ordinary (fun N => frontendCap Cf df (U N) k) :=
    ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 10) (ordinary_add hU (ordinary_const 1)))
      (ordinary_mul (ordinary_const Cf) (ordinary_pow hK df))) (ordinary_const 12)
  have hA := ordinary_add hS hF
  have hP : Ordinary (fun N => preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k) :=
    ordinary_add (ordinary_add hA (ordinary_mul (ordinary_const Cp)
      (ordinary_pow (ordinary_add hA (ordinary_const 1)) dp))) (ordinary_const 1)
  obtain ⟨C,d,hC⟩ := ordinary_add (ordinary_add (ordinary_add (ordinary_add hS hF) hP)
    (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)
  refine ⟨C,d,?_⟩
  intro N L hL
  have hs := sourceCap_mono Cn dn Cl dl N k L (U N) hL
  have hf := frontendCap_mono Cf df k L (U N) hL
  have hp := preparedCap_mono Cp dp Cn dn Cl dl Cf df N k L (U N) hL
  exact (by omega : sourceCap Cn dn Cl dl N L k + frontendCap Cf df L k +
    preparedCap Cp dp Cn dn Cl dl Cf df N L k + 4*N+6 ≤
      sourceCap Cn dn Cl dl N (U N) k + frontendCap Cf df (U N) k +
        preparedCap Cp dp Cn dn Cl dl Cf df N (U N) k +4*N+6).trans (hC N)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQuerySpaceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial space for the actual complete marked and accepted queries.
The input cap is the same immutable leaf bound used by preparation. The
conditioned stream, high loop and whole-word return use their own proved
prefix bounds; no query runtime or number of attained tuples enters space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds

open SqrtLog LeafParametersProgram NativeQueryInputBounds
open CostAssembly.Polynomial

private theorem envelope_mono (C e W U : ℕ) (h : W ≤ U) :
    envelope C e W ≤ envelope C e U := by
  unfold envelope
  gcongr

/-- Coefficients and degree are fixed before the query, mark, source state,
node, signature or head assignment. This substitutes the genuine common
leaf bound directly; the retained hidden frame never enters the polynomial. -/
theorem polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ (N L : ℕ) (q : LeafQueryFrontend.Query) (n h t d J f B : ℕ),
      L ≤ C0*(N+1)^d0 → BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f B ≤
        max (C*(N+1)^e) B := by
  obtain ⟨Cs,es,hspace⟩ := envelope_bound
  obtain ⟨Cw,ew,hwords⟩ := cap_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  have hw : Ordinary (fun N => Cw*(N+1)^ew) :=
    ordinary_mul (ordinary_const Cw)
      (ordinary_pow (ordinary_add ordinary_id (ordinary_const 1)) ew)
  have hp : Ordinary (fun N => envelope Cs es (Cw*(N+1)^ew)) :=
    ordinary_add (ordinary_mul (ordinary_const 1000) (ordinary_add hw (ordinary_const 1)))
      (ordinary_mul (ordinary_const (1000*Cs))
        (ordinary_pow (ordinary_mul (ordinary_const 30) (ordinary_add hw (ordinary_const 1))) es))
  obtain ⟨C,e,hbound⟩ := hp
  refine ⟨C,e,?_⟩
  intro N L q n h t d J f B hL hqn hn hh ht hd hJ hf
  have h := hspace Cp dp Cn dn Cl dl Cf df N L k q n h t d J f B hqn hn hh ht hd hJ hf
  exact h.trans (max_le_max_right B
    ((envelope_mono Cs es _ _ (hwords N L hL)).trans (hbound N)))

/-- The bounded shadow query has no suspended frame, so its complete
source-prefix bound is this fixed polynomial in the true encoded input. -/
theorem shadow_polynomial (Cp dp Cn dn Cl dl Cf df C0 d0 k : ℕ) :
    ∃ C e : ℕ, ∀ (N L : ℕ) (q : LeafQueryFrontend.Query) (n h t d J f : ℕ),
      L ≤ C0*(N+1)^d0 → BinaryArithmetic.toNat q.ambient = n → n ≤ N → h ≤ n →
      t ≤ sourceCap Cn dn Cl dl N L k →
      d ≤ sourceCap Cn dn Cl dl N L k →
      J ≤ sourceCap Cn dn Cl dl N L k → f ≤ frontendCap Cf df L k →
      querySpace q Cp dp Cn dn Cl dl Cf df N L k n h t d J f 0 ≤ C*(N+1)^e := by
  obtain ⟨C,e,h⟩ := polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,e,?_⟩
  intro N L q n hsize t d J f hL hqn hn hh ht hd hJ hf
  simpa only [Nat.max_zero] using h N L q n hsize t d J f 0 hL hqn hn hh ht hd hJ hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQuerySpaceBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQueries
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Literal marked and accepted query continuations for the actual prepared
leaf. Shadow execution preserves unrestricted caller words for time; the
same replay counts those words separately in maximum prefix storage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

/-- Equality transport of the ambient dimension preserves the original
literal width bound used by the actual high-query execution. -/
theorem source_width {n N k : ℕ} (F : RawCNF n) (h : n = N)
    (hv : SparseDFSRefinement.Valid k F) :
    ∀ clause ∈ Eq.mp (congrArg RawCNF h) F, clause.length ≤ k := by
  cases h
  exact hv.width


open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources


/-- The high iterator's natural count never exceeds all assignments of the
unchanged ambient dimension. This gives the complete count word's width. -/
theorem literalCount_le (q : LeafQueryFrontend.Query)
    (source : RawCNF (BinaryArithmetic.toNat q.ambient))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source) :
    literalCount q source hsource ≤ 2^(BinaryArithmetic.toNat q.ambient) :=
  HighQueryLoop.full_count_le _ _ _


open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

/-- The fixed final query counts precisely the attained history at the
original ambient dimension. Every retained caller byte is restored, and the
canonical full count is the only changed word788. -/
theorem accepted_oai (k C0 d0 : ℕ) (hk : 2 ≤ k) :
    ∃ C E : ℝ, ∃ degree Cs es cutoff : ℕ,
      1 ≤ C ∧ 1 ≤ E ∧ 1 ≤ degree ∧
    ∀ n N R : ℕ, cutoff ≤ n → n ≤ N →
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k-1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
      F.length ≤ n*B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (base d : State 40 896) (frameBound : ℕ),
      NativeLeafPreparation.Ready n F.length B (initial shifts Q) base →
      (∀ i, (base.stacks i).length ≤ R) →
      base.stacks 784 = Encoding.encodeList id (NativeTerminal.clauseRecords F) →
      BinaryArithmetic.toNat (base.stacks 785) = n →
      NativeLeafRun.commonBound n F.length B R ≤ C0*(N+1)^d0 →
      (∀ i : Fin 896, (788 ≤ i.val ∧ i.val ≤ 794) ∨ (832 ≤ i.val ∧ i.val ≤ 894) →
        base.stacks i = []) →
      HashGreedyRound.RowBoundary base
        (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
          (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds) d →
      let input := AcceptedQueryStage.staged d
      (∀ i, i ∈ HighQueryProgram.Carried.words → (input.stacks i).length ≤ frameBound) →
      ∃ steps output,
        Eval (HighQueryProgram.accepted k) steps input output ∧
        steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) ∧
        output.stacks = Function.update input.stacks 788 (countWord
          (HashSelect.acceptedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
            (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
              (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds))) ∧
        (output.stacks 788).length ≤ n+1 ∧
        StageSpace (HighQueryProgram.accepted k) (steps+1) input
          (max (Cs*(N+1)^es) frameBound) := by
  obtain ⟨Cp,dp,Cn,dn,Cl,dl,Cf,df,Nsetup,hsetup⟩ := NativeHashQuerySetup.accepted_with_shadow k hk
  obtain ⟨Nrecord,hrecord⟩ := HashQueryParameterBounds.accepted_envelope k 1 1 1 1 1 hk
  obtain ⟨C,E,degree,Ntime,hC,hE,hdegree,htime⟩ :=
    NativeQueryTimeBounds.runtime_bound k (2*(k-1)+1) (4*k+3) 17
      Cp dp Cn dn Cl dl Cf df C0 d0
  obtain ⟨Cs,es,hspace⟩ := NativeQuerySpaceBounds.shadow_polynomial Cp dp Cn dn Cl dl Cf df C0 d0 k
  refine ⟨C,E,degree,Cs,es,max (max Nsetup Nrecord) Ntime,hC,hE,hdegree,?_⟩
  intro n N R hcut hN B F hv hm hmb shifts Q rounds hr base d frameBound
    hbaseReady hbase hformula hamb hL hupper hselected input hhidden
  let q := acceptedQuery F hm shifts Q rounds d
  let L := NativeLeafRun.commonBound n F.length B R
  let S := sourceCap Cn dn Cl dl N L k
  let P := preparedCap Cp dp Cn dn Cl dl Cf df N L k
  let A := 12*P+4*N+6
  obtain ⟨entry,hqn,hindex,_hS,_hnS,_hiS,hvalues,hfront,_original,⟨run⟩⟩ :=
    hsetup n N R (by omega) hN F hv hm hmb shifts Q rounds hr base d frameBound
      hbaseReady hbase hformula hamb hselected hhidden
  have hSA : S ≤ A := by
    dsimp only [A,P,preparedCap,HighQuerySetup.localBound]
    omega
  have h783 : d.stacks 783 = base.stacks 783 := hselected.frame 783 (by decide) (by decide)
  have h782 : d.stacks 782 = base.stacks 782 := hselected.frame 782 (by decide) (by decide)
  have h785 : d.stacks 785 = base.stacks 785 := hselected.frame 785 (by decide) (by decide)
  obtain ⟨_valid,_ambient,_scan,_small,henvelope⟩ :=
    hrecord n (by omega) F hv hm hmb shifts Q rounds hr d
      (by rw [h783,hbaseReady.width]; exact hbaseReady.modulus_length)
      (by rw [h782]; exact hbaseReady.clauses) (h785 ▸ hamb)
  let resource := ofPacking q k B 1 1 (2*(k-1)+1) 1 run.guard run.prepared.first run.prepared.rest
  have hresource : CostAssembly.Bounds (2*(k-1)+1) (4*k+3) 17 n resource :=
    (henvelope run.guard run.prepared.first run.prepared.rest run.prepared.nodup run.prepared.complete).1
  have hhigh : (highSet q).card ≤ n := by
    have h := Finset.card_le_univ (highSet q)
    simpa only [Fintype.card_fin,← hqn] using h
  have hhighEq : (highSet q).card = resource.branchVars := by
    simpa only [resource, ofPacking, make] using (high_mask_count q).symm
  have hhighQ : (highSet q).card ≤ BinaryArithmetic.toNat q.ambient := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (highSet q)
  have hb := htime (ambient q) (by rw [hqn]; omega) N L (hqn.trans_le hN) hL resource
    (by rw [hqn]; exact hresource)
    (HighMarkedFrontend.acceptedBudget q k)
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 21)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (highSet q).card
    hfront (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 21).2 (hvalues _ 42).2 hhighQ hhighEq
  have hs := hspace N L q (ambient q) (highSet q).card
    ((Execute.guardedModel (q.input k) run.padding).val 33)
    ((Execute.guardedModel (q.input k) run.padding).val 34)
    ((Execute.guardedModel (q.input k) run.padding).val 42) (HighMarkedFrontend.acceptedBudget q k)
    hL rfl (hqn.trans_le hN) hhighQ (hvalues _ 33).2 (hvalues _ 34).2 (hvalues _ 42).2 hfront
  let source : RawCNF (BinaryArithmetic.toNat q.ambient) := Eq.mp (congrArg RawCNF hqn.symm) F
  have hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source :=
    HashQueryCount.rawQuery_source_bytes F hqn.symm _ _ _ _ _ _
  have hblank := NativeLeafRun.accepted_entry_discarded_blank base d hbaseReady hupper hselected
  obtain ⟨steps,output,he,ht,hcount,htrace⟩ :=
    accepted_replay run B (2*(k-1)+1) (frontendCap Cf df L k) frameBound entry hindex
      source hsource (source_width F hqn.symm hv) (hvalues run.padding) hSA hfront
      (fun i _ hi => hblank i hi) hhidden
  have ht' : steps+1 ≤ Nat.ceil (runtimeBound C E degree N n) := by
    have hbound := hb.2
    have hreal : ((steps+1 : ℕ) : ℝ) ≤ runtimeBound C E degree N n := by
      have hh : ((steps+1 : ℕ) : ℝ) ≤ _ := Nat.cast_le.mpr ht
      exact (hh.trans hbound).trans_eq (congrArg (runtimeBound C E degree N) hqn)
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  have hlen : (output.stacks 788).length ≤ n+1 := by
    rw [hcount,Function.update_self]
    apply countWord_length_le
    exact (literalCount_le q source hsource).trans_eq (congrArg (fun x : ℕ => 2^x) hqn)
  have hc := literal_accepted_count F hm shifts Q rounds d hqn.symm hsource
  rw [hc] at hcount
  refine ⟨steps,output,he,ht',hcount,hlen,?_⟩
  constructor
  intro t z htz hz i
  exact (htrace.bound t z htz hz i).trans (max_le_max_right frameBound (by
    simpa only [NativeQuerySpaceBounds.querySpace] using hs))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_oai
