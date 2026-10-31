-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:46:51.236085+00:00
-- url     : https://prove2.me/submissions/3b53f8f2-b80f-40c2-b4c8-ab0aaac05619

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramIndex
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime, self-delimiting natural-index alphabet. The range control is the
existing unary loop, with one delimiter inserted in each emitted payload. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Index
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpIncidencePlanPrimitives
open SubexponentialSAT.SubexpUnaryRangeProgram (data unary testedRegs )

theorem mem_alphabet (s j : ℕ) : Encoding.encodeNat j ∈ alphabet s ↔ j < s := by
  simp [alphabet, Encoding.encodeNat_injective.eq_iff]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Index

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-size bounds for explicit scopes. These bounds use actual duplicate-free
original-coordinate scope rows, with no value-only replacement for their bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeInputBounds
open LeafStatisticsProgram LeafStatisticsSemantics

/-- A field occupies no more bytes than its containing framed list. -/
theorem encoded_member_length {α : Type*} (encode : α → List Bool)
    (rows : List α) (a : α) (ha : a ∈ rows) :
    (encode a).length ≤ (Encoding.encodeList encode rows).length := by
  induction rows with
  | nil => simp at ha
  | cons b bs ih =>
    rw [Encoding.length_encodeList_cons]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have h := ih ha
      omega

end SubexponentialSAT.SqrtLog.LeafScopeInputBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryShadow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The literal staged collector entry has a uniformly bounded proof shadow.
Only the five caller words left unrestricted by the query-time binder are
erased. No executable instruction, query evaluation, or semantic answer is
assumed in these physical input bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay
open HashMassAdapter HashGreedyExecution

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322 ∨
  Fin.val i = 770 ∨ Fin.val i = 771 ∨ Fin.val i = 781)

private theorem encoded_singleton_length (word : List Bool) :
    (Encoding.encodeList id [word]).length = 2 * word.length + 3 := by
  simp [Encoding.encodeList]

/-- A candidate boundary has only three visible changing words: history,
framed counter, and the empty scratch. The incumbent and outer unary counter
remain completely unrestricted. -/
theorem boundary_visible_bound (base d : State 40 896) (L : ℕ)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hcounter : (d.stacks 778).length ≤ L) (hscratch : d.stacks 779 = []) :
    ∀ i, ¬ H i → (d.stacks i).length ≤ L := by
  intro i hi
  by_cases h777 : i = 777
  · subst i; exact hhistory
  by_cases h778 : i = 778
  · subst i; exact hcounter
  by_cases h779 : i = 779
  · subst i; simp [hscratch]
  have hne (j : Fin 896) (hj : H j) : i ≠ j := by
    intro he
    subst i
    exact hi hj
  rw [hframe i (hne 770 (by decide)) (hne 771 (by decide)) h777 h778 h779
    (hne 781 (by decide))]
  exact hbase i

/-- Normalization has the declared fixed payload width even for losing or
padded counter words. All other visible words retain their actual contents. -/
theorem trial_visible_bound (d : State 40 896) (m depth L : ℕ) (word : List Bool)
    (hd : ∀ i, ¬ H i → (d.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L) :
    ∀ i, ¬ H i → ((trialState d m depth word).stacks i).length ≤ L := by
  intro i hi
  by_cases h768 : i = 768
  · subst i
    simpa [trialState] using hC
  · simpa only [trialState, Function.update_of_ne h768] using hd i hi

/-- Actual trial staging copies only visible sources and prefixes the actual
candidate to the actual history. It does not copy any erased caller word. -/
theorem staged_visible_bound (a : State 40 896) (L : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ L) :
    ∀ i, ¬ H i → ((LeafOuterNative.trialStaged a).stacks i).length ≤ 3 * L + 2 := by
  intro i hi
  have hsrc := LeafOuterNative.trialStaged_sources a
  by_cases hs : i ∈ HashMassStaged.stagedPorts
  · simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hsrc.1]; have := ha 784 (by decide); omega
    · rw [hsrc.2.1]
      simp only [List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse]
      have := ha 768 (by decide)
      have := ha 777 (by decide)
      omega
    · rw [show (LeafOuterNative.trialStaged a).stacks 702 = [] from
        LeafOuterNative.prefixed_scratch _]
      simp
    · rw [hsrc.2.2.1]; have := ha 782 (by decide); omega
    · rw [hsrc.2.2.2.1]; have := ha 783 (by decide); omega
    · rw [hsrc.2.2.2.2]; have := ha 785 (by decide); omega
  · rw [HashMassStaged.staged_frame a i hs]
    have := ha i hi
    omega

/-- At the real parser callback,321 is the current finite reference and
323/324 are empty. The unread tail320 and accumulated mass322 may have any
length; they disappear only in this proof-side shadow. -/
theorem record_shadow_bound (staged a : State 40 896) (L : ℕ)
    (hstage : ∀ i, ¬ H i → (staged.stacks i).length ≤ L)
    (hready : Ready (fun ws => ws = workspace staged) a)
    (tail bits : List Bool) (hbits : bits.length ≤ L) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail bits.reverse)).stacks i).length ≤ L := by
  apply CommandStackTransport.shadow_stack_bound
  intro i hi
  by_cases h321 : i = 321
  · subst i
    simpa [RecordPrograms.state, recordPorts] using hbits
  by_cases h323 : i = 323
  · subst i
    simp [RecordPrograms.state, recordPorts, hready.result_empty]
  by_cases h324 : i = 324
  · subst i
    simp [RecordPrograms.state, recordPorts, hready.scratch_empty]
  have h320 : i ≠ 320 := by
    intro he; subst i; exact hi (by decide)
  have h322 : i ≠ 322 := by
    intro he; subst i; exact hi (by decide)
  have hf := workspace_frame staged a hready.workspace_ready i h320 h321 h322 h323 h324
  simpa only [RecordPrograms.state, recordPorts, Function.update_of_ne h320,
    Function.update_of_ne h321, hf] using hstage i hi

/-- The exact staged-round caller already bounds the complete encoded
reference stream. Its actual current reference is a member of that stream,
so no additional clause-count inequality is required. -/
theorem marked_shadow_bound_of_references_oai (base d a : State 40 896) (m depth L : ℕ)
    (word tail : List Bool) (e : Fin m)
    (hbase : ∀ i, (base.stacks i).length ≤ L)
    (hframe : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i)
    (hhistory : (d.stacks 777).length ≤ L)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : d.stacks 778 = Encoding.encodeList id [word])
    (hscratch : d.stacks 779 = [])
    (hcounterBound : 2 * HashCandidates.payloadWidth m depth + 3 ≤ L)
    (href : (Encoding.encodeList id (RowSelectionProgram.Index.alphabet m)).length ≤ 3 * L + 2)
    (hready : Ready (fun ws => ws = workspace
      (LeafOuterNative.trialStaged (trialState d m depth word))) a) :
    ∀ i, ((rebaseState H (fun _ => [])
      (RecordPrograms.state recordPorts a false true false tail
        (Encoding.encodeNat e.val).reverse)).stacks i).length ≤ 3 * L + 2 := by
  have hc : (d.stacks 778).length ≤ L := by
    rw [hcounter, encoded_singleton_length, hword]
    omega
  have hd := boundary_visible_bound base d L hbase hframe hhistory hc hscratch
  have ht := trial_visible_bound d m depth L word hd (by omega)
  apply record_shadow_bound _ a (3 * L + 2) (staged_visible_bound _ L ht) hready
  exact (LeafScopeInputBounds.encoded_member_length id _ _
    ((RowSelectionProgram.Index.mem_alphabet m e.val).mpr e.isLt)).trans href

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryShadow.marked_shadow_bound_of_references_oai
