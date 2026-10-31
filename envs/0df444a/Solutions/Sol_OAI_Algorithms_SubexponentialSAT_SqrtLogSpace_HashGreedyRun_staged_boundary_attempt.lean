-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:37:41.186201+00:00
-- url     : https://prove2.me/submissions/eb544398-05f7-43f0-8f25-45f2cf533c72

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S151
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashCandidateProgram_Leaf_prepare_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate_attempt_entry_of_query
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashMassStaged_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CountModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

private theorem digits_two_eq_map_toNat (n : ℕ) :
    Nat.digits 2 n = n.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction n.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

@[simp] theorem binaryNat_decode (n : ℕ) :
    Nat.ofDigits 2 ((binaryNat n).map Bool.toNat) = n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rw [binaryNat, ite_eq_right hn, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 n

theorem binaryNat_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (binaryNat a).length ≤ n + 1 := by
  by_cases hzero : a = 0
  · simp [binaryNat, hzero]
  · simpa only [binaryNat, ite_eq_right hzero, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical unsigned binary output by a fixed finite word program.
The program reverses its input, removes high zeroes, reverses back, and emits
one false bit in the empty case. All source stack prefixes have a linear local
bound. No algebraic construction is imported to implement normalization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

open BitProgram StructuredCalls CounterPrograms

theorem ofDigits_eq_value (word : List Bool) :
    Nat.ofDigits 2 (word.map Bool.toNat) = value word := by
  induction word with
  | nil => rfl
  | cons b word ih => simp only [List.map_cons, Nat.ofDigits_cons, value, ih]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact natural-valued mass for finite sparse-hash selection.
The row semantics are abstract here; no evaluator is assumed computable
from this definition at the target cost. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

variable {X R I : Type*}

theorem mass_le [Fintype X] (rowAccept : R → X → Bool)
    (weight : X → ℕ) (rows : List R) (m : ℕ)
    (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight rows ≤ Fintype.card X * m := by
  calc
    mass rowAccept weight rows ≤ ∑ _x : X, m := by
      apply Finset.sum_le_sum
      intro x _
      cases hx : accepts rowAccept rows x <;> simp [ hw x]
    _ = Fintype.card X * m := by simp

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

section Hash
variable [Fintype E] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
theorem violationWeight_le (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight C x ≤ Fintype.card E := by
  calc
    _ ≤ ∑ _e : E, 1 := Finset.sum_le_sum fun e _ => by split_ifs <;> omega
    _ = _ := by simp

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTermination
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entirely integer termination for the finite greedy selector. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

theorem initial_mass_lt_cap_power {X R : Type*} [Fintype X]
    (rowAccept : R → X → Bool) (weight : X → ℕ) (initial : List R)
    (n m : ℕ) (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    mass rowAccept weight initial < 2 ^ (n + Nat.size m + 1) := by
  have hm := Nat.lt_size_self m
  calc
    mass rowAccept weight initial ≤ Fintype.card X * m :=
      mass_le rowAccept weight initial m hw
    _ ≤ 2 ^ n * m := Nat.mul_le_mul_right m hx
    _ < 2 ^ n * 2 ^ Nat.size m := Nat.mul_lt_mul_of_pos_left hm (by positivity)
    _ ≤ 2 ^ (n + Nat.size m + 1) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)

end SubexponentialSAT.SqrtLog.HashSelect

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- A singleton shape contains exactly the one physical payload word. -/
theorem tuple_eq_singleton_flatten {words : List (List Bool)} {width : ℕ}
    (hshape : words.map List.length = [width]) : words = [words.flatten] := by
  obtain ⟨word, rfl, _⟩ := List.map_eq_singleton_iff.mp hshape
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Canonical mass words fit the saved round-count shape even when all m
marked counts contribute. An n+1 count bound is not used for this score. -/
theorem canonical_mass_length {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m : ℕ) (rows : List (List Bool))
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    (DisjointReuse.binaryNat (HashSelect.mass rowAccept weight rows)).length ≤
      HashSelect.loopCap n m := by
  have h := DisjointReuse.binaryNat_length_le
    (HashSelect.initial_mass_lt_cap_power rowAccept weight rows n m hx hw).le
  unfold HashSelect.loopCap
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMarked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Weighted selector mass is the sum of ordinary marked-clause counts.
This identity justifies executing the same count pipeline once per supplied
clause; no weighted arithmetic is hidden in the local indicator evaluator. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open scoped BigOperators

variable {X Row E : Type*} [Fintype X] [Fintype E]

theorem sum_markedCount (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) :
    (∑ e, markedCount rowAccept rows bad e) =
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  unfold markedCount HashSelect.mass violationWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases h : HashSelect.accepts rowAccept rows x <;> simp []

variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem cnf_weight (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight (fun e x => !(C e).eval x) x = HashInput.violationWeight C x := by
  unfold violationWeight HashInput.violationWeight
  apply Finset.sum_congr rfl
  intro e _
  cases h : (C e).eval x <;> simp [h]

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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


open LeafOuterProgram

open scoped BigOperators

/-- The concrete descending reference stream visits each original selector
exactly once; reversing its order does not change the full marked sum. -/
theorem alphabet_sum_marked {X Row : Type*} [Fintype X] {m : ℕ}
    (rowAccept : Row → X → Bool) (rows : List Row) (bad : Fin m → X → Bool)
    (count : List Bool → ℕ)
    (hcount : ∀ e : Fin m, count (Encoding.encodeNat e.val) = markedCount rowAccept rows bad e) :
    ((RowSelectionProgram.Index.alphabet m).map count).sum =
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  rw [RowSelectionProgram.Index.alphabet, List.map_map, List.map_reverse, List.sum_reverse]
  rw [← List.map_coe_finRange m, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  simp only [Function.comp_def]
  simp_rw [hcount]
  exact sum_markedCount rowAccept rows bad


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

theorem staged_stacks_congr (a b : State 40 896) (h : a.stacks = b.stacks) :
    (LeafOuterNative.trialStaged a).stacks = (LeafOuterNative.trialStaged b).stacks := by
  funext i
  have ha := LeafOuterNative.trialStaged_sources a
  have hb := LeafOuterNative.trialStaged_sources b
  by_cases hi : i ∈ stagedPorts
  · simp only [stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [ha.1,hb.1,h]
    · rw [ha.2.1,hb.2.1,h]
    · exact (LeafOuterNative.prefixed_scratch _).trans (LeafOuterNative.prefixed_scratch _).symm
    · rw [ha.2.2.1,hb.2.2.1,h]
    · rw [ha.2.2.2.1,hb.2.2.2.1,h]
    · rw [ha.2.2.2.2,hb.2.2.2.2,h]
  · rw [staged_frame a i hi,staged_frame b i hi,h]

/-- Literal cost formula: only the six overwritten sources, the five copied
masters/history words, and the current candidate contribute. -/
theorem stagingBudget_eq (a : State 40 896) :
    stagingBudget a =
      2 * ((a.stacks 700).length + (a.stacks 701).length + (a.stacks 702).length +
        (a.stacks 707).length + (a.stacks 708).length + (a.stacks 709).length) +
      9 * ((a.stacks 777).length + (a.stacks 782).length + (a.stacks 783).length +
        (a.stacks 784).length + (a.stacks 785).length) + 16 * (a.stacks 768).length + 83 := by
  have h := LeafOuterNative.trialStaged_sources a
  have h702 : (LeafOuterNative.trialStaged a).stacks 702 = [] :=
    LeafOuterNative.prefixed_scratch _
  unfold stagingBudget cleanupCost
  simp only [stagedPorts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,h702,List.length_cons,List.length_nil,
    List.length_append,Encoding.length_frame,List.length_reverse]
  simp [LeafOuterNative.stageTrialCost,LeafOuterNative.stageFinalCost,
    LeafOuterNative.prefixCost,LeafOuterNative.finalStaged,LeafOuterNative.masterRoutes,
    routesCost,routesState,routed,routeCost]
  ring

theorem stagingBudget_le_sources (a : State 40 896) (L : ℕ)
    (hempty : ∀ i ∈ stagedPorts, a.stacks i = [])
    (hsource : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (a.stacks i).length ≤ L)
    (hcandidate : (a.stacks 768).length ≤ L) : stagingBudget a ≤ 95 * L + 103 := by
  have h777 := hsource 777 (by simp)
  have h782 := hsource 782 (by simp)
  have h783 := hsource 783 (by simp)
  have h784 := hsource 784 (by simp)
  have h785 := hsource 785 (by simp)
  rw [stagingBudget_eq]
  simp only [hempty 700 (by simp [stagedPorts]),hempty 701 (by simp [stagedPorts]),
    hempty 702 (by simp [stagedPorts]),hempty 707 (by simp [stagedPorts]),
    hempty 708 (by simp [stagedPorts]),hempty 709 (by simp [stagedPorts]),List.length_nil]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

theorem reference_sum {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) :
    ((RowSelectionProgram.Index.alphabet m).map (referenceCount clauses rows)).sum =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) rows := by
  rw [alphabet_sum_marked (HashGreedyCNF.rowAccept clauses) rows
    (fun e x => !(clauses e).eval x) _ (referenceCount_encode clauses rows)]
  congr 1
  funext x
  exact cnf_weight clauses x

/-- Paid trial-source staging and cleanup are included in the actual attempt;
the only query premise is the per-mark evaluator on these produced sources. -/
theorem staged_attempt_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (rows : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (a : State 40 896) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = [])
    (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (a.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hq : ∀ (e : Fin m) tail (base : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState a m depth word)) ∧
        read middle = read base ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ stagedAttemptBudget a n m depth queryCost L, ∃ b,
      Eval (attempt (HashMassStaged.command query)) t a b ∧
      b.stacks = Function.update (Function.update a.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).score := by
  let trialRows := HashCandidates.normalize m depth word.reverse :: rows
  obtain ⟨np, hnp, b, hp, hprep⟩ := HashCandidateProgram.Leaf.prepare_eval hm a word
    hword hcounter hclean hlow ht hwidth hvalue
  have hws : workspace (LeafOuterNative.trialStaged b) =
      workspace (LeafOuterNative.trialStaged (trialState a m depth word)) := by
    funext i
    exact congrFun (HashMassStaged.staged_stacks_congr b (trialState a m depth word) hprep) (workPort i)
  have hb : ReferencesReady b := by
    constructor
    · simp [hprep, ht]
    · intro i hi
      have he : a.stacks i = [] := by
        rcases hi with hi | rfl
        · exact hlow i (by omega)
        · exact hcollector 320 (by decide) (by decide)
      have hne : i ≠ 768 := by
        intro h
        subst i
        rcases hi with hi | hi
        · exact (by decide : ¬ (768 : Fin 896).val < 9) hi
        · exact (by decide : (768 : Fin 896) ≠ 320) hi
      simp [hprep, hne, he]
  have hq' : ∀ bits tail (base : State 40 896),
      (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      ∃ t middle, t ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged b) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) =
          referenceCount clauses trialRows bits ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by
    intro bits tail base hvalid hb
    obtain ⟨e, he⟩ := hvalid
    subst bits
    simpa only [hws, referenceCount_encode, trialRows] using hq e tail base (by simpa only [hws] using hb)
  have hemptyB : ∀ i ∈ HashMassStaged.stagedPorts, b.stacks i = [] := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [hprep,hne] using hempty i hi
  have hcB : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → b.stacks i = [] := by
    intro i hi hj
    have hne : i ≠ 768 := by intro he; subst i; omega
    simpa [hprep,hne] using hcollector i (by omega) hj
  obtain ⟨nq, hnq, c, heq, hquery⟩ := HashMassStaged.eval query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m hb
    (by simpa [hprep] using hmword) hcB hemptyB (fun e => ⟨e, rfl⟩) hq'
  rw [reference_sum] at hquery
  let score := DisjointReuse.binaryNat
    (HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows)
  have hlen : score.length ≤ HashSelect.loopCap n m :=
    HashGreedyCandidate.canonical_mass_length _ _ n m trialRows
      (by simp [SAT.Assignment]) (fun x => by simpa using HashInput.violationWeight_le clauses x)
  have hv : BinaryArithmetic.toNat score =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows := by
    rw [← CounterPrograms.value_eq_toNat, ← DisjointReuse.CanonicalWordProgram.ofDigits_eq_value]
    exact DisjointReuse.binaryNat_decode _
  obtain ⟨d, he, hd⟩ := HashGreedyCandidate.attempt_entry_of_query
    (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) n m depth rows
    (HashMassStaged.command query) a b c np nq word score hword hp hprep heq hquery
    (hlow 0 (by decide)) (hlow 1 (by decide)) (hlow 2 (by decide)) hshape hlen hv
  refine ⟨np + (nq + (23 * HashSelect.loopCap n m + 20)), ?_, d, he, hd⟩
  have hbudget : massBudget b queryCost (fun _ => n + 1) m =
      massBudget a queryCost (fun _ => n + 1) m := by
    simp [massBudget, LeafOuterProgram.routeCost, hprep]
  have hsourceB : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (b.stacks i).length ≤ L := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [hprep,hne] using hsource i hi
  have hcandidateB : (b.stacks 768).length ≤ L := by
    simpa [hprep] using hC
  have hstage := HashMassStaged.stagingBudget_le_sources b L hemptyB hsourceB hcandidateB
  unfold HashMassStaged.budget at hnq
  rw [hbudget] at hnq
  unfold stagedAttemptBudget attemptBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CNF scores instantiate the actual unary-controlled greedy run.
The only execution seam is the actual per-mark query. Initial-code distance
is used only for the final zero-mass and exact model-set consequences. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

private theorem loader_clean (a : State 40 896)
    (h0 : a.stacks 768 = []) (h1 : a.stacks 769 = []) (hcore : CoreClean a)
    (hs : a.stacks 779 = []) :
    ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [] := by
  rcases hcore with ⟨h2,h3,h4,h5,h6⟩
  intro j hj2 hj3 hj9
  fin_cases j <;> simp_all [HashCandidateProgram.Leaf.loaderStacks]

/-- Concrete per-boundary staged attempt, with a uniform cost over the actual
history-byte domain. Its frame reconstruction is shared by time and space proofs. -/
theorem staged_boundary_attempt_oai {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (query : Cmd 40 896) (queryCost : List Bool → ℕ)
    (base : State 40 896)
    (h0 : base.stacks 768 = []) (h1 : base.stacks 769 = []) (hcore : CoreClean base)
    (hlow : ∀ i : Fin 896, i.val < 12 → base.stacks i = [])
    (ht : base.stacks 767 = [])
    (hwidth : (base.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (base.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (base.stacks 782) = m)
    (hshape : (base.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → base.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([782,783,784,785] : List (Fin 896)), (base.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, base.stacks i = [])
    (rows : List (List Bool)) (a : State 40 896) (ha : RowBoundary base rows a)
    (hbytes : (encodedHistory rows).length ≤ L)
    (words : List (List Bool)) (d : State 40 896)
    (hwords : words.map List.length = [HashCandidates.payloadWidth m depth])
    (hd : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 → d.stacks i = a.stacks i)
    (hcounterD : d.stacks 778 = Encoding.encodeList id words) (hsD : d.stacks 779 = [])
    (hq : ∀ (e : Fin m) tail (a : State 40 896),
      Ready (fun ws => ws = workspace
        (LeafOuterNative.trialStaged (trialState d m depth words.flatten))) a →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState d m depth words.flatten)) ∧
        read middle = read a ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth words.flatten.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts a false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ stagedAttemptBudget base n m depth queryCost L, ∃ b,
      Eval (attempt (HashMassStaged.command query)) t d b ∧
      b.stacks = Function.update (Function.update d.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value words.flatten)).score := by
  have hword : words.flatten.length = HashCandidates.payloadWidth m depth := by
    have hh := congrArg List.sum hwords
    simpa [List.length_flatten] using hh
  have hsingle : words = [words.flatten] := HashCandidateRank.tuple_eq_singleton_flatten hwords
  have hf : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 777 → i ≠ 778 → i ≠ 779 → i ≠ 781 →
      d.stacks i = base.stacks i := by
    intro i h770 h771 h777 h778 h779 h781
    exact (hd i h770 h771 h778 h779).trans (ha.frame i h777 h781)
  have hcoreD : CoreClean d := by
    constructor
    · rw [hf 772 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch772
    · rw [hf 773 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch773
    · rw [hf 774 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch774
    · rw [hf 775 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.scratch775
    · rw [hf 776 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcore.queue776
  have hlowD : ∀ i : Fin 896, i.val < 12 → d.stacks i = [] := by
    intro i hi
    have hneq (j : Fin 896) (hj : 12 ≤ j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hlow i hi
  have hcD : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → d.stacks i = [] := by
    intro i hi hj
    have hneq (j : Fin 896) (hj : 324 < j.val) : i ≠ j := by
      intro he
      subst i
      omega
    rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
      (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
    exact hcollector i hi hj
  have hcounterD' : d.stacks 778 = Encoding.encodeList id [words.flatten] := by
    exact hcounterD.trans (congrArg (Encoding.encodeList id) hsingle)
  have hhistD : d.stacks 777 = encodedHistory rows :=
    (hd 777 (by decide) (by decide) (by decide) (by decide)).trans ha.history
  obtain ⟨t, ht, b, he, hb⟩ := staged_attempt_eval clauses hm rows query queryCost d words.flatten
    hword hcounterD'
    (loader_clean d
      ((hf 768 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h1)
      hcoreD hsD) hlowD
    (by rw [hf 767 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hf 780 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hvalue)
    (by rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hmword)
    (by rw [hf 818 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hshape)
    hcD L
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl
      · rw [hhistD]
        exact hbytes
      · rw [hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 782 (by simp)
      · rw [hf 783 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 783 (by simp)
      · rw [hf 784 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 784 (by simp)
      · rw [hf 785 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hsource 785 (by simp)) hC
    (by
      intro i hi
      have hsmall : i.val < 770 := by
        simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      have hneq (j : Fin 896) (hj : 770 ≤ j.val) : i ≠ j := by
        intro he
        subst i
        omega
      rw [hf i (hneq 770 (by decide)) (hneq 771 (by decide)) (hneq 777 (by decide))
        (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 781 (by decide))]
      exact hempty i hi) hq
  refine ⟨t, ?_, b, he, hb⟩
  have hbudget : stagedAttemptBudget d n m depth queryCost L = stagedAttemptBudget base n m depth queryCost L := by
    simp only [stagedAttemptBudget, attemptBudget, massBudget, LeafOuterProgram.routeCost,
      hf 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 769 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hf 782 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hbudget ▸ ht

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRun.staged_boundary_attempt_oai
