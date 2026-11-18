-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyCoarseInputWork_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:09.441066+00:00
-- url     : https://prove2.me/submissions/26f8f6bb-40cf-42d5-803c-d3ab3990a94c

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_OAIQ361V3Ea004

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A finite binary dictionary for gathered and globally memoized inputs.
Each recursive step reads one key bit and touches one node. The explicit
counters charge pointer/node operations; multiword key/value processing
is accounted for separately by their bit lengths. -/

namespace EditApproximation



namespace BinaryMemo

variable {α : Type*}











theorem lookup_insert_other (tree : BinaryMemo α) (key query : List Bool) (a : α)
    (hne : query ≠ key) : (tree.insert key a).lookup query = tree.lookup query := by
  induction key generalizing tree query with
  | nil =>
    cases query with
    | nil => exact False.elim (hne rfl)
    | cons b rest => cases b <;> rfl
  | cons b rest ih =>
    cases query with
    | nil => cases b <;> rfl
    | cons c tail =>
      cases b <;> cases c
      · exact ih tree.left tail (fun h => hne (congrArg (List.cons false) h))
      · rfl
      · rfl
      · exact ih tree.right tail (fun h => hne (congrArg (List.cons true) h))

/-- Persistent insertion allocates one new node at each visited level;
the two untouched subtrees are retained by pointer. -/


theorem insertCosted_spec (tree : BinaryMemo α) (key : List Bool) (a : α) :
    tree.insertCosted key a = (tree.insert key a, key.length + 1) := by
  induction key generalizing tree with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [insertCosted, insert, ih, List.length_cons]

end BinaryMemo

theorem binaryMemoKey_injective (d : ℕ) :
    Set.InjOn (binaryMemoKey d) {n | n < 2 ^ d} := by
  induction d with
  | zero => intro n hn m hm _; simp only [pow_zero, Set.mem_ofPred_eq] at hn hm; omega
  | succ d ih =>
    intro n hn m hm heq
    have hpair := List.cons.inj heq
    have hmod : n % 2 = m % 2 := by
      have hiff := decide_eq_decide.mp hpair.1
      omega
    have hnq : n / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hn
      omega
    have hmq : m / 2 < 2 ^ d := by
      simp only [Set.mem_ofPred_eq, pow_succ] at hm
      omega
    have hquot := ih hnq hmq hpair.2
    omega

theorem binaryMemo_lookup_insert {α : Type*} (tree : BinaryMemo α)
    (d key query : ℕ) (hkey : key < 2 ^ d) (hquery : query < 2 ^ d) (a : α) :
    (tree.insert (binaryMemoKey d key) a).lookup (binaryMemoKey d query) =
      if query = key then some a else tree.lookup (binaryMemoKey d query) := by
  split_ifs with heq
  · subst query
    exact BinaryMemo.lookup_insert_same _ _ _
  · apply BinaryMemo.lookup_insert_other
    intro hencoded
    exact heq (binaryMemoKey_injective d hquery hkey hencoded)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BalancedWidths
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalSubtreeNode_zero _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Width and node counts for the fixed interval tree

Repeated ceiling division gives the physical-depth width bound. This
includes empty children and repeated interval labels, which must still
be counted as distinct nodes in the lazy evaluation analysis.
-/

namespace EditApproximation

open Finset

theorem ceilDiv_comp (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a * b) := by
  apply eq_of_forall_ge_iff
  intro k
  rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha,
    ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb), Nat.mul_assoc]

theorem balanced_child_width_le_ceiling (width M i : ℕ) (hM : 0 < M) :
    ((i + 1) * width / M) - i * width / M ≤ width ⌈/⌉ M := by
  let c := width ⌈/⌉ M
  have hceil : width ≤ M * c := (ceilDiv_le_iff_le_mul hM).mp (le_refl c)
  have hfloor := Nat.lt_mul_div_succ (i * width) hM
  have hsum : i * width + width < (i * width / M + c + 1) * M := by nlinarith
  have hdiv := (Nat.div_lt_iff_lt_mul hM).2 hsum
  have hid : (i + 1) * width = i * width + width := by ring
  rw [hid]
  omega

theorem sourceChild_width_le_ceiling {n M : ℕ} (parent : TargetInterval n) (child : Fin M) :
    (sourceChild parent child).hi - (sourceChild parent child).lo ≤
      (parent.hi - parent.lo) ⌈/⌉ M := by
  dsimp only [sourceChild, balancedCut]
  rw [Nat.add_sub_add_left]
  exact balanced_child_width_le_ceiling _ _ _ (Nat.zero_lt_of_lt child.isLt)

theorem sourceIntervalAt_width (M n d : ℕ) (hM : 0 < M) (node : TreeLayer M d) :
    (sourceIntervalAt M n d node).hi - (sourceIntervalAt M n d node).lo ≤ n ⌈/⌉ M ^ d := by
  induction d with
  | zero => simp [sourceIntervalAt]
  | succ d ih =>
    have hchild := sourceChild_width_le_ceiling (sourceIntervalAt M n d node.1) node.2
    have hmono := (gc_mul_ceilDiv hM).monotone_l (ih node.1)
    have hcomp := ceilDiv_comp n (M ^ d) M (pow_pos hM d) hM
    change (sourceChild (sourceIntervalAt M n d node.1) node.2).hi -
        (sourceChild (sourceIntervalAt M n d node.1) node.2).lo ≤ n ⌈/⌉ M ^ (d + 1)
    exact hchild.trans (hmono.trans_eq (by rw [hcomp, pow_succ]))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dependency expansions with two edge sorts. The certificate
checks progress and local branching at every actual node; the global
count follows from these local conditions. -/

namespace EditApproximation

open Finset

namespace DependencyExpansion

section Builder

variable {ι : Type*} (d r m n : ι → ℕ)
  (s : (x : ι) → Fin (m x) → ι) (e : (x : ι) → Fin (n x) → ι)
  (hs : ∀ x i, d (s x i) < d x ∧ r (s x i) ≤ r x)
  (he : ∀ x i, d (e x i) ≤ d x ∧ r (e x i) < r x)

theorem build_depth (root : ι) : (build d r m n s e hs he root).depth = d root := by
  rw [build]
  rfl

end Builder

end DependencyExpansion
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoizedOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent dictionary requests. A fresh oracle is called only on a
cache miss; subsequent requests preserve and return the stored answer. -/

namespace EditApproximation

section Requests

variable {ι : Type*} (bits : ℕ) (encode : ι → ℕ) (oracle : ι → ℚ)

theorem memoSound_empty : memoSound bits encode oracle .empty := by
  intro key value hvalue
  rw [BinaryMemo.lookup_empty] at hvalue
  cases hvalue

end Requests

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Well-founded recursive memo evaluation. A local query program may
choose later requests from earlier answers. Each recursive request carries
its strict rank decrease; no complete table is evaluated in advance. -/

namespace EditApproximation





namespace FiniteQuery



theorem run_sound {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
        memoSound bits encode expected (ask key memory).memory)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    (run ask program memory).value = program.value answer ∧
      memoSound bits encode expected (run ask program memory).memory := by
  induction program generalizing memory with
  | done result => exact ⟨rfl, hsound⟩
  | read key next ih =>
    have hfirst := hask key memory hsound
    have hrest := ih (ask key memory).value (ask key memory).memory hfirst.2
    refine ⟨?_, hrest.2⟩
    simpa only [run, value, hfirst.1] using hrest.1

end FiniteQuery



theorem memoSound_insert {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (expected : κ → ℚ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) (key : κ) :
    memoSound bits encode expected
      (memory.insert (binaryMemoKey bits (encode key)) (expected key)) := by
  intro other result hresult
  rw [binaryMemo_lookup_insert _ bits (encode key) (encode other)
    (hbounded key) (hbounded other)] at hresult
  split_ifs at hresult with heq
  · have hkey : other = key := hinjective heq
    subst other
    exact Option.some.inj hresult.symm
  · exact hsound other result hresult

theorem rankedMemoEvaluate_sound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    (rankedMemoEvaluate rank program bits encode key memory).value = rankedProgramValue rank program key ∧
      memoSound bits encode (rankedProgramValue rank program)
        (rankedMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      (rankedMemoEvaluate rank program bits encode key memory).value = rankedProgramValue rank program key ∧
        memoSound bits encode (rankedProgramValue rank program)
          (rankedMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · rename_i result hresult
        exact ⟨hmemory key result hresult, hmemory⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
              memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hprevious
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hprevious
        have hrun := FiniteQuery.run_sound bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        have hvalue : (FiniteQuery.run
            (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedProgramValue rank program key := by
          rw [rankedProgramValue]
          exact hrun.1
        simp only [BinaryMemo.insertCosted_spec]
        refine ⟨hvalue, ?_⟩
        rw [hvalue]
        exact memoSound_insert bits encode hinjective hbounded _ _ hrun.2 key
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_eq_sum {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) :
    program.cost oracle weight = ((program.keys oracle).map weight).sum := by
  induction program with
  | done _ => rfl
  | read key next ih => exact congrArg (weight key + ·) (ih (oracle key))

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedCoarseOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All initial-entry information used by a charged table body arrives
through explicit requests. Flattening those requests gives an adaptive
coarse oracle program whose shape is independent of coarse answers. -/

namespace EditApproximation

namespace FiniteQuery

theorem substitute_cost {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (weight : κ → ℕ) (query : FiniteQuery ι) :
    (query.substitute ask).cost oracle weight = query.cost
      (fun key => (ask key).value oracle) (fun key => (ask key).cost oracle weight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, cost_bind, cost]
    exact congrArg ((ask key).cost oracle weight + ·) (ih ((ask key).value oracle))

theorem substitute_value {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).value oracle = query.value (fun key => (ask key).value oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, bind_value, value]
    exact ih ((ask key).value oracle)

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Random source coordinates and recursive table entries share the same
memo evaluator. Source coordinates have rank zero; each table rank is
shifted by one. Consequently repeated source reads reuse their stored draw. -/

namespace EditApproximation

namespace SourceRanked

variable {σ κ : Type*}







 theorem body_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    (body tableRank tableBody sourceValue key).value
      (fun next => value sourceValue tableValue next.val) = value sourceValue tableValue key := by
  cases key with
  | inl source => rfl
  | inr table =>
    rw [body, FiniteQuery.mapKeys_value]
    have horacle : (fun next => value sourceValue tableValue next.val) ∘ child tableRank table =
        Sum.elim sourceValue (fun next => tableValue next.val) := by
      funext next
      cases next <;> rfl
    rw [horacle]
    exact hbody table

 theorem program_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (key : Sum σ κ) :
    rankedProgramValue (rank tableRank) (body tableRank tableBody sourceValue) key =
      value sourceValue tableValue key :=
  rankedProgramValue_eq _ _ _ (body_value tableRank tableBody sourceValue tableValue hbody) key

end SourceRanked

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryCostOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.FiniteQuery

theorem cost_mono_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (hle : ∀ key, left key ≤ right key) :
    program.cost oracle left ≤ program.cost oracle right := by
  induction program with
  | done result => exact le_rfl
  | read key next ih => exact Nat.add_le_add (hle key) (ih (oracle key))

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source leaves add only their executed read count to each table body.
Projecting them away preserves the table dependency program, so a uniform
local source budget multiplies its uncached request bound. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

include hbody in
 theorem projectedProgram_value (key : κ) :
    rankedProgramValue tableRank (projectedBody tableRank tableBody sourceValue) key = tableValue key :=
  rankedProgramValue_eq tableRank _ tableValue
    (projectedBody_value tableRank tableBody sourceValue tableValue hbody) key

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseOracle
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed accepted source family leaves a nonanticipating coarse query:
coarse values enter only when the corresponding leaf is requested. -/

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

theorem physicalRandomGlobalQuery_refinement_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : PhysicalTableRequest M J target.length)
    (hi : ¬ parent.index ≤ T) (hd : parent.node.1.val < J)
    (hw : ¬ (physicalSourceInterval source.length parent.node).hi -
      (physicalSourceInterval source.length parent.node).lo ≤ 1) :
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger left parent =
    physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger right parent := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨by omega, hd, hw⟩, dite_eq_left ⟨by omega, hd, hw⟩]

/-- Coarse answers enter the charged program only at coarse leaves. -/
theorem chargedRandomGlobalQuery_table_initial_independent
    (left right : PhysicalEntry M J target.length → ℕ)
    (parent : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger left (.inr parent) =
    chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger right (.inr parent) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  split_ifs with hi hd hw
  · rfl
  · rfl
  · unfold physicalRandomBoundedQuery SourceRanked.restrictBody
    rw [physicalRandomGlobalQuery_refinement_initial_independent source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger left right parent.val hi hd hw]
  · rfl

theorem chargedRandomCoarseQuery_value
    (initial : PhysicalEntry M J target.length → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
    rankedProgramValue ChargedPhysicalRequest.rank
      (SourceRanked.projectedBody ChargedPhysicalRequest.rank
        (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
  have hall : ∀ level root, root.rank = level →
      (chargedRandomCoarseQuery source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger sourceAnswer root).value (fun entry => (initial entry : ℚ)) =
      rankedProgramValue ChargedPhysicalRequest.rank
        (SourceRanked.projectedBody ChargedPhysicalRequest.rank
          (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial) sourceAnswer) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedProgramValue]
        rfl
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_value, rankedProgramValue]
        unfold SourceRanked.projectedBody
        rw [
          chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S passes copies
            factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        congr 1
        funext child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKeys
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryMemo.mapValues_insert _root_.OAI.EditApproximation.BinaryMemo.mapValues_left _root_.OAI.EditApproximation.BinaryMemo.mapValues_lookup _root_.OAI.EditApproximation.BinaryMemo.mapValues_nodes _root_.OAI.EditApproximation.BinaryMemo.mapValues_right _root_.OAI.EditApproximation.BinaryMemo.mapValues_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A cache miss is among the requests of the uncached execution with
identical answers. This includes adaptive continuations and cache hits. -/

namespace EditApproximation

namespace FiniteQuery

theorem substitute_keys {ι κ : Type*} (ask : ι → FiniteQuery κ) (oracle : κ → ℚ)
    (query : FiniteQuery ι) :
    (query.substitute ask).keys oracle =
      (query.keys (fun key => (ask key).value oracle)).flatMap (fun key => (ask key).keys oracle) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    simp only [substitute, keys_bind, keys, List.flatMap_cons]
    rw [ih]

theorem run_freshKeys_mem {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ) (allowed : ι → List κ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
      memoSound bits encode expected (ask key memory).memory ∧
      ∀ item ∈ (ask key memory).freshKeys, item ∈ allowed key)
    (query : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    ∀ item ∈ (run ask query memory).freshKeys, item ∈ (query.keys answer).flatMap allowed := by
  induction query generalizing memory with
  | done value => simp only [run, List.not_mem_nil, false_implies, implies_true]
  | read key next ih =>
    have hf := hask key memory hsound
    intro item hitem
    simp only [run, List.mem_append] at hitem
    rcases hitem with hfirst | hrest
    · exact List.mem_flatMap.mpr ⟨key, List.mem_cons_self, hf.2.2 item hfirst⟩
    · have hr := ih (ask key memory).value (ask key memory).memory hf.2.1 item hrest
      rw [hf.1] at hr
      obtain ⟨child, hc, hi⟩ := List.mem_flatMap.mp hr
      exact List.mem_flatMap.mpr ⟨child, List.mem_cons_of_mem key hc, hi⟩

theorem eraseSources_inr_mem_iff {σ κ : Type*} (source : σ → ℚ) (table : κ → ℚ)
    (query : FiniteQuery (Sum σ κ)) (key : κ) :
    Sum.inr key ∈ query.keys (Sum.elim source table) ↔
      key ∈ (eraseSources source query).keys table := by
  induction query with
  | done value => simp only [keys, eraseSources, List.not_mem_nil]
  | read next continuation ih =>
    cases next with
    | inl scalar => simpa only [keys, eraseSources, Sum.elim_inl, List.mem_cons,
        Sum.inr_ne_inl, false_or] using ih (source scalar)
    | inr child => simpa only [keys, eraseSources, Sum.elim_inr, List.mem_cons,
        Sum.inr.injEq] using or_congr Iff.rfl (ih (table child))

end FiniteQuery

theorem rankedMemoEvaluate_freshKeys_mem {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
      item ∈ rankedUncachedKeys rank program key := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      ∀ item ∈ (rankedMemoEvaluate rank program bits encode key memory).freshKeys,
        item ∈ rankedUncachedKeys rank program key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · simp
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
            ∀ item ∈ (rankedMemoEvaluate rank program bits encode child.val previous).freshKeys,
              item ∈ rankedUncachedKeys rank program child.val := by
          intro child previous hp
          have hs := rankedMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp⟩
        have hr := FiniteQuery.run_freshKeys_mem bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child => rankedUncachedKeys rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        intro item hi
        simp only [List.mem_cons] at hi
        rw [rankedUncachedKeys]
        rcases hi with rfl | hi
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem key (hr item hi)
  exact hall (rank key) key rfl memory hsound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ)
  (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
  (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
  (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
    tableValue key)

include hbody

/-- Forgetting source leaves preserves every table request, including
those which the mixed memo execution first encounters after a cache hit. -/
theorem uncachedKeys_table_mem (root item : κ)
    (hitem : Sum.inr item ∈ rankedUncachedKeys (rank tableRank)
      (body tableRank tableBody sourceValue) (.inr root)) :
    item ∈ rankedUncachedKeys tableRank (projectedBody tableRank tableBody sourceValue) root := by
  let mixed := body tableRank tableBody sourceValue
  let projected := projectedBody tableRank tableBody sourceValue
  have hvm (key : Sum σ κ) : rankedProgramValue (rank tableRank) mixed key =
      value sourceValue tableValue key := program_value tableRank tableBody sourceValue tableValue hbody key
  have hvp (key : κ) : rankedProgramValue tableRank projected key = tableValue key :=
    projectedProgram_value tableRank tableBody sourceValue tableValue hbody key
  have hall : ∀ level root, tableRank root = level → ∀ item,
      Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inr root) →
      item ∈ rankedUncachedKeys tableRank projected root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel item hm
      rw [rankedUncachedKeys] at hm ⊢
      rcases List.mem_cons.mp hm with heq | hm
      · exact List.mem_cons.mpr (.inl (Sum.inr.inj heq))
      · have hanswer :
            (fun next => rankedProgramValue (rank tableRank) mixed next.val) ∘ child tableRank root =
              Sum.elim sourceValue (fun next => tableValue next.val) := by
          funext next
          rw [Function.comp_apply, hvm]
          cases next <;> rfl
        change Sum.inr item ∈ ((mixed (.inr root)).keys _).flatMap _ at hm
        dsimp only [mixed, body] at hm
        rw [FiniteQuery.mapKeys_keys, hanswer] at hm
        obtain ⟨next, hn, hi⟩ := List.mem_flatMap.mp hm
        obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hn
        cases raw with
        | inl scalar =>
          change Sum.inr item ∈ rankedUncachedKeys (rank tableRank) mixed (.inl scalar) at hi
          rw [rankedUncachedKeys] at hi
          simp only [mixed, body, FiniteQuery.keys, List.flatMap_nil,
            List.mem_cons, Sum.inr_ne_inl, List.not_mem_nil, or_false] at hi
        | inr next =>
          have ht := (FiniteQuery.eraseSources_inr_mem_iff sourceValue
            (fun child => tableValue child.val) (tableBody root) next).mp hr
          have hi' := ih (tableRank next.val) (hlevel ▸ next.property) next.val rfl item hi
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨next, ?_, hi'⟩
          change next ∈ (FiniteQuery.eraseSources sourceValue (tableBody root)).keys
            (fun child => rankedProgramValue tableRank projected child.val)
          simpa only [hvp] using ht
  exact hall (tableRank root) root rfl item hitem

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseKeys
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Keys

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (initial : PhysicalEntry M J target.length → ℕ)

local notation "mixed" => chargedRandomGlobalQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixed sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P F exponent H Q T S
  passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer

 theorem chargedRandomCoarseQuery_uncached_keys
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  have hall : ∀ level root, root.rank = level → ∀ entry,
      Sum.inl entry ∈ rankedUncachedKeys ChargedPhysicalRequest.rank program root →
      entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel entry he
      cases root with
      | inl base =>
        rw [rankedUncachedKeys] at he
        simp only [SourceRanked.projectedBody, chargedRandomGlobalQuery,
          FiniteQuery.eraseSources, FiniteQuery.keys, List.flatMap_nil, List.mem_cons,
          List.not_mem_nil, or_false, Sum.inl.injEq] at he
        subst entry
        rw [chargedRandomCoarseQuery]
        exact List.mem_cons_self
      | inr parent =>
        rw [rankedUncachedKeys] at he
        rcases List.mem_cons.mp he with he | he
        · cases he
        obtain ⟨child, hc, he⟩ := List.mem_flatMap.mp he
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_keys]
        apply List.mem_flatMap.mpr
        refine ⟨child, ?_, ih child.val.rank (hlevel ▸ child.property) child.val rfl entry he⟩
        have hv (child) := chargedRandomCoarseQuery_value source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P F exponent H Q T S
          passes copies factor multiplier tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        exact hc
  exact hall root.rank root rfl entry hentry

 theorem chargedRandomMemo_coarse_key
    (values : ChargedPhysicalRequest M J target.length passes copies T S → ℚ)
    (hbody : ∀ key, (mixed key).value (Sum.elim sourceAnswer (fun next => values next.val)) = values key)
    (bits : ℕ) (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (entry : PhysicalEntry M J target.length)
    (hentry : Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
        tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).freshKeys) :
    entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ)) := by
  apply chargedRandomCoarseQuery_uncached_keys source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial root entry
  apply SourceRanked.uncachedKeys_table_mem ChargedPhysicalRequest.rank mixed sourceAnswer values hbody root
    (Sum.inl entry)
  exact rankedMemoEvaluate_freshKeys_mem _ _ bits encode hinjective hbounded (.inr root) .empty
    (memoSound_empty _ _ _) (.inr (.inl entry)) hentry

end Keys

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDependencyExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency tree here is obtained from the requests made by the
finite adaptive program at its actual answers. Local depth/index progress
therefore bounds execution, rather than an independently supplied tree. -/

namespace EditApproximation

open Finset

section Queries

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})

theorem queryRequestList_cost (key : κ) (weight : κ → ℕ) :
    (program key).cost
        (fun child => rankedProgramValue (fun x => depth x + index x) program child.val)
        (fun child => weight child.val) =
      ((queryRequestList depth index program key).map weight).sum := by
  rw [FiniteQuery.cost_eq_sum]
  simp only [queryRequestList, List.map_map, Function.comp_def]

theorem sum_map_partition (predicate : κ → Bool) (weight : κ → ℕ) (keys : List κ) :
    ((keys.filter (fun key => !predicate key)).map weight).sum +
      ((keys.filter predicate).map weight).sum = (keys.map weight).sum := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
    cases hp : predicate key <;> simp only [List.filter_cons, hp, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, reduceIte, List.map_cons, List.sum_cons]
    all_goals omega

variable (progress : ∀ key child, child ∈ queryRequestList depth index program key →
  (depth child < depth key ∧ index child ≤ index key) ∨
  (depth child ≤ depth key ∧ index child < index key))

include progress

theorem queryDependencyExpansion_depth (root : κ) :
    (queryDependencyExpansion depth index program progress root).depth = depth root :=
  DependencyExpansion.build_depth _ _ _ _ _ _ _ _ root

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FreshCoordinateCost
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A first request can depend on earlier answers, but cannot depend on
its own unexposed coordinate. Finite product independence then preserves
that coordinate's unconditional expected cost. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory Finset

attribute [local instance] Classical.propDecidable



theorem sum_distinct_requests_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, if i ∈ keys then weight i else 0) ≤ (keys.map weight).sum := by
  have hset : univ.filter (fun i => i ∈ keys) = keys.toFinset := by ext i; simp
  rw [← sum_filter, hset]
  clear hset
  induction keys with
  | nil => simp
  | cons key keys ih =>
    by_cases hmem : key ∈ keys
    · simp only [List.toFinset_cons, insert_eq_of_mem (List.mem_toFinset.mpr hmem),
        List.map_cons, List.sum_cons]
      omega
    · rw [List.toFinset_cons, sum_insert (by simpa only [List.mem_toFinset] using hmem),
        List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

theorem sum_selected_nat_weights_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (keys : List ι) (weight : ι → ℕ) :
    (∑ i, selectionIndicator (i ∈ keys) * (weight i : ℝ)) ≤
      ((keys.map weight).sum : ℕ) := by
  calc
    _ = ∑ i, if i ∈ keys then (weight i : ℝ) else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ keys <;> simp [selectionIndicator, hi]
    _ ≤ _ := by exact_mod_cast sum_distinct_requests_le keys weight

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWeightedWork
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Per-request local work summed along the actual adaptive expansion.
This is a weighted analogue of the uncached request count. -/

namespace EditApproximation

open Finset

section Weighted

variable {κ : Type*} (depth index : κ → ℕ)
  (program : (key : κ) → FiniteQuery
    {child : κ // depth child + index child < depth key + index key})
  (progress : ∀ key child, child ∈ queryRequestList depth index program key →
    (depth child < depth key ∧ index child ≤ index key) ∨
    (depth child ≤ depth key ∧ index child < index key))

theorem queryDependencyExpansion_weighted (weight : ℕ → ℕ) (root : κ) :
    (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
      rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
  have hall : ∀ level root, depth root + index root = level →
      (queryDependencyExpansion depth index program progress root).depthWeightedCount weight =
        rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hroot
      conv_lhs => unfold queryDependencyExpansion
      rw [DependencyExpansion.build]
      change weight (depth root) + (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) +
        (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) = _
      have hs (i : Fin (querySameRequests depth index program root).length) :=
        querySameRequests_progress depth index program progress root i
      have he (i : Fin (queryEarlierRequests depth index program root).length) :=
        queryEarlierRequests_progress depth index program progress root i
      have hsame : (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).depthWeightedCount weight) =
        (((querySameRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (querySameRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((querySameRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_lt_of_le (hs i).1 (hs i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      have hearlier : (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).depthWeightedCount weight) =
        (((queryEarlierRequests depth index program root).map
          (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))).sum) := by
        calc
          _ = ∑ i : Fin (queryEarlierRequests depth index program root).length,
              rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key))
                ((queryEarlierRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_le_of_lt (he i).1 (he i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      rw [hsame, hearlier, rankedUncachedWork, queryRequestList_cost]
      have hp := sum_map_partition (fun child => decide (index child < index root))
        (rankedUncachedWork (fun key => depth key + index key) program (fun key => weight (depth key)))
        (queryRequestList depth index program root)
      change weight (depth root) + _ + _ = _ + weight (depth root)
      change _ + _ = _ at hp
      dsimp only [querySameRequests, queryEarlierRequests]
      omega
  exact hall (depth root + index root) root rfl

end Weighted

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCoarseWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial) sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger sourceAnswer
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

 theorem chargedRandomCoarseQuery_cost_le (weight : ℕ → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => weight (J - entry.1.1.val)) ≤
    rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
  have hall : ∀ level root, root.rank = level →
      (coarse root).cost (fun entry => (initial entry : ℚ))
        (fun entry => weight (J - entry.1.1.val)) ≤
      rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedUncachedWork]
        simp only [FiniteQuery.cost, SourceRanked.projectedBody, chargedRandomGlobalQuery, FiniteQuery.eraseSources, ChargedPhysicalRequest.depth, Nat.zero_add,
          Nat.add_zero, le_refl]
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_cost]
        have hv (child) := chargedRandomCoarseQuery_value source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        rw [rankedUncachedWork]
        apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans (Nat.le_add_right _ _)
        intro child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

variable
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody
 theorem chargedRandomCoarseQuery_width_cost_le
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => 1 + source.length ⌈/⌉ M ^ entry.1.1.val) ≤
    (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length := by
  have hweight := chargedRandomCoarseQuery_cost_le source target N P H T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial
    (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  have hdepth : ∀ entry : PhysicalEntry M J target.length,
      J - (J - entry.1.1.val) = entry.1.1.val := by
    intro entry
    have := entry.1.1.isLt
    omega
  simp only [hdepth] at hweight
  apply hweight.trans_eq
  have hw := queryDependencyExpansion_weighted depth index program
    (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  change _ = (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depthWeightedCount
      (fun d => 1 + source.length ⌈/⌉ M ^ (_ - d))
  rw [show (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depth = depth root from
    queryDependencyExpansion_depth depth index program
      (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root]
  rw [hroot]
  exact hw.symm

end Coarse

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseInputWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.chargedPhysicalCodeWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalFamilyCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalTableCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalBoundedWithWork_value _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.querySupportedChildWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Coarse
variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw

theorem physicalFamilyCoarseQuery_input_cost_le_width (root : Table) (hroot : root.depth = J) :
    (physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
      tau eta kappa delta draw root).cost (fun entry => (initial entry : ℚ))
      (fun entry => (physicalSource source entry.1).length + 1) ≤
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length := by
  apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans
    (chargedRandomCoarseQuery_width_cost_le source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw)
      (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw) root hroot)
  intro entry
  rw [physicalSource_length_eq]
  simpa only [physicalSourceInterval, Nat.add_comm] using Nat.add_le_add_right
    (sourceIntervalAt_width M source.length entry.1.1.val (Nat.pos_of_neZero M) entry.1.2) 1

theorem physicalFamilyCoarseInputWork_le_oai (bits : ℕ) (encode : Sum Key Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : Table) (hroot : root.depth = J) :
    physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial draw bits encode root ≤
    ((physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hP draw root).widthWork M source.length : ℝ) := by
  classical
  let query := physicalFamilyCoarseQuery source target N P H T S passes copies factor multiplier
    tau eta kappa delta draw root
  have hkey (entry : PhysicalEntry M J target.length) :=
    chargedRandomMemo_coarse_key source target N P ell exponent H (ell ^ 80) T S
      (passes + 1) copies factor multiplier tau eta kappa delta readGroup readInteger answer initial
      (physicalFamilyRequestValue source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      (physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80) T S passes copies
        factor multiplier tau eta kappa delta initial hP draw)
      bits encode hinjective hbounded root entry
  have hs := sum_selected_nat_weights_le (query.keys (fun entry => (initial entry : ℚ)))
    (fun entry => (physicalSource source entry.1).length + 1)
  have hc := physicalFamilyCoarseQuery_input_cost_le_width source target N P H T S passes copies
    factor multiplier tau eta kappa delta initial hP draw root hroot
  change query.cost (fun entry => (initial entry : ℚ))
    (fun entry => (physicalSource source entry.1).length + 1) ≤ _ at hc
  rw [FiniteQuery.cost_eq_sum] at hc
  apply le_trans (b := ∑ entry, selectionIndicator (entry ∈ query.keys
    (fun entry => (initial entry : ℚ))) * ((physicalSource source entry.1).length + 1 : ℕ))
  · unfold physicalFamilyCoarseInputWork
    apply Finset.sum_le_sum
    intro entry _
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    by_cases he : Sum.inr (Sum.inl entry) ∈
        (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
          copies factor multiplier tau eta kappa delta readGroup readInteger initial answer
          bits encode root).freshKeys
    · have hq := hkey entry he
      change entry ∈ query.keys (fun entry => (initial entry : ℚ)) at hq
      simp only [selectionIndicator, he, hq, ite_true, if_true, le_refl]
    · simp only [selectionIndicator, he, ite_false, if_false]
      split <;> norm_num
  · exact hs.trans (by exact_mod_cast hc)

end Coarse
end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalFamilyCoarseInputWork_le_oai.{u_1} := @OAI.EditApproximation.physicalFamilyCoarseInputWork_le_oai.{u_1}
