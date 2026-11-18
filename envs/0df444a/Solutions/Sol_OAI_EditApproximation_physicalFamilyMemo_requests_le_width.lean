-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyMemo_requests_le_width
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:28.835225+00:00
-- url     : https://prove2.me/submissions/df891dd0-eac3-44e0-ae54-873d42640ff7

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
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
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

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

theorem run_requests_le {ι κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → ℚ) (answer : ι → ℚ) (weight : ι → ℕ)
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, memoSound bits encode expected memory →
      (ask key memory).value = answer key ∧
      memoSound bits encode expected (ask key memory).memory ∧
      (ask key memory).requests ≤ weight key)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode expected memory) :
    (run ask program memory).requests ≤ program.cost answer weight := by
  induction program generalizing memory with
  | done _ => exact le_rfl
  | read key next ih =>
    have hf := hask key memory hsound
    have hr := ih (ask key memory).value (ask key memory).memory hf.2.1
    simp only [run, cost]
    rw [hf.1] at hr
    rw [hf.1]
    exact Nat.add_le_add hf.2.2 hr

end FiniteQuery

theorem rankedUncachedCalls_pos {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key}) (key : κ) :
    1 ≤ rankedUncachedCalls rank program key := by
  rw [rankedUncachedCalls]
  omega

theorem rankedMemoEvaluate_requests_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo ℚ)
    (hsound : memoSound bits encode (rankedProgramValue rank program) memory) :
    (rankedMemoEvaluate rank program bits encode key memory).requests ≤
      rankedUncachedCalls rank program key := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      memoSound bits encode (rankedProgramValue rank program) memory →
      (rankedMemoEvaluate rank program bits encode key memory).requests ≤
        rankedUncachedCalls rank program key := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmemory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact rankedUncachedCalls_pos rank program key
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            memoSound bits encode (rankedProgramValue rank program) previous →
            (rankedMemoEvaluate rank program bits encode child.val previous).value =
                rankedProgramValue rank program child.val ∧
            memoSound bits encode (rankedProgramValue rank program)
                (rankedMemoEvaluate rank program bits encode child.val previous).memory ∧
            (rankedMemoEvaluate rank program bits encode child.val previous).requests ≤
                rankedUncachedCalls rank program child.val := by
          intro child previous hprevious
          have hs := rankedMemoEvaluate_sound rank program bits encode hinjective hbounded
            child.val previous hprevious
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hprevious⟩
        have hr := FiniteQuery.run_requests_le bits encode (rankedProgramValue rank program)
          (fun child : {child : κ // rank child < rank key} => rankedProgramValue rank program child.val)
          (fun child => rankedUncachedCalls rank program child.val)
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmemory
        rw [rankedUncachedCalls]
        exact Nat.add_le_add_right hr 1
  exact hall (rank key) key rfl memory hsound

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

theorem queryDependencyExpansion_nodes (root : κ) :
    (queryDependencyExpansion depth index program progress root).nodeCount =
      rankedUncachedCalls (fun key => depth key + index key) program root := by
  have hall : ∀ level root, depth root + index root = level →
      (queryDependencyExpansion depth index program progress root).nodeCount =
        rankedUncachedCalls (fun key => depth key + index key) program root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hroot
      conv_lhs => unfold queryDependencyExpansion
      rw [DependencyExpansion.build]
      change 1 + (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).nodeCount) +
        (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).nodeCount) = _
      have hs (i : Fin (querySameRequests depth index program root).length) :=
        querySameRequests_progress depth index program progress root i
      have he (i : Fin (queryEarlierRequests depth index program root).length) :=
        queryEarlierRequests_progress depth index program progress root i
      have hsame : (∑ i : Fin (querySameRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((querySameRequests depth index program root).get i)).nodeCount) =
        (((querySameRequests depth index program root).map
          (rankedUncachedCalls (fun key => depth key + index key) program)).sum) := by
        calc
          _ = ∑ i : Fin (querySameRequests depth index program root).length,
              rankedUncachedCalls (fun key => depth key + index key) program
                ((querySameRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_lt_of_le (hs i).1 (hs i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      have hearlier : (∑ i : Fin (queryEarlierRequests depth index program root).length,
          (queryDependencyExpansion depth index program progress
            ((queryEarlierRequests depth index program root).get i)).nodeCount) =
        (((queryEarlierRequests depth index program root).map
          (rankedUncachedCalls (fun key => depth key + index key) program)).sum) := by
        calc
          _ = ∑ i : Fin (queryEarlierRequests depth index program root).length,
              rankedUncachedCalls (fun key => depth key + index key) program
                ((queryEarlierRequests depth index program root).get i) := by
            apply sum_congr rfl
            intro i hi
            apply ih _ _ _ rfl
            rw [← hroot]
            exact Nat.add_lt_add_of_le_of_lt (he i).1 (he i).2
          _ = _ := Fin.sum_univ_fun_getElem _ _
      rw [hsame, hearlier, rankedUncachedCalls, queryRequestList_cost]
      have hp := sum_map_partition (fun child => decide (index child < index root))
        (rankedUncachedCalls (fun key => depth key + index key) program)
        (queryRequestList depth index program root)
      change 1 + _ + _ = _ + 1
      change _ + _ = _ at hp
      dsimp only [querySameRequests, queryEarlierRequests]
      omega
  exact hall (depth root + index root) root rfl

end Queries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCells
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Direct bounded-range enumeration of the cells meeting a query square. -/

namespace EditApproximation



theorem localCellCoordinates_length_le (side : ℚ) (hside : 0 < side)
    (p radius K : ℕ) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localCellCoordinates side p radius).length ≤ K + 2 := by
  let first := ⌊((p - radius : ℕ) : ℚ) / side⌋₊
  let last := ⌊((p + radius : ℕ) : ℚ) / side⌋₊
  have horder : first ≤ last := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (by exact_mod_cast (show p - radius ≤ p + radius by omega)) hside.le)
  have hhi : (last : ℚ) ≤ ((p + radius : ℕ) : ℚ) / side :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hside.le)
  have hlo : ((p - radius : ℕ) : ℚ) / side < (first : ℚ) + 1 := Nat.lt_floor_add_one _
  have hwidth : ((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ) ≤ 2 * radius := by
    have h : p + radius - (p - radius) ≤ 2 * radius := by omega
    have hR : ((p + radius - (p - radius) : ℕ) : ℚ) ≤ ((2 * radius : ℕ) : ℚ) := by exact_mod_cast h
    simpa only [Nat.cast_sub (show p - radius ≤ p + radius by omega), Nat.cast_mul, Nat.cast_ofNat] using hR
  have hquotient : ((p + radius : ℕ) : ℚ) / side - ((p - radius : ℕ) : ℚ) / side ≤ K := by
    calc
      _ = (((p + radius : ℕ) : ℚ) - ((p - radius : ℕ) : ℚ)) / side := by ring
      _ ≤ (2 * radius) / side := div_le_div_of_nonneg_right hwidth hside.le
      _ ≤ K := hbudget
  have hcount : ((last + 1 - first : ℕ) : ℚ) < (K : ℚ) + 2 := by
    rw [Nat.cast_sub (by omega : first ≤ last + 1), Nat.cast_add, Nat.cast_one]
    linarith only [hhi, hlo, hquotient]
  have hcountN : last + 1 - first < K + 2 := by exact_mod_cast hcount
  exact (by simpa only [localCellCoordinates, List.length_range', first, last] using hcountN.le)



theorem localTargetCells_length_le {n : ℕ} (side : ℚ) (hside : 0 < side)
    (radius K : ℕ) (q : TargetInterval n) (hbudget : 2 * (radius : ℚ) / side ≤ K) :
    (localTargetCells side radius q).length ≤ (K + 2) ^ 2 := by
  have hfirst := localCellCoordinates_length_le side hside q.lo radius K hbudget
  have hsecond := localCellCoordinates_length_le side hside q.hi radius K hbudget
  have h := list_flatMap_length_le (localCellCoordinates side q.lo radius)
    (fun lo => (localCellCoordinates side q.hi radius).map fun hi => (lo, hi)) (K + 2)
    (fun lo _ => by simpa only [List.length_map] using hsecond)
  exact h.trans (by simpa only [pow_two] using Nat.mul_le_mul_right (K + 2) hfirst)

/-- Every retained query scale has only polynomially many nearby cells,
even when the initial seed is inaccurate. -/
theorem localTargetCells_query_length {n : ℕ} (F b exponent : ℕ)
    (q : TargetInterval n) (w : ℚ) (hF : 1 ≤ F) (hb : 1 ≤ b)
    (hw : 0 ≤ w) (hwindow : w / (16 * F) ≤ b) :
    (localTargetCells ((2 : ℚ) ^ (-(exponent : ℤ)) * b) ⌈w⌉₊ q).length ≤
      ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hbpos : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hbR : (1 : ℚ) ≤ b := by exact_mod_cast hb
  have hside : 0 < (2 : ℚ) ^ (-(exponent : ℤ)) * b := by positivity
  apply localTargetCells_length_le _ hside _ ((32 * F + 2) * 2 ^ exponent) q
  apply (div_le_iff₀ hside).2
  have hwidth : w ≤ 16 * (F : ℚ) * b :=
    by nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow]
  have hceil : (⌈w⌉₊ : ℚ) < w + 1 := Nat.ceil_lt_add_one hw
  have hcancel : (((32 * F + 2) * 2 ^ exponent : ℕ) : ℚ) *
      ((2 : ℚ) ^ (-(exponent : ℤ)) * b) = (32 * (F : ℚ) + 2) * b := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [hcancel]
  nlinarith only [hceil, hwidth, hbR]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DyadicQueryWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The query scale window has length controlled by the refinement
factor, independently of the number of dyadic scales below N. -/

namespace EditApproximation

open Finset



theorem dyadicQueryWindow_length_le (N C : ℕ) (w a F : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hbudget : 128 * a * F ≤ (2 : ℚ) ^ C) :
    (dyadicQueryWindow N w a F).length ≤ C + 1 := by
  let keep : ℕ → Bool := fun e => decide (w / (16 * F) ≤ (2 ^ e : ℕ) ∧
    ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w)
  let indices := ((List.range (Nat.log 2 N + 1)).filter keep).toFinset
  have hlength : (dyadicQueryWindow N w a F).length = indices.card := by
    simp only [dyadicQueryWindow, dyadicScales, List.filter_map, List.length_map]
    exact (List.toFinset_card_of_nodup
      ((show (List.range (Nat.log 2 N + 1)).Nodup from List.nodup_range).filter keep)).symm
  rw [hlength]
  by_cases hnonempty : indices.Nonempty
  · let first := indices.min' hnonempty
    have hfirst : first ∈ indices := Finset.min'_mem _ _
    have hfirstKeep : w / (16 * F) ≤ (2 ^ first : ℕ) ∧ ((2 ^ first : ℕ) : ℚ) ≤ 8 * a * w :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hfirst)).2
    have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
    have hwfirst : w ≤ 16 * F * (2 ^ first : ℕ) := by
      nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hfirstKeep.1]
    have hsub : indices ⊆ Finset.Icc first (first + C) := by
      intro e he
      have hkeep : w / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w :=
        of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
      have hmul := mul_le_mul_of_nonneg_left hwfirst (show 0 ≤ 8 * a by positivity)
      have hpower := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) (2 ^ first))
      have hbound : ((2 ^ e : ℕ) : ℚ) ≤ (2 : ℚ) ^ C * (2 ^ first : ℕ) := by
        nlinarith only [hkeep.2, hmul, hpower]
      have hboundN : 2 ^ e ≤ 2 ^ (first + C) := by
        have heq : (2 : ℚ) ^ C * (2 ^ first : ℕ) = ((2 ^ (first + C) : ℕ) : ℚ) := by
          push_cast
          rw [pow_add]
          ring
        rw [heq] at hbound
        exact_mod_cast hbound
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ he,
        (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hboundN⟩
    have hcard := Finset.card_le_card hsub
    have hinterval : (Finset.Icc first (first + C)).card = C + 1 := by rw [Nat.card_Icc]; omega
    rwa [hinterval] at hcard
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using Nat.zero_le (C + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryBudget
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal online loop is bounded by the applicable scale window,
which is polynomial in ell throughout the computed factor schedule. -/

namespace EditApproximation

open Finset

theorem refinement_query_window_length (N F initialExponent : ℕ) (A w : ℚ)
    (hF : 1 ≤ F) (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (dyadicQueryWindow N w (refinementFactor A F) F).length ≤ initialExponent + 8 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hfactor : refinementFactor A F ≤ (2 : ℚ) ^ initialExponent / F := by
    apply max_le
    · exact (le_div_iff₀ hFpos).2 (by simpa only [one_mul] using hFbound)
    · exact div_le_div_of_nonneg_right hAbound hFpos.le
  have hproduct := mul_le_mul_of_nonneg_right hfactor hFpos.le
  rw [div_mul_cancel₀ _ hFpos.ne'] at hproduct
  have hbudget : 128 * refinementFactor A F * F ≤ (2 : ℚ) ^ (initialExponent + 7) := by
    have h := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℚ) ≤ 128)
    rw [pow_add]
    norm_num only [show (2 : ℚ) ^ 7 = 128 by norm_num]
    nlinarith only [h]
  simpa only [Nat.add_assoc, show (7 : ℕ) + 1 = 8 by rfl] using
    dyadicQueryWindow_length_le N (initialExponent + 7) w (refinementFactor A F) F
      (le_max_left _ _) (by exact_mod_cast hF) hbudget

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CurrentQueryInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Distinct current-index inputs of the bounded query loops. The cover
includes all whole-cell shared estimates, selected cell actions, and
online actions; repeated uses do not add recursive calls. -/

namespace EditApproximation

open Finset



theorem localGroupQueryKeys_scale {n N F exponent : ℕ} {a : ℚ}
    {initial : TargetInterval n → ℚ} {q : TargetInterval n} {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ localGroupQueryKeys N F exponent a initial q) :
    key.1 ∈ dyadicScales N := by
  obtain ⟨b, hb, hcell⟩ := List.mem_flatMap.mp hkey
  obtain ⟨cell, _, rfl⟩ := List.mem_map.mp hcell
  exact (List.mem_filter.mp hb).1

theorem localGroupQueryKeys_length {n : ℕ} (N F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n)
    (hF : 1 ≤ F) (hw : 0 ≤ initial q) :
    (localGroupQueryKeys N F exponent a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length *
        ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 := by
  unfold localGroupQueryKeys
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hbpos : 1 ≤ b := by
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hb).1
    exact Nat.one_le_two_pow
  simpa only [List.length_map] using
    localTargetCells_query_length F b exponent q (initial q) hF hbpos hw hwindow.1



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

theorem cost_collect {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).cost oracle weight =
      (keys.map fun key => (reader key).cost oracle weight).sum +
      (next (keys.map fun key => (reader key).value oracle)).cost oracle weight := by
  induction keys generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key keys ih =>
    simp only [collect, cost_bind, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

theorem computed_group_scale_count (N eb : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    (groupDyadicScales (integerParameters N).M (2 ^ eb) (inputSmallLog N)).length ≤
      2 * inputSmallLog N := by
  have hlogs := (inputSmallLog_bounds N hN).1
  have hsmall : smallLogExponent N ≤ inputSmallLog N :=
    (smallLogExponent N).lt_two_pow_self.le
  have hdiv := Nat.div_le_div_right (c := 20) hlogs
  change (groupDyadicScales (2 ^ (heightExponent N / 20)) (2 ^ eb)
    ((2 ^ smallLogExponent N : ℕ) : ℚ)).length ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat, groupDyadicScales_length_dyadic]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem mapKeys_cost {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (weight : κ → ℕ)
    (program : FiniteQuery ι) :
    (mapKeys f program).cost oracle weight = program.cost (oracle ∘ f) (weight ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (fun rest => weight (f key) + rest) (ih (oracle (f key)))

 theorem restrict_cost {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (weight : ι → ℕ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).cost (fun key => oracle key.val) (fun key => weight key.val) =
      program.cost oracle weight := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, cost] using
      congrArg (fun rest => weight key + rest) (ih (oracle key) hnext)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementDataQueryWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read counts for the full adaptive data query. Weighting reads permits
the same theorem to count current-index and earlier-index dependencies
separately. The bounds count executed readers, including repeated reads
across successive gathering stages. -/

namespace EditApproximation

theorem list_map_sum_le_constant {ι : Type*} (inputs : List ι) (cost : ι → ℕ) (bound : ℕ)
    (hcost : ∀ input, cost input ≤ bound) :
    (inputs.map cost).sum ≤ inputs.length * bound := by
  calc
    _ ≤ (inputs.map fun _ => bound).sum := List.sum_le_sum (fun input _ => hcost input)
    _ = _ := by simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GlobalQueryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted-cost transport for the full internal refinement body.
In this branch every request is an ordinary table request: parent initial,
child mass, child initial, old history or a current physical child. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_congr_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (heq : ∀ key ∈ program.keys oracle, left key = right key) :
    program.cost oracle left = program.cost oracle right := by
  rw [cost_eq_sum, cost_eq_sum]
  congr 1
  exact List.map_congr_left heq

end FiniteQuery

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

theorem cost_zero {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι) :
    program.cost oracle (fun _ => 0) = 0 := by
  induction program with
  | done result => rfl
  | read key next ih => simpa only [cost, Nat.zero_add] using ih (oracle key)

theorem cost_eq_zero_of_keys {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (weight : ι → ℕ) (hzero : ∀ key ∈ program.keys oracle, weight key = 0) :
    program.cost oracle weight = 0 :=
  (cost_congr_weights oracle program weight (fun _ => 0) hzero).trans (cost_zero oracle program)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCurrentQueryBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial same-index call budget after substituting the
computed window, cell, scale-label, sampling and rounding parameters. -/

namespace EditApproximation

theorem computed_window_exponent_bound (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    computedSeedInitialExponent N + 8 ≤ 2 * inputSmallLog N ^ 2 := by
  have hh := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right hp 4) hh
  unfold computedSeedInitialExponent
  have hslack : 4 * inputSmallLog N + 8 ≤ inputSmallLog N ^ 2 := by nlinarith
  nlinarith only [hmul, hslack]

theorem computed_local_cell_budget (N : ℕ) (hell : 1 ≤ inputSmallLog N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      1296 * inputSmallLog N ^ 82 := by
  have hpower : 2 ^ (40 * smallLogExponent N) = inputSmallLog N ^ 40 := by
    unfold inputSmallLog
    rw [← pow_mul, Nat.mul_comm]
  rw [hpower]
  have hinner : (32 * inputSmallLog N + 2) * inputSmallLog N ^ 40 + 2 ≤
      36 * inputSmallLog N ^ 41 := by
    have ha := Nat.mul_le_mul_right (inputSmallLog N ^ 40) (show 32 * inputSmallLog N + 2 ≤
      34 * inputSmallLog N by omega)
    have hb : 2 ≤ 2 * inputSmallLog N ^ 41 := Nat.mul_le_mul_left 2 (one_le_pow₀ hell)
    calc
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 := Nat.add_le_add_right ha _
      _ ≤ 34 * inputSmallLog N * inputSmallLog N ^ 40 + 2 * inputSmallLog N ^ 41 :=
        Nat.add_le_add_left hb _
      _ = _ := by ring
  calc
    _ ≤ (36 * inputSmallLog N ^ 41) ^ 2 := Nat.pow_le_pow_left hinner 2
    _ = _ := by ring

theorem computed_refinement_window (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N)
    (A w : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ)) :
    (dyadicQueryWindow N w (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length ≤
      computedSeedInitialExponent N + 8 := by
  have hh := inputSmallLog_bounds N hN
  have hf : smallLogExponent N ≤ inputSmallLog N := (smallLogExponent N).lt_two_pow_self.le
  have he0 : smallLogExponent N ≤ computedSeedInitialExponent N := by
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent (inputSmallLog N) + 4 by omega)
    unfold computedSeedInitialExponent
    nlinarith only [hh.2, hf, hfour]
  apply refinement_query_window_length N (inputSmallLog N) (computedSeedInitialExponent N) A w (by omega)
  · simpa only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he0
  · exact hA.trans_eq (computedSeed_initial_factor N).symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

theorem computed_window_le_height_cube (N : ℕ) (hN : 0 < N)
    (hell : 8 ≤ inputSmallLog N) (hH : 2 ≤ inputHeight N) :
    computedSeedInitialExponent N + 8 ≤ inputHeight N ^ 3 := by
  calc
    _ ≤ 2 * inputSmallLog N ^ 2 := computed_window_exponent_bound N hN hell
    _ ≤ inputHeight N * inputHeight N ^ 2 :=
      Nat.mul_le_mul hH (Nat.pow_le_pow_left (computed_smallLog_le_height N) 2)
    _ = _ := by ring

theorem computed_cell_budget_le_height_pow (N : ℕ) (hH : 64 ≤ inputHeight N) :
    ((32 * inputSmallLog N + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 ≤
      inputHeight N ^ 84 := by
  have hconstant : 1296 ≤ inputHeight N ^ 2 :=
    (by norm_num : 1296 ≤ (64 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hH 2)
  calc
    _ ≤ 1296 * inputSmallLog N ^ 82 :=
      computed_local_cell_budget N Nat.one_le_two_pow
    _ ≤ inputHeight N ^ 2 * inputHeight N ^ 82 :=
      Nat.mul_le_mul hconstant (Nat.pow_le_pow_left (computed_smallLog_le_height N) 82)
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedQueryAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-linear bounds for the executed request tree. These count
requests and depth-weighted source widths, independently of accuracy events.
Local arithmetic and random-source costs are separate obligations. -/

namespace EditApproximation

open Filter
open scoped Topology

namespace DependencyExpansion

theorem nodeCount_le_depthWeightedCount (weight : ℕ → ℕ)
    (hweight : ∀ d, 1 ≤ weight d) (tree : DependencyExpansion) :
    tree.nodeCount ≤ tree.depthWeightedCount weight := by
  induction tree with
  | node d k m n same earlier ihs ihe =>
    exact Nat.add_le_add (Nat.add_le_add (hweight d) (Finset.sum_le_sum fun i _ => ihs i))
      (Finset.sum_le_sum fun i _ => ihe i)

theorem nodeCount_le_widthWork (M n : ℕ) (tree : DependencyExpansion) :
    tree.nodeCount ≤ tree.widthWork M n :=
  nodeCount_le_depthWeightedCount _ (fun _ => by omega) tree

end DependencyExpansion

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restrict only the recursive table keys of a mixed source/table query.
The source reads remain explicit. This preserves the finite cache domain
without materializing any counterfactual table. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ) (supported : κ → Prop)







 theorem restrictBody_cost
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).cost
        (Sum.elim sourceValue (fun key => tableValue key.val.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) =
      (tableBody parent.val).cost (Sum.elim sourceValue (fun key => tableValue key.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_cost]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  have hweight :
      (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceWeight (fun key => tableWeight key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle, hweight]
  exact FiniteQuery.restrict_cost _ _ _ _ hkeys

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalOnlineSourceQuery
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online ranges are computed from already gathered band data. The
following query reads only the scale/center pairs for the current entry,
then evaluates the existing local step with the returned integers. -/

namespace EditApproximation



section Query

variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (draw : CellGroupDraws M F Q) (q : TargetInterval target.length)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)



theorem localOnlineSourceStepQuery_cost (oracle : ι → ℚ) (weight : ι → ℕ) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).cost oracle weight =
    let keys := localOnlineSourceKeys N P F a parentInitial q
    let reader := fun key => readInteger key
      (keyedOnlineSourceRange source target parent P exponent H tau child key)
    (keys.map fun key => (reader key).cost oracle weight).sum +
      (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw
        (fun b r => ⌊finiteAnswerTable keys (keys.map fun key => (reader key).value oracle) (b, r)⌋₊)
        q readEarlier readCurrent).cost oracle weight := by
  unfold localOnlineSourceStepQuery
  rw [FiniteQuery.cost_collect]

end Query

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGroupSourceQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Whole-cell group samples are exposed through scalar source reads.
Every needed scale/sample coordinate is enumerated once per group; unused
groups are absent from this query. -/

namespace EditApproximation





theorem groupScalarKeys_length_le (M F Q labels : ℕ) (groups : List (ℕ × (ℕ × ℕ)))
    (hlabels : ∀ key ∈ groups, (groupDyadicScales M key.1 F).length ≤ labels) :
    (groupScalarKeys M F Q groups).length ≤ groups.length * labels * M := by
  have hgroup (key : ℕ × (ℕ × ℕ)) (hk : key ∈ groups) :
      ((List.finRange (groupDyadicScales M key.1 F).length).flatMap fun scale =>
        (List.finRange (groupSampleCount M Q key.1 (groupDyadicScaleAt M key.1 F scale))).map
          fun sample => (⟨key, scale, sample⟩ : GroupScalarKey M F Q)).length ≤ labels * M := by
    apply le_trans (list_flatMap_length_le _ _ M ?_) ?_
    · intro scale _
      simp only [List.length_map, List.length_finRange]
      exact min_le_left _ _
    · simpa only [List.length_finRange] using Nat.mul_le_mul_right M (hlabels key hk)
  calc
    _ ≤ groups.length * (labels * M) := list_flatMap_length_le _ _ _ hgroup
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomBoundedCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)

 theorem physicalRandomBoundedQuery_cost (sourceWeight : σ → ℕ)
    (tableWeight : PhysicalTableRequest M J target.length → ℕ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceValue (fun child => tableValue child.val.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).cost
      (Sum.elim sourceValue (fun child => tableValue child.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_cost _ _ _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (sourceWeight : σ → ℕ) (coarse : ℕ) (weight : PhysicalTableRequest M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_refinement_cost
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (readGroup request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).cost (Sum.elim sourceAnswer (fun child => answer child.val))
        (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hshort⟩, FiniteQuery.mapKeys_cost]
  congr 1 <;> (funext key; cases key <;> rfl)

 theorem chargedRandomGlobalQuery_refinement_cost
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim sourceWeight (fun child => chargedTableWeight coarse weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1))) parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr hindex), ite_eq_left hbelow, ite_eq_right hshort, FiniteQuery.mapKeys_cost]
  have hcost := physicalRandomBoundedQuery_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
    sourceWeight weight parent
  have heq : (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
      (Sum.elim sourceAnswer (fun child => answer child.val.val))
      (Sum.elim sourceWeight (fun child => weight child.val.val)) = _ := hcost
  calc
    _ = (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
        (Sum.elim sourceAnswer (fun child => answer child.val.val))
        (Sum.elim sourceWeight (fun child => weight child.val.val)) := by
      congr 1 <;> (funext key; cases key <;> rfl)
    _ = _ := heq.trans (physicalRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
      sourceWeight weight parent.val hindex hbelow hshort)

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceErasure
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing already fixed source answers is a proof operation on a
query. It preserves the table trace and separates source/table charges;
the implementation continues to cache and sample explicit source keys. -/

namespace EditApproximation.FiniteQuery

variable {σ κ : Type*}

 theorem eraseSources_cost (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (tableWeight : κ → ℕ) (query : FiniteQuery (Sum σ κ)) :
    (eraseSources sourceAnswer query).cost tableAnswer tableWeight =
      query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim (fun _ => 0) tableWeight) := by
  induction query with
  | done value => rfl
  | read key next ih =>
    cases key with
    | inl source => simpa only [eraseSources, cost, Sum.elim_inl, Nat.zero_add] using ih (sourceAnswer source)
    | inr table => exact congrArg (tableWeight table + ·) (ih (tableAnswer table))

 theorem cost_add_weights {ι : Type*} (answer : ι → ℚ) (left right : ι → ℕ)
    (query : FiniteQuery ι) :
    query.cost answer (fun key => left key + right key) =
      query.cost answer left + query.cost answer right := by
  induction query with
  | done value => rfl
  | read key next ih => simp only [cost, ih]; omega

 theorem cost_mul_weight {ι : Type*} (answer : ι → ℚ) (weight : ι → ℕ)
    (multiplier : ℕ) (query : FiniteQuery ι) :
    query.cost answer (fun key => multiplier * weight key) =
      multiplier * query.cost answer weight := by
  induction query with
  | done value => simp only [cost, Nat.mul_zero]
  | read key next ih => simp only [cost, ih, Nat.mul_add]

 theorem cost_source_table (sourceAnswer : σ → ℚ) (tableAnswer : κ → ℚ)
    (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ) (query : FiniteQuery (Sum σ κ)) :
    query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim sourceWeight tableWeight) =
      query.cost (Sum.elim sourceAnswer tableAnswer) (Sum.elim sourceWeight (fun _ => 0)) +
      (eraseSources sourceAnswer query).cost tableAnswer tableWeight := by
  rw [eraseSources_cost, ← cost_add_weights]
  congr 1
  funext key
  cases key <;> simp

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

include hbody in
 theorem uncachedCalls_le_source_factor (sourceBudget : ℕ)
    (hsource : ∀ key, (tableBody key).cost
      (Sum.elim sourceValue (fun next => tableValue next.val)) (Sum.elim (fun _ => 1) (fun _ => 0)) ≤
        sourceBudget) (key : κ) :
    rankedUncachedCalls (rank tableRank) (body tableRank tableBody sourceValue) (.inr key) ≤
      (sourceBudget + 1) *
        rankedUncachedCalls tableRank (projectedBody tableRank tableBody sourceValue) key := by
  let mixed := body tableRank tableBody sourceValue
  let projected := projectedBody tableRank tableBody sourceValue
  let W := rankedUncachedCalls tableRank projected
  have hvalue (next : Sum σ κ) :
      rankedProgramValue (rank tableRank) mixed next = value sourceValue tableValue next :=
    program_value tableRank tableBody sourceValue tableValue hbody next
  have hpvalue (next : κ) : rankedProgramValue tableRank projected next = tableValue next :=
    projectedProgram_value tableRank tableBody sourceValue tableValue hbody next
  have hW (parent : κ) : W parent = (projected parent).cost
      (fun next => tableValue next.val) (fun next => W next.val) + 1 := by
    dsimp only [W]
    rw [rankedUncachedCalls]
    simp only [hpvalue]
  have hall : ∀ level parent, tableRank parent = level →
      rankedUncachedCalls (rank tableRank) mixed (.inr parent) ≤ (sourceBudget + 1) * W parent := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro parent hlevel
      have horacle :
          (fun next => rankedProgramValue (rank tableRank) mixed next.val) ∘ child tableRank parent =
          Sum.elim sourceValue (fun next => tableValue next.val) := by
        funext next
        rw [Function.comp_apply, hvalue]
        cases next <;> rfl
      have hcost := FiniteQuery.cost_mono_weights
        (Sum.elim sourceValue (fun next => tableValue next.val)) (tableBody parent)
        (fun next => rankedUncachedCalls (rank tableRank) mixed (child tableRank parent next).val)
        (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) (by
          intro next
          cases next with
          | inl source =>
            change rankedUncachedCalls (rank tableRank) mixed (.inl source) ≤ 1
            rw [rankedUncachedCalls]
            exact le_rfl
          | inr next =>
            exact ih (tableRank next.val) (hlevel ▸ next.property) next.val rfl)
      have hsplit : (tableBody parent).cost
          (Sum.elim sourceValue (fun next => tableValue next.val))
          (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) =
          (tableBody parent).cost (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun _ => 0)) +
          (sourceBudget + 1) * (projected parent).cost
            (fun next => tableValue next.val) (fun next => W next.val) := by
        rw [FiniteQuery.cost_source_table, FiniteQuery.cost_mul_weight]
        rfl
      change rankedUncachedCalls (rank tableRank) (body tableRank tableBody sourceValue) (.inr parent) ≤ _
      rw [rankedUncachedCalls]
      change (FiniteQuery.mapKeys (child tableRank parent) (tableBody parent)).cost
        (fun next => rankedProgramValue (rank tableRank) mixed next.val)
        (fun next => rankedUncachedCalls (rank tableRank) mixed next.val) + 1 ≤ _
      rw [FiniteQuery.mapKeys_cost, horacle]
      calc
        _ ≤ (tableBody parent).cost
            (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun next => (sourceBudget + 1) * W next.val)) + 1 :=
          Nat.add_le_add_right hcost 1
        _ = (tableBody parent).cost (Sum.elim sourceValue (fun next => tableValue next.val))
            (Sum.elim (fun _ => 1) (fun _ => 0)) +
            (sourceBudget + 1) * (projected parent).cost
              (fun next => tableValue next.val) (fun next => W next.val) + 1 := by rw [hsplit]
        _ ≤ sourceBudget + (sourceBudget + 1) * (projected parent).cost
              (fun next => tableValue next.val) (fun next => W next.val) + 1 := by
          exact Nat.add_le_add_right (Nat.add_le_add_right (hsource parent) _) _
        _ = (sourceBudget + 1) * W parent := by rw [hW]; ring
  exact hall (tableRank key) key rfl

include hbody in
 theorem memo_requests_le_source_factor (sourceBudget : ℕ)
    (hsource : ∀ key, (tableBody key).cost
      (Sum.elim sourceValue (fun next => tableValue next.val)) (Sum.elim (fun _ => 1) (fun _ => 0)) ≤
        sourceBudget)
    (bits : ℕ) (encode : Sum σ κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedMemoEvaluate (rank tableRank) (body tableRank tableBody sourceValue)
      bits encode (.inr key) .empty).requests ≤
      (sourceBudget + 1) *
        rankedUncachedCalls tableRank (projectedBody tableRank tableBody sourceValue) key :=
  (rankedMemoEvaluate_requests_le _ _ bits encode hinjective hbounded (.inr key) .empty
    (memoSound_empty _ _ _)).trans
      (uncachedCalls_le_source_factor tableRank tableBody sourceValue tableValue hbody
        sourceBudget hsource key)

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalSourceReadCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source-read overhead of a local refinement step. The table
reads are charged separately by the existing current/earlier budgets. -/

namespace EditApproximation

section Cost

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (parentInitial : TargetInterval target.length → ℚ)
  (child initial : Fin M → TargetInterval target.length → ℚ)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → weight key = 0)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → weight key = 0)

include hearlier hcurrent

omit [NeZero M] in
 theorem localOnlineSourceStepQuery_source_cost_le (draw : CellGroupDraws M F Q)
    (bound : ℕ) (hread : ∀ key range, (readInteger key range).cost oracle weight ≤ bound) :
    (localOnlineSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial draw q readInteger readEarlier readCurrent).cost oracle weight ≤
      (localOnlineSourceKeys N P F a parentInitial q).length * bound := by
  rw [localOnlineSourceStepQuery_cost]
  dsimp only
  have hzero (integer : ℕ → TargetInterval target.length → ℕ) :
      (localRefinementStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
        parentInitial child initial draw integer q readEarlier readCurrent).cost oracle weight = 0 := by
    apply FiniteQuery.cost_eq_zero_of_keys
    exact localRefinementStepQuery_keys_all source target parent N P F exponent H Q
      tau a eta kappa delta t parentInitial child initial draw integer q readEarlier readCurrent
      oracle (fun key => weight key = 0) hearlier hcurrent
  rw [hzero, Nat.add_zero]
  apply list_map_sum_le_constant
  intro key
  exact hread key _

 theorem localRandomSourceStepQuery_source_cost_le (groupBound onlineBound : ℕ)
    (hgroup : ∀ key, (readGroup key).cost oracle weight ≤ groupBound)
    (honline : ∀ key range, (readInteger key range).cost oracle weight ≤ onlineBound) :
    (localRandomSourceStepQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readGroup readInteger readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q)).length * groupBound +
        (localOnlineSourceKeys N P F a parentInitial q).length * onlineBound := by
  unfold localRandomSourceStepQuery
  rw [FiniteQuery.cost_collect]
  exact Nat.add_le_add
    (list_map_sum_le_constant _ _ _ hgroup)
    (localOnlineSourceStepQuery_source_cost_le source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial child initial q readInteger readEarlier readCurrent oracle weight hearlier hcurrent _
      onlineBound honline)

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalRandomSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source charges survive the two adaptive data-gathering stages unchanged.
All table reads have weight zero here; their dependency cost is accounted for
by the projected table program. No accuracy event is used. -/

namespace EditApproximation

section Cost

variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q : ℕ)
  (tau a eta kappa delta : ℚ) (t : ℕ)
  (readMass readInitial : Fin M × TargetInterval target.length → FiniteQuery ι)
  (readGroup : GroupScalarKey M F Q → FiniteQuery ι)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
  (readCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
  (oracle : ι → ℚ) (weight : ι → ℕ)
  (hmass : ∀ input, (readMass input).cost oracle weight = 0)
  (hinitial : ∀ input, (readInitial input).cost oracle weight = 0)
  (hearlier : ∀ input key, key ∈ (readEarlier input).keys oracle → weight key = 0)
  (hcurrent : ∀ input key, key ∈ (readCurrent input).keys oracle → weight key = 0)
  (groupBound onlineBound : ℕ)
  (hgroup : ∀ key, (readGroup key).cost oracle weight ≤ groupBound)
  (honline : ∀ key range, (readInteger key range).cost oracle weight ≤ onlineBound)

include hmass hinitial hearlier hcurrent hgroup honline

 theorem localRandomBandDataQuery_source_cost_le
    (parentInitial : TargetInterval target.length → ℚ) :
    (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a parentInitial q)).length * groupBound +
      (localOnlineSourceKeys N P F a parentInitial q).length * onlineBound := by
  unfold localRandomBandDataQuery
  rw [FiniteQuery.cost_collect, FiniteQuery.cost_collect]
  simp only [hmass, hinitial, List.map_const', List.sum_replicate, smul_eq_mul,
    Nat.mul_zero, Nat.zero_add]
  exact localRandomSourceStepQuery_source_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t parentInitial _ _ q readGroup readInteger readEarlier readCurrent
    oracle weight hearlier hcurrent groupBound onlineBound hgroup honline

 theorem localRandomDataQuery_source_cost_le
    (readParent : TargetInterval target.length → FiniteQuery ι)
    (hparent : ∀ r, (readParent r).cost oracle weight = 0) :
    let actualInitial := fun r => (readParent r).value oracle
    (localRandomDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
      readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a actualInitial q)).length * groupBound +
      (localOnlineSourceKeys N P F a actualInitial q).length * onlineBound := by
  dsimp only
  unfold localRandomDataQuery
  rw [FiniteQuery.cost_bind, hparent q, Nat.zero_add, FiniteQuery.cost_collect]
  simp only [hparent, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.zero_add]
  let keys := refinementInitialSupport N P F exponent a ((readParent q).value oracle) q
  let cached := finiteAnswerTable keys (keys.map fun r => (readParent r).value oracle)
  have hq : cached q = (readParent q).value oracle :=
    finiteAnswerTable_map keys _ q (refinementInitialSupport_query N P F exponent a _ q)
  have hb := localRandomBandDataQuery_source_cost_le source target parent N P F exponent H Q
    tau a eta kappa delta t readMass readInitial readGroup readInteger q readEarlier readCurrent
    oracle weight hmass hinitial hearlier hcurrent groupBound onlineBound hgroup honline cached
  change (localRandomBandDataQuery source target parent N P F exponent H Q tau a eta kappa delta t
    cached readMass readInitial readGroup readInteger q readEarlier readCurrent).cost oracle weight ≤ _
  apply hb.trans
  simp only [localGroupQueryKeys, localOnlineSourceKeys, hq]
  exact le_rfl

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomMemoWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Source reads and dictionary visits in the actual shared-cache evaluator
are bounded by the width of its projected table dependency expansion. -/

namespace EditApproximation

section Work

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "mixedProgram" => chargedRandomGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixedProgram sourceAnswer
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

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


 theorem chargedRandomMemoEvaluate_requests_le_widthWork
    (sourceBudget bits : ℕ)
    (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (hsource : ∀ key, (mixedProgram key).cost
      (Sum.elim sourceAnswer (fun next => values next.val))
      (Sum.elim (fun _ => 1) (fun _ => 0)) ≤ sourceBudget)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomMemoEvaluate source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode root).requests ≤
    (sourceBudget + 1) *
      (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork
          M source.length := by
  apply (SourceRanked.memo_requests_le_source_factor ChargedPhysicalRequest.rank mixedProgram
    sourceAnswer values hbody sourceBudget hsource bits encode hinjective hbounded root).trans
  apply Nat.mul_le_mul_left
  calc
    rankedUncachedCalls ChargedPhysicalRequest.rank program root =
        (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
          tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).nodeCount :=
      (queryDependencyExpansion_nodes depth index program
        (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
          tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root).symm
    _ ≤ _ := DependencyExpansion.nodeCount_le_widthWork _ _ _

end Work

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree source-read bounds for a refinement entry. These hold on
all stored initial values, including outcomes outside accuracy events. -/

namespace EditApproximation

 theorem computed_source_key_budget {n M : ℕ} (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hw : 0 ≤ initial q) :
    (groupScalarKeys M (inputSmallLog N) (inputSmallLog N ^ 80)
      (localGroupQueryKeys N (inputSmallLog N) (40 * smallLogExponent N)
        (refinementFactor A (inputSmallLog N)) initial q)).length +
      (localOnlineSourceKeys N P (inputSmallLog N)
        (refinementFactor A (inputSmallLog N)) initial q).length ≤ inputHeight N ^ 91 := by
  let H := inputHeight N
  let ell := inputSmallLog N
  have hF : ell ≤ H := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ ell).trans hF
  have hMbound : M ≤ H := by
    rw [hM]
    exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hW : (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length ≤ H ^ 3 :=
    (computed_refinement_window N hN (by omega) A (initial q) hA).trans
      (computed_window_le_height_cube N hN (by omega) (by omega))
  have hkeys : (localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) initial q).length ≤ H ^ 87 := by
    calc
      _ ≤ (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length *
          ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 :=
        localGroupQueryKeys_length N ell (40 * smallLogExponent N)
          (refinementFactor A ell) initial q (by omega) hw
      _ ≤ H ^ 3 * H ^ 84 := Nat.mul_le_mul hW (computed_cell_budget_le_height_pow N hH)
      _ = H ^ 87 := by rw [← pow_add]
  have hlabels : ∀ key ∈ localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) initial q, (groupDyadicScales M key.1 ell).length ≤ 2 * ell := by
    intro key hk
    have hb := localGroupQueryKeys_scale hk
    obtain ⟨eb, _, heq⟩ := List.mem_map.mp hb
    rw [hM, ← heq]
    exact computed_group_scale_count N eb hN (by omega)
  have hgroup : (groupScalarKeys M ell (ell ^ 80) (localGroupQueryKeys N ell
      (40 * smallLogExponent N) (refinementFactor A ell) initial q)).length ≤ H ^ 90 := by
    calc
      _ ≤ (localGroupQueryKeys N ell (40 * smallLogExponent N)
          (refinementFactor A ell) initial q).length * (2 * ell) * M :=
        groupScalarKeys_length_le M ell (ell ^ 80) (2 * ell) _ hlabels
      _ ≤ H ^ 87 * (H * H) * H := Nat.mul_le_mul
        (Nat.mul_le_mul hkeys (Nat.mul_le_mul (by omega) hF)) hMbound
      _ = H ^ 90 := by ring
  simp only [localOnlineSourceKeys, List.length_map]
  have hsmall : H ^ 3 ≤ H ^ 90 := pow_le_pow_right₀ (by omega) (by omega)
  calc
    _ ≤ H ^ 90 + H ^ 90 := Nat.add_le_add hgroup (hW.trans hsmall)
    _ = H ^ 90 * 2 := by omega
    _ ≤ H ^ 90 * H := Nat.mul_le_mul_left _ (by omega)
    _ = H ^ 91 := (pow_succ H 90).symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

namespace FiniteQuery

 theorem mapRight_source_cost {σ κ : Type*} (query : FiniteQuery κ)
    (source : σ → ℚ) (table : κ → ℚ) (weight : σ → ℕ) :
    (mapKeys Sum.inr query).cost (Sum.elim source table) (Sum.elim weight (fun _ => 0)) = 0 := by
  rw [mapKeys_cost]
  exact cost_zero table query

 theorem mapRight_source_keys {σ κ : Type*} (query : FiniteQuery κ)
    (source : σ → ℚ) (table : κ → ℚ) (weight : σ → ℕ) :
    ∀ key ∈ (mapKeys Sum.inr query).keys (Sum.elim source table),
      (Sum.elim weight (fun _ => 0)) key = 0 := by
  rw [mapKeys_keys]
  intro key hk
  obtain ⟨other, _, rfl⟩ := List.mem_map.mp hk
  rfl

end FiniteQuery

 theorem physicalRandomDataRequest_source_cost_le {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (sourceAnswer : σ → ℚ)
    (answer : PhysicalTableRequest M J target.length → ℚ) (weight : σ → ℕ)
    (groupBound onlineBound : ℕ)
    (hgroup : ∀ key, (readGroup key).cost sourceAnswer weight ≤ groupBound)
    (honline : ∀ key range, (readInteger key range).cost sourceAnswer weight ≤ onlineBound) :
    let initial := fun r => answer (PhysicalTableRequest.warmup pass copy node 0 r)
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
        (Sum.elim sourceAnswer (fun key => answer key.val)) (Sum.elim weight (fun _ => 0)) ≤
      (groupScalarKeys M F Q (localGroupQueryKeys N F exponent a initial q)).length * groupBound +
      (localOnlineSourceKeys N P F a initial q).length * onlineBound := by
  dsimp only
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_source_cost_le
  · intro input
    exact FiniteQuery.mapRight_source_cost _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_cost _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_keys _ _ _ _
  · intro input
    exact FiniteQuery.mapRight_source_keys _ _ _ _
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact hgroup key
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact honline key range
  · intro r
    exact FiniteQuery.mapRight_source_cost _ _ _ _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGlobalSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_physicalRandomGlobalQuery_source_cost {σ α : Type*} [DecidableEq α]
    {M J R : ℕ} [NeZero M] [NeZero R] (source target : List α)
    (N P H T S copies : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (tau eta kappa delta : ℚ) (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
      GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
    (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
      (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (initial : PhysicalEntry M J target.length → ℕ) (sourceAnswer : σ → ℚ)
    (answer : PhysicalTableRequest M J target.length → ℚ) (weight : σ → ℕ) (bound : ℕ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).cost sourceAnswer weight ≤ bound)
    (honline : ∀ pass copy node time key range,
      (readInteger pass copy node time key range).cost sourceAnswer weight ≤ bound)
    (hpositive : ∀ pass copy node q, 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q))
    (request : PhysicalTableRequest M J target.length) :
    (physicalRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S copies factor multiplier tau eta kappa delta readGroup readInteger
      initial request).cost (Sum.elim sourceAnswer (fun key => answer key.val))
        (Sum.elim weight (fun _ => 0)) ≤ inputHeight N ^ 91 * bound := by
  unfold physicalRandomGlobalQuery
  by_cases ha : T < request.index ∧ request.node.1.val < J ∧
      ¬ (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1
  · rw [dite_eq_left ha, FiniteQuery.mapKeys_cost]
    let node : PhysicalInternalNode M J := ⟨request.node, ha.2.1⟩
    let time : Fin R := Fin.ofNat R (request.index - T - 1)
    have hlocal := physicalRandomDataRequest_source_cost_le source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) tau
      (refinementFactor (factor request.pass) (inputSmallLog N)) eta kappa delta
      request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt ha.1)
      request.node ha.2.1 (readGroup request.pass request.copy node time)
      (readInteger request.pass request.copy node time) request.state sourceAnswer answer weight bound bound
      (hgroup request.pass request.copy node time) (honline request.pass request.copy node time)
    have hkeys := computed_source_key_budget N P hN hell hM (factor request.pass) (hA _)
      (fun r => answer (PhysicalTableRequest.warmup request.pass request.copy request.node 0 r))
      request.state (hpositive _ _ _ _)
    have hbound := hlocal.trans (show _ ≤ inputHeight N ^ 91 * bound by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right bound hkeys)
    convert hbound using 1
    all_goals try with_reducible_and_instances rfl
    congr 1 <;> (funext key; cases key <;> rfl)
  · rw [dite_eq_right ha]
    rw [FiniteQuery.mapRight_source_cost]
    exact Nat.zero_le _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedChargedRandomSourceCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (weight : σ → ℕ) (bound : ℕ)
  (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
  (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).cost sourceAnswer weight ≤ bound)
  (honline : ∀ pass copy node time key range,
    (readInteger pass copy node time key range).cost sourceAnswer weight ≤ bound)

local notation "tableValue" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

include hN hell hM hA hgroup honline in
 theorem computed_chargedRandomGlobalQuery_source_cost
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta group integer initial child.val))
      (Sum.elim weight (fun _ => 0)) ≤ inputHeight N ^ 91 * bound := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      rw [FiniteQuery.cost_zero]
      exact Nat.zero_le _
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          rw [FiniteQuery.cost_zero]
          exact Nat.zero_le _
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => tableValue r.val) := by
            funext key
            cases key <;> rfl
          have hz : (fun _ : ChargedPhysicalRequest M J target.length passes copies T S => 0) =
              chargedTableWeight 0 (fun _ => 0) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          have hcost := chargedRandomGlobalQuery_refinement_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger initial sourceAnswer tableValue weight 0 (fun _ => 0)
            parent (by omega) hb hs
          simp only [← hz] at hcost
          rw [hcost]
          rw [← physicalRandomGlobalQuery_refinement_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
            tau eta kappa delta readGroup readInteger initial sourceAnswer tableValue weight (fun _ => 0)
            parent.val (by omega) hb hs]
          apply computed_physicalRandomGlobalQuery_source_cost source target N P H T S copies
            hN hell hM factor multiplier tau eta kappa delta hA readGroup readInteger initial
            sourceAnswer tableValue weight bound hgroup honline
          intro pass copy node q
          rw [localRequestValue_initial]
          exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        rw [FiniteQuery.cost_zero]
        exact Nat.zero_le _

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarReadCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each physical group or online source reader requests at most one
scalar. The guards and dependent index transports do not create reads. -/

namespace EditApproximation

section Cost

variable (M J N n exponent F Q R B : ℕ) [NeZero M]
  (oracle : PhysicalScalarKey M J N n exponent F Q R B → ℚ)
  (weight : PhysicalScalarKey M J N n exponent F Q R B → ℕ)
  (bound : ℕ) (hweight : ∀ key, weight key ≤ bound)

omit [NeZero M] in
private theorem groupQuery_transport_cost (b c : ℕ) (h : b = c)
    (queries : PhysicalGroupQueries M J N n exponent F Q R B b)
    (hq : ∀ scale sample, (queries scale sample).cost oracle weight ≤ bound) :
    ∀ scale sample,
      ((Eq.mp (congrArg (PhysicalGroupQueries M J N n exponent F Q R B) h) queries) scale sample).cost
        oracle weight ≤ bound := by
  subst c
  exact hq

omit [NeZero M] in
include hweight in
 theorem physicalScalarGroupRead_cost_le (node : PhysicalInternalNode M J) (time : Fin R)
    (key : GroupScalarKey M F Q) :
    (physicalScalarGroupRead M J N n exponent F Q R B node time key).cost oracle weight ≤ bound := by
  rcases key with ⟨⟨b, cell⟩, scale, sample⟩
  unfold physicalScalarGroupRead physicalScalarGroupQueries
  dsimp only
  split_ifs with hb hc
  · let group : PhysicalLocalGroupKey M J N n exponent :=
      (node, physicalScaleIndex N b hb,
        ⟨cell.1, Nat.lt_succ_of_le hc.1⟩, ⟨cell.2, Nat.lt_succ_of_le hc.2⟩)
    exact groupQuery_transport_cost M J N n exponent F Q R B oracle weight bound
      ((dyadicScales N).get group.2.1) b (physicalScaleIndex_get N b hb)
      (physicalScalarGroupQueriesAt M J N n exponent F Q R B group time)
      (fun _ _ => by simpa only [physicalScalarGroupQueriesAt, FiniteQuery.cost, Nat.add_zero] using hweight _)
      scale sample
  · exact Nat.zero_le _
  · exact Nat.zero_le _

omit [NeZero M] in
include hweight in
 theorem physicalScalarOnlineRead_cost_le (node : PhysicalInternalNode M J) (time : Fin R)
    (key : ℕ × TargetInterval n) (range : ℕ) :
    (physicalScalarOnlineRead M J N n exponent F Q R B node time key range).cost oracle weight ≤ bound := by
  unfold physicalScalarOnlineRead
  split_ifs <;> simp only [FiniteQuery.cost, Nat.add_zero]
  · exact hweight _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

end Cost

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)
  (oracle : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℚ)
  (weight : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies → ℕ)
  (bound : ℕ) (hweight : ∀ key, weight key ≤ bound)

omit [NeZero M] in
include hweight in
 theorem physicalFamilyGroupRead_cost_le (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : GroupScalarKey M F Q) :
    (physicalFamilyGroupRead target N P F exponent H Q passes copies pass copy node time key).cost
      oracle weight ≤ bound := by
  rw [physicalFamilyGroupRead, FiniteQuery.mapKeys_cost]
  exact physicalScalarGroupRead_cost_le M J N target.length exponent F Q R (localOnlineMassBound M P H)
    _ _ bound (fun _ => hweight _) node time key

omit [NeZero M] in
include hweight in
 theorem physicalFamilyOnlineRead_cost_le (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (time : Fin R) (key : ℕ × TargetInterval target.length) (range : ℕ) :
    (physicalFamilyOnlineRead target N P F exponent H Q passes copies pass copy node time key range).cost
      oracle weight ≤ bound := by
  rw [physicalFamilyOnlineRead, FiniteQuery.mapKeys_cost]
  exact physicalScalarOnlineRead_cost_le M J N target.length exponent F Q R (localOnlineMassBound M P H)
    _ _ bound (fun _ => hweight _) node time key range

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual scalar family supplies the body-value and source-read
bounds required by the mixed source/table dependency analysis. -/

namespace EditApproximation

section ComputedCost

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) passes copies)

 theorem computed_physicalFamilyProgram_source_cost
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyProgram source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta initial request).cost
      (Sum.elim (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) passes copies draw)
        (fun child => physicalFamilyRequestValue source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta initial hP draw child.val))
      (Sum.elim (fun _ => 1) (fun _ => 0)) ≤ inputHeight N ^ 91 := by
  have hg := physicalFamilyGroupRead_cost_le target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies
    (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) passes copies draw) (fun _ => 1) 1 (fun _ => le_rfl)
  have ho := physicalFamilyOnlineRead_cost_le target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies
    (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) passes copies draw) (fun _ => 1) 1 (fun _ => le_rfl)
  simpa only [physicalFamilyProgram, physicalFamilyRequestValue, Nat.mul_one] using
    (computed_chargedRandomGlobalQuery_source_cost source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta
      (physicalFamilyGroup target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) passes copies draw)
      (physicalFamilyInteger source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta hP draw initial)
      initial _ _ _ (fun _ => 1) 1 hN hell hM hA hg ho request)

end ComputedCost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Work

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hPpos : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "integer" => physicalFamilyInteger source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta hPpos draw initial
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw
local notation "bodyValue" => physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta initial hPpos draw

 theorem physicalFamilyMemo_requests_le_width_oai
    (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
    (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (bits : ℕ) (encode : Sum
      (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
        target N P ell exponent H (ell ^ 80) passes copies)
      (ChargedPhysicalRequest M J target.length (passes + 1) copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
      copies factor multiplier tau eta kappa delta readGroup readInteger initial answer bits encode root).requests ≤
    (inputHeight N ^ 91 + 1) *
      (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta initial hPpos draw root).widthWork M source.length :=
  chargedRandomMemoEvaluate_requests_le_widthWork source target N P H T S (passes + 1)
    copies factor multiplier tau eta kappa delta group integer initial readGroup readInteger answer
    bodyValue (inputHeight N ^ 91) bits encode hinjective hbounded
    (computed_physicalFamilyProgram_source_cost source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw hN hell hM hAmax) root

end Work

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.physicalFamilyMemo_requests_le_width_oai.{u_1} := @OAI.EditApproximation.physicalFamilyMemo_requests_le_width_oai.{u_1}
