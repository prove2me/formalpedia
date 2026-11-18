-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryTemporaryCells_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:24:00.071941+00:00
-- url     : https://prove2.me/submissions/01fd01e2-9e02-4efc-bf8f-34b30e410559

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedFamilyKernelWork_polynomial
import Theorems.Thm_OAI_EditApproximation_computedFamilyMemoCode_fits
import Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_near_linear
import Theorems.Thm_OAI_EditApproximation_computedQueryLocalWork_cap
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoNormalized_correct
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoResult_decode

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

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
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoHeap
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A cumulative allocation counter for the actual memo execution. It keeps
all local allocations until the entire run finishes, so it also bounds peak
space. A read retains three continuation/result cells. Each memo call reserves
its address workspace, key bits, traversal frames and the possible new trie
path; existing values and input words are shared by reference. -/

namespace EditApproximation
namespace BitQuery.Heap

theorem runCells_le {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ) (D : ℕ)
    (hchild : ∀ key memory, childCells key memory + 3 ≤
      3 * (ask key memory).localWork + D * (ask key memory).requests)
    {program : BitQuery ι BinaryFraction} (heap : Heap program)
    (memory : BinaryMemo BinaryFraction) :
    heap.runCells ask childCells memory ≤
      3 * (BitQuery.runMemo ask program memory).localWork +
        D * (BitQuery.runMemo ask program memory).requests := by
  induction heap generalizing memory with
  | done value => simp only [runCells, BitQuery.runMemo, Nat.mul_zero, Nat.add_zero, le_refl]
  | charge cells bound next ih =>
    have h := ih memory
    simp only [runCells, BitQuery.runMemo]
    omega
  | read key next continuation ih =>
    have hc := hchild key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    simp only [runCells, BitQuery.runMemo, Nat.mul_add]
    omega

end BitQuery.Heap

theorem rankedBitMemoCells_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, BitQuery.Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (A : ℕ)
    (haddress : ∀ key, addressCells key ≤ A) (key : κ) (memory : BinaryMemo BinaryFraction) :
    rankedBitMemoCells rank program heap bits encode addressCells key memory + 3 ≤
      3 * (rankedBitMemoEvaluate rank program bits encode key memory).localWork +
        (memoRequestCells bits A + 3) * (rankedBitMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedBitMemoCells rank program heap bits encode addressCells key memory + 3 ≤
        3 * (rankedBitMemoEvaluate rank program bits encode key memory).localWork +
          (memoRequestCells bits A + 3) * (rankedBitMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      have ha : memoRequestCells bits (addressCells key) ≤ memoRequestCells bits A := by
        unfold memoRequestCells
        exact Nat.add_le_add_right (Nat.add_le_add_right (haddress key) _) _
      rw [rankedBitMemoCells, rankedBitMemoEvaluate]
      dsimp only
      cases hf : (memory.lookupCosted (binaryMemoKey bits (encode key))).1 with
      | some value =>
        simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_add]
        omega
      | none =>
        have hc (child : {child : κ // rank child < rank key}) previous :=
          ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := BitQuery.Heap.runCells_le
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedBitMemoCells rank program heap bits encode addressCells child.val previous)
          (memoRequestCells bits A + 3) hc (heap key) memory
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoSound
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Memo hits return the same concrete binary word as the deterministic
rank-decreasing program. This stronger invariant also fixes the local
arithmetic work on repeated reads, independently of cache history. -/

namespace EditApproximation


theorem bitMemoSound_empty {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (expected : κ → BinaryFraction) : bitMemoSound bits encode expected .empty := by
  intro key value hvalue
  rw [BinaryMemo.lookup_empty] at hvalue
  cases hvalue

namespace BitQuery

theorem runMemo_sound {ι κ : Type*} (answer : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (hask : ∀ key memory, invariant memory →
      (ask key memory).value = answer key ∧ invariant (ask key memory).memory)
    (program : BitQuery ι BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : invariant memory) :
    (runMemo ask program memory).value = program.value answer ∧
      invariant (runMemo ask program memory).memory := by
  induction program generalizing memory with
  | done result => exact ⟨rfl, hmemory⟩
  | charge steps next ih => exact ih memory hmemory
  | read key next ih =>
    have hf := hask key memory hmemory
    have hr := ih (ask key memory).value (ask key memory).memory hf.2
    exact ⟨by simpa only [runMemo, value, hf.1] using hr.1, hr.2⟩

end BitQuery



theorem bitMemoSound_insert {κ : Type*} (bits : ℕ) (encode : κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (expected : κ → BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode expected memory) (key : κ) :
    bitMemoSound bits encode expected
      (memory.insert (binaryMemoKey bits (encode key)) (expected key)) := by
  intro other value hvalue
  rw [binaryMemo_lookup_insert _ bits (encode key) (encode other) (hbounded key) (hbounded other)] at hvalue
  split_ifs at hvalue with heq
  · have hk := hinjective heq
    subst other
    exact Option.some.inj hvalue.symm
  · exact hmemory other value hvalue

theorem rankedBitMemoEvaluate_sound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).value = rankedBitProgramValue rank program key ∧
      bitMemoSound bits encode (rankedBitProgramValue rank program)
        (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).value = rankedBitProgramValue rank program key ∧
        bitMemoSound bits encode (rankedBitProgramValue rank program)
          (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · rename_i result hresult
        exact ⟨hmem key result hresult, hmem⟩
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hp
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp
        have hr := BitQuery.runMemo_sound
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory hmem
        have hv : (BitQuery.runMemo
            (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedBitProgramValue rank program key := by
          rw [rankedBitProgramValue]
          exact hr.1
        simp only [BinaryMemo.insertCosted_spec]
        refine ⟨hv, ?_⟩
        rw [hv]
        exact bitMemoSound_insert bits encode hinjective hbounded _ _ hr.2 key
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoOn
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reachable-oracle simulation retains the exact memo trace while allowing
local output normalization justified by the actual grid invariant. -/

namespace EditApproximation.BitQuery

theorem runMemo_decode_on {ι κ : Type*} (oracle : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (expectedAsk : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (hask : ∀ key memory, invariant memory →
      (ask key memory).value = oracle key ∧ invariant (ask key memory).memory ∧
        (ask key memory).decode = expectedAsk key (memory.mapValues BinaryFraction.value))
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (memory : BinaryMemo BinaryFraction) (hmemory : invariant memory) :
    (runMemo ask program memory).decode =
      FiniteQuery.run expectedAsk expected (memory.mapValues BinaryFraction.value) ∧
        invariant (runMemo ask program memory).memory := by
  induction h generalizing memory with
  | done h =>
    exact ⟨by simp only [runMemo, FiniteQuery.run, BitRecursiveMemoResult.decode, h], hmemory⟩
  | charge steps h ih => exact ih memory hmemory
  | read key next expected h ih =>
    have hf := hask key memory hmemory
    have hvalue := congrArg RecursiveMemoResult.value hf.2.2
    have hmem := congrArg RecursiveMemoResult.memory hf.2.2
    have hfresh := congrArg RecursiveMemoResult.freshKeys hf.2.2
    have hdict := congrArg RecursiveMemoResult.dictionaryVisits hf.2.2
    have hrequests := congrArg RecursiveMemoResult.requests hf.2.2
    have hr := ih (ask key memory).memory hf.2.1
    rw [← hf.1] at hr
    refine ⟨?_, hr.2⟩
    unfold runMemo FiniteQuery.run
    dsimp only
    unfold BitRecursiveMemoResult.decode at hvalue hmem hfresh hdict hrequests hr ⊢
    simp only at hvalue hmem hfresh hdict hrequests
    rw [hvalue, hmem] at hr
    rw [← hr.1]
    simp only [hfresh, hdict, hrequests]

end EditApproximation.BitQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The binary memo's local-work counter is exactly the intrinsic Boolean
work summed over actual cache misses. Recursive calls and cache hits do
not trigger a second charge for a previously computed local body. -/

namespace EditApproximation
namespace BitQuery

theorem runMemo_work_eq {ι κ : Type*} (answer : ι → BinaryFraction)
    (invariant : BinaryMemo BinaryFraction → Prop)
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ) (weight : κ → ℕ)
    (hsound : ∀ key memory, invariant memory →
      (ask key memory).value = answer key ∧ invariant (ask key memory).memory)
    (hwork : ∀ key memory, invariant memory →
      (ask key memory).localWork = ((ask key memory).freshKeys.map weight).sum)
    (program : BitQuery ι BinaryFraction) (memory : BinaryMemo BinaryFraction)
    (hmemory : invariant memory) :
    (runMemo ask program memory).localWork = program.work answer (fun _ => 0) +
      ((runMemo ask program memory).freshKeys.map weight).sum := by
  induction program generalizing memory with
  | done result => rfl
  | charge steps next ih =>
    simp only [runMemo, work]
    rw [ih memory hmemory]
    omega
  | read key next ih =>
    have hf := hsound key memory hmemory
    have hw := hwork key memory hmemory
    have hr := ih (ask key memory).value (ask key memory).memory hf.2
    simp only [runMemo, work, List.map_append, List.sum_append, Nat.zero_add]
    rw [hw, hr, hf.1]
    omega

end BitQuery



theorem rankedBitMemoEvaluate_localWork {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
      ((rankedBitMemoEvaluate rank program bits encode key memory).freshKeys.map
        (rankedBitLocalWork rank program)).sum := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
        ((rankedBitMemoEvaluate rank program bits encode key memory).freshKeys.map
          (rankedBitLocalWork rank program)).sum := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate]
      split
      · rfl
      · have hs : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory := by
          intro child previous hp
          exact rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
        have hw : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).localWork =
              ((rankedBitMemoEvaluate rank program bits encode child.val previous).freshKeys.map
                (rankedBitLocalWork rank program)).sum := by
          intro child previous hp
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp
        have hr := BitQuery.runMemo_work_eq
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (rankedBitLocalWork rank program) hs hw (program key) memory hmem
        simpa only [List.map_cons, List.sum_cons, rankedBitLocalWork] using hr
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Computable base-M node labels and mixed-radix table-entry keys.
Equal source intervals at different physical nodes keep distinct keys. -/

namespace EditApproximation



theorem treeLayerCode_bound (M d : ℕ) (path : TreeLayer M d) :
    treeLayerCode M d path < M ^ d := by
  induction d with
  | zero => exact Nat.zero_lt_one
  | succ d ih =>
    have hp := ih path.1
    have hi := path.2.isLt
    change path.2.val + M * treeLayerCode M d path.1 < M ^ (d + 1)
    rw [pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hp)]

theorem treeLayerCode_injective (M d : ℕ) : Function.Injective (treeLayerCode M d) := by
  induction d with
  | zero => intro first second _; cases first; cases second; rfl
  | succ d ih =>
    rintro ⟨first, i⟩ ⟨second, j⟩ heq
    obtain ⟨hlabel, hpath⟩ := mixedRadix_injective i.isLt j.isLt heq
    exact Prod.ext (ih hpath) (Fin.ext hlabel)



theorem physicalNode_layer_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    treeLayerCode M node.1.val node.2 < M ^ J :=
  (treeLayerCode_bound M node.1.val node.2).trans_le
    (pow_le_pow_right₀ hM (Nat.le_of_lt_succ node.1.isLt))

theorem physicalNodeCode_injective {M J : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalNodeCode M J) := by
  rintro ⟨depth, path⟩ ⟨depth', path'⟩ heq
  obtain ⟨hp, hd⟩ := mixedRadix_injective
    (physicalNode_layer_bound hM ⟨depth, path⟩)
    (physicalNode_layer_bound hM ⟨depth', path'⟩) heq
  have hdepth : depth = depth' := Fin.ext hd
  subst depth'
  have hpath := treeLayerCode_injective M depth.val hp
  change path = path' at hpath
  subst path'
  rfl

theorem physicalNodeCode_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    physicalNodeCode node < M ^ J * (J + 1) := by
  have hpath := physicalNode_layer_bound hM node
  have hdepth := node.1.isLt
  unfold physicalNodeCode
  nlinarith only [hpath, Nat.mul_le_mul_left (M ^ J) (Nat.succ_le_of_lt hdepth)]



theorem physicalEntryCode_injective {M J n : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalEntryCode M J n) := by
  rintro ⟨node, q⟩ ⟨node', q'⟩ heq
  obtain ⟨hq, hn⟩ := mixedRadix_injective
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q))
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q')) heq
  have hstate := childInputCode_injective 1 n hq
  have hqeq : q = q' := congrArg (fun pair : Fin 1 × TargetInterval n => pair.2) hstate
  exact Prod.ext (physicalNodeCode_injective hM hn) hqeq

theorem physicalEntryCode_bound {M J n : ℕ} (hM : 1 ≤ M) (state : PhysicalEntry M J n) :
    physicalEntryCode state < (n + 1) ^ 2 * (M ^ J * (J + 1)) := by
  have hstate : childInputCode ((0 : Fin 1), state.2) < (n + 1) ^ 2 := by
    simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), state.2)
  have hnode := physicalNodeCode_bound hM state.1
  unfold physicalEntryCode
  nlinarith only [hstate, Nat.mul_le_mul_left ((n + 1) ^ 2) (Nat.succ_le_of_lt hnode)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





theorem code_injective {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ) :
    Function.Injective (fun request : {r : PhysicalTableRequest M J n // Bounded passes copies T S r} =>
      code copies T S request.val) := by
  intro first second heq
  obtain ⟨hindex, hrest⟩ := mixedRadix_injective
    (Nat.lt_succ_of_le first.2.2.2) (Nat.lt_succ_of_le second.2.2.2) heq
  obtain ⟨hcopy, hrest⟩ := mixedRadix_injective first.2.2.1 second.2.2.1 hrest
  obtain ⟨hentry, hpass⟩ := mixedRadix_injective
    (physicalEntryCode_bound hM (first.1.node, first.1.state))
    (physicalEntryCode_bound hM (second.1.node, second.1.state)) hrest
  have he := physicalEntryCode_injective hM hentry
  have hnode := congrArg Prod.fst he
  have hstate := congrArg Prod.snd he
  apply Subtype.ext
  cases first with
  | mk first hf =>
    cases second with
    | mk second hs =>
      cases first
      cases second
      simp only at hpass hcopy hnode hindex hstate
      cases hpass
      cases hcopy
      cases hnode
      cases hindex
      cases hstate
      rfl

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem code_injective {M J ny passes copies T S : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@code M J ny passes copies T S) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hentry : physicalEntryCode left = physicalEntryCode right := by
        change 2 * physicalEntryCode left = 2 * physicalEntryCode right at heq
        omega
      exact congrArg Sum.inl (physicalEntryCode_injective hM hentry)
    | inr right =>
      change 2 * physicalEntryCode left = 2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * PhysicalTableRequest.code copies T S left.val + 1 = 2 * physicalEntryCode right at heq
      omega
    | inr right =>
      have htable : PhysicalTableRequest.code copies T S left.val =
          PhysicalTableRequest.code copies T S right.val := by
        change 2 * PhysicalTableRequest.code copies T S left.val + 1 =
          2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
        omega
      exact congrArg Sum.inr (PhysicalTableRequest.code_injective hM passes copies T S htable)

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-seed numerical dimension and source-range bounds after substituting
the computed grid size. These bounds do not use an accuracy event. -/

namespace EditApproximation

theorem wide_coordinate_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    M * (40 * P + 2) ^ 2 ≤ H ^ (2 * p + 45) := by
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hconstant : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hconstant hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H 2 (p + 20)).symm
      _ = _ := by congr 1; omega
  calc
    _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul hM (Nat.pow_le_pow_left hbox 2)
    _ = H * H ^ ((p + 22) * 2) := by rw [pow_mul]
    _ = H ^ ((p + 22) * 2 + 1) := (pow_succ' H _).symm
    _ = _ := by congr 1; omega

theorem optimizer_parameter_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    H + M * (40 * P + 2) ^ 2 + 4 ≤ H ^ (2 * p + 46) := by
  have hdimension := wide_coordinate_budget_le H M P p hH hM hP hPcap
  have hlarge : H ≤ H ^ (2 * p + 45) := Nat.le_pow (by omega)
  have hfour : 4 ≤ H ^ (2 * p + 45) := (by omega : 4 ≤ H).trans hlarge
  calc
    _ ≤ 3 * H ^ (2 * p + 45) := by omega
    _ ≤ H * H ^ (2 * p + 45) := Nat.mul_le_mul_right _ (by omega)
    _ = H ^ (2 * p + 45 + 1) := (pow_succ' H _).symm
    _ = _ := rfl

theorem optimizerTriangularMass_le_square (K : ℕ) : optimizerTriangularMass K ≤ K ^ 2 := by
  have htwice := optimizerTriangularMass_twice K
  have hpower : K ≤ K ^ 2 := Nat.le_pow (by decide)
  nlinarith only [htwice, hpower]

theorem localOnlineMassBound_polynomial (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    localOnlineMassBound M P H ≤ H ^ (8000 * (p + 1)) := by
  have hG : H + M * (40 * P + 2) ^ 2 + 2 ≤ H ^ (2 * p + 46) :=
    (by omega : H + M * (40 * P + 2) ^ 2 + 2 ≤ H + M * (40 * P + 2) ^ 2 + 4).trans
      (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  calc
    _ ≤ ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ^ 2 := optimizerTriangularMass_le_square _
    _ = (H + M * (40 * P + 2) ^ 2 + 2) ^ (80 * 2) := (pow_mul _ 80 2).symm
    _ ≤ (H ^ (2 * p + 46)) ^ (80 * 2) := Nat.pow_le_pow_left hG _
    _ = H ^ ((2 * p + 46) * (80 * 2)) := (pow_mul H _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem computed_localOnlineMassBound_polynomial (N : ℕ) (hH : 64 ≤ inputHeight N) :
    localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N) ≤
      inputHeight N ^ (8000 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply localOnlineMassBound_polynomial _ _ _ _ hH
  · exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  · exact Nat.one_le_pow _ _ (by omega)
  · exact le_rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uniform source-range address fits in one logarithmic input
word eventually. The coefficient can be any fixed natural number. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_sourceAddressBits_div_height_tendsto (C : ℕ) :
    Tendsto (fun N =>
      ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) /
        inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (4 * (C : ℝ) + 1)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := (inputSmallLog_bounds N hN).1
  have hp := coarseExponent_le_smallLog N
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hs : Nat.size (inputHeight N) = heightExponent N + 1 := by
    simp only [inputHeight, Nat.size_pow]
  have hsmall : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hell
  have hpR : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show coarseExponent (inputSmallLog N) + 1 ≤ 2 * inputSmallLog N by omega)
  have hsR : (Nat.size (inputHeight N) : ℝ) ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show Nat.size (inputHeight N) ≤ 2 * inputSmallLog N by omega)
  have hproduct := mul_le_mul hpR hsR (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hscaled := mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hnum : ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) ≤
      (4 * (C : ℝ) + 1) * (inputSmallLog N : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hscaled, hsmall, sq_nonneg ((inputSmallLog N : ℝ) - 1)]
  have h := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (inputHeight N) : (0 : ℝ) ≤ inputHeight N)
  simpa only [mul_div_assoc] using h

theorem computed_sourceAddressBits_le_height (C : ℕ) :
    ∀ᶠ N in atTop,
      C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 ≤ inputHeight N := by
  filter_upwards [(computed_sourceAddressBits_div_height_tendsto C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with N h
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlt := (div_lt_one hH).mp h
  exact_mod_cast hlt.le

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRequestSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem two_pow_inputHeight_le (N : ℕ) : 2 ^ inputHeight N ≤ 4 * (N + 2) ^ 2 := by
  have hc : 0 < Nat.clog 2 (N + 2) :=
    Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega)
  have hH := (rejectionWord_range (Nat.clog 2 (N + 2)) hc).2
  have hN := (rejectionWord_range (N + 2) (by omega)).2
  change inputHeight N < 2 * Nat.clog 2 (N + 2) at hH
  change 2 ^ Nat.clog 2 (N + 2) < 2 * (N + 2) at hN
  calc
    _ ≤ 2 ^ (2 * Nat.clog 2 (N + 2)) := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hH.le
    _ = (2 ^ Nat.clog 2 (N + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * (N + 2)) ^ 2 := Nat.pow_le_pow_left hN.le 2
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An explicit parity tag separates source coordinates and table keys.
The code is computed from coordinates without enumerating the key type. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



 theorem keyCode_injective (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (hs : Function.Injective sourceCode) (ht : Function.Injective tableCode) :
    Function.Injective (keyCode sourceCode tableCode) := by
  intro left right h
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have heq : sourceCode left = sourceCode right := by
        change 2 * sourceCode left = 2 * sourceCode right at h
        omega
      exact congrArg Sum.inl (hs heq)
    | inr right =>
      change 2 * sourceCode left = 2 * tableCode right + 1 at h
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * tableCode left + 1 = 2 * sourceCode right at h
      omega
    | inr right =>
      have heq : tableCode left = tableCode right := by
        change 2 * tableCode left + 1 = 2 * tableCode right + 1 at h
        omega
      exact congrArg Sum.inr (ht heq)

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Scalar-source addresses are computed from physical coordinates by
integer pairing. No enumeration of the probability space is performed. -/

namespace EditApproximation

variable {M J N n exponent F Q R B : ℕ}



 theorem physicalScalarCode_injective (hM : 1 ≤ M) :
    Function.Injective (@physicalScalarCode M J N n exponent F Q R B) := by
  intro left right heq
  rcases left with ⟨left, li⟩
  rcases right with ⟨right, ri⟩
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hp : Nat.pair (physicalEntryCode (left.1.1.val, left.1.2.2))
          (Nat.pair left.1.2.1.val (Nat.pair left.2.val.val li.val)) =
          Nat.pair (physicalEntryCode (right.1.1.val, right.1.2.2))
          (Nat.pair right.1.2.1.val (Nat.pair right.2.val.val ri.val)) := by
        change 2 * _ = 2 * _ at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨he, hs⟩
      rcases Nat.pair_eq_pair.mp hs with ⟨hs, hr⟩
      rcases Nat.pair_eq_pair.mp hr with ⟨hr, ht⟩
      have he := physicalEntryCode_injective hM he
      have hn : left.1.1 = right.1.1 := Subtype.ext (congrArg Prod.fst he)
      have hq := congrArg Prod.snd he
      have hs : left.1.2.1 = right.1.2.1 := Fin.ext hs
      have hr : left.2 = right.2 := Subtype.ext (Fin.ext hr)
      have ht : li = ri := Fin.ext ht
      rcases left with ⟨⟨node, scale, q⟩, range⟩
      rcases right with ⟨⟨node', scale', q'⟩, range'⟩
      dsimp only at hn hq hs hr
      subst node'
      subst scale'
      subst q'
      subst range'
      cases ht
      rfl
    | inr right =>
      change 2 * _ = 2 * _ + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * _ + 1 = 2 * _ at heq
      omega
    | inr right =>
      have hp : Nat.pair (physicalNodeCode left.1.val)
          (Nat.pair left.2.1.val (Nat.pair left.2.2.1.val (Nat.pair left.2.2.2.val
            (Nat.pair li.1.val (Nat.pair li.2.1.val li.2.2.val))))) =
          Nat.pair (physicalNodeCode right.1.val)
          (Nat.pair right.2.1.val (Nat.pair right.2.2.1.val (Nat.pair right.2.2.2.val
            (Nat.pair ri.1.val (Nat.pair ri.2.1.val ri.2.2.val))))) := by
        change 2 * _ + 1 = 2 * _ + 1 at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨hn, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hs, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hx, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hy, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨ht, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hl, hv⟩
      have hn : left.1 = right.1 := Subtype.ext (physicalNodeCode_injective hM hn)
      have hs : left.2.1 = right.2.1 := Fin.ext hs
      have hx : left.2.2.1 = right.2.2.1 := Fin.ext hx
      have hy : left.2.2.2 = right.2.2.2 := Fin.ext hy
      rcases left with ⟨node, scale, x, y⟩
      rcases right with ⟨node', scale', x', y'⟩
      dsimp only at hn hs hx hy
      subst node'
      subst scale'
      subst x'
      subst y'
      rcases li with ⟨time, label, value⟩
      rcases ri with ⟨time', label', value'⟩
      have ht : time = time' := Fin.ext ht
      cases ht
      have hl : label = label' := Fin.ext hl
      cases hl
      have hv : value = value' := Fin.ext hv
      cases hv
      rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Encoding

variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 theorem physicalFamilyCode_injective (hM : 1 ≤ M) :
    Function.Injective (physicalFamilyCode (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) := by
  intro first second h
  obtain ⟨hp, h⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨hc, hs⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext hc) (physicalScalarCode_injective hM hs))

end Encoding

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyMemoCode
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation







 theorem computedFamilyMemoCode_injective (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    Function.Injective (computedFamilyMemoCode source target N R) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN hell).1
  exact SourceRanked.keyCode_injective _ _
    (physicalFamilyCode_injective target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) hM)
    (ChargedPhysicalRequest.code_injective hM)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_MemoCodeWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Address generation is charged separately from binary trie traversal.
The loops visit only coordinates in a key, never the ambient key space. -/
namespace EditApproximation



 theorem naturalPairWithWork_cost (a b : ℕ) : (naturalPairWithWork a b).2 ≤ 5 := by
  unfold naturalPairWithWork
  split_ifs <;> dsimp only <;> decide



 theorem physicalNodeCodeWithWork_cost {M J : ℕ} (node : PhysicalNode M J) :
    (physicalNodeCodeWithWork node).2 ≤ 5 * J + 5 := by
  have h := node.1.isLt
  simp only [physicalNodeCodeWithWork, treeLayerCodeWithWork_cost, parameterPowerWithWork_spec]
  omega



 theorem physicalEntryCodeWithWork_cost {M J n : ℕ} (entry : PhysicalEntry M J n) :
    (physicalEntryCodeWithWork entry).2 ≤ 5 * J + 13 := by
  have h := physicalNodeCodeWithWork_cost entry.1
  change (physicalNodeCodeWithWork entry.1).2 + 8 ≤ _
  omega



 theorem physicalTableCodeWithWork_cost {M J n : ℕ} (copies T S : ℕ)
    (request : PhysicalTableRequest M J n) :
    (physicalTableCodeWithWork copies T S request).2 ≤ 7 * J + 29 := by
  have he := physicalEntryCodeWithWork_cost (request.node, request.state)
  simp only [physicalTableCodeWithWork, parameterPowerWithWork_spec]
  omega



 theorem chargedPhysicalCodeWithWork_cost {M J n passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J n passes copies T S) :
    (chargedPhysicalCodeWithWork request).2 ≤ 7 * J + 32 := by
  cases request with
  | inl entry => have h := physicalEntryCodeWithWork_cost entry
                 change (physicalEntryCodeWithWork entry).2 + 2 ≤ _
                 omega
  | inr request => have h := physicalTableCodeWithWork_cost copies T S request.val
                   change (physicalTableCodeWithWork copies T S request.val).2 + 3 ≤ _
                   omega



 theorem physicalScalarCodeWithWork_cost {M J N n exponent F Q R B : ℕ}
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    (physicalScalarCodeWithWork key).2 ≤ 5 * J + 40 := by
  rcases key with ⟨online | group, index⟩
  · have hn := physicalEntryCodeWithWork_cost (online.1.1.val, online.1.2.2)
    have ha := naturalPairWithWork_cost online.2.val.val index.val
    have hb := naturalPairWithWork_cost online.1.2.1.val
      (naturalPairWithWork online.2.val.val index.val).1
    have hc := naturalPairWithWork_cost (physicalEntryCodeWithWork (online.1.1.val, online.1.2.2)).1
      (naturalPairWithWork online.1.2.1.val (naturalPairWithWork online.2.val.val index.val).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega
  · have hn := physicalNodeCodeWithWork_cost group.1.val
    have ha := naturalPairWithWork_cost index.2.1.val index.2.2.val
    have hb := naturalPairWithWork_cost index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1
    have hc := naturalPairWithWork_cost group.2.2.2.val
      (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1
    have hd := naturalPairWithWork_cost group.2.2.1.val
      (naturalPairWithWork group.2.2.2.val
        (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1
    have he := naturalPairWithWork_cost group.2.1.val
      (naturalPairWithWork group.2.2.1.val
        (naturalPairWithWork group.2.2.2.val
          (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1
    have hf := naturalPairWithWork_cost (physicalNodeCodeWithWork group.1.val).1
      (naturalPairWithWork group.2.1.val
        (naturalPairWithWork group.2.2.1.val
          (naturalPairWithWork group.2.2.2.val
            (naturalPairWithWork index.1.val (naturalPairWithWork index.2.1.val index.2.2.val).1).1).1).1).1
    dsimp only [physicalScalarCodeWithWork]
    omega

section Family
variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)



 theorem physicalFamilyCodeWithWork_cost
    (key : PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) :
    (physicalFamilyCodeWithWork target N P F exponent H Q passes copies key).2 ≤ 5 * J + 52 := by
  have hs := physicalScalarCodeWithWork_cost key.2.2
  have hc := naturalPairWithWork_cost key.2.1.val (physicalScalarCodeWithWork key.2.2).1
  have hp := naturalPairWithWork_cost key.1.val
    (naturalPairWithWork key.2.1.val (physicalScalarCodeWithWork key.2.2).1).1
  dsimp only [physicalFamilyCodeWithWork]
  omega
end Family



 theorem computedFamilyMemoCodeWithWork_cost (source target : List ℕ) (N R : ℕ)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    (computedFamilyMemoCodeWithWork source target N R key).2 ≤
      7 * intervalTreeDepth (integerParameters N).M source.length + 60 := by
  cases key with
  | inl key =>
    have h := physicalFamilyCodeWithWork_cost target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key
    change (physicalFamilyCodeWithWork target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key).2 + 2 ≤ _
    omega
  | inr key =>
    have h := chargedPhysicalCodeWithWork_cost key
    change (chargedPhysicalCodeWithWork key).2 + 3 ≤ _
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKernelFresh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace FiniteQuery

theorem requestWork_eq_fresh_sum {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (cost : ι → BinaryMemo ℚ → ℕ) (weight : κ → ℕ)
    (hcost : ∀ key memory, cost key memory = ((ask key memory).freshKeys.map weight).sum)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    requestWork ask cost program memory = ((run ask program memory).freshKeys.map weight).sum := by
  induction program generalizing memory with
  | done value => rfl
  | read key next ih =>
    simp only [requestWork, run, hcost, ih, List.map_append, List.sum_append]

end FiniteQuery

/-- The local kernel annotation is exactly the sum over the freshly
evaluated keys, including the actual adaptive recursive execution. -/
theorem rankedMemoKernelWork_eq_fresh_sum {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoKernelWork rank program bits encode cost key memory =
      ((rankedMemoEvaluate rank program bits encode key memory).freshKeys.map cost).sum := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoKernelWork rank program bits encode cost key memory =
        ((rankedMemoEvaluate rank program bits encode key memory).freshKeys.map cost).sum := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoKernelWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only [List.map_nil, List.sum_nil]
      · rename_i hfound
        simp only [List.map_cons, List.sum_cons]
        congr 1
        apply FiniteQuery.requestWork_eq_fresh_sum
        intro child previous
        exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitRankedMemoOn
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational trace transfer when local output normalization is
proved only on the canonical reachable child words. -/

namespace EditApproximation

theorem rankedBitMemoEvaluate_decode_on {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank program child.val)
      (fun word value => word.value = value) (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).decode =
      rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      (rankedBitMemoEvaluate rank program bits encode key memory).decode =
        rankedMemoEvaluate rank expected bits encode key (memory.mapValues BinaryFraction.value) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hmem
      rw [rankedBitMemoEvaluate, rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec, BinaryMemo.mapValues_lookup]
      cases hfound : memory.lookup (binaryMemoKey bits (encode key)) with
      | some value => simp only [Option.map_some, BitRecursiveMemoResult.decode]
      | none =>
        simp only [Option.map_none]
        have hchildren (child : {child : κ // rank child < rank key}) previous
            (hp : bitMemoSound bits encode (rankedBitProgramValue rank program) previous) :
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
            bitMemoSound bits encode (rankedBitProgramValue rank program)
                (rankedBitMemoEvaluate rank program bits encode child.val previous).memory ∧
            (rankedBitMemoEvaluate rank program bits encode child.val previous).decode =
              rankedMemoEvaluate rank expected bits encode child.val
                (previous.mapValues BinaryFraction.value) := by
          have hs := rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp
          exact ⟨hs.1, hs.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp⟩
        have hr := (BitQuery.runMemo_decode_on
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (bitMemoSound bits encode (rankedBitProgramValue rank program))
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoEvaluate rank expected bits encode child.val previous)
          hchildren (hprogram key) memory hmem).1
        have hv := congrArg RecursiveMemoResult.value hr
        have hm := congrArg RecursiveMemoResult.memory hr
        have hf := congrArg RecursiveMemoResult.freshKeys hr
        have hd := congrArg RecursiveMemoResult.dictionaryVisits hr
        have hq := congrArg RecursiveMemoResult.requests hr
        simp only [BitRecursiveMemoResult.decode] at hv hm hf hd hq
        simp only [BinaryMemo.insertCosted_spec, BitRecursiveMemoResult.decode,
          BinaryMemo.mapValues_insert, hv, hm, hf, hd, hq]
  exact hall (rank key) key rfl memory hmemory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoWorkOn
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same exact fresh-key work accounting applies to normalized
programs whose simulation is justified on reachable child values. -/

namespace EditApproximation

theorem rankedBitMemoEvaluate_work_transfer_on {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (expected : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (hprogram : ∀ key, BitQuery.RefinesOn
      (fun child => rankedBitProgramValue rank program child.val)
      (fun word value => word.value = value) (program key) (expected key))
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) (memory : BinaryMemo BinaryFraction)
    (hmemory : bitMemoSound bits encode (rankedBitProgramValue rank program) memory) :
    (rankedBitMemoEvaluate rank program bits encode key memory).localWork =
      rankedMemoKernelWork rank expected bits encode (rankedBitLocalWork rank program)
        key (memory.mapValues BinaryFraction.value) := by
  have hf := congrArg RecursiveMemoResult.freshKeys
    (rankedBitMemoEvaluate_decode_on rank program expected hprogram bits encode hinjective hbounded
      key memory hmemory)
  dsimp only [BitRecursiveMemoResult.decode] at hf
  rw [rankedMemoKernelWork_eq_fresh_sum, ← hf]
  exact rankedBitMemoEvaluate_localWork rank program bits encode hinjective hbounded key memory hmemory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- A single logarithmic word accommodates every power exponent needed
by the global integer and online-mass constructors. -/
 theorem computedParameterPower_word :
    ∀ᶠ N in atTop, ∀ k : ℕ,
      k ≤ 8000 * (coarseExponent (inputSmallLog N) + 1) →
      Nat.size (inputHeight N ^ k) ≤ inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000] with N hN
  intro k hk
  exact (natural_power_bit_length _ _).trans
    ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1).trans hN)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryConstants
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryMass_word :
    ∀ᶠ N : ℕ in atTop, Nat.size (localOnlineMassBound (integerParameters N).M
      (integerParameters N).P (inputHeight N)) ≤ inputHeight N := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hp hell
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  exact (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (hp _ le_rfl)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRetainedValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_height_polynomial (N : ℕ) : inputHeight N ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := Nat.lt_two_pow_self.le
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryExecution
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

section Correct
variable (source target : List ℕ) (N : ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (input : ComputedFamilyInput source target N) (hN : 0 < N)
  (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
  (hsize : source.length + target.length ≤ N)
  (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
    (inputHeight N)) ≤ inputHeight N)
  (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
  (hp : target.length ≤ 2 ^ positionBits)
  (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_localWork :
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).localWork =
      computedFamilyKernelWork source target N input
        (computedQueryLocalWork source target N occurrence symbolBits positionBits input) := by
  exact rankedBitMemoEvaluate_work_transfer_on (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryReference source target N input)
    (fun key => (computedQueryMemoNormalized_correct source target N occurrence symbolBits positionBits
      input hf hs ht hp htable key).2)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hMass)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty
    (bitMemoSound_empty _ _ _)

end Correct
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryTemporarySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryChargedReadHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryTemporaryCells_bound (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤
      3 * computedFamilyKernelWork source target N input
          (computedQueryLocalWork source target N occurrence symbolBits positionBits input) +
        (memoRequestCells (16384 * inputHeight N + 5)
          (7 * intervalTreeDepth (integerParameters N).M source.length + 60) + 3) *
          (computedFamilyResult source target N input).requests := by
  have h := rankedBitMemoCells_le (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoHeap source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (7 * intervalTreeDepth (integerParameters N).M source.length + 60)
    (computedFamilyMemoCodeWithWork_cost source target N (inputHeight N ^ 2))
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty
  change computedQueryTemporaryCells source target N occurrence symbolBits positionBits input + 3 ≤
    3 * (computedQueryMemoResult source target N occurrence symbolBits positionBits input).localWork +
      _ * (computedQueryMemoResult source target N occurrence symbolBits positionBits input).requests at h
  rw [computedQueryMemoResult_localWork source target N occurrence symbolBits positionBits input
    hN hell hf hsize hMass hs ht hp htable] at h
  have hd := congrArg RecursiveMemoResult.requests
    (computedQueryMemoResult_decode source target N occurrence symbolBits positionBits input
      hN hell hf hsize hMass hs ht hp htable)
  change (computedQueryMemoResult source target N occurrence symbolBits positionBits input).requests = _ at hd
  rw [hd] at h
  omega

private theorem requestCells_factor (H J : ℕ) (hH : 100 ≤ H) (hJ : J ≤ H) :
    memoRequestCells (16384 * H + 5) (7 * J + 60) + 3 ≤ H ^ 4 := by
  have hcoef : 200000 ≤ H ^ 3 :=
    (by norm_num : 200000 ≤ (100 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hH 3)
  have hp : 200000 * H ≤ H ^ 4 := (Nat.mul_le_mul_right H hcoef).trans_eq (by ring)
  unfold memoRequestCells
  omega

theorem computedQueryTemporaryCells_polynomial_oai :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤ (N + 2) ^ 20 := by
  filter_upwards [computedQueryLocalWork_cap,
    computedFamilyKernelWork_polynomial computedQueryWorkDegree,
    computedFamilyResult_requests_near_linear 1 (by norm_num), computedQueryMass_word,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N hcap hwork hrequests hMass hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hl := hwork source target hsize input _
    (hcap source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc)
  have hr : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hrequests source target hsize input
    norm_num at h
    exact_mod_cast h
  have hH : 100 ≤ inputHeight N :=
    (by have := two_hundred_le_two_pow_thousand.trans hell; omega : 100 ≤ inputSmallLog N).trans
      (computed_smallLog_le_height N)
  have hd := computed_tree_depth_bound N source.length hN (by omega)
    (two_hundred_le_two_pow_thousand.trans hell)
  have hhundred : 100 ≤ inputSmallLog N := by
    have := two_hundred_le_two_pow_thousand.trans hell
    omega
  have hm := Nat.mul_le_mul_left (intervalTreeDepth (integerParameters N).M source.length) hhundred
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    nlinarith only [hd, hm]
  have hc := requestCells_factor (inputHeight N) _ hH hJ
  have hpoly : inputHeight N ^ 4 ≤ (N + 2) ^ 16 :=
    (Nat.pow_le_pow_left (computed_height_polynomial N) 4).trans_eq (by rw [← pow_mul])
  have hb := computedQueryTemporaryCells_bound source target N occurrence symbolBits positionBits
    input hN hell hf hsize hMass hs ht hp hoc
  have hprod := Nat.mul_le_mul (hc.trans hpoly) hr
  have h2 : (N + 2) ^ 2 ≤ (N + 2) ^ 18 := Nat.pow_le_pow_right (by omega) (by decide)
  have hfour : 4 * (N + 2) ^ 18 ≤ (N + 2) ^ 20 := by
    calc
      _ ≤ (N + 2) ^ 2 * (N + 2) ^ 18 := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le N])
      _ = _ := by rw [← pow_add]
  rw [← pow_add] at hprod
  change _ ≤ (N + 2) ^ 18 at hprod
  omega

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryTemporaryCells_polynomial_oai := @OAI.EditApproximation.computedQueryTemporaryCells_polynomial_oai
