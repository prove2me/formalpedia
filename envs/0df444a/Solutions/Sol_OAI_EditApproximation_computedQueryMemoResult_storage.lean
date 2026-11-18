-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryMemoResult_storage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:16.701067+00:00
-- url     : https://prove2.me/submissions/f0ed7d00-426b-47db-81b9-924ed326dbad

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
import Theorems.Thm_OAI_EditApproximation_computedFamilyMemoCode_fits
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoNormalized_width
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMemoSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-width binary memo has bounded height on every execution,
including failed approximation events and repeated lookups. This bound
uses the actual returned tree and does not count a complete table allocation. -/

namespace EditApproximation

namespace BinaryMemo

theorem insert_height {α : Type*} (tree : BinaryMemo α) (key : List Bool) (value : α) :
    (tree.insert key value).height ≤ max tree.height (key.length + 1) := by
  induction key generalizing tree with
  | nil =>
    cases tree <;> simp only [insert, left, right, height, List.length_nil] <;> omega
  | cons bit key ih =>
    cases tree with
    | empty =>
      have h := ih (.empty : BinaryMemo α)
      cases bit <;> simp only [insert, left, right, height, List.length_cons] at * <;> omega
    | node old left right =>
      have hl := ih left
      have hr := ih right
      cases bit <;> simp only [insert, BinaryMemo.left, BinaryMemo.right, height, List.length_cons] at * <;> omega

theorem nodes_le_height {α : Type*} (tree : BinaryMemo α) :
    tree.nodes + 1 ≤ 2 ^ tree.height := by
  induction tree with
  | empty => rfl
  | node value left right hl hr =>
    have hleft := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_left left.height right.height)
    have hright := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_right left.height right.height)
    simp only [nodes, height, pow_succ]
    omega

end BinaryMemo

namespace FiniteQuery

theorem run_height_bound {ι κ : Type*}
    (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ) (bound : ℕ)
    (hask : ∀ key memory, (ask key memory).memory.height ≤ max memory.height bound)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    (run ask program memory).memory.height ≤ max memory.height bound := by
  induction program generalizing memory with
  | done result => exact le_max_left _ _
  | read key next ih =>
    have hf := hask key memory
    have hr := ih (ask key memory).value (ask key memory).memory
    change (run ask (next (ask key memory).value) (ask key memory).memory).memory.height ≤ _
    exact hr.trans (max_le (hf.trans (le_refl _)) (le_max_right _ _))

end FiniteQuery

theorem rankedMemoEvaluate_height_bound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) (memory : BinaryMemo ℚ) :
    (rankedMemoEvaluate rank program bits encode key memory).memory.height ≤
      max memory.height (bits + 1) := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      (rankedMemoEvaluate rank program bits encode key memory).memory.height ≤
        max memory.height (bits + 1) := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact le_max_left _ _
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            (rankedMemoEvaluate rank program bits encode child.val previous).memory.height ≤
              max previous.height (bits + 1) := by
          intro child previous
          exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
        have hr := FiniteQuery.run_height_bound _ (bits + 1) hchildren (program key) memory
        simp only [BinaryMemo.insertCosted_spec]
        exact (BinaryMemo.insert_height _ _ _).trans
          (max_le hr (by simp only [binaryMemoKey_length]; exact le_max_right _ _))
  exact hall (rank key) key rfl memory

theorem rankedMemoEvaluate_nodes_bound {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (key : κ) :
    (rankedMemoEvaluate rank program bits encode key .empty).memory.nodes + 1 ≤ 2 ^ (bits + 1) := by
  have h := rankedMemoEvaluate_height_bound rank program bits encode key .empty
  simp only [BinaryMemo.height, max_eq_right (Nat.zero_le _)] at h
  exact (BinaryMemo.nodes_le_height _).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every value retained by the actual binary dictionary obeys the
semantic value bound. This includes every allocated path, not only keys
queried after the computation. -/

namespace EditApproximation
namespace BinaryMemo

theorem AllValues.insert {α : Type*} {P : α → Prop} {memory : BinaryMemo α}
    (hmem : AllValues P memory) (key : List Bool) (a : α) (ha : P a) :
    AllValues P (memory.insert key a) := by
  intro query value hvalue
  by_cases heq : query = key
  · subst query
    rw [lookup_insert_same] at hvalue
    cases hvalue
    exact ha
  · rw [lookup_insert_other memory key query a heq] at hvalue
    exact hmem query value hvalue

end BinaryMemo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitMemoStorage
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Storage of the actual binary-word memo. Node paths are identical to
the rational evaluator, while stored numerator/denominator bits are
bounded using the deterministic returned-word invariant. -/

namespace EditApproximation
namespace BinaryMemo



theorem fractionStorage_le (memory : BinaryMemo BinaryFraction) (B : ℕ)
    (hmem : AllValues (fun word => word.width ≤ B) memory) :
    memory.fractionStorage ≤ (2 * B + 4) * memory.nodes := by
  induction memory with
  | empty => simp only [fractionStorage, nodes, Nat.mul_zero, le_refl]
  | node word left right ihl ihr =>
    have hl : AllValues (fun word => word.width ≤ B) left := by
      intro key value h
      exact hmem (false :: key) value h
    have hr : AllValues (fun word => word.width ≤ B) right := by
      intro key value h
      exact hmem (true :: key) value h
    have hw : (word.map fun w => w.numerator.bits.length + w.denominator.length + 1).getD 0 ≤ 2 * B + 1 := by
      cases word with
      | none => exact Nat.zero_le _
      | some word =>
        have h := hmem [] word rfl
        have hn := (le_max_left word.numerator.bits.length word.denominator.length).trans h
        have hd := (le_max_right word.numerator.bits.length word.denominator.length).trans h
        change _ + _ + 1 ≤ _
        omega
    have hleft := ihl hl
    have hright := ihr hr
    simp only [fractionStorage, nodes]
    nlinarith only [hw, hleft, hright]

end BinaryMemo

theorem rankedBitMemoEvaluate_widths {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (B : ℕ)
    (hwidth : ∀ key, (rankedBitProgramValue rank program key).width ≤ B)
    (key : κ) (memory : BinaryMemo BinaryFraction)
    (hsound : bitMemoSound bits encode (rankedBitProgramValue rank program) memory)
    (hmem : BinaryMemo.AllValues (fun word => word.width ≤ B) memory) :
    BinaryMemo.AllValues (fun word => word.width ≤ B)
      (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      bitMemoSound bits encode (rankedBitProgramValue rank program) memory →
      BinaryMemo.AllValues (fun word => word.width ≤ B) memory →
      BinaryMemo.AllValues (fun word => word.width ≤ B)
        (rankedBitMemoEvaluate rank program bits encode key memory).memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory hs hm
      rw [rankedBitMemoEvaluate]
      simp only [BinaryMemo.lookupCosted_spec]
      split
      · exact hm
      · have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            bitMemoSound bits encode (rankedBitProgramValue rank program) previous ∧
              BinaryMemo.AllValues (fun word => word.width ≤ B) previous →
            (rankedBitMemoEvaluate rank program bits encode child.val previous).value =
                rankedBitProgramValue rank program child.val ∧
              (bitMemoSound bits encode (rankedBitProgramValue rank program)
                  (rankedBitMemoEvaluate rank program bits encode child.val previous).memory ∧
                BinaryMemo.AllValues (fun word => word.width ≤ B)
                  (rankedBitMemoEvaluate rank program bits encode child.val previous).memory) := by
          intro child previous hp
          have hv := rankedBitMemoEvaluate_sound rank program bits encode hinjective hbounded child.val previous hp.1
          exact ⟨hv.1, hv.2, ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous hp.1 hp.2⟩
        have hr := BitQuery.runMemo_sound
          (fun child : {child : κ // rank child < rank key} => rankedBitProgramValue rank program child.val)
          (fun previous => bitMemoSound bits encode (rankedBitProgramValue rank program) previous ∧
            BinaryMemo.AllValues (fun word => word.width ≤ B) previous)
          (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
          hchildren (program key) memory ⟨hs, hm⟩
        have hv : (BitQuery.runMemo
            (fun child previous => rankedBitMemoEvaluate rank program bits encode child.val previous)
            (program key) memory).value = rankedBitProgramValue rank program key := by
          rw [rankedBitProgramValue]
          exact hr.1
        simp only [BinaryMemo.insertCosted_spec]
        exact hr.2.2.insert _ _ (hv.symm ▸ hwidth key)
  exact hall (rank key) key rfl memory hsound hmem

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_mixed_cache_nodes {κ : Type*} (N : ℕ)
    (rank : κ → ℕ) (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (encode : κ → ℕ) (key : κ) :
    (rankedMemoEvaluate rank program (16384 * inputHeight N + 5) encode key .empty).memory.nodes + 1 ≤
      (N + 2) ^ 65542 := by
  have hcache := rankedMemoEvaluate_nodes_bound rank program (16384 * inputHeight N + 5) encode key
  apply hcache.trans
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith [Nat.zero_le N]
  have hbase : 2 ^ inputHeight N ≤ (N + 2) ^ 4 := by
    apply (two_pow_inputHeight_le N).trans
    calc
      _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
      _ = _ := by ring
  calc
    2 ^ (16384 * inputHeight N + 5 + 1) = (2 ^ inputHeight N) ^ 16384 * 2 ^ 6 := by
      rw [show 16384 * inputHeight N + 5 + 1 = inputHeight N * 16384 + 6 by omega, pow_add, pow_mul]
    _ ≤ ((N + 2) ^ 4) ^ 16384 * (N + 2) ^ 6 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hbase _) (Nat.pow_le_pow_left (by omega) _)
    _ = (N + 2) ^ (4 * 16384 + 6) := by
      generalize (16384 : ℕ) = exponent
      rw [← pow_mul, ← pow_add]
    _ = (N + 2) ^ 65542 := congrArg (fun exponent : ℕ => (N + 2) ^ exponent) (by decide)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRejectionWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Work

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

 theorem physicalFamilyMemo_nodes_polynomial (hH : 0 < H)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length)
    (input : SeedState × PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) :
    (physicalFamilyMemoResult source target N P T S H hH (16384 * inputHeight N + 5)
      encode rootQ input).memory.nodes + 1 ≤ (N + 2) ^ 65542 :=
  computed_mixed_cache_nodes N _ _ encode _

end Work

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryStorage
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

section Storage
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
theorem computedQueryMemoResult_allWidths :
    BinaryMemo.AllValues (fun word => word.width ≤ inputHeight N ^ 3)
      (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory := by
  apply rankedBitMemoEvaluate_widths
    (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN
      (two_hundred_le_two_pow_thousand.trans hell))
    (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hMass)
    (inputHeight N ^ 3)
  · exact computedQueryMemoNormalized_width source target N occurrence symbolBits positionBits input
      hN (two_hundred_le_two_pow_thousand.trans hell) hf hsize hMass hs ht hp htable
  · exact bitMemoSound_empty _ _ _
  · intro key word h
    simp only [BinaryMemo.lookup_empty, reduceCtorEq] at h

include hN hell hf hsize hMass hs ht hp htable in
theorem computedQueryMemoResult_storage_oai :
    (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory.fractionStorage ≤
      (N + 2) ^ 65557 := by
  have hw := computedQueryMemoResult_allWidths source target N occurrence symbolBits positionBits
    input hN hell hf hsize hMass hs ht hp htable
  have hs' := BinaryMemo.fractionStorage_le _ (inputHeight N ^ 3) hw
  have hd := congrArg (fun result : RecursiveMemoResult (ComputedFamilyMemoKey source target N) =>
    result.memory.nodes) (computedQueryMemoResult_decode source target N occurrence symbolBits positionBits
      input hN hell hf hsize hMass hs ht hp htable)
  simp only [BitRecursiveMemoResult.decode, BinaryMemo.mapValues_nodes] at hd
  have hn : (computedQueryMemoResult source target N occurrence symbolBits positionBits input).memory.nodes ≤
      (N + 2) ^ 65542 := by
    rw [hd]
    exact Nat.le_trans (Nat.le_succ _) (physicalFamilyMemo_nodes_polynomial source target N
      (integerParameters N).P (integerParameters N).T (integerParameters N).S (inputHeight N)
      (Nat.two_pow_pos _) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (finalTargetState target.length) input)
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hh
  change inputHeight N ^ 3 ≤ (N + 2) ^ 12 at hh
  have hu : 1 ≤ (N + 2) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have he : 8 ≤ (N + 2) ^ 3 := (by decide : 8 ≤ (2 : ℕ) ^ 3).trans
    (Nat.pow_le_pow_left (by omega) 3)
  have hc : 2 * inputHeight N ^ 3 + 4 ≤ (N + 2) ^ 15 := by
    calc
      _ ≤ 8 * (N + 2) ^ 12 := by omega
      _ ≤ (N + 2) ^ 3 * (N + 2) ^ 12 := Nat.mul_le_mul_right _ he
      _ = _ := by rw [← pow_add]
  exact hs'.trans ((Nat.mul_le_mul hc hn).trans_eq (by rw [← pow_add]))

end Storage
end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryMemoResult_storage_oai := @OAI.EditApproximation.computedQueryMemoResult_storage_oai
