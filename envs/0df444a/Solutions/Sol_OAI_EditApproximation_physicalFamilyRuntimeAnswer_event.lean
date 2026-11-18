-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyRuntimeAnswer_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:52.301491+00:00
-- url     : https://prove2.me/submissions/29e7ae47-3902-4c7e-829f-2ef7888a73ca

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
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
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_physicalFamilyFinalAnswer_law

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

theorem rankedMemoEvaluate_empty {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedMemoEvaluate rank program bits encode key .empty).value = rankedProgramValue rank program key :=
  (rankedMemoEvaluate_sound rank program bits encode hinjective hbounded key .empty
    (memoSound_empty bits encode _)).1

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

 theorem memo_value (tableRank : κ → ℕ)
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ)
    (hbody : ∀ key, (tableBody key).value (Sum.elim sourceValue (fun next => tableValue next.val)) =
      tableValue key) (bits : ℕ) (encode : Sum σ κ → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (key : Sum σ κ) :
    (rankedMemoEvaluate (rank tableRank) (body tableRank tableBody sourceValue)
      bits encode key .empty).value = value sourceValue tableValue key := by
  rw [rankedMemoEvaluate_empty _ _ bits encode hinjective hbounded]
  exact program_value tableRank tableBody sourceValue tableValue hbody key

end SourceRanked

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The charged evaluator actually caches random source coordinates and
physical entries in one rank-decreasing memo computation. -/

namespace EditApproximation

section Memo

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ)



 theorem chargedRandomMemoEvaluate_value
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
      groupScalarValue (group pass copy node time) key)
    (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
      (readInteger pass copy node time key
        (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
          P exponent H tau (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S
            copies factor multiplier tau eta kappa delta group integer initial (PhysicalTableRequest.warmup
              pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
        (integer pass copy node time key.1 key.2 : ℚ))
    (bits : ℕ) (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode request).value =
    chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request := by
  unfold chargedRandomMemoEvaluate
  exact SourceRanked.memo_value ChargedPhysicalRequest.rank _ sourceAnswer
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedRandomGlobalQuery_value source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial group integer sourceAnswer
      (physicalRandomBoundedQuery_localValue source target N P F exponent H Q T S passes copies factor
        multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hgroup honline))
    bits encode hinjective hbounded (.inr request)

end Memo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionSelectedCost
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rejection counts are independent of all accepted values. Thus even
an adaptive choice of coordinates incurs fewer than two word trials per
selected coordinate in expectation. No unused source is charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Selected

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]



 theorem rejectionRuntimeArrayLaw_accepted :
    (rejectionRuntimeArrayLaw range).map Prod.snd = rejectionAcceptedLaw range := by
  unfold rejectionRuntimeArrayLaw
  simp



end Selected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyMemo
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite family is consumed through actual source reads in the shared
memo evaluator. Its final value and law agree with the proved local answer. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Memo

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



 theorem physicalFamilyMemoResult_value (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (rootQ : TargetInterval target.length)
    (input : Seed × Family) :
    ((physicalFamilyMemoResult source target N P T S H hH bits encode rootQ input).value : ℝ) =
      physicalFamilyFinalValue source target N P T S H hP rootQ input := by
  unfold physicalFamilyMemoResult
  rw [chargedRandomMemoEvaluate_value source target N P ell exponent H (ell ^ 80) T S
    (passes + 1) (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (physicalFamilyGroupRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (physicalFamilyOnlineRead target N P ell exponent H (ell ^ 80) passes (H ^ 2))
    (clampedSeedNat input.1)
    (physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2)
    (physicalFamilyInteger source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1))]
  · rfl
  · exact physicalFamilyGroupRead_value target N P ell exponent H (ell ^ 80) passes (H ^ 2) input.2
  · exact physicalFamilyOnlineRead_value source target N P ell exponent H (ell ^ 80) T S passes (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta hP input.2
      (clampedSeedNat input.1)
  · exact hinjective
  · exact hbounded

 theorem physicalFamilyMemoAnswer_eq (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (rootQ : TargetInterval target.length)
    (input : Seed × Family) :
    physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ input =
      physicalFamilyFinalAnswer source target N P T S H hP rootQ input := by
  unfold physicalFamilyMemoAnswer physicalFamilyFinalAnswer
  rw [physicalFamilyMemoResult_value source target N P T S H hP hH bits encode hinjective hbounded]

 theorem physicalFamilyMemoAnswer_law (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (incoming : Measure Seed)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
        (physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ) =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  have heq : physicalFamilyMemoAnswer (R := R) source target N P T S H hH bits encode rootQ =
      physicalFamilyFinalAnswer source target N P T S H hP rootQ := by
    funext input
    exact physicalFamilyMemoAnswer_eq source target N P T S H hP hH bits encode hinjective hbounded rootQ input
  rw [heq]
  exact physicalFamilyFinalAnswer_law source target N P T S H hP hH incoming rootQ

end Memo

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite family is consumed through actual source reads in the shared
memo evaluator. Its final value and law agree with the proved local answer. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Accuracy

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S


 theorem physicalFamilyMemoAnswer_event (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (incoming : Measure Seed)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).real
      {input | physicalFamilyMemoAnswer source target N P T S H hH bits encode rootQ input ∈ event} =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {input | localFinalProgramAnswer (R := R) source target N P T S H rootQ input ∈ event} := by
  classical
  have h := congrArg (fun law : Measure ℕ => law.real event)
    (physicalFamilyMemoAnswer_law source target N P T S H hP hH bits encode hinjective hbounded incoming rootQ)
  simpa only [map_measureReal_apply (measurable_of_finite _) (Set.to_countable _).measurableSet,
    Set.preimage] using h

end Accuracy

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilySampling
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The finite scalar family is exactly the accepted output of the
independent literal rejection samplers. Only requested coordinates need
be generated; their failure counts have a product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Family

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)





 theorem physicalFamily_rejection_runtime_law :
    (rejectionRuntimeArrayLaw (physicalFamilyRange (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map Prod.snd =
    physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies :=
  rejectionRuntimeArrayLaw_accepted _

end Family

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRuntime
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The source family is the projection of terminating rejection-sampling executions. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Runtime

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S



omit [DecidableEq α] [NeZero R] in
 theorem physicalFamilyRuntimeAccepted_law (incoming : Measure SeedState) [IsProbabilityMeasure incoming] :
    (physicalFamilyRuntimeLaw (R := R) target N P H incoming).map
      (physicalFamilyRuntimeAccepted (R := R) target N P H) =
    incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) := by
  change (incoming.prod (rejectionRuntimeArrayLaw FamilyRange)).map
    (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    physicalFamily_rejection_runtime_law]

 theorem physicalFamilyRuntimeAnswer_event_oai (hP : 0 < P) (hH : 0 < H) (bits : ℕ)
    (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2)) Table → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (incoming : Measure SeedState) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) (event : Set ℕ) :
    (physicalFamilyRuntimeLaw (R := R) target N P H incoming).real
      {execution | physicalFamilyRuntimeAnswer source target N P T S H hH bits encode rootQ execution ∈ event} =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).real
      {input | localFinalProgramAnswer (R := R) source target N P T S H rootQ input ∈ event} := by
  rw [← physicalFamilyMemoAnswer_event source target N P T S H hP hH bits encode hinjective hbounded
    incoming rootQ event, ← physicalFamilyRuntimeAccepted_law target N P H incoming,
    map_measureReal_apply (by unfold physicalFamilyRuntimeAccepted; fun_prop) (by exact (Set.toFinite _).measurableSet)]
  rfl

end Runtime

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.physicalFamilyRuntimeAnswer_event_oai := @OAI.EditApproximation.physicalFamilyRuntimeAnswer_event_oai
