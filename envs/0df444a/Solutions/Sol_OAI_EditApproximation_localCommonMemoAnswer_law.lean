-- Prove2me | solution 1 for OAI.EditApproximation.localCommonMemoAnswer_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:47.705311+00:00
-- url     : https://prove2.me/submissions/9bf7b875-399d-4c69-94a2-bef11508327f

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
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
-- module Solutions.OAIQ361V3_EA.Compat
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
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
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
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

theorem code_bound {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) (hrequest : Bounded passes copies T S request) :
    code copies T S request < capacity M J n passes copies T S := by
  have he := physicalEntryCode_bound hM (request.node, request.state)
  change physicalEntryCode (request.node, request.state) < entryCapacity M J n at he
  have hinner : physicalEntryCode (request.node, request.state) +
      entryCapacity M J n * request.pass < entryCapacity M J n * passes := by
    nlinarith only [he, Nat.mul_le_mul_left (entryCapacity M J n) (Nat.succ_le_of_lt hrequest.1)]
  have hmiddle : request.copy + copies *
      (physicalEntryCode (request.node, request.state) + entryCapacity M J n * request.pass) <
        copies * (entryCapacity M J n * passes) := by
    nlinarith only [hrequest.2.1, Nat.mul_le_mul_left copies (Nat.succ_le_of_lt hinner)]
  unfold code capacity
  nlinarith only [hrequest.2.2, Nat.mul_le_mul_left (T + S + 1) (Nat.succ_le_of_lt hmiddle)]

end PhysicalTableRequest
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
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

 theorem code_bound {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < capacity M J ny passes copies T S := by
  cases request with
  | inl entry =>
    have h := physicalEntryCode_bound hM entry
    change physicalEntryCode entry < PhysicalTableRequest.entryCapacity M J ny at h
    simp only [code, capacity]
    omega
  | inr request =>
    have h := PhysicalTableRequest.code_bound hM passes copies T S request.val request.property
    simp only [code, capacity]
    omega

 theorem code_fits {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < 2 ^ bits M J ny passes copies T S :=
  (code_bound hM request).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local recurrence equalities identify the complete table semantics
of a lazy query program. No complete table is evaluated by the memo
interpreter; it is used only as the mathematical specification. -/

namespace EditApproximation

theorem rankedMemoEvaluate_specification {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (expected : κ → ℚ)
    (hstep : ∀ key, (program key).value (fun child => expected child.val) = expected key)
    (bits : ℕ) (encode : κ → ℕ) (hinjective : Function.Injective encode)
    (hbounded : ∀ key, encode key < 2 ^ bits) (key : κ) :
    (rankedMemoEvaluate rank program bits encode key .empty).value = expected key :=
  (rankedMemoEvaluate_empty rank program bits encode hinjective hbounded key).trans
    (rankedProgramValue_eq rank program expected hstep key)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedProgramRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict a well-founded query program to its proved finite key domain.
Values, executed read lists and weighted read costs are preserved. -/

namespace EditApproximation

 theorem restrictRankedProgram_value {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (P : κ → Prop) [DecidablePred P] (expected : κ → ℚ) (key : {key // P key})
    (hvalid : ∀ child ∈ (program key.val).keys (fun child => expected child.val), P child.val) :
    (restrictRankedProgram rank program P key).value (fun child => expected child.val.val) =
      (program key.val).value (fun child => expected child.val) := by
  unfold restrictRankedProgram
  rw [FiniteQuery.mapKeys_value]
  exact FiniteQuery.restrict_value _ _ _ hvalid

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalBoundedQuery
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global read program stays within the bounded cache-key
domain. Restricting its type therefore preserves the complete local-pass
value and gives an injectively encoded memo evaluator. -/

namespace EditApproximation

section Bounded

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem physicalBoundedQuery_value
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value
        (fun child => localRequestValue source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial child.val.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val := by
  unfold physicalBoundedQuery
  rw [restrictRankedProgram_value _ _ _ _ request
    (physicalGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request.val request.property _)]
  exact physicalGlobalQuery_value source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial request.val

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedGlobalQuery
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The global lazy program exposes coarse entries as ordinary memo requests.
Warmup uses these explicit seed reads; positive internal refinement uses the
proved finite table query, whose data reads are all earlier table entries. -/

namespace EditApproximation





section Global

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

theorem chargedGlobalQuery_value (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    chargedRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta group integer initial request := by
  cases request with
  | inl entry => rfl
  | inr parent =>
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val
    unfold chargedGlobalQuery
    dsimp only
    split_ifs with hi hd hw
    · exact chargedWarmupQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent hi
    · rw [localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val (Or.inr hw)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)
    · rw [FiniteQuery.mapKeys_value]
      exact physicalBoundedQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent
    · rw [localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val (Or.inl hd)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)

theorem chargedMemoEvaluate_value (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value =
    chargedRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta group integer initial request := by
  unfold chargedMemoEvaluate
  exact rankedMemoEvaluate_specification ChargedPhysicalRequest.rank
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedGlobalQuery_value source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    _ _ (ChargedPhysicalRequest.code_injective hM) (ChargedPhysicalRequest.code_fits hM) request

end Global

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveSeedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fresh streams indexed by every possible incoming seed make adaptive
seed-dependent draw types compatible with a single finite product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_integral_test {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (test : Ω → Prop) [DecidablePred test] :
    (∫ ω, if test ω then (1 : ℝ) else 0 ∂μ) = μ.real {ω | test ω} := by
  have h := integral_indicator_one (μ := μ) (Set.toFinite {ω | test ω}).measurableSet
  simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_AdaptiveMarginalLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adaptive passes need the correct marginal for the actual incoming
seed. Independence between unused, counterfactual seed-indexed draws is
unnecessary. This permits one common keyed random source. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Marginal

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : Seed → Type*} [∀ seed, Fintype (Draw seed)]
  [∀ seed, MeasurableSpace (Draw seed)] [∀ seed, MeasurableSingletonClass (Draw seed)]
  (drawLaw : ∀ seed, Measure (Draw seed)) [∀ seed, IsProbabilityMeasure (drawLaw seed)]
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (randomLaw : Measure Ω) [IsProbabilityMeasure randomLaw]
  (sample : ∀ seed, Ω → Draw seed)
  (hmarginal : ∀ seed, randomLaw.map (sample seed) = drawLaw seed)

include hmarginal in
/-- The common random source can correlate draws for distinct hypothetical
incoming seeds; only its independence from the actual incoming seed matters. -/
theorem adaptiveSeedLaw_eq_of_marginals (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (next : ∀ seed, Draw seed → Seed) :
    (incoming.prod randomLaw).map
        (fun pair : Seed × Ω => next pair.1 (sample pair.1 pair.2)) =
      adaptiveSeedLaw drawLaw incoming next := by
  classical
  apply Measure.ext
  intro event hevent
  apply (measureReal_eq_measureReal_iff).mp
  rw [adaptiveSeedLaw, map_measureReal_apply (measurable_of_finite _) hevent,
    map_measureReal_apply (measurable_of_finite _) hevent]
  change (incoming.prod randomLaw).real
      {pair : Seed × Ω | next pair.1 (sample pair.1 pair.2) ∈ event} =
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | next pair.1 (pair.2 pair.1) ∈ event}
  rw [← finite_integral_test (incoming.prod randomLaw)
      (fun pair : Seed × Ω => next pair.1 (sample pair.1 pair.2) ∈ event),
    ← finite_integral_test (incoming.prod (Measure.pi drawLaw))
      (fun pair : Seed × (∀ seed, Draw seed) => next pair.1 (pair.2 pair.1) ∈ event)]
  rw [integral_prod _ (.of_finite), integral_prod _ (.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with seed
  have hmap := integral_map (μ := randomLaw) (φ := sample seed)
    (measurable_of_finite _).aemeasurable
    (f := fun draw => if next seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [hmarginal seed] at hmap
  rw [← hmap]
  symm
  exact integral_comp_eval (μ := drawLaw) (i := seed)
    (f := fun draw => if next seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable

include hmarginal in
/-- The same replacement preserves the final integer answer law, rather
than only a seed transition. -/
theorem adaptiveAnswerLaw_eq_of_marginals (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (answer : ∀ seed, Draw seed → ℕ) :
    (incoming.prod randomLaw).map
        (fun pair : Seed × Ω => answer pair.1 (sample pair.1 pair.2)) =
      (incoming.prod (Measure.pi drawLaw)).map
        (fun pair : Seed × (∀ seed, Draw seed) => answer pair.1 (pair.2 pair.1)) := by
  classical
  apply Measure.ext
  intro event hevent
  apply (measureReal_eq_measureReal_iff).mp
  rw [map_measureReal_apply (measurable_of_finite _) hevent,
    map_measureReal_apply (measurable_of_finite _) hevent]
  change (incoming.prod randomLaw).real
      {pair : Seed × Ω | answer pair.1 (sample pair.1 pair.2) ∈ event} =
    (incoming.prod (Measure.pi drawLaw)).real
      {pair : Seed × (∀ seed, Draw seed) | answer pair.1 (pair.2 pair.1) ∈ event}
  rw [← finite_integral_test (incoming.prod randomLaw)
      (fun pair : Seed × Ω => answer pair.1 (sample pair.1 pair.2) ∈ event),
    ← finite_integral_test (incoming.prod (Measure.pi drawLaw))
      (fun pair : Seed × (∀ seed, Draw seed) => answer pair.1 (pair.2 pair.1) ∈ event)]
  rw [integral_prod _ (.of_finite), integral_prod _ (.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with seed
  have hmap := integral_map (μ := randomLaw) (φ := sample seed)
    (measurable_of_finite _).aemeasurable
    (f := fun draw => if answer seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [hmarginal seed] at hmap
  rw [← hmap]
  symm
  exact integral_comp_eval (μ := drawLaw) (i := seed)
    (f := fun draw => if answer seed draw ∈ event then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable

end Marginal

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonSeedTrace
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Adaptive seed passes driven by common per-pass random sources. The
trace stores one source for the actual pass, with no seed-indexed family.
Its returned seed has the original adaptive law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Common

variable {Seed : Type} [Fintype Seed] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  {Draw : ℕ → Seed → Type} [∀ pass seed, Fintype (Draw pass seed)]
  [∀ pass seed, MeasurableSpace (Draw pass seed)]
  [∀ pass seed, MeasurableSingletonClass (Draw pass seed)]
  {Ω : ℕ → Type} [∀ pass, Fintype (Ω pass)]
  [∀ pass, MeasurableSpace (Ω pass)] [∀ pass, MeasurableSingletonClass (Ω pass)]
  (drawLaw : ∀ pass seed, Measure (Draw pass seed))
  [∀ pass seed, IsProbabilityMeasure (drawLaw pass seed)]
  (randomLaw : ∀ pass, Measure (Ω pass)) [∀ pass, IsProbabilityMeasure (randomLaw pass)]
  (sample : ∀ pass seed, Ω pass → Draw pass seed)
  (next : ∀ pass seed, Draw pass seed → Seed)

theorem commonTraceLaw_map (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (hmarginal : ∀ pass seed, (randomLaw pass).map (sample pass seed) = drawLaw pass seed)
    (passes : ℕ) :
    (commonTraceLaw randomLaw incoming passes).map (commonTraceValue sample next passes) =
      adaptiveSeedSequence drawLaw incoming next passes := by
  induction passes with
  | zero => exact Measure.map_id
  | succ pass ih =>
    let reindex : CommonSeedTrace Seed Ω pass × Ω pass → Seed × Ω pass :=
      Prod.map (commonTraceValue sample next pass) id
    let step : Seed × Ω pass → Seed := fun pair => next pass pair.1 (sample pass pair.1 pair.2)
    have hvalue : commonTraceValue sample next (pass + 1) = step ∘ reindex := rfl
    have hproduct : ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)).map reindex =
        ((commonTraceLaw randomLaw incoming pass).map (commonTraceValue sample next pass)).prod
          (randomLaw pass) := by
      simpa only [Measure.map_id] using
        (Measure.map_prod_map (commonTraceLaw randomLaw incoming pass) (randomLaw pass)
          (measurable_of_finite (commonTraceValue sample next pass)) measurable_id).symm
    change ((commonTraceLaw randomLaw incoming pass).prod (randomLaw pass)).map _ = _
    rw [hvalue, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hproduct, ih]
    exact adaptiveSeedLaw_eq_of_marginals (drawLaw pass) (randomLaw pass) (sample pass)
      (hmarginal pass) (adaptiveSeedSequence drawLaw incoming next pass) (next pass)

end Common

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteKeyRestriction
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalNodeFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalScalarIndexFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting independent finite key streams preserves their exact
product law. Unused keys need not be allocated by a lazy implementation. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_restrict_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key) :
    (Measure.pi mu).map (fun draw k => draw (key k)) =
      Measure.pi (fun k => mu (key k)) := by
  have hindependent : iIndepFun (fun i (draw : ∀ j, X j) => draw i) (Measure.pi mu) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hrestricted := hindependent.precomp hinjective
  have hmap := hrestricted.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (key k)).aemeasurable)
  simpa only [(measurePreserving_eval mu _).map_eq] using hmap

theorem finite_pi_restrict_image_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : κ → Type*} [∀ k, MeasurableSpace (Y k)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (key : κ → ι) (hinjective : Function.Injective key)
    (image : ∀ k, X (key k) → Y k) (himage : ∀ k, Measurable (image k)) :
    (Measure.pi mu).map (fun draw k => image k (draw (key k))) =
      Measure.pi (fun k => (mu (key k)).map (image k)) := by
  have hrestrict := finite_pi_restrict_map mu key hinjective
  have hproject : Measurable (fun draw : ∀ i, X i => fun k => draw (key k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (key k))
  have htransform : Measurable (fun draw : ∀ k, X (key k) => fun k => image k (draw k)) :=
    Measurable.of_eval (fun k => (himage k).comp (measurable_pi_apply k))
  refine (Measure.map_map htransform hproject).symm.trans ?_
  rw [hrestrict]
  exact Measure.pi_map_pi (fun k => (himage k).aemeasurable)

theorem finite_uniform_array_cast (R n m : ℕ) [NeZero n] [NeZero m] (h : n = m) :
    (Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin n)).toMeasure)).map
      (fun draw t => Fin.cast h (draw t)) =
    Measure.pi (fun _ : Fin R => (PMF.uniformOfFintype (Fin m)).toMeasure) := by
  subst m
  simp only [Fin.cast_refl, id_eq, Measure.map_id']

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCommonSource
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual bounded physical program can share one source universe
across incoming seed tables. Online coordinates include their requested
range; group coordinates share whole-cell arrays. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



section Selection

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T exponent H Q R B : ℕ) (tau : ℚ)
  (hbound : ∀ key, physicalLocalOnlineMass source target U N P F A T exponent H tau key ≤ B)

omit [NeZero M] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem physicalCommonSelectedKey_injective : Function.Injective
    (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right => exact congrArg Sum.inl (congrArg Prod.fst (Sum.inl.inj heq))
    | inr right => exact False.elim (Sum.inl_ne_inr heq)
  | inr left =>
    cases right with
    | inl right => exact False.elim (Sum.inr_ne_inl heq)
    | inr right => exact congrArg Sum.inr (Sum.inr.inj heq)

theorem physicalCommonSample_law :
    (physicalCommonLaw M J N target.length exponent F Q R B).map
        (physicalCommonSample source target U N P F A T exponent H Q R B tau hbound) =
      physicalLocalProgramDrawLaw (R := R) source target U N P F A T exponent H Q tau := by
  have h := finite_pi_restrict_image_map
    (physicalCommonCoordinateLaw M J N target.length exponent F Q R B)
    (physicalCommonSelectedKey source target U N P F A T exponent H B tau hbound)
    (physicalCommonSelectedKey_injective source target U N P F A T exponent H B tau hbound)
    (physicalCommonCoordinateImage source target U N P F A T exponent H Q R B tau hbound)
    (fun _ => measurable_of_finite _)
  refine h.trans ?_
  unfold physicalLocalProgramDrawLaw
  congr 1
  funext key
  cases key with
  | inl online =>
    exact finite_uniform_array_cast R _ _
      (physicalCommonSelectedOnlineKey_range source target U N P F A T exponent H B tau hbound online)
  | inr group => exact Measure.map_id

end Selection

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonSeed
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete common-source seed passes. The sampler range cap is proved
for every seed; no good-seed event is used to define or bound the draws. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section CommonSeed

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

omit [NeZero R] in
theorem localCommonSample_law (hP : 0 < P) (pass : ℕ) (seed : Seed) :
    (localCommonDrawLaw (M := M) (J := J) (R := R) target N P H).map
        (localCommonSample source target N P T H hP pass seed) =
      localScheduledSeedDrawLaw (R := R) source target N P T H pass seed := by
  have h := Measure.pi_map_pi (μ := fun _ : Fin (H ^ 2) =>
    physicalCommonLaw M J N target.length thetaExponent ell (ell ^ 80) R cap)
    (fun _ => (measurable_of_finite
      (physicalCommonSample source target (clampedSeedNat seed) N P ell
        (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
        (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
          (scheduledSeedFactor N pass) T thetaExponent H tau hP))).aemeasurable)
  refine h.trans ?_
  congr 1
  funext copy
  exact physicalCommonSample_law source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N pass) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N pass) T thetaExponent H tau hP)

theorem localCommonSeed_law (hP : 0 < P) (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (passes : ℕ) :
    (localCommonTraceLaw (M := M) (J := J) (R := R) target N P H incoming passes).map
        (localCommonSeed source target N P T S H hP passes) =
      localScheduledSeedLaw (R := R) source target N P T S H incoming passes := by
  classical
  exact commonTraceLaw_map (localScheduledSeedDrawLaw (R := R) source target N P T H)
    (fun _ => localCommonDrawLaw (M := M) (J := J) (R := R) target N P H)
    (localCommonSample source target N P T H hP)
    (localScheduledSeedNext (R := R) source target N P T S H) incoming
    (localCommonSample_law source target N P T H hP) passes

end CommonSeed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceProgram
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extract the actual per-pass streams from a finite adaptive draw trace.
Earlier-pass streams are preserved when a new draw is appended, and the
lazy program's seed recurrence is exactly the trace's returned table. -/

namespace EditApproximation

theorem localSeedSequence_streams_congr {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
    (source target : List α) (N P F exponent H Q T S copies : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
    (group group' : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer integer' : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ →
      TargetInterval target.length → ℕ)
    (initial : PhysicalEntry M J target.length → ℕ) (pass : ℕ)
    (hgroup : ∀ p < pass, group p = group' p)
    (hinteger : ∀ p < pass, integer p = integer' p) :
    localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass =
      localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group' integer' initial pass := by
  induction pass with
  | zero => rfl
  | succ pass ih =>
    have hprev := ih (fun p hp => hgroup p (by omega)) (fun p hp => hinteger p (by omega))
    simp only [localSeedSequence, hprev, localPassValue, hgroup pass (by omega), hinteger pass (by omega)]

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

theorem localTraceSeed_succ (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1)) :
    localTraceSeed source target N P T S H (passes + 1) trace =
      localScheduledSeedNext source target N P T S H passes
        (localTraceSeed source target N P T S H passes trace.1)
        (trace.2 (localTraceSeed source target N P T S H passes trace.1)) := rfl

theorem localTraceGroup_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (pass : ℕ) (hpass : pass < passes) :
    localTraceGroup source target N P T S H (passes + 1) trace pass =
      localTraceGroup source target N P T S H passes trace.1 pass := by
  funext copy node time
  simp only [localTraceGroup, ite_eq_right (show pass ≠ passes by omega)]

theorem localTraceInteger_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (pass : ℕ) (hpass : pass < passes) :
    localTraceInteger source target N P T S H (passes + 1) trace pass =
      localTraceInteger source target N P T S H passes trace.1 pass := by
  funext copy
  simp only [localTraceInteger, ite_eq_right (show pass ≠ passes by omega)]

theorem localTracePassValue (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1))
    (copy : Fin (H ^ 2)) (node : PhysicalNode M J) (t : ℕ)
    (q : TargetInterval target.length) :
    localPassValue source target N P ell thetaExponent H (ell ^ 80) T
      (scheduledSeedFactor N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
      passes copy.val node t q =
    physicalLocalJointValue source target
      (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
      N P ell (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) tau eta kappa delta
      (trace.2 (localTraceSeed source target N P T S H passes trace.1) copy) node t q := by
  simp only [localPassValue, localTraceGroup, localTraceInteger, ite_true, if_true, dite_eq_left copy.isLt,
    physicalLocalJointValue]

theorem localTraceSeed_eq : ∀ (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H passes),
    localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H passes trace)
      (localTraceInteger source target N P T S H passes trace)
      (clampedSeedNat (localTraceInitial source target N P T H passes trace)) passes =
    clampedSeedNat (localTraceSeed source target N P T S H passes trace) := by
  intro passes
  induction passes with
  | zero => intro trace; rfl
  | succ passes ih =>
    intro trace
    have hprevious := localSeedSequence_streams_congr source target N P ell thetaExponent H (ell ^ 80)
      T S (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceGroup source target N P T S H passes trace.1)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H passes trace.1)
      (clampedSeedNat (localTraceInitial source target N P T H passes trace.1)) passes
      (localTraceGroup_before source target N P T S H passes trace)
      (localTraceInteger_before source target N P T S H passes trace)
    have hseed := hprevious.trans (ih trace.1)
    conv_lhs => rw [localSeedSequence]
    rw [show localTraceInitial source target N P T H (passes + 1) trace =
      localTraceInitial source target N P T H passes trace.1 from rfl]
    rw [hseed]
    rw [localTraceSeed_succ]
    funext state
    change min N (upperMedian (List.ofFn _)) =
      min N (upperMedian (List.ofFn fun copy : Fin (H ^ 2) =>
        ⌈(scheduledSeedMultiplier N passes : ℚ) * physicalLocalJointValue source target
          (clampedSeedNat (localTraceSeed source target N P T S H passes trace.1))
          N P ell (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) tau eta kappa delta
          (trace.2 (localTraceSeed source target N P T S H passes trace.1) copy) state.1 S state.2⌉₊))
    apply congrArg (fun values : Fin (H ^ 2) → ℕ => min N (upperMedian (List.ofFn values)))
    funext copy
    rw [localTracePassValue source target N P T S H passes trace copy state.1 S state.2]

theorem localTraceSeed_before (passes : ℕ)
    (trace : LocalScheduledTrace (M := M) (J := J) (R := R) source target N P T H (passes + 1)) :
    localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceInitial source target N P T H (passes + 1) trace)) passes =
    clampedSeedNat (localTraceSeed source target N P T S H passes trace.1) := by
  apply (localSeedSequence_streams_congr source target N P ell thetaExponent H (ell ^ 80)
    T S (H ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceGroup source target N P T S H passes trace.1)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H passes trace.1)
    (clampedSeedNat (localTraceInitial source target N P T H passes trace.1)) passes
    (localTraceGroup_before source target N P T S H passes trace)
    (localTraceInteger_before source target N P T S H passes trace)).trans
  exact localTraceSeed_eq source target N P T S H passes trace.1

end Trace

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonTrace
attribute [-instance] _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common keyed source gives a lazy functional view of the seed trace.
Only the actual incoming seed is selected during execution. -/

namespace EditApproximation

section Trace

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localCommonToScheduled_seed (hP : 0 < P) : ∀ (passes : ℕ)
    (trace : LocalCommonTrace (M := M) (J := J) (R := R) target N P H passes),
    localTraceSeed source target N P T S H passes
        (localCommonToScheduled source target N P T H hP passes trace) =
      localCommonSeed source target N P T S H hP passes trace := by
  intro passes
  induction passes with
  | zero => intro trace; rfl
  | succ passes ih =>
    intro trace
    change localScheduledSeedNext source target N P T S H passes
        (localTraceSeed source target N P T S H passes
          (localCommonToScheduled source target N P T H hP passes trace.1))
        (localCommonSample source target N P T H hP passes
          (localTraceSeed source target N P T S H passes
            (localCommonToScheduled source target N P T H hP passes trace.1)) trace.2) =
      localScheduledSeedNext source target N P T S H passes
        (localCommonSeed source target N P T S H hP passes trace.1)
        (localCommonSample source target N P T H hP passes
          (localCommonSeed source target N P T S H hP passes trace.1) trace.2)
    rw [ih]

end Trace

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalTraceMemoOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The bounded-key adaptive trace drives the actual charged memo program.
Its final root query has the same distribution as the local answer. The program
uses all previous-pass copies from the trace and one fresh terminal copy. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "eta" => RationalParameters.eta (rationalParameters ell)
local notation "kappa" => RationalParameters.kappa (rationalParameters ell)
local notation "delta" => RationalParameters.delta (rationalParameters ell)
local notation "tau" => RationalParameters.tau (rationalParameters ell)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localTraceMemoResult_value (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    ((localTraceMemoResult source target N P T S H hH rootQ outcome).value : ℝ) =
      freshSeedValue (localFinalProgramValue (R := R) source target N P T S H rootQ)
        (localTraceFinalProjection source target N P T S H outcome) := by
  let trace := localTraceAppendFinal source target N P T H outcome
  unfold localTraceMemoResult
  rw [chargedMemoEvaluate_value source target N P ell thetaExponent H (ell ^ 80) T S (passes + 1) (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))]
  change (localRequestValue source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
    (localTraceGroup source target N P T S H (passes + 1) trace)
    (localTraceInteger source target N P T S H (passes + 1) trace)
    (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1))
    (PhysicalTableRequest.refinement passes 0
      (Sigma.mk (Fin.mk 0 (Nat.zero_lt_succ J)) PUnit.unit) T S rootQ) : ℝ) = _
  rw [localRequestValue_refinement]
  have hseed := localTraceSeed_before source target N P T S H passes trace
  change localSeedSequence source target N P ell thetaExponent H (ell ^ 80) T S (H ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) tau eta kappa delta
      (localTraceGroup source target N P T S H (passes + 1) trace)
      (localTraceInteger source target N P T S H (passes + 1) trace)
      (clampedSeedNat (localTraceInitial source target N P T H passes outcome.1)) passes = _ at hseed
  rw [hseed]
  rw [localTracePassValue source target N P T S H passes trace ⟨0, pow_pos hH 2⟩]
  rfl

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localTraceMemoAnswer_eq (hH : 0 < H) (rootQ : TargetInterval target.length)
    (outcome : LocalTraceFinalOutcome (M := M) (J := J) (R := R) source target N P T H) :
    localTraceMemoAnswer source target N P T S H hH rootQ outcome =
      localFinalProgramAnswer (R := R) source target N P T S H rootQ
        (localTraceFinalProjection source target N P T S H outcome) := by
  unfold localTraceMemoAnswer localFinalProgramAnswer
  rw [localTraceMemoResult_value]

end Output

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalCommonOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged memo answer under one common random source per pass and
one fresh terminal source. Correct marginal laws suffice; hypothetical
seed-indexed draw families are not part of the execution. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  [NeZero M] [NeZero R] [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
  (source target : List α) (N P T S H : ℕ)

local notation "Seed" => ClampedPhysicalSeed M J target.length N
local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "thetaExponent" => (40 * smallLogExponent N : ℕ)
local notation "tau" => RationalParameters.tau (rationalParameters ell)
local notation "cap" => localOnlineMassBound M P H

omit [NeZero R] in
theorem localCommonTerminalSample_law (hP : 0 < P) (seed : Seed) :
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H).map
        (localCommonTerminalSample source target N P T H hP seed) =
      localFinalProgramDrawLaw (R := R) source target N P T H seed :=
  physicalCommonSample_law source target (clampedSeedNat seed) N P ell
    (scheduledSeedFactor N passes) T thetaExponent H (ell ^ 80) R cap tau
    (physicalLocalOnlineMass_le source target (clampedSeedNat seed) N P ell
      (scheduledSeedFactor N passes) T thetaExponent H tau hP)

omit [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)] in
theorem localCommonMemoAnswer_eq (hP : 0 < P) (hH : 0 < H)
    (rootQ : TargetInterval target.length)
    (outcome : LocalCommonFinalOutcome (M := M) (J := J) (R := R) target N P H) :
    localCommonMemoAnswer source target N P T S H hP hH rootQ outcome =
      localFinalProgramAnswer (R := R) source target N P T S H rootQ
        (localCommonSeed source target N P T S H hP passes outcome.1,
          fun seed => localCommonTerminalSample source target N P T H hP seed outcome.2) := by
  rw [localCommonMemoAnswer, localTraceMemoAnswer_eq]
  unfold localTraceFinalProjection localCommonFinalToTrace
  rw [localCommonToScheduled_seed]

theorem localCommonMemoAnswer_law_oai (hP : 0 < P) (hH : 0 < H)
    (incoming : Measure Seed) [IsProbabilityMeasure incoming]
    (rootQ : TargetInterval target.length) :
    (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map
        (localCommonMemoAnswer source target N P T S H hP hH rootQ) =
      (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  classical
  let reindex := Prod.map (localCommonSeed (M := M) (J := J) (R := R) source target N P T S H hP passes)
    (id : LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H → _)
  let answer : Seed × LocalCommonTerminalDraw (M := M) (J := J) (R := R) target N P H → ℕ :=
    fun pair => localFinalProgramAnswer (R := R) source target N P T S H rootQ
      (pair.1, fun seed => localCommonTerminalSample source target N P T H hP seed pair.2)
  have hanswer : localCommonMemoAnswer (R := R) source target N P T S H hP hH rootQ =
      answer ∘ reindex := by
    funext outcome
    exact localCommonMemoAnswer_eq source target N P T S H hP hH rootQ outcome
  have hproduct :
      (localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming).map reindex =
        (localScheduledSeedLaw (R := R) source target N P T S H incoming passes).prod
          (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H) := by
    unfold localCommonFinalLaw
    rw [show reindex = Prod.map (localCommonSeed (M := M) (J := J) (R := R) source target N P T S H hP passes) id from rfl]
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id,
      Measure.map_id, localCommonSeed_law]
  rw [hanswer, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hproduct]
  unfold localFinalProgramLaw
  change _ = (Measure.map (fun pair : LocalFinalProgramOutcome
    (M := M) (J := J) (R := R) source target N P T H =>
    if source = substring target rootQ.lo rootQ.hi then 0 else
      integerAnswer N (localFinalProgramValue (R := R) source target N P T S H rootQ
        pair.1 (pair.2 pair.1))) _)
  convert (adaptiveAnswerLaw_eq_of_marginals
    (localFinalProgramDrawLaw (R := R) source target N P T H)
    (localCommonTerminalLaw (M := M) (J := J) (R := R) target N P H)
    (localCommonTerminalSample source target N P T H hP)
    (localCommonTerminalSample_law source target N P T H hP)
    (localScheduledSeedLaw (R := R) source target N P T S H incoming passes)
    (fun seed draw => if source = substring target rootQ.lo rootQ.hi then 0 else
      integerAnswer N (localFinalProgramValue (R := R) source target N P T S H rootQ seed draw))) using 1
  · rfl

end Output

end EditApproximation

end OAI
end

theorem solution.{u_1} : type_of% @OAI.EditApproximation.localCommonMemoAnswer_law_oai.{u_1} := @OAI.EditApproximation.localCommonMemoAnswer_law_oai.{u_1}
