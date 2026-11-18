-- Prove2me | solution 1 for OAI.EditApproximation.integerBinarySpaceFootprint_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:02:28.571347+00:00
-- url     : https://prove2.me/submissions/f9162dff-181b-4840-8cea-3dd09f8d7420

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_EditApproxScheme_17
import Definitions.Def_OAIQ361V3Ea004

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_Footprint
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI.EditApproximation.BitQuery

/- The allocation trace of a query, without a proof relating allocations to work.
The trace retains every allocation and every adaptive continuation. -/


namespace Footprint





















theorem runCells_congr {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells otherCells : ι → BinaryMemo BinaryFraction → ℕ)
    (h : ∀ key memory, childCells key memory = otherCells key memory)
    {program : BitQuery ι BinaryFraction} (heap : Footprint program)
    (memory : BinaryMemo BinaryFraction) :
    heap.runCells ask childCells memory = heap.runCells ask otherCells memory := by
  induction heap generalizing memory with
  | done => rfl
  | read key next continuation ih => simp only [runCells, h, ih]
  | charge localCells next ih => simp only [runCells, ih]

end Footprint

namespace Heap

private theorem map_decidable_cases {p : Prop} (d : Decidable p) {α β : Sort*}
    (f : α → β) (no : ¬p → α) (yes : p → α) :
    f (Decidable.casesOn d no yes) =
      Decidable.casesOn d (fun h => f (no h)) (fun h => f (yes h)) := by
  cases d <;> rfl

private theorem footprint_mpr_congr {ι β : Type*} {p q : BitQuery ι β}
    (eqn : p = q) (a : Heap q) (b : Footprint q) (hab : a.footprint = b) :
    ((congrArg Heap eqn).mpr a).footprint = (congrArg Footprint eqn).mpr b := by
  cases eqn
  exact hab

@[simp] theorem footprint_restrictWithWork {ι : Type*} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (test key).2)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) :
    (heap.restrictWithWork P test htest allocation ha).footprint =
      heap.footprint.restrictWithWork P test htest allocation := by
  induction heap with
  | done => rfl
  | charge localCells bound next ih =>
    exact congrArg (Footprint.charge localCells) ih
  | read key next continuation ih =>
    simp only [footprint_read]
    unfold restrictWithWork Footprint.restrictWithWork
    apply congrArg (Footprint.charge (allocation key))
    rw [map_decidable_cases (f := footprint)]
    congr 1
    · funext h
      apply footprint_mpr_congr (dite_eq_right h)
      exact ih (BinaryFraction.nat 0)
    · funext h
      apply footprint_mpr_congr (dite_eq_left h)
      apply congrArg (Footprint.read _ _)
      funext word
      exact ih word

@[simp] theorem footprint_rankedBitMemoCells {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) :
    Footprint.rankedBitMemoCells rank program (fun key => (heap key).footprint)
      bits encode addressCells key memory =
      EditApproximation.rankedBitMemoCells rank program heap bits encode addressCells key memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      Footprint.rankedBitMemoCells rank program (fun key => (heap key).footprint)
        bits encode addressCells key memory =
        EditApproximation.rankedBitMemoCells rank program heap bits encode addressCells key memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [Footprint.rankedBitMemoCells, EditApproximation.rankedBitMemoCells]
      cases hf : (memory.lookupCosted (binaryMemoKey bits (encode key))).1 with
      | some value => rfl
      | none =>
        dsimp only
        congr 1
        rw [← footprint_runCells]
        apply Footprint.runCells_congr
        intro child previous
        exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
  exact hall (rank key) key rfl memory

end Heap
end OAI.EditApproximation.BitQuery
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_ConcreteFootprintBridges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation

universe u_1 u_2

private theorem footprint_cases {ι β : Type*} {program : BitQuery ι β}
    {p : Prop} (d : Decidable p) (no : ¬p → BitQuery.Heap program)
    (yes : p → BitQuery.Heap program) :
    (Decidable.casesOn (motive := fun _ => BitQuery.Heap program) d no yes).footprint =
      Decidable.casesOn (motive := fun _ => BitQuery.Footprint program) d
        (fun h => (no h).footprint) (fun h => (yes h).footprint) := by
  cases d <;> rfl

private theorem cases_congr {p : Prop} (d : Decidable p) {α : Sort*}
    {no otherNo : ¬p → α} {yes otherYes : p → α}
    (hn : ∀ h, no h = otherNo h) (hy : ∀ h, yes h = otherYes h) :
    Decidable.casesOn (motive := fun _ => α) d no yes =
      Decidable.casesOn (motive := fun _ => α) d otherNo otherYes := by
  cases d with
  | isFalse h => exact hn h
  | isTrue h => exact hy h

private theorem footprint_congr_seven {α₁ : Sort*} {α₂ : Sort*} {α₃ : Sort*} {α₄ : Sort*}
    {α₅ : Sort*} {α₆ : Sort*} {α₇ : Sort*} {β : Sort*}
    {f : α₁ → α₂ → α₃ → α₄ → α₅ → α₆ → α₇ → β}
    {a₁ b₁ : α₁} {a₂ b₂ : α₂} {a₃ b₃ : α₃} {a₄ b₄ : α₄}
    {a₅ b₅ : α₅} {a₆ b₆ : α₆} {a₇ b₇ : α₇}
    (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃) (h₄ : a₄ = b₄)
    (h₅ : a₅ = b₅) (h₆ : a₆ = b₆) (h₇ : a₇ = b₇) :
    f a₁ a₂ a₃ a₄ a₅ a₆ a₇ = f b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  cases h₁; cases h₂; cases h₃; cases h₄; cases h₅; cases h₆; cases h₇
  rfl

private theorem footprint_mpr_congr {ι β : Type*} {p q : BitQuery ι β}
    (eqn : p = q) (a : BitQuery.Heap q) (b : BitQuery.Footprint q)
    (hab : a.footprint = b) :
    ((congrArg BitQuery.Heap eqn).mpr a).footprint =
      (congrArg BitQuery.Footprint eqn).mpr b := by
  cases eqn
  exact hab

private theorem footprint_groupTransport (M J N n exponent F Q R B b c : ℕ) (h : b = c)
    (actual : BitPhysicalGroupQueries M J N n exponent F Q R B b)
    (heap : ∀ s j, BitQuery.Heap (actual s j))
    (footprint : ∀ s j, BitQuery.Footprint (actual s j))
    (hfp : ∀ s j, (heap s j).footprint = footprint s j) :
    ∀ s j, (groupHeapTransportBridge M J N n exponent F Q R B b c h actual heap s j).footprint =
      groupFootprintTransportBridge M J N n exponent F Q R B b c h actual footprint s j := by
  cases h
  intro s j
  exact hfp s j

-- Supply case arguments directly so inference does not normalize indexed branch values.
universe u

private theorem heq_decidable_cases_from {p : Prop} (left right : Decidable p → Sort u)
    {α β : Sort u} (outerLeft : α) (outerRight : β)
    (leftNo : ∀ h : ¬p, left (.isFalse h)) (leftYes : ∀ h : p, left (.isTrue h))
    (rightNo : ∀ h : ¬p, right (.isFalse h)) (rightYes : ∀ h : p, right (.isTrue h))
    (decision : Decidable p)
    (hleft : HEq outerLeft (Decidable.casesOn (motive := left) decision leftNo leftYes))
    (hright : HEq (Decidable.casesOn (motive := right) decision rightNo rightYes) outerRight)
    (hn : ∀ h, HEq (leftNo h) (rightNo h)) (hy : ∀ h, HEq (leftYes h) (rightYes h)) :
    HEq outerLeft outerRight := by
  refine hleft.trans ?_
  refine HEq.trans ?_ hright
  cases decision with
  | isFalse h => exact hn h
  | isTrue h => exact hy h

set_option maxHeartbeats 2000000
private theorem heq_mpr_both {α β γ δ : Sort u} (leftEq : α = β) (rightEq : γ = δ)
    (left : β) (right : δ) (h : HEq left right) : HEq (leftEq.mpr left) (rightEq.mpr right) := by
  cases leftEq
  cases rightEq
  exact h

@[simp] theorem queryPhysicalEarlierReadHeap_footprint :
    ∀ {M J n : Nat} (copies pass copy T S t : Nat) (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (q : OAI.EditApproximation.TargetInterval n)
  (input : Prod.{0, 0} (Fin M) (Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval n))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S child)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
            (@OAI.EditApproximation.PhysicalTableRequest.refinement M J n pass copy node T t q)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalEarlierRead M J n copies pass copy T S t node hbelow q input))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S child)
          (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
            (@OAI.EditApproximation.PhysicalTableRequest.refinement M J n pass copy node T t q)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalEarlierRead M J n copies pass copy T S t node hbelow q input)
      (@OAI.EditApproximation.queryPhysicalEarlierReadHeap M J n copies pass copy T S t node hbelow q input))
    (@OAI.EditApproximation.queryPhysicalEarlierReadFootprint M J n copies pass copy T S t node hbelow q input) := by
  intros
  unfold queryPhysicalEarlierReadHeap queryPhysicalEarlierReadFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  with_unfolding_all apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    rfl
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    apply queryPhysicalTableReadHeap_footprint

@[simp] theorem queryPhysicalRandomDataRequestHeap_footprint :
    ∀ {σ : Type u_1} {α : Type u_2} (source target : List.{u_2} α) {M J : Nat}
  [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M] (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (copies pass copy T S t : Nat)
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
  (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (readGroup :
    OAI.EditApproximation.GroupScalarKey M F Q →
      OAI.EditApproximation.BitQuery.{u_1, 0} σ OAI.EditApproximation.BinaryFraction)
  (readInteger :
    Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target)) →
      Nat → OAI.EditApproximation.BitQuery.{u_1, 0} σ OAI.EditApproximation.BinaryFraction)
  (q : OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))
  (hg :
    (key : OAI.EditApproximation.GroupScalarKey M F Q) →
      @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readGroup key))
  (hz :
    (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_2} α target))) →
      (range : Nat) →
        @OAI.EditApproximation.BitQuery.Heap.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readInteger key range)),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_2} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_2} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalRandomDataRequest.{u_1, u_2} σ α source target M J _inst N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_2} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_2} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_2} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalRandomDataRequest.{u_1, u_2} σ α source target M J _inst N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q)
      (@OAI.EditApproximation.queryPhysicalRandomDataRequestHeap.{u_1, u_2} σ α source target M J _inst N P F exponent H
        Q eM eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q hg hz))
    (@OAI.EditApproximation.queryPhysicalRandomDataRequestFootprint.{u_1, u_2} σ α source target M J _inst N P F exponent
      H Q eM eF hP hM hF tau a eta kappa delta copies pass copy T S t ht node hbelow readGroup readInteger q
      (fun key =>
        @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} σ OAI.EditApproximation.BinaryFraction (readGroup key)
          (hg key))
      fun key range =>
      @OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0} σ OAI.EditApproximation.BinaryFraction
        (readInteger key range) (hz key range)) := by
  intros
  unfold queryPhysicalRandomDataRequestHeap queryPhysicalRandomDataRequestFootprint queryPhysicalRandomDataRequest
  refine (queryLocalProgramHeap_footprint ..).trans ?_
  apply footprint_congr_seven
  all_goals funext input
  all_goals try funext range
  all_goals refine (BitQuery.Heap.footprint_mapKeysWithWork _ _ _ _).trans ?_
  all_goals apply congrArg (BitQuery.Footprint.mapKeysWithWork _ _)
  all_goals first
    | rfl
    | apply queryPhysicalTableReadHeap_footprint
    | apply queryPhysicalEarlierReadHeap_footprint
    | (refine (queryMeanReadHeap_footprint ..).trans ?_; congr 1)

@[simp] theorem queryPhysicalScalarGroupQueriesHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R) (b : Nat)
  (cell : Prod.{0, 0} Nat Nat)
  (s : Fin (@List.length.{0} Rat (OAI.EditApproximation.groupDyadicScales M b (@Nat.cast.{0} Rat Rat.instNatCast F))))
  (j :
    Fin
      (OAI.EditApproximation.groupSampleCount M Q b
        (OAI.EditApproximation.groupDyadicScaleAt M b (@Nat.cast.{0} Rat Rat.instNatCast F) s))),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupQueries M J N n exponent F Q R B node time b cell s j)
      (OAI.EditApproximation.queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time b cell s j))
    (OAI.EditApproximation.queryPhysicalScalarGroupQueriesFootprint M J N n exponent F Q R B node time b cell s j) := by
  intro M J N n exponent F Q R B node time b cell s j
  have hbridge : (queryPhysicalScalarGroupQueriesHeap M J N n exponent F Q R B node time b cell s j).footprint =
      scalarGroupFootprintBridge M J N n exponent F Q R B node time b cell s j := by
    unfold queryPhysicalScalarGroupQueriesHeap scalarGroupFootprintBridge
    apply footprint_mpr_congr (congrArg
      (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
      (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell))
    dsimp only [id]
    rw [footprint_cases (instDecidableEqBool (queryScalePresentWithWork N b).1 true)]
    refine congrFun ?_ (instDecidableEqBool (queryScalePresentWithWork N b).1 true)
    funext decision
    cases decision with
    | isFalse h =>
        apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_right h))
        rfl
    | isTrue h =>
        apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_left h))
        rw [footprint_cases (instDecidableEqBool (queryCellValidWithWork n exponent cell).1 true)]
        refine congrFun ?_ (instDecidableEqBool (queryCellValidWithWork n exponent cell).1 true)
        funext decision
        cases decision with
        | isFalse h' =>
            apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_right h'))
            rfl
        | isTrue h' =>
            apply footprint_mpr_congr (congrArg (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j) (dite_eq_left h'))
            let key : PhysicalLocalGroupKey M J N n exponent :=
              (node, physicalScaleIndex N b ((queryScalePresentWithWork_value N b).mp h),
                ⟨cell.1, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp h').1⟩,
                ⟨cell.2, Nat.lt_succ_of_le ((queryCellValidWithWork_value n exponent cell).mp h').2⟩)
            with_unfolding_all
              apply footprint_groupTransport M J N n exponent F Q R B _ b
                (physicalScaleIndex_get N b ((queryScalePresentWithWork_value N b).mp h))
                (queryPhysicalScalarGroupQueriesAt M J N n exponent F Q R B key time)
            intro scale sample
            apply footprint_mpr_congr
              (queryPhysicalScalarGroupQueriesAt.eq_1 M J N n exponent F Q R B key time scale sample)
            apply queryPhysicalScalarReadHeap_footprint
  have hsame : queryPhysicalScalarGroupQueriesFootprint M J N n exponent F Q R B node time b cell s j =
      scalarGroupFootprintBridge M J N n exponent F Q R B node time b cell s j := by
    have heq_mpr_right {α β γ : Sort _} (eqn : α = β) (a : γ) (b : β) (hab : HEq a b) :
        HEq a (eqn.mpr b) := by
      cases eqn
      exact hab
    apply eq_of_heq
    unfold scalarGroupFootprintBridge
    apply heq_mpr_right (congrArg BitQuery.Footprint (congrArg
      (fun f : BitPhysicalGroupQueries M J N n exponent F Q R B b => f s j)
      (queryPhysicalScalarGroupQueries.eq_1 M J N n exponent F Q R B node time b cell)))
    unfold queryPhysicalScalarGroupQueriesFootprint
    refine heq_decidable_cases_from _ _ _ _ _ _ _ _ _ (heq_of_eq (id_eq _)) HEq.rfl ?hn ?hy
    case hn =>
      intro h
      refine heq_mpr_both _ _ _ _ ?_
      rfl
    case hy =>
      intro h
      refine heq_mpr_both _ _ _ _ ?_
      refine heq_decidable_cases_from _ _ _ _ _ _ _ _ _ HEq.rfl HEq.rfl ?hn ?hy
      case hn =>
        intro h'
        refine heq_mpr_both _ _ _ _ ?_
        rfl
      case hy =>
        intro h'
        refine heq_mpr_both _ _ _ _ ?_
        rfl
  exact hbridge.trans hsame.symm


@[simp] theorem queryPhysicalScalarGroupReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : OAI.EditApproximation.GroupScalarKey M F Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarGroupRead M J N n exponent F Q R B node time key)
      (OAI.EditApproximation.queryPhysicalScalarGroupReadHeap M J N n exponent F Q R B node time key))
    (OAI.EditApproximation.queryPhysicalScalarGroupReadFootprint M J N n exponent F Q R B node time key) := by
  intros
  simp [queryPhysicalScalarGroupReadHeap, queryPhysicalScalarGroupReadFootprint, queryPhysicalScalarGroupRead]

@[simp] theorem queryPhysicalScalarOnlineReadHeap_footprint :
    ∀ (M J N n exponent F Q R B : Nat) (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval n)) (range : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0} (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B)
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (OAI.EditApproximation.PhysicalScalarKey M J N n exponent F Q R B) OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.queryPhysicalScalarOnlineRead M J N n exponent F Q R B node time key range)
      (OAI.EditApproximation.queryPhysicalScalarOnlineReadHeap M J N n exponent F Q R B node time key range))
    (OAI.EditApproximation.queryPhysicalScalarOnlineReadFootprint M J N n exponent F Q R B node time key range) := by
  intro M J N n exponent F Q R B node time key range
  have hbridge : (queryPhysicalScalarOnlineReadHeap M J N n exponent F Q R B node time key range).footprint =
      scalarOnlineFootprintBridge M J N n exponent F Q R B node time key range := by
    unfold queryPhysicalScalarOnlineReadHeap scalarOnlineFootprintBridge
    apply footprint_mpr_congr
      (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases (instDecidableEqBool (queryScalePresentWithWork N key.1).1 true)]
    congr! (config := {closePre := false, closePost := false, sameFun := true}) 1
    · funext h
      apply footprint_mpr_congr (dite_eq_right h)
      rfl
    · funext h
      apply footprint_mpr_congr (dite_eq_left h)
      rw [footprint_cases (instDecidableEqBool (queryRangeValidWithWork B range).1 true)]
      congr! (config := {closePre := false, closePost := false, sameFun := true}) 1
      · funext h'
        apply footprint_mpr_congr (dite_eq_right h')
        rfl
      · funext h'
        apply footprint_mpr_congr (dite_eq_left h')
        apply queryPhysicalScalarReadHeap_footprint
  have hsame : queryPhysicalScalarOnlineReadFootprint M J N n exponent F Q R B node time key range =
      scalarOnlineFootprintBridge M J N n exponent F Q R B node time key range := by
    have heq_mpr_right {α β γ : Sort _} (eqn : α = β) (a : γ) (b : β) (hab : HEq a b) :
        HEq a (eqn.mpr b) := by
      cases eqn
      exact hab
    apply eq_of_heq
    unfold scalarOnlineFootprintBridge
    apply heq_mpr_right (congrArg BitQuery.Footprint
      (queryPhysicalScalarOnlineRead.eq_1 M J N n exponent F Q R B node time key range))
    unfold queryPhysicalScalarOnlineReadFootprint
    try dsimp (config := {beta := false, iota := false, proj := false}) only
    apply heq_of_eq
    apply congrArg (BitQuery.Footprint.chargeOf
      (queryScalePresentAllocation N key.1 + queryRangeValidAllocation B range))
    apply eq_of_heq
    refine heq_decidable_cases_from _ _ _ _ _ _ _ _ _ HEq.rfl HEq.rfl ?hn ?hy
    case hn =>
      intro h
      refine heq_mpr_both _ _ _ _ ?_
      rfl
    case hy =>
      intro h
      refine heq_mpr_both _ _ _ _ ?_
      refine heq_decidable_cases_from _ _ _ _ _ _ _ _ _ HEq.rfl HEq.rfl ?hn ?hy
      case hn =>
        intro h'
        refine heq_mpr_both _ _ _ _ ?_
        rfl
      case hy =>
        intro h'
        refine heq_mpr_both _ _ _ _ ?_
        rfl
  exact hbridge.trans hsame.symm

@[simp] theorem queryFamilyGroupReadHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} (target : List.{u_1} α) (N P F exponent H Q passes copies pass copy : Nat)
  (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : OAI.EditApproximation.GroupScalarKey M F Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyGroupRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyGroupRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key)
      (@OAI.EditApproximation.queryFamilyGroupReadHeap.{u_1} α M J R target N P F exponent H Q passes copies pass copy
        node time key))
    (@OAI.EditApproximation.queryFamilyGroupReadFootprint.{u_1} α M J R target N P F exponent H Q passes copies pass
      copy node time key) := by
  intros
  simp [queryFamilyGroupReadHeap, queryFamilyGroupReadFootprint, queryFamilyGroupRead]

@[simp] theorem queryFamilyOnlineReadHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} (target : List.{u_1} α) (N P F exponent H Q passes copies pass copy : Nat)
  (node : OAI.EditApproximation.PhysicalInternalNode M J) (time : Fin R)
  (key : Prod.{0, 0} Nat (OAI.EditApproximation.TargetInterval (@List.length.{u_1} α target))) (range : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyOnlineRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key range))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyOnlineRead.{u_1} α M J R target N P F exponent H Q passes copies pass copy node
        time key range)
      (@OAI.EditApproximation.queryFamilyOnlineReadHeap.{u_1} α M J R target N P F exponent H Q passes copies pass copy
        node time key range))
    (@OAI.EditApproximation.queryFamilyOnlineReadFootprint.{u_1} α M J R target N P F exponent H Q passes copies pass
      copy node time key range) := by
  intros
  simp [queryFamilyOnlineReadHeap, queryFamilyOnlineReadFootprint, queryFamilyOnlineRead]

@[simp] theorem queryRestrictPhysicalBodyHeap_footprint :
    ∀ {σ : Type u_1} {M J n : Nat} (passes copies T S : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (program :
    OAI.EditApproximation.BitQuery.{u_1, 0}
      (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
      OAI.EditApproximation.BinaryFraction)
  (heap :
    @OAI.EditApproximation.BitQuery.Heap.{u_1, 0}
      (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
      OAI.EditApproximation.BinaryFraction program),
  @Eq.{u_1 + 1}
    (@OAI.EditApproximation.BitQuery.Footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryRestrictPhysicalBody.{u_1} σ M J n passes copies T S parent program))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
      (Sum.{u_1, 0} σ
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J n T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J n)
                (fun r => @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r) parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryRestrictPhysicalBody.{u_1} σ M J n passes copies T S parent program)
      (@OAI.EditApproximation.queryRestrictPhysicalBodyHeap.{u_1} σ M J n passes copies T S parent program heap))
    (@OAI.EditApproximation.queryRestrictPhysicalBodyFootprint.{u_1} σ M J n passes copies T S parent program
      (@OAI.EditApproximation.BitQuery.Heap.footprint.{u_1, 0}
        (@OAI.EditApproximation.QueryPhysicalChild.{u_1} σ M J n passes copies T S parent)
        OAI.EditApproximation.BinaryFraction program heap)) := by
  intros
  simp [queryRestrictPhysicalBodyHeap, queryRestrictPhysicalBodyFootprint, queryRestrictPhysicalBody]

@[simp] theorem queryFamilyRefinementHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  (source target : List.{u_1} α) (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (passes copies pass copy T S t : Nat)
  (ht : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
  (node : OAI.EditApproximation.PhysicalNode M J)
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          node))
      J)
  (time : Fin R) (q : OAI.EditApproximation.TargetInterval (@List.length.{u_1} α target)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_1} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyRefinement.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@OAI.EditApproximation.PhysicalTableRequest.refinement M J (@List.length.{u_1} α target) pass copy node T
                t q))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyRefinement.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q)
      (@OAI.EditApproximation.queryFamilyRefinementHeap.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q))
    (@OAI.EditApproximation.queryFamilyRefinementFootprint.{u_1} α M J R _inst source target N P F exponent H Q eM eF hP
      hM hF tau a eta kappa delta passes copies pass copy T S t ht node hbelow time q) := by
  intros
  simp [queryFamilyRefinementHeap, queryFamilyRefinementFootprint, queryFamilyRefinement]

@[simp] theorem queryFamilyActiveHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{u_1} α)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (T S passes copies : Nat)
  (request : OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
  (hindex :
    @LT.lt.{0} Nat instLTNat T
      (@OAI.EditApproximation.PhysicalTableRequest.index M J (@List.length.{u_1} α target) request))
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          (@OAI.EditApproximation.PhysicalTableRequest.node M J (@List.length.{u_1} α target) request)))
      J),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S request)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta T S passes copies request hindex hbelow))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S child)
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S request)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP hM
        hF tau a eta kappa delta T S passes copies request hindex hbelow)
      (@OAI.EditApproximation.queryFamilyActiveHeap.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF hP
        hM hF tau a eta kappa delta T S passes copies request hindex hbelow))
    (@OAI.EditApproximation.queryFamilyActiveFootprint.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta T S passes copies request hindex hbelow) := by
  intros
  simp [queryFamilyActiveHeap, queryFamilyActiveFootprint, queryFamilyActive]

@[simp] theorem queryFamilyBoundedActiveHeap_footprint :
    ∀ {α : Type u_1} {M J R : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{u_1} α)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction) (T S passes copies : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        copies T S r)
  (hindex :
    @LT.lt.{0} Nat instLTNat T
      (@OAI.EditApproximation.PhysicalTableRequest.index M J (@List.length.{u_1} α target)
        (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
          (fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          parent)))
  (hbelow :
    @LT.lt.{0} Nat instLTNat
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Sigma.fst.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (fun d =>
            OAI.EditApproximation.TreeLayer M
              (@Fin.val
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) J
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                d))
          (@OAI.EditApproximation.PhysicalTableRequest.node M J (@List.length.{u_1} α target)
            (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
              (fun r =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  copies T S r)
              parent))))
      J),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyBoundedActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (Sum.{0, 0} (@OAI.EditApproximation.PhysicalFamilyScalarKey.{u_1} α M J R target N P F exponent H Q passes copies)
        (@Subtype.{1}
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target)) fun r =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S r)
          fun child =>
          @LT.lt.{0} Nat instLTNat
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                child))
            (@OAI.EditApproximation.PhysicalTableRequest.combinedRank M J (@List.length.{u_1} α target) T S
              (@Subtype.val.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{u_1} α target))
                (fun r =>
                  @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{u_1} α target)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    copies T S r)
                parent))))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyBoundedActive.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM eF
        hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow)
      (@OAI.EditApproximation.queryFamilyBoundedActiveHeap.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow))
    (@OAI.EditApproximation.queryFamilyBoundedActiveFootprint.{u_1} α M J R _inst _inst_1 source target N P F exponent H Q
      eM eF hP hM hF tau a eta kappa delta T S passes copies parent hindex hbelow) := by
  intros
  simp [queryFamilyBoundedActiveHeap, queryFamilyBoundedActiveFootprint, queryFamilyBoundedActive]

@[simp] theorem queryChargedSeedAtHeap_footprint :
    ∀ {M J n passes copies T S : Nat}
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S r)
  (N : Nat) (multiplier : Nat → Nat) (q : OAI.EditApproximation.TargetInterval n),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedSeedAt M J n passes copies T S parent N multiplier q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J n passes copies T S) fun child =>
        @LT.lt.{0} Nat instLTNat (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J n passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J n)
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J n) fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J n passes copies T S request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedSeedAt M J n passes copies T S parent N multiplier q)
      (@OAI.EditApproximation.queryChargedSeedAtHeap M J n passes copies T S parent N multiplier q))
    (@OAI.EditApproximation.queryChargedSeedAtFootprint M J n passes copies T S parent N multiplier q) := by
  intros
  unfold queryChargedSeedAtHeap queryChargedSeedAtFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    refine (BitQuery.Heap.footprint_chargeOf _ _ _).trans ?_
    apply congrArg (BitQuery.Footprint.chargeOf _)
    refine (BitQuery.Heap.footprint_collect _ _ _ _ _).trans ?_
    congr 1
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    apply queryChargedReadHeap_footprint

@[simp] theorem queryPhysicalInitialHeap_footprint :
    ∀ (source target : List.{0} Nat) {M J passes copies T S : Nat} (N P F : Nat)
  (A a : OAI.EditApproximation.BinaryFraction) (multiplier : Nat → Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S r)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (q : OAI.EditApproximation.TargetInterval (@List.length.{0} Nat target)),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalInitial source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryPhysicalInitial source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q)
      (@OAI.EditApproximation.queryPhysicalInitialHeap source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits q))
    (@OAI.EditApproximation.queryPhysicalInitialFootprint source target M J passes copies T S N P F A a multiplier
      parent occurrence symbolBits positionBits q) := by
  intros
  unfold queryPhysicalInitialHeap queryPhysicalInitialFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (ite_eq_right h)
    simp
  · intro h
    apply footprint_mpr_congr (ite_eq_left h)
    rfl

@[simp] theorem queryChargedWarmupHeap_footprint :
    ∀ (source target : List.{0} Nat) {M J passes copies T S : Nat} (N P F : Nat)
  (A a : OAI.EditApproximation.BinaryFraction) (multiplier : Nat → Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S r)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedWarmup source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target) passes copies T S)
        fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S child)
          (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target) passes copies T S
            (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
              (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target))
                fun request =>
                @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target) passes copies T S
                  request)
              parent)))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedWarmup source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits)
      (@OAI.EditApproximation.queryChargedWarmupHeap source target M J passes copies T S N P F A a multiplier parent
        occurrence symbolBits positionBits))
    (@OAI.EditApproximation.queryChargedWarmupFootprint source target M J passes copies T S N P F A a multiplier parent
      occurrence symbolBits positionBits) := by
  intros
  unfold queryChargedWarmupHeap queryChargedWarmupFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases]
    apply cases_congr
    · intro h'
      apply footprint_mpr_congr (dite_eq_right h')
      simp
    · intro h'
      apply footprint_mpr_congr (dite_eq_left h')
      apply congrArg (BitQuery.Footprint.charge _)
      rw [footprint_cases]
      apply cases_congr
      · intro h''
        apply footprint_mpr_congr (ite_eq_right h'')
        refine (queryWarmupProgramHeap_footprint _ _ _ _ _ _ _ _ _ _).trans ?_
        congr 1
        funext r
        apply queryPhysicalInitialHeap_footprint
      · intro h''
        apply footprint_mpr_congr (ite_eq_left h'')
        simp
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    simp

@[simp] theorem queryChargedFamilyTableHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (parent :
    @Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun r =>
      @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        copies T S r),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q
        (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun request =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S request)
          parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyTable M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q
        (@Sum.inr.{0, 0} (OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target))
          (@Subtype.{1} (OAI.EditApproximation.PhysicalTableRequest M J (@List.length.{0} Nat target)) fun request =>
            @OAI.EditApproximation.PhysicalTableRequest.Bounded M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S request)
          parent))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyTable M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent)
      (@OAI.EditApproximation.queryChargedFamilyTableHeap M J R passes copies T S _inst _inst_1 source target N P F
        exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent))
    (@OAI.EditApproximation.queryChargedFamilyTableFootprint M J R passes copies T S _inst _inst_1 source target N P F
      exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent) := by
  intros
  unfold queryChargedFamilyTableHeap queryChargedFamilyTableFootprint
  apply congrArg (BitQuery.Footprint.charge _)
  rw [footprint_cases]
  apply cases_congr
  · intro h
    apply footprint_mpr_congr (dite_eq_right h)
    apply congrArg (BitQuery.Footprint.charge _)
    rw [footprint_cases]
    apply cases_congr
    · intro h'
      apply footprint_mpr_congr (dite_eq_right h')
      simp
    · intro h'
      apply footprint_mpr_congr (dite_eq_left h')
      apply congrArg (BitQuery.Footprint.charge _)
      rw [footprint_cases]
      apply cases_congr
      · intro h''
        apply footprint_mpr_congr (ite_eq_right h'')
        simp
      · intro h''
        apply footprint_mpr_congr (ite_eq_left h'')
        simp
  · intro h
    apply footprint_mpr_congr (dite_eq_left h)
    simp

@[simp] theorem queryChargedFamilyGlobalHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (coarse :
    OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) → Nat)
  (hc :
    ∀ (entry : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target)),
      @LE.le.{0} Nat instLENat (allocation entry)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (coarse entry))))
  (request :
    OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      copies T S),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q request)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyGlobal M J R passes copies T S _inst _inst_1 source target N P F exponent
        H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@OAI.EditApproximation.ChargedFamilyQueryKey M J R passes copies T S target N P F exponent H Q request)
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryChargedFamilyGlobal M J R passes copies T S _inst _inst_1 source target N P F exponent
        H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse request)
      (@OAI.EditApproximation.queryChargedFamilyGlobalHeap M J R passes copies T S _inst _inst_1 source target N P F
        exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse
        allocation hc request))
    (@OAI.EditApproximation.queryChargedFamilyGlobalFootprint M J R passes copies T S _inst _inst_1 source target N P F
      exponent H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse
      allocation request) := by
  intros
  rename_i request
  cases request <;> simp [queryChargedFamilyGlobalHeap, queryChargedFamilyGlobalFootprint, queryChargedFamilyGlobal]

@[simp] theorem queryFamilyMemoRawHeap_footprint :
    ∀ {M J R passes copies T S : Nat} [_inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) M]
  [_inst_1 : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) R] (source target : List.{0} Nat)
  (N P F exponent H Q eM eF : Nat)
  (hP : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P)
  (hM :
    @Eq.{1} Nat M
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eM))
  (hF :
    @Eq.{1} Nat F
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) eF))
  (A a : Nat → OAI.EditApproximation.BinaryFraction) (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
  (multiplier : Nat → Nat) (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat)
  (coarse :
    OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) →
      Prod.{0, 0} OAI.EditApproximation.BinaryFraction Nat)
  (allocation : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target) → Nat)
  (hc :
    ∀ (entry : OAI.EditApproximation.PhysicalEntry M J (@List.length.{0} Nat target)),
      @LE.le.{0} Nat instLENat (allocation entry)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Prod.snd.{0, 0} OAI.EditApproximation.BinaryFraction Nat (coarse entry))))
  (draw : @OAI.EditApproximation.PhysicalFamilyScalarDraw.{0} Nat M J R target N P F exponent H Q passes copies)
  (key : @OAI.EditApproximation.QueryFamilyMemoKey M J R passes copies T S target N P F exponent H Q),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
          (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            copies T S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            key))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyMemoRaw M J R passes copies T S _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
          (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            copies T S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat M J R target N P F exponent H Q passes copies)
            (OAI.EditApproximation.ChargedPhysicalRequest M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank M J (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) passes
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              copies T S)
            key))
      OAI.EditApproximation.BinaryFraction
      (@OAI.EditApproximation.queryFamilyMemoRaw M J R passes copies T S _inst _inst_1 source target N P F exponent H Q eM
        eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key)
      (@OAI.EditApproximation.queryFamilyMemoRawHeap M J R passes copies T S _inst _inst_1 source target N P F exponent H
        Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation hc draw
        key))
    (@OAI.EditApproximation.queryFamilyMemoRawFootprint M J R passes copies T S _inst _inst_1 source target N P F exponent
      H Q eM eF hP hM hF A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation draw
      key) := by
  intros
  rename_i key
  cases key <;> simp [queryFamilyMemoRawHeap, queryFamilyMemoRawFootprint, queryFamilyMemoRaw]
  · apply BitQuery.Heap.footprint_computeOf
  · refine (BitQuery.Heap.footprint_mapKeysWithWork _ _ _ _).trans ?_
    apply congrArg (BitQuery.Footprint.mapKeysWithWork _ _)
    apply queryChargedFamilyGlobalHeap_footprint

@[simp] theorem computedQueryMemoRawHeap_footprint :
    ∀ (source target : List.{0} Nat) (N : Nat)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (input : OAI.EditApproximation.ComputedFamilyInput source target N)
  (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
              (OAI.EditApproximation.smallLogExponent N))
            (OAI.EditApproximation.inputHeight N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (OAI.EditApproximation.computedSeedPassCount N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (OAI.EditApproximation.ChargedPhysicalRequest
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (OAI.EditApproximation.computedSeedPassCount N)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoRaw source target N occurrence symbolBits positionBits input key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1}
        (Sum.{0, 0}
          (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
              (OAI.EditApproximation.smallLogExponent N))
            (OAI.EditApproximation.inputHeight N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (OAI.EditApproximation.computedSeedPassCount N)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (OAI.EditApproximation.ChargedPhysicalRequest
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) (OAI.EditApproximation.heightExponent N)
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
            (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
              (@List.length.{0} Nat source))
            (@List.length.{0} Nat target)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (OAI.EditApproximation.computedSeedPassCount N)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S))
        fun next =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            next)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (@OAI.EditApproximation.PhysicalFamilyScalarKey.{0} Nat
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                (OAI.EditApproximation.smallLogExponent N))
              (OAI.EditApproximation.inputHeight N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputSmallLog N) (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
              (OAI.EditApproximation.computedSeedPassCount N)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                  (OAI.EditApproximation.heightExponent N)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoRaw source target N occurrence symbolBits positionBits input key)
      (OAI.EditApproximation.computedQueryMemoRawHeap source target N occurrence symbolBits positionBits input key))
    (OAI.EditApproximation.computedQueryMemoRawFootprint source target N occurrence symbolBits positionBits input key) := by
  intros
  simp [computedQueryMemoRawHeap, computedQueryMemoRawFootprint, computedQueryMemoRaw]
  with_unfolding_all apply queryFamilyMemoRawHeap_footprint

@[simp] theorem computedQueryMemoHeap_footprint :
    ∀ (source target : List.{0} Nat) (N : Nat)
  (occurrence : OAI.EditApproximation.BinaryMemo.{0} OAI.EditApproximation.PositionCounts)
  (symbolBits positionBits : Nat) (input : OAI.EditApproximation.ComputedFamilyInput source target N)
  (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N),
  @Eq.{1}
    (@OAI.EditApproximation.BitQuery.Footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ComputedFamilyMemoKey source target N) fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            child)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key))
    (@OAI.EditApproximation.BitQuery.Heap.footprint.{0, 0}
      (@Subtype.{1} (OAI.EditApproximation.ComputedFamilyMemoKey source target N) fun child =>
        @LT.lt.{0} Nat instLTNat
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            child)
          (@OAI.EditApproximation.SourceRanked.rank.{0, 0}
            (OAI.EditApproximation.ComputedFamilyScalarKey source target N
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (OAI.EditApproximation.ChargedPhysicalRequest (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            (@OAI.EditApproximation.ChargedPhysicalRequest.rank (OAI.EditApproximation.integerParameters N).M
              (OAI.EditApproximation.intervalTreeDepth (OAI.EditApproximation.integerParameters N).M
                (@List.length.{0} Nat source))
              (@List.length.{0} Nat target)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (OAI.EditApproximation.computedSeedPassCount N)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (OAI.EditApproximation.inputHeight N) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S)
            key))
      OAI.EditApproximation.BinaryFraction
      (OAI.EditApproximation.computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key)
      (OAI.EditApproximation.computedQueryMemoHeap source target N occurrence symbolBits positionBits input key))
    (OAI.EditApproximation.computedQueryMemoFootprint source target N occurrence symbolBits positionBits input key) := by
  intro source target N occurrence symbolBits positionBits input key
  unfold computedQueryMemoHeap computedQueryMemoFootprint
  refine (BitQuery.Heap.footprint_normalize _ _ _ _).trans ?_
  exact congrArg
      (fun footprint : BitQuery.Footprint
          (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key) =>
        footprint.normalize (computedQueryBase N) (computedQueryBase_pos N)
          (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
            (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key))
      (computedQueryMemoRawHeap_footprint source target N occurrence symbolBits positionBits input key)

end OAI.EditApproximation
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Specification_FootprintMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.EditApproximation
open Filter MeasureTheory
attribute [local instance] queryRoundsNeZero

theorem computedQueryTemporaryCellsFootprint_eq (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedQueryTemporaryCellsFootprint source target N occurrence symbolBits positionBits input =
      computedQueryTemporaryCells source target N occurrence symbolBits positionBits input := by
  have h : computedQueryMemoFootprint source target N occurrence symbolBits positionBits input =
      (fun key => (computedQueryMemoHeap source target N occurrence symbolBits positionBits input key).footprint) := by
    funext key
    exact (computedQueryMemoHeap_footprint source target N occurrence symbolBits positionBits input key).symm
  unfold computedQueryTemporaryCellsFootprint computedQueryTemporaryCells
  rw [h]
  exact BitQuery.Heap.footprint_rankedBitMemoCells _ _ _ _ _ _ _ _

theorem integerAcceptedSpaceTermsFootprint_eq (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerAcceptedSpaceTermsFootprint source target N epsilon input =
      integerAcceptedSpaceTerms source target N epsilon input := by
  simp only [integerAcceptedSpaceTermsFootprint, integerAcceptedSpaceTerms,
    computedQueryTemporaryCellsFootprint_eq]

theorem integerBinarySpaceFootprint_eq_oai (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinarySpaceFootprint source target N epsilon outcome =
      integerBinarySpace source target N epsilon outcome := by
  simp only [integerBinarySpaceFootprint, integerBinarySpace, integerAcceptedSpaceTermsFootprint_eq]
  try rfl

end OAI.EditApproximation
end

theorem solution : type_of% @OAI.EditApproximation.integerBinarySpaceFootprint_eq_oai := @OAI.EditApproximation.integerBinarySpaceFootprint_eq_oai
