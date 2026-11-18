-- Prove2me | solution 1 for OAI.EditApproximation.queryLocalRefinement_work_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:31:37.60756+00:00
-- url     : https://prove2.me/submissions/e17154c7-7dae-4810-80fd-ea388290d37f

import Mathlib
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_07
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalCellGroupsSourceWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_preparedLocalOnlineActionsWithWork_cost
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryEarlierInputsWithWork_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_queryLocalRefinement_finish_bounds
import Theorems.Thm_OAI_EditApproximation_BinaryFraction_querySharedInputsWithWork_bounds_on

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryArithmeticWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean ripple addition. The counter counts Boolean gates and
bit writes, not unit-cost arithmetic on unbounded integers. -/

namespace EditApproximation







theorem bitAddWithWork_cost (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem bitAddWithWork_length (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).1.length ≤ max left.length right.length + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil, Nat.zero_max]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil, Nat.zero_max] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil, Nat.max_zero]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil, Nat.max_zero] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem binaryNaturalAddWithWork_cost (a b : ℕ) :
    (binaryNaturalAddWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len] using
    bitAddWithWork_cost a.bits b.bits false



theorem bitMulWithWork_length (left right : List Bool) :
    (bitMulWithWork left right).1.length ≤ 2 * left.length + right.length + 1 := by
  induction left with
  | nil => simp [bitMulWithWork]
  | cons bit bits ih =>
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      have h := bitAddWithWork_length (false :: (bitMulWithWork bits right).1) right false
      simp only [List.length_cons] at h
      omega

theorem bitMulWithWork_cost (left right : List Bool) :
    (bitMulWithWork left right).2 ≤ 20 * (left.length + 1) * (left.length + right.length + 1) := by
  induction left with
  | nil => simp [bitMulWithWork]; omega
  | cons bit bits ih =>
    have hlength := bitMulWithWork_length bits right
    have hadd := bitAddWithWork_cost (false :: (bitMulWithWork bits right).1) right false
    simp only [List.length_cons] at hadd
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      nlinarith only [ih]
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      nlinarith only [ih, hlength, hadd]



theorem binaryNaturalMulWithWork_cost (a b : ℕ) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (Nat.size a + 1) * (Nat.size a + Nat.size b + 1) := by
  simpa only [binaryNaturalMulWithWork, Nat.size_eq_bits_len] using bitMulWithWork_cost a.bits b.bits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteEnumerationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal finite enumeration with counters. Each callback is evaluated
once and its returned work is charged; list cells and copied output cells
are charged separately. -/

namespace EditApproximation



theorem arithmeticFlatMapWithWork_cost {α β : Type*} (f : α → List β × ℕ) (values : List α)
    (C L : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) (hL : ∀ a ∈ values, (f a).1.length ≤ L) :
    (arithmeticFlatMapWithWork f values).2 ≤ values.length * (C + L + 3) := by
  induction values with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have hla := hL a List.mem_cons_self
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
      (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [arithmeticFlatMapWithWork, List.length_cons]
    nlinarith only [ha, hla, htail]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryMedianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Binary multiplication, natural ceiling, sorting and clamping for the
literal seed median. The stored words are sorted without decoding them. -/

namespace EditApproximation

theorem wordLEWithWork_cost (a b : List Bool) :
    (wordLEWithWork a b).2 ≤ 4 * (a.length + b.length) + 2 := by
  have h := bitCompareWithWork_cost b a
  change _ + 1 ≤ _
  omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Materialization of the online coordinate array includes its equality
tests and duplicate-removal scan. Endpoints and child indices are compared
by the verified binary natural comparator. -/

namespace EditApproximation



theorem memberByWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (a : α) (xs : List α) :
    (memberByWithWork equal a xs).2 ≤ 1 + xs.length * (C + 1) := by
  induction xs with
  | nil => simp only [memberByWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_refl]
  | cons b xs ih =>
    have h := hC a b
    change _ + _ + 1 ≤ _
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReads
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Online objective construction charges every historical table read,
including repeated uses in gain and decrement terms. -/

namespace EditApproximation
namespace BinaryFraction





theorem optimisticTermReadWithWork_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (coefficient : BinaryFraction)
    (s : ℕ) (i : β × σ) (R : ℕ) (hs : (read s i).2 ≤ R) (hs' : (read (s + 1) i).2 ≤ R) :
    (optimisticTermReadWithWork mass read coefficient s i).2 ≤
      (optimisticTermWithWork mass (fun t j => (read t j).1) coefficient s i).2 + 3 * R := by
  simp only [optimisticTermReadWithWork, optimisticTermWithWork, gainReadWithWork,
    decrementReadWithWork, gainWithWork, decrementWithWork]
  omega



theorem onlineLinearReadWithWork_eq_cost {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).1 =
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).1 ∧
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 + (3 * t + 1) * R := by
  have ht := vectorMapWithWork_extra t
    (fun s => optimisticTermReadWithWork mass read (coefficientWithWork kappa).1 s.val i)
    (fun s => optimisticTermWithWork mass (fun t j => (read t j).1) (coefficientWithWork kappa).1 s.val i)
    (3 * R) (fun _ => rfl) (fun s => optimisticTermReadWithWork_cost mass read _ s.val i R
      (hr _ (by omega)) (hr _ (by omega)))
  have hcur := hr t (by omega)
  unfold onlineLinearReadWithWork onlineLinearWithWork
  dsimp only
  rw [ht.1]
  refine ⟨rfl, ?_⟩
  simp only [gainReadWithWork, gainWithWork]
  nlinarith only [ht.2, hcur]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandActionReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The actual labelled online action, with charged initial and history reads. -/

namespace EditApproximation
namespace BinaryFraction




theorem countedPreparedActionReadWithWork_eq_cost {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).1 =
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hl := vectorMapWithWork_extra (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    ((3 * t + 1) * R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).2)
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value]
  rw [hl.1]
  exact ⟨rfl, by omega⟩



theorem countedBandActionReadWithWork_eq_cost {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R C : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).1 =
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).1 ∧
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hm := envelopeVectorReadWithWork_eq_cost b band initial C hi
  have hs := countedPreparedActionReadWithWork_eq_cost
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read
    eta kappa band G j t R hr
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hm.1]
  exact ⟨hs.1, by omega⟩



theorem countedSampledOnlineReadWithWork_eq_cost {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R C : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ C)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).1 =
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).1 ∧
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 +
        M * (band.length * (C + 3)) +
        (listedBandCoordinates band).length * ((3 * t + 1) * R) := by
  have hs := countedBandActionReadWithWork_eq_cost b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R C hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  rw [hs.1]
  exact ⟨rfl, by omega⟩

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryReadCostBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lookup overhead is controlled by the loops that actually run.
These comparisons require only a bound on one finite-buffer lookup. -/

namespace EditApproximation

theorem arithmeticMapWithWork_factor {α β : Type*} (read plain : α → β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (arithmeticMapWithWork read xs).1 = (arithmeticMapWithWork plain xs).1 ∧
    (arithmeticMapWithWork read xs).2 ≤ (arithmeticMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [arithmeticMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [arithmeticMapWithWork, hx, ht.1]
    · simp only [arithmeticMapWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem vectorMapWithWork_factor {α : Type*} (d : ℕ) (read plain : Fin d → α × ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hv : ∀ i, (read i).1 = (plain i).1)
    (hc : ∀ i, (read i).2 ≤ (plain i).2 * K) :
    (vectorMapWithWork d read).1 = (vectorMapWithWork d plain).1 ∧
    (vectorMapWithWork d read).2 ≤ (vectorMapWithWork d plain).2 * K := by
  constructor
  · apply Vector.ext
    intro i hi
    change (vectorMapWithWork d read).1.get ⟨i, hi⟩ = (vectorMapWithWork d plain).1.get ⟨i, hi⟩
    rw [vectorMapWithWork_value, vectorMapWithWork_value]
    exact hv _
  · simp only [vectorMapWithWork, Vector.toList_map, Vector.toList_ofFn,
      List.map_ofFn, Function.comp_def, List.sum_ofFn]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hc i)
    rw [← Finset.sum_mul] at hs
    have hd := Nat.mul_le_mul_left (6 * d) hK
    simp only [Nat.mul_one] at hd
    nlinarith only [hs, hd]


theorem filterWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterWithWork read xs).1 = (filterWithWork plain xs).1 ∧
    (filterWithWork read xs).2 ≤ (filterWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [filterWithWork, hx, ht.1]
    · simp only [filterWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem allWithWork_factor {α : Type*} (read plain : α → Bool × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
    (allWithWork read xs).2 ≤ (allWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [allWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · simp only [allWithWork, hx, ht.1]
    · simp only [allWithWork]
      nlinarith only [hcx, ht.2, hK]

theorem filterMapWithWork_factor {α β : Type*} (read plain : α → Option β × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (filterMapWithWork read xs).1 = (filterMapWithWork plain xs).1 ∧
    (filterMapWithWork read xs).2 ≤ (filterMapWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [filterMapWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    simp only [filterMapWithWork, hx, ht.1]
    cases (plain x).1 with
    | none => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩
    | some value => exact ⟨trivial, by nlinarith only [hcx, ht.2, hK]⟩

/-- Multiplicative work bounds are preserved when the same nonnegative
overhead is added to both counters. -/
theorem cost_replace_factor (a c old new K : ℕ) (hc : c ≤ a * K) (hK : 1 ≤ K)
    (ha : a ≤ old) (hn : new + a ≤ old + c) : new ≤ old * K := by
  have hx := Nat.mul_le_mul_left (old - a) hK
  simp only [Nat.mul_one] at hx
  have he : a + (old - a) = old := by omega
  calc
    new ≤ c + (old - a) := by omega
    _ ≤ a * K + (old - a) * K := Nat.add_le_add hc hx
    _ = old * K := by rw [← Nat.add_mul, he]

/-- A compulsory constant instruction pays for one additional lookup. -/
theorem cost_factor_with_read (a c x r R K : ℕ) (hc : c ≤ a * K)
    (hr : r ≤ R) (hx : 1 ≤ x) (hK : R + 1 ≤ K) :
    r + c + x ≤ (a + x) * K := by
  have hmul := Nat.mul_le_mul_left x hK
  have hR := Nat.mul_le_mul_right R hx
  simp only [Nat.one_mul] at hR
  have hrest : r + x ≤ x * K := by nlinarith only [hmul, hR, hr]
  calc
    r + c + x = c + (r + x) := by omega
    _ ≤ a * K + x * K := Nat.add_le_add hc hrest
    _ = (a + x) * K := by ring

namespace BinaryFraction

theorem tableReadFactor_pos (R : ℕ) : 1 ≤ tableReadFactor R := by
  unfold tableReadFactor
  omega

theorem tableReadFactor_absorb (a c n R : ℕ) (hc : c ≤ a + n * (R + 3)) (hn : n ≤ a) :
    c ≤ a * tableReadFactor R := by
  have hm := Nat.mul_le_mul_right (R + 3) hn
  have hk : R + 4 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    c ≤ a + a * (R + 3) := hc.trans (Nat.add_le_add_left hm a)
    _ = a * (R + 4) := by ring
    _ ≤ a * tableReadFactor R := Nat.mul_le_mul_left a hk

theorem endpointScoreReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (endpointScoreReadWithWork r read states).2 ≤
      (endpointScoreWithWork r (fun i q => (read i q).1) states).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ M R (endpointScoreReadWithWork_cost r read states R hr)
  simp only [endpointScoreWithWork, endpointConnectionWithWork]
  omega

theorem prefixReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx) (r : TargetInterval n)
    (states : Fin M → TargetInterval n) (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * tableReadFactor R := by
  have hc := prefixReadWithWork_cost parent r states read j p R hr
  have hn : M ≤ (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 := by
    simp only [prefixWithWork]
    omega
  have hm := Nat.mul_le_mul_right (R + 4) hn
  have hk : R + 5 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  calc
    _ ≤ _ + M * (R + 4) := hc
    _ ≤ _ + (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 4) :=
      Nat.add_le_add_left hm _
    _ = (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 * (R + 5) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hk

theorem bandEnvelopeReadWithWork_factor {M n : ℕ} (b : ℕ) (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (i : Fin M) (R : ℕ)
    (hr : ∀ action ∈ band, (read i (action i)).2 ≤ R) :
    (bandEnvelopeReadWithWork b band read i).2 ≤
      (bandEnvelopeWithWork b band (fun j q => (read j q).1) i).2 * tableReadFactor R := by
  apply tableReadFactor_absorb _ _ band.length R (bandEnvelopeReadWithWork_cost b band read i R hr)
  simp only [bandEnvelopeWithWork]
  omega

theorem onlineLinearReadWithWork_factor {β σ : Type*} (mass : β → BinaryFraction)
    (read : ℕ → β × σ → BinaryFraction × ℕ) (eta kappa : BinaryFraction)
    (t : ℕ) (i : β × σ) (R : ℕ) (hr : ∀ s ≤ t + 1, (read s i).2 ≤ R) :
    (onlineLinearReadWithWork mass read eta kappa t i).2 ≤
      (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 * tableReadFactor R := by
  have hc := (onlineLinearReadWithWork_eq_cost mass read eta kappa t i R hr).2
  have ht : 6 * t ≤ (vectorMapWithWork t (fun s => optimisticTermWithWork mass
      (fun v j => (read v j).1) (coefficientWithWork kappa).1 s.val i)).2 := by
    simp only [vectorMapWithWork]
    omega
  have hn : 3 * t + 1 ≤ (onlineLinearWithWork mass (fun s j => (read s j).1) eta kappa t i).2 := by
    simp only [onlineLinearWithWork, gainWithWork]
    omega
  apply tableReadFactor_absorb _ _ (3 * t + 1) R _ hn
  exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : R ≤ R + 3)) _)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryUnskippedReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The accepted-band record is built from the reader-aware tests.
Only proof fields are erased; numerical tests and reads remain charged. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedUnskippedReadWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).1 =
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).1 := by
  have hband := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband]
  split_ifs with hempty hguard
  · rfl
  · rfl
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hplain (hg.symm.trans hguard))
  · rename_i hplain
    have hg := (unskippedGuardReadWithWork_eq_cost parent center b exponent F _ ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi).1
    exact False.elim (hguard (hg.trans hplain))
  · rfl


theorem preparedUnskippedReadWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R C : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ C)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F read initial R C hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 +
      representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) +
      M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1.length * (C + 3)) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hband.1]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial C hi
    simp only [hg.1]
    split_ifs <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryBandReadCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-buffer lookup multiplies local band-loop work by a fixed
linear factor. Every comparison uses the same actual band and output. -/

namespace EditApproximation
namespace BinaryFraction

theorem wideMinimumReadWithWork_factor {n M : ℕ} (r : TargetInterval n)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (wideMinimumReadWithWork r read actions hne).2 ≤
      (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).2 * tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (endpointScoreReadWithWork r read) (endpointScoreWithWork r (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => endpointScoreReadWithWork_eq r read action)
    (fun action ha => endpointScoreReadWithWork_factor r read action R (hr action ha))
  have hf := endpointScoreReadWithWork_factor r read (actions.head hne) R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold wideMinimumWithWork
    dsimp only
    omega
  · unfold wideMinimumReadWithWork wideMinimumWithWork
    dsimp only
    rw [hm.1, endpointScoreReadWithWork_eq]
    omega

theorem prefixMinimumReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 *
        tableReadFactor R := by
  have hm := arithmeticMapWithWork_factor
    (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_factor parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_factor parent r (actions.head hne) read j p R
    (hr _ (List.head_mem hne))
  have hc := Nat.add_le_add hf hm.2
  rw [← Nat.add_mul] at hc
  apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R)
  · unfold prefixMinimumWithWork
    dsimp only
    omega
  · unfold prefixMinimumReadWithWork prefixMinimumWithWork
    dsimp only
    rw [hm.1, prefixReadWithWork_eq]
    omega

theorem cutGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 *
        tableReadFactor R := by
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · simpa only [Nat.one_mul] using tableReadFactor_pos R
  · have h := prefixMinimumReadWithWork_factor parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R)
    · omega
    · omega

theorem bandPredicateReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (states : Fin M → TargetInterval n)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1) states).2 *
        tableReadFactor R := by
  have hc := allWithWork_factor
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (List.finRange M) (tableReadFactor R) (tableReadFactor_pos R)
    (fun j _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ j)
    (fun j _ => cutGuardReadWithWork_factor parent r actions hne read states velocity _ j R hr)
  apply cost_replace_factor _ _ _ _ _ hc.2 (tableReadFactor_pos R)
  · unfold bandPredicateWithWork
    dsimp only
    omega
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    omega

theorem bandFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (hne : actions ≠ [])
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 *
        tableReadFactor R := by
  have hf := filterWithWork_factor
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    actions (tableReadFactor R) (tableReadFactor_pos R)
    (fun action _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne
      read action R hr).1)
    (fun action _ => bandPredicateReadWithWork_factor parent r b tau theta velocity actions hne
      read action R hr)
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · apply cost_replace_factor _ _ _ _ _ hf.2 (tableReadFactor_pos R)
    · omega
    · omega
  · exact Nat.le_mul_of_pos_right _ (by have := tableReadFactor_pos R; omega)

theorem representativeFromActionsReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval n)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta
        (fun i q => (read i q).1) actions).2 * tableReadFactor R := by
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    simpa only [Nat.one_mul] using tableReadFactor_pos R
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_factor r read actions hne R hr
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_factor parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      have hc := Nat.add_le_add hz hb
      rw [← Nat.add_mul] at hc
      apply cost_replace_factor _ _ _ _ _ hc (tableReadFactor_pos R) <;> omega
    · apply cost_replace_factor _ _ _ _ _ hz (tableReadFactor_pos R) <;> omega

theorem preparedRepresentativeReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent r sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent r sourceLength b P tau theta
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have h := representativeFromActionsReadWithWork_factor parent r sourceLength b tau theta read
    ((wideActionGridWithWork M parent r b P).1.map Vector.get) R (fun _ _ i => hr i _)
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem envelopeVectorReadWithWork_factor {n M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval n))
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (envelopeVectorReadWithWork b band read).2 ≤
      (envelopeVectorWithWork b band (fun i q => (read i q).1)).2 * tableReadFactor R := by
  exact (vectorMapWithWork_factor M
    (bandEnvelopeReadWithWork b band read)
    (bandEnvelopeWithWork b band (fun i q => (read i q).1))
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun i => bandEnvelopeReadWithWork_eq b band read i)
    (fun i => bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _))).2

theorem roundedBandReadWithWork_factor {n M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (roundedBandReadWithWork exponent b band hne read).2 ≤
      (roundedBandWithWork exponent b band hne (fun i q => (read i q).1)).2 * tableReadFactor R := by
  apply (vectorMapWithWork_factor M _ _ (tableReadFactor R) (tableReadFactor_pos R) ?_ ?_).2
  · intro i
    simp only [bandEnvelopeReadWithWork_eq]
  · intro i
    have h := bandEnvelopeReadWithWork_factor b band read i R (fun _ _ => hr i _)
    dsimp only
    simp only [bandEnvelopeReadWithWork_eq]
    apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem unskippedGuardReadWithWork_factor {nx n M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval n) (b exponent : ℕ) (F : BinaryFraction)
    (band wide : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (read : Fin M → TargetInterval n → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (unskippedGuardReadWithWork parent r b exponent F band wide hne read).2 ≤
      (unskippedGuardWithWork parent r b exponent F band wide hne
        (fun i q => (read i q).1)).2 * tableReadFactor R := by
  have he := envelopeVectorReadWithWork_factor b band read R hr
  have heq := (envelopeVectorReadWithWork_eq_cost b band read R hr).1
  have hrnd := roundedBandReadWithWork_factor exponent b band hne read R hr
  have hrndq := (roundedBandReadWithWork_eq_cost exponent b band hne read R hr).1
  have h := Nat.add_le_add he hrnd
  rw [← Nat.add_mul] at h
  unfold unskippedGuardReadWithWork unskippedGuardWithWork
  dsimp only
  rw [heq, hrndq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem preparedUnskippedReadWithWork_factor {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau F : BinaryFraction)
    (read initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hr : ∀ i q, (read i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (center : TargetInterval target.length) :
    (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau F
      read initial R R hr hi center).2 ≤
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau F
        (fun i q => (read i q).1) (fun i q => (initial i q).1) center).2 * tableReadFactor R := by
  have hband := preparedRepresentativeReadWithWork_factor parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr
  have hbandq := (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) read R hr).1
  unfold preparedUnskippedReadWithWork preparedUnskippedCandidateWithWork
  dsimp only
  simp only [hbandq]
  by_cases hempty : (preparedRepresentativeWithWork parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1 = []
  · simp only [dite_eq_left hempty]
    apply cost_replace_factor _ _ _ _ _ hband (tableReadFactor_pos R) <;> omega
  · simp only [dite_eq_right hempty]
    have hg := unskippedGuardReadWithWork_factor parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi
    have hgq := (unskippedGuardReadWithWork_eq_cost parent center b exponent F
      (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
        tau (inversePowerTwo exponent) (fun i q => (read i q).1)).1
      ((wideActionGridWithWork M parent center b P).1.map Vector.get) hempty initial R hi).1
    simp only [hgq]
    have h := Nat.add_le_add hband hg
    rw [← Nat.add_mul] at h
    split_ifs <;> apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedOnlineReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prepared online candidate executes its band reads, guard reads,
and historical reads. The accepted source integer and counted coordinate
representation are exactly the original ones. -/

namespace EditApproximation
namespace BinaryFraction

private theorem preparedOnlineReadCore_compare {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (B C E : ℕ) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 + B)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 + C)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).1 = (plainSample plain.1 hne G draw).1 ∧
      (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 + E) :
    (preparedOnlineReadCore H integer band guard sample).1 =
      (preparedOnlineReadCore H integer plain plainGuard plainSample).1 ∧
    (preparedOnlineReadCore H integer band guard sample).2 ≤
      (preparedOnlineReadCore H integer plain plainGuard plainSample).2 + (B + C + E) := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold preparedOnlineReadCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · exact ⟨rfl, by omega⟩
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    exact ⟨congrArg some hsample.1, by omega⟩
  · exact ⟨rfl, by omega⟩

theorem preparedOnlineReadWithWork_eq_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).1 =
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).1 ∧
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 +
      preparedOnlineReadExtra M parent center b P exponent R t tau (fun i q => (child i q).1) := by
  have hband := preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
    b P tau (inversePowerTwo exponent) child R hc
  have hguard := preparedUnskippedReadWithWork_value source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have hguardCost := preparedUnskippedReadWithWork_cost source target parent b P exponent hb hP
    tau (nat F) child initial R R hc hi center
  have h := preparedOnlineReadCore_compare H integer
    (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) child)
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) (fun i q => (child i q).1))
    ((preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center).1.isSome,
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).2)
    ((preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1) center).1.isSome,
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1) center).2)
    (fun xs hxs G draw => countedSampledOnlineReadWithWork center b initial table eta kappa
      xs hxs G (G ^ 80) t draw)
    (fun xs hxs G draw => countedSampledOnlineWithWork center b
      (fun i q => (initial i q).1) (fun s i => (table s i).1) eta kappa xs hxs G (G ^ 80) t draw)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R)
    (representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R +
      2 * (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3))))
    (M * ((preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1.length * (R + 3)) +
      (listedBandCoordinates (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
        (inversePowerTwo exponent) (fun i q => (child i q).1)).1).length * ((3 * t + 1) * R))
    hband.1 hband.2 (congrArg Option.isSome hguard) (by omega)
    (fun hne G draw => by
      simpa only [Nat.add_assoc] using countedSampledOnlineReadWithWork_eq_cost center b initial table eta kappa
        _ hne G (G ^ 80) t R R draw hi (fun s hs i => ht s hs _))
  refine ⟨h.1, ?_⟩
  convert h.2 using 1 <;> first
  | rfl
  | (dsimp only [preparedOnlineReadExtra, preparedOnlineWithWork, preparedOnlineReadCore]; ring)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineReads
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Query-local online scales explicitly read the initial value at the
query and at each rounded center before running the full band kernel. -/

namespace EditApproximation
namespace BinaryFraction

section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

theorem preparedLocalOnlineScaleReadWithWork_eq (e : ℕ) (query : TargetInterval target.length)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
    (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · exact (preparedOnlineReadWithWork_eq_cost source target parent P F exponent H (2 ^ e)
      (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi t _ _ ht).1
  · rfl

theorem preparedLocalOnlineActionsReadWithWork_eq (N : ℕ) (query : TargetInterval target.length)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query).1 := by
  simp only [preparedLocalOnlineActionsReadWithWork, preparedLocalOnlineActionsWithWork,
    filterMapWithWork_value]
  apply List.filterMap_congr
  intro e _
  exact preparedLocalOnlineScaleReadWithWork_eq source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial table R hc hi t integer e query ht

end Local
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalOnlineSource
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online candidate selection charges the finite source-buffer decoder
at the point where its integer is consumed. Ineligible centers do not
read a random coordinate. -/

namespace EditApproximation.BinaryFraction
section Local
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)

theorem preparedLocalOnlineScaleSourceWithWork_eq_cost_on (e : ℕ) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : (centerEligibilityWithWork (2 ^ e) F a
      (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
        (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).1).1 = true →
      (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
        (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).2 ≤ S) :
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).1 =
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).1 ∧
    (preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).2 ≤
      (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query).2 * (S + 4) := by
  unfold preparedLocalOnlineScaleSourceWithWork preparedLocalOnlineScaleReadWithWork
  dsimp only
  split_ifs with hguard
  · refine ⟨rfl, ?_⟩
    have hsample := hs hguard
    nlinarith only [hsample]
  · exact ⟨rfl, by nlinarith only [Nat.zero_le S]⟩

theorem preparedLocalOnlineActionsSourceWithWork_eq_cost_on (N : ℕ) (query : TargetInterval target.length)
    (S : ℕ)
    (hs : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial query).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1).2 ≤ S) :
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).1 =
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).1 ∧
    (preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).2 ≤
      (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
        parentInitial child initial table R hc hi t (fun b q => (integer b q).1) N query).2 * (S + 4) := by
  have h := filterMapWithWork_factor
    (fun e => preparedLocalOnlineScaleSourceWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t (fun b q => (integer b q).1) e query)
    (queryExponentsWithWork N F a (parentInitial query).1).1 (S + 4) (by omega)
    (fun e he => (preparedLocalOnlineScaleSourceWithWork_eq_cost_on source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query S (hs e he)).1)
    (fun e he => (preparedLocalOnlineScaleSourceWithWork_eq_cost_on source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query S (hs e he)).2)
  unfold preparedLocalOnlineActionsSourceWithWork preparedLocalOnlineActionsReadWithWork
  dsimp only
  rw [h.1]
  exact ⟨rfl, by nlinarith only [h.2]⟩

end Local
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOnlineReadCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Online sampler arithmetic and lookup costs share one linear read factor. -/

namespace EditApproximation
namespace BinaryFraction

theorem countedPreparedActionReadWithWork_factor {M n : ℕ} (mass : Vector BinaryFraction M)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedPreparedActionReadWithWork mass read eta kappa band G j t).2 ≤
      (countedPreparedActionWithWork mass (fun s i => (read s i).1) eta kappa band G j t).2 *
        tableReadFactor R := by
  have hl := vectorMapWithWork_factor (listedBandCoordinates band).length
    (fun i => onlineLinearReadWithWork (fun j => mass.get j) read eta kappa t
      ((listedBandCoordinateVector band).get i))
    (fun i => onlineLinearWithWork (fun j => mass.get j) (fun s k => (read s k).1) eta kappa t
      ((listedBandCoordinateVector band).get i))
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun i => (onlineLinearReadWithWork_eq_cost _ read eta kappa t _ R
      (fun s hs => hr s hs i)).1)
    (fun i => onlineLinearReadWithWork_factor _ read eta kappa t _ R (fun s hs => hr s hs i))
  unfold countedPreparedActionReadWithWork countedPreparedActionWithWork
  simp only [coordinateVectorWithWork_value, hl.1]
  apply cost_replace_factor _ _ _ _ _ hl.2 (tableReadFactor_pos R) <;> omega

theorem countedBandActionReadWithWork_factor {M n : ℕ} (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (G j t R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedBandActionReadWithWork b initial read eta kappa band G j t).2 ≤
      (countedBandActionWithWork b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band G j t).2 * tableReadFactor R := by
  have hm := envelopeVectorReadWithWork_factor b band initial R hi
  have hmq := (envelopeVectorReadWithWork_eq_cost b band initial R hi).1
  have hs := countedPreparedActionReadWithWork_factor
    (envelopeVectorWithWork b band (fun i q => (initial i q).1)).1 read eta kappa band G j t R hr
  have h := Nat.add_le_add hm hs
  rw [← Nat.add_mul] at h
  unfold countedBandActionReadWithWork countedBandActionWithWork
  dsimp only
  rw [hmq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem countedSampledOnlineReadWithWork_factor {n M : ℕ} (center : TargetInterval n) (b : ℕ)
    (initial : Fin M → TargetInterval n → BinaryFraction × ℕ)
    (read : ℕ → Fin M × TargetInterval n → BinaryFraction × ℕ)
    (eta kappa : BinaryFraction) (band : List (Fin M → TargetInterval n)) (hne : band ≠ [])
    (G K t R : ℕ) (integer : Fin (optimizerTriangularMass K))
    (hi : ∀ i q, (initial i q).2 ≤ R)
    (hr : ∀ s ≤ t + 1, ∀ i : Fin (listedBandCoordinates band).length,
      (read s ((listedBandCoordinateVector band).get i)).2 ≤ R) :
    (countedSampledOnlineReadWithWork center b initial read eta kappa band hne G K t integer).2 ≤
      (countedSampledOnlineWithWork center b (fun i q => (initial i q).1)
        (fun s i => (read s i).1) eta kappa band hne G K t integer).2 * tableReadFactor R := by
  have hs := countedBandActionReadWithWork_factor b initial read eta kappa band G
    (triangularChoiceWithWork K integer).1.val t R hi hr
  unfold countedSampledOnlineReadWithWork countedSampledOnlineWithWork
  dsimp only
  apply cost_replace_factor _ _ _ _ _ hs (tableReadFactor_pos R) <;> omega

private theorem onlineCostCore_factor {n M : ℕ} {Action : Type*} (H integer : ℕ)
    (band plain : List (Fin M → TargetInterval n) × ℕ) (guard plainGuard : Bool × ℕ)
    (sample plainSample : (xs : List (Fin M → TargetInterval n)) → xs ≠ [] → (G : ℕ) →
      Fin (optimizerTriangularMass (G ^ 80)) → Action × ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hb : band.1 = plain.1) (hbc : band.2 ≤ plain.2 * K)
    (hg : guard.1 = plainGuard.1) (hgc : guard.2 ≤ plainGuard.2 * K)
    (hs : ∀ hne G draw, (sample plain.1 hne G draw).2 ≤ (plainSample plain.1 hne G draw).2 * K) :
    (onlineCostCore H integer band guard sample).2 ≤
      (onlineCostCore H integer plain plainGuard plainSample).2 * K := by
  rcases band with ⟨xs, cost⟩
  rcases plain with ⟨ys, plainCost⟩
  dsimp only at hb hbc hs ⊢
  subst ys
  unfold onlineCostCore
  dsimp only
  simp only [hg]
  split_ifs with he ha
  · apply cost_replace_factor _ _ _ _ _ hbc hK <;> omega
  · have hG : 0 < (onlineIndexSetupWithWork H xs).1 := by
      rw [onlineIndexSetupWithWork_value]
      omega
    have hsample := hs he (onlineIndexSetupWithWork H xs).1
      (reduceOnlineIntegerWithWork ((onlineIndexSetupWithWork H xs).1 ^ 80)
        (pow_pos hG _) integer).1
    have h := Nat.add_le_add (Nat.add_le_add hbc hgc) hsample
    simp only [← Nat.add_mul] at h
    apply cost_replace_factor _ _ _ _ _ h hK <;> omega
  · have h := Nat.add_le_add hbc hgc
    rw [← Nat.add_mul] at h
    apply cost_replace_factor _ _ _ _ _ h hK <;> omega

theorem preparedOnlineReadWithWork_factor {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P F exponent H b : ℕ) (hb : 0 < b) (hP : 0 < P)
    (tau eta kappa : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
    (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
    (t : ℕ) (center : TargetInterval target.length) (integer : ℕ)
    (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedOnlineReadWithWork source target parent P F exponent H b hb hP tau eta kappa
      child initial table R hc hi t center integer).2 ≤
      (preparedOnlineWithWork source target parent P F exponent H b hb hP tau eta kappa
        (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t center integer).2 * tableReadFactor R := by
  apply onlineCostCore_factor H integer
    (preparedRepresentativeReadWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) child)
    (preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P tau
      (inversePowerTwo exponent) (fun i q => (child i q).1))
    ((preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
      child initial R R hc hi center).1.isSome,
      (preparedUnskippedReadWithWork source target parent b P exponent hb hP tau (nat F)
        child initial R R hc hi center).2)
    ((preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
      (fun i q => (child i q).1) (fun i q => (initial i q).1) center).1.isSome,
      (preparedUnskippedCandidateWithWork source target parent b P exponent hb hP tau (nat F)
        (fun i q => (child i q).1) (fun i q => (initial i q).1) center).2)
    (fun xs hxs G draw => countedSampledOnlineReadWithWork center b initial table eta kappa
      xs hxs G (G ^ 80) t draw)
    (fun xs hxs G draw => countedSampledOnlineWithWork center b
      (fun i q => (initial i q).1) (fun s i => (table s i).1) eta kappa xs hxs G (G ^ 80) t draw)
    (tableReadFactor R) (tableReadFactor_pos R)
  · exact (preparedRepresentativeReadWithWork_eq_cost parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) child R hc).1
  · exact preparedRepresentativeReadWithWork_factor parent center (parent.hi - parent.lo)
      b P tau (inversePowerTwo exponent) child R hc
  · exact congrArg Option.isSome (preparedUnskippedReadWithWork_value source target parent
      b P exponent hb hP tau (nat F) child initial R R hc hi center)
  · exact preparedUnskippedReadWithWork_factor source target parent b P exponent hb hP
      tau (nat F) child initial R hc hi center
  · intro hne G draw
    exact countedSampledOnlineReadWithWork_factor center b initial table eta kappa _ hne
      G (G ^ 80) t R draw hi (fun s hs i => ht s hs _)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryOuterReadCosts
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.PhysicalTableRequest.refinement_rank _root_.OAI.EditApproximation.PhysicalTableRequest.warmup_rank _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The outer local loops preserve the same lookup factor, including
initial-value reads at the query and at rounded representative centers. -/

namespace EditApproximation
namespace BinaryFraction

theorem cost_replace_with_read (a c old new r R : ℕ) (hc : c ≤ a * tableReadFactor R)
    (hr : r ≤ R) (ha : a + 1 ≤ old) (hn : new + a ≤ old + c + r) :
    new ≤ old * tableReadFactor R := by
  have hK : R + 1 ≤ tableReadFactor R := by unfold tableReadFactor; omega
  have h := cost_factor_with_read a c (old - a) r R (tableReadFactor R)
    hc hr (by omega) hK
  have he : a + (old - a) = old := by omega
  rw [he] at h
  exact (by omega : new ≤ r + c + (old - a)).trans h

section Online
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (P F exponent H : ℕ) (hP : 0 < P)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i q, (child i q).2 ≤ R) (hi : ∀ i q, (initial i q).2 ≤ R)
  (t : ℕ) (integer : ℕ → TargetInterval target.length → ℕ)

theorem preparedLocalOnlineScaleReadWithWork_factor (e : ℕ) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query).2 ≤
      (preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t integer query).2 * tableReadFactor R := by
  let center := (roundStateWithWork
    (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
    (seedGridSpacingWithWork_pos (2 ^ e) P hP) query).1
  have hpcenter := hp center
  dsimp only [center] at hpcenter
  unfold preparedLocalOnlineScaleReadWithWork preparedLocalOnlineScaleWithWork
  dsimp only
  split_ifs
  · have h := preparedOnlineReadWithWork_factor source target parent P F exponent H (2 ^ e)
      (Nat.two_pow_pos e) hP tau eta kappa child initial table R hc hi t
      center (integer (2 ^ e) center) ht
    dsimp only [center] at h
    apply cost_replace_with_read _ _ _ _ _ R h hpcenter <;> omega
  · apply cost_replace_with_read 0 0 _ _ _ R (by simp) hpcenter <;> omega

theorem preparedLocalOnlineActionsReadWithWork_factor (N : ℕ) (query : TargetInterval target.length)
    (hp : ∀ r, (parentInitial r).2 ≤ R) (ht : ∀ s ≤ t + 1, ∀ i, (table s i).2 ≤ R) :
    (preparedLocalOnlineActionsReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer N query).2 ≤
      (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
        (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
        (fun s i => (table s i).1) t integer query).2 * tableReadFactor R := by
  have hs := filterMapWithWork_factor
    (fun e => preparedLocalOnlineScaleReadWithWork source target parent P F exponent H hP tau a eta kappa
      parentInitial child initial table R hc hi t integer e query)
    (fun e => preparedLocalOnlineScaleWithWork source target parent P F exponent H e hP tau a eta kappa
      (fun r => (parentInitial r).1) (fun i q => (child i q).1) (fun i q => (initial i q).1)
      (fun s i => (table s i).1) t integer query)
    (queryExponentsWithWork N F a (parentInitial query).1).1
    (tableReadFactor R) (tableReadFactor_pos R)
    (fun e _ => preparedLocalOnlineScaleReadWithWork_eq source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query ht)
    (fun e _ => preparedLocalOnlineScaleReadWithWork_factor source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial table R hc hi t integer e query hp ht)
  unfold preparedLocalOnlineActionsReadWithWork preparedLocalOnlineActionsWithWork
  dsimp only
  apply cost_replace_with_read _ _ _ _ (parentInitial query).2 R hs.2 (hp query) <;> omega

end Online
end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryPreparedListBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal candidate counts of the three local loops, on every seed. -/

namespace EditApproximation
namespace BinaryFraction

theorem queryExponentsWithWork_length_le (N F B : ℕ) (a w : BinaryFraction)
    (hN : Nat.size N ≤ B) : (queryExponentsWithWork N F a w).1.length ≤ B + 1 := by
  change (filterWithWork _ (List.range (max 1 N.bits.length))).1.length ≤ _
  rw [filterWithWork_value]
  apply (List.length_filter_le _ _).trans
  rw [List.length_range, Nat.size_eq_bits_len]
  omega

theorem preparedLocalOnlineActionsWithWork_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H B : ℕ) (hP : 0 < P)
    (tau a eta kappa : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (table : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ) (query : TargetInterval target.length)
    (hN : Nat.size N ≤ B) :
    (preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial table t integer query).1.length ≤ B + 1 := by
  change (filterMapWithWork _ (queryExponentsWithWork N F a (parentInitial query)).1).1.length ≤ _
  rw [filterMapWithWork_value]
  exact (List.length_filterMap_le _ _).trans (queryExponentsWithWork_length_le N F B a _ hN)

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySourceSelectorBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete selector bounds with table and scalar-source reads. The
source-cost premises range only over the guards and cells actually visited. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (old current : Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (t : ℕ) (draw : CellGroupReadDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S t
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun s => (old s).1) (fun s => (current s).1) (fun s i => (history s i).1)
    (fun b r => (integer b r).1))
  (hp : ∀ r, (parentInitial r).2 ≤ R)

include hb hp hM in
theorem preparedLocalOnlineActionsSourceWithWork_bounds
    (hh : ∀ s ≤ t + 1, ∀ input, (history s input).2 ≤ R) (D : ℕ)
    (hd : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ D) :
    let selected := preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP
      tau a eta kappa parentInitial child initial history R hc hi t integer N q
    selected.1.length ≤ B + 1 ∧
    selected.2 ≤ preparedLocalOnlineBitBudget M P B S * tableReadFactor R * (D + 4) := by
  have hs := preparedLocalOnlineActionsSourceWithWork_eq_cost_on source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t integer N q D hd
  have heq := preparedLocalOnlineActionsReadWithWork_eq source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t (fun b r => (integer b r).1) N q hh
  have hr := preparedLocalOnlineActionsReadWithWork_factor source target parent P F exponent H hP
    tau a eta kappa parentInitial child initial history R hc hi t (fun b r => (integer b r).1) N q hp hh
  have hcost := preparedLocalOnlineActionsWithWork_cost source target parent N P F exponent H B E S hP
    (by rw [hM]; exact Nat.two_pow_pos _) tau a eta kappa (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1) (fun s i => (history s i).1)
    t (fun b r => (integer b r).1) q (by have := hb.largeBits; omega) hb.inputSize hb.sourceSize
    hb.targetSize (by have := hb.aritySize; omega) hb.precisionSize hb.factorSize hb.thetaSize
    hb.heightSize hb.coordinateSize hb.iterationSize hb.drawSize hb.tauSize hb.factorWidth
    hb.rateSize hb.optimismSize hb.parentSize hb.massSize hb.initialSize hb.historySize hb.rateMagnitude
    hb.optimismRange hb.historyRange hb.scalePositive hb.arityCap hb.precisionCap hb.rateCap hb.timeCap
    hb.wordCap hb.actionCap hb.cartesianCap hb.iterationCap
  constructor
  · rw [hs.1, heq]
    exact preparedLocalOnlineActionsWithWork_length_le source target parent N P F exponent H B hP
      tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
      (fun i r => (initial i r).1) (fun s i => (history s i).1) t (fun b r => (integer b r).1) q hb.inputSize
  · exact hs.2.trans (Nat.mul_le_mul_right (D + 4)
      (hr.trans (Nat.mul_le_mul_right (tableReadFactor R) hcost)))

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BitQuery
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Adaptive queries whose answers are stored binary fractions. Local Boolean
computations appear as explicit charged steps. The simulation relation below
preserves the ordered requests as well as the final value; it does not gather
a rational query's keys in advance. -/

namespace EditApproximation



namespace BitQuery



theorem work_bind {ι α β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (program : BitQuery ι α) (next : α → BitQuery ι β) :
    (program.bind next).work oracle readWork =
      program.work oracle readWork + (next (program.value oracle)).work oracle readWork := by
  induction program with
  | done result => simp only [bind, work, value, Nat.zero_add]
  | read key continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]
  | charge steps continuation ih => simp only [bind, work, value, ih, Nat.add_assoc]

/- A local charged step executes a Boolean routine with an explicit cost. -/


theorem work_collect {ι κ β : Type*} (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (reader : κ → BitQuery ι BinaryFraction) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) :
    (collect reader inputs next).work oracle readWork =
      (inputs.map fun key => (reader key).work oracle readWork + 3).sum +
      (next (inputs.map fun key => (reader key).value oracle)).work oracle readWork := by
  induction inputs generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key inputs ih =>
    simp only [collect, work_bind, work, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end BitQuery
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GatheredLocalStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The current-index part of a local step can be evaluated in two
stages: gather the shared sampled inputs, select the whole-cell actions,
then gather their actual costs and the online action costs. -/

namespace EditApproximation

open Finset

theorem orderedInputs_length {ι : Type*} [DecidableEq ι] (encode : ι → ℕ)
    (hinjective : Function.Injective encode) (inputs : Finset ι) :
    (orderedInputs encode hinjective inputs).length = inputs.card := by
  let _ : LinearOrder ι := LinearOrder.lift' encode hinjective
  exact Finset.length_sort (r := (· ≤ ·))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryListWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! First-occurrence duplicate removal for the literal adaptive query lists.
The equality tests, accumulated list, and final reversal are charged. -/

namespace EditApproximation





theorem queryEraseLoopWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1 = List.eraseDupsBy.loop (· == ·) xs seen := by
  induction xs generalizing seen with
  | nil => rfl
  | cons a xs ih =>
    have ht : (memberByWithWork equal a seen).1 = seen.any (a == ·) := by
      apply Bool.eq_iff_iff.mpr
      simp only [memberByWithWork_value equal heq, List.any_eq_true, beq_iff_eq]
      exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨b, hb, hab⟩ => hab ▸ hb⟩
    simp only [queryEraseLoopWithWork, ht, ih, List.eraseDupsBy.loop]
    cases seen.any (a == ·) <;> rfl

@[simp] theorem queryEraseWithWork_value {α : Type*} [BEq α] [LawfulBEq α]
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1 = xs.eraseDups :=
  queryEraseLoopWithWork_value equal heq xs []

theorem queryEraseLoopWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs seen : List α) (hs : seen.Nodup) :
    (queryEraseLoopWithWork equal xs seen).1.Nodup := by
  induction xs generalizing seen with
  | nil => simpa only [queryEraseLoopWithWork, List.nodup_reverse] using hs
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.Nodup
    by_cases h : (memberByWithWork equal a seen).1 = true
    · rw [ite_eq_left h]
      exact ih seen hs
    · rw [ite_eq_right h]
      apply ih
      exact List.nodup_cons.mpr ⟨fun ha => h ((memberByWithWork_value equal heq a seen).mpr ha), hs⟩

theorem queryEraseWithWork_nodup {α : Type*}
    (equal : α → α → Bool × ℕ) (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (xs : List α) : (queryEraseWithWork equal xs).1.Nodup :=
  queryEraseLoopWithWork_nodup equal heq xs [] (by simp)

theorem queryEraseLoopWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).2 ≤
      (xs.length + 1) * (xs.length + seen.length + 1) * (C + 4) := by
  induction xs generalizing seen with
  | nil =>
    simp only [queryEraseLoopWithWork, List.length_nil, zero_add, one_mul]
    nlinarith
  | cons a xs ih =>
    have hm := memberByWithWork_cost equal C hC a seen
    have hs : (if (memberByWithWork equal a seen).1 then seen else a :: seen).length ≤
        seen.length + 1 := by
      split
      · omega
      · simp only [List.length_cons]; omega
    have hi := ih (if (memberByWithWork equal a seen).1 then seen else a :: seen)
    have hh : (queryEraseLoopWithWork equal xs
        (if (memberByWithWork equal a seen).1 then seen else a :: seen)).2 ≤
        (xs.length + 1) * (xs.length + (seen.length + 1) + 1) * (C + 4) :=
      hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    change (memberByWithWork equal a seen).2 + _ + 2 ≤ _
    simp only [List.length_cons]
    nlinarith only [hm, hh, Nat.zero_le xs.length, Nat.zero_le seen.length, Nat.zero_le C]

theorem queryEraseWithWork_cost {α : Type*} (equal : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (equal a b).2 ≤ C) (xs : List α) :
    (queryEraseWithWork equal xs).2 ≤ (xs.length + 1) ^ 2 * (C + 4) := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero, pow_two] using
    queryEraseLoopWithWork_cost equal C hC xs []



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted insertion sorting for the distinct-key lists. The numerical
encoding determines exactly the order used by the reference query. -/

namespace EditApproximation





theorem queryInsertWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).1 = List.orderedInsert r a xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [queryInsertWithWork, hle, List.orderedInsert_cons, decide_eq_true_eq]
    split <;> simp only [ih]

theorem querySortWithWork_value {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b)) (xs : List α) :
    (querySortWithWork le xs).1 = xs.insertionSort r := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [querySortWithWork, queryInsertWithWork_value r le hle, ih, List.insertionSort_cons]

theorem queryInsertWithWork_cost {α : Type*} (le : α → α → Bool × ℕ)
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (a : α) (xs : List α) :
    (queryInsertWithWork le a xs).2 ≤ (xs.length + 1) * (C + 2) := by
  induction xs with
  | nil => simp only [queryInsertWithWork, List.length_nil]; omega
  | cons b xs ih =>
    have h := hC a b
    simp only [queryInsertWithWork, List.length_cons]
    split <;> dsimp only
    · nlinarith only [h, Nat.zero_le xs.length, Nat.zero_le C]
    · nlinarith only [h, ih]

theorem querySortWithWork_cost {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (le : α → α → Bool × ℕ) (hle : ∀ a b, (le a b).1 = decide (r a b))
    (C : ℕ) (hC : ∀ a b, (le a b).2 ≤ C) (xs : List α) :
    (querySortWithWork le xs).2 ≤ (xs.length + 1) ^ 2 * (C + 3) := by
  induction xs with
  | nil => simp only [querySortWithWork, List.length_nil]; omega
  | cons a xs ih =>
    have hi := queryInsertWithWork_cost le C hC a (querySortWithWork le xs).1
    have hl : (querySortWithWork le xs).1.length = xs.length := by
      rw [querySortWithWork_value r le hle, List.length_insertionSort]
    rw [hl] at hi
    change (querySortWithWork le xs).2 + _ + 1 ≤ _
    simp only [List.length_cons]
    nlinarith only [ih, hi, Nat.zero_le xs.length, Nat.zero_le C]



theorem queryOrderedInputsWithWork_value {α : Type*} [DecidableEq α]
    (encode : α → ℕ) (hinjective : Function.Injective encode)
    (equal le : α → α → Bool × ℕ)
    (heq : ∀ a b, (equal a b).1 = true ↔ a = b)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b)) (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).1 = orderedInputs encode hinjective xs.toFinset := by
  let : LinearOrder α := LinearOrder.lift' encode hinjective
  have hle' : ∀ a b, (le a b).1 = decide (a ≤ b) := hle
  rw [queryOrderedInputsWithWork, querySortWithWork_value (· ≤ ·) le hle',
    queryEraseWithWork_value equal heq]
  have hd := queryEraseWithWork_nodup equal heq xs
  rw [queryEraseWithWork_value equal heq] at hd
  have hn : (xs.eraseDups.insertionSort (· ≤ ·)).Nodup :=
    (List.perm_insertionSort (· ≤ ·) xs.eraseDups).nodup_iff.mpr hd
  have hs := (List.toFinset_sort (r := (· ≤ ·)) hn).mpr
    (List.pairwise_insertionSort (· ≤ ·) xs.eraseDups)
  have hf : (xs.eraseDups.insertionSort (· ≤ ·)).toFinset = xs.toFinset := by
    ext x
    simp only [List.mem_toFinset, List.mem_insertionSort, List.mem_eraseDups]
  rw [hf] at hs
  exact hs.symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInputCodes
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Boolean arithmetic for the existing child/history key encodings.
The sorting comparison charges both encodings and the word comparison. -/

namespace EditApproximation



theorem queryEncodedLEWithWork_value {α : Type*} (code : α → ℕ × ℕ) (a b : α) :
    (queryEncodedLEWithWork code a b).1 = decide ((code a).1 ≤ (code b).1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [queryEncodedLEWithWork, wordLEWithWork_value, bitWordValue_bits, decide_eq_true_eq]



@[simp] theorem queryOrderedChildInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1 =
      orderedInputs childInputCode (childInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value childInputCode (childInputCode_injective M n)
    _ _ coordinateEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value]



@[simp] theorem queryOrderedHistoryInputsWithWork_value {M n : ℕ}
    (inputs : List (Fin M × ℕ × TargetInterval n)) :
    (queryOrderedHistoryInputsWithWork inputs).1 =
      orderedInputs historyInputCode (historyInputCode_injective M n) inputs.toFinset := by
  apply queryOrderedInputsWithWork_value historyInputCode (historyInputCode_injective M n)
    _ _ queryHistoryEqualWithWork_value
  intro a b
  simp only [queryEncodedLEWithWork_value, queryHistoryCodeWithWork_value]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryOrderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quadratic work bounds for actual duplicate removal and encoded sorting.
The bound counts comparisons and list allocation, including duplicates. -/

namespace EditApproximation

theorem queryEraseLoopWithWork_length {α : Type*} (equal : α → α → Bool × ℕ)
    (xs seen : List α) :
    (queryEraseLoopWithWork equal xs seen).1.length ≤ xs.length + seen.length := by
  induction xs generalizing seen with
  | nil => simp only [queryEraseLoopWithWork, List.length_reverse, List.length_nil, Nat.zero_add, le_refl]
  | cons a xs ih =>
    change (queryEraseLoopWithWork equal xs
      (if (memberByWithWork equal a seen).1 then seen else a :: seen)).1.length ≤ _
    split_ifs
    · exact (ih seen).trans (by simp only [List.length_cons]; omega)
    · exact (ih (a :: seen)).trans (by simp only [List.length_cons]; omega)

theorem queryEraseWithWork_length {α : Type*} (equal : α → α → Bool × ℕ) (xs : List α) :
    (queryEraseWithWork equal xs).1.length ≤ xs.length := by
  simpa only [queryEraseWithWork, List.length_nil, Nat.add_zero] using
    queryEraseLoopWithWork_length equal xs []

theorem queryOrderedInputsWithWork_cost {α : Type*}
    (encode : α → ℕ) (equal le : α → α → Bool × ℕ)
    (hle : ∀ a b, (le a b).1 = decide (encode a ≤ encode b))
    (C D : ℕ) (hequal : ∀ a b, (equal a b).2 ≤ C) (horder : ∀ a b, (le a b).2 ≤ D)
    (xs : List α) :
    (queryOrderedInputsWithWork equal le xs).2 ≤
      (xs.length + 1) ^ 2 * (C + D + 8) := by
  have he := queryEraseWithWork_cost equal C hequal xs
  have hs := querySortWithWork_cost (fun a b => encode a ≤ encode b) le hle D horder
    (queryEraseWithWork equal xs).1
  have hl := queryEraseWithWork_length equal xs
  have hp : ((queryEraseWithWork equal xs).1.length + 1) ^ 2 ≤ (xs.length + 1) ^ 2 := by
    gcongr
  have hb := hs.trans (Nat.mul_le_mul_right (D + 3) hp)
  change (queryEraseWithWork equal xs).2 + _ + 1 ≤ _
  nlinarith only [he, hb, Nat.zero_le C, Nat.zero_le D, Nat.zero_le xs.length]

theorem queryEncodedLEWithWork_cost {α : Type*} (code : α → ℕ × ℕ)
    (a b : α) (C B : ℕ) (ha : (code a).2 ≤ C) (hb : (code b).2 ≤ C)
    (hva : Nat.size (code a).1 ≤ B) (hvb : Nat.size (code b).1 ≤ B) :
    (queryEncodedLEWithWork code a b).2 ≤ 2 * C + 10 * B + 5 := by
  have hc := wordLEWithWork_cost (code a).1.bits (code b).1.bits
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hc
  change _ + _ + _ + _ + _ + 3 ≤ _
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCodeBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.balancedCutWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.saturatingSubtractWithWork_value _root_.OAI.EditApproximation.seedGridSpacingWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.triangularMassWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Key encoding uses only a fixed number of natural-word operations.
Its word sizes and Boolean work are polynomial in the coordinate widths. -/

namespace EditApproximation

theorem queryNaturalAdd_size (a b : ℕ) : Nat.size (a + b) ≤ Nat.size a + Nat.size b + 1 := by
  have h := bitAddWithWork_length a.bits b.bits false
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalAddWithWork a b).1)
  rw [binaryNaturalAddWithWork_value] at hs
  simp only [binaryNaturalAddWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalMul_size (a b : ℕ) : Nat.size (a * b) ≤ 2 * Nat.size a + Nat.size b + 1 := by
  have h := bitMulWithWork_length a.bits b.bits
  have hs := Nat.size_le.mpr (bitWordValue_lt_pow_length (binaryNaturalMulWithWork a b).1)
  rw [binaryNaturalMulWithWork_value] at hs
  simp only [binaryNaturalMulWithWork] at hs
  simp only [Nat.size_eq_bits_len] at h
  omega

theorem queryNaturalAdd_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalAddWithWork a b).2 ≤ 18 * K + 1 := by
  have h := binaryNaturalAddWithWork_cost a b
  omega

theorem queryNaturalMul_cost (a b K : ℕ) (ha : Nat.size a ≤ K) (hb : Nat.size b ≤ K) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (K + 1) * (2 * K + 1) := by
  apply (binaryNaturalMulWithWork_cost a b).trans
  gcongr
  omega

theorem queryChildCodeWithWork_bounds {M n : ℕ} (input : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    Nat.size (queryChildCodeWithWork input).1 ≤ 8 * (B + 1) ∧
      (queryChildCodeWithWork input).2 ≤ 100000 * (B + 1) ^ 2 := by
  have hi : Nat.size input.1.val ≤ B := (Nat.size_le_size input.1.isLt.le).trans hM
  have hl : Nat.size input.2.lo ≤ B :=
    (Nat.size_le_size (input.2.ordered.trans input.2.valid)).trans hn
  have hh : Nat.size input.2.hi ≤ B := (Nat.size_le_size input.2.valid).trans hn
  have hw : Nat.size (n + 1) ≤ B + 2 := by
    have h := queryNaturalAdd_size n 1
    norm_num only [Nat.size_one] at h
    omega
  have hhigh : Nat.size ((n + 1) * input.2.hi) ≤ 3 * B + 5 := by
    have h := queryNaturalMul_size (n + 1) input.2.hi
    omega
  have hcoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ 4 * B + 6 := by
    have h := queryNaturalAdd_size input.2.lo ((n + 1) * input.2.hi)
    omega
  have hscaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 6 * B + 7 := by
    have h := queryNaturalMul_size M (input.2.lo + (n + 1) * input.2.hi)
    omega
  have hout : Nat.size (input.1.val + M * (input.2.lo + (n + 1) * input.2.hi)) ≤ 7 * B + 8 := by
    have h := queryNaturalAdd_size input.1.val (M * (input.2.lo + (n + 1) * input.2.hi))
    omega
  constructor
  · rw [queryChildCodeWithWork_value]
    exact hout.trans (by omega)
  · let K := 8 * (B + 1)
    have h1 : Nat.size 1 ≤ K := by norm_num only [Nat.size_one]; dsimp [K]; omega
    have hN : Nat.size n ≤ K := by dsimp [K]; omega
    have hW : Nat.size (n + 1) ≤ K := by dsimp [K]; omega
    have hI : Nat.size input.1.val ≤ K := by dsimp [K]; omega
    have hL : Nat.size input.2.lo ≤ K := by dsimp [K]; omega
    have hH : Nat.size input.2.hi ≤ K := by dsimp [K]; omega
    have hM' : Nat.size M ≤ K := by dsimp [K]; omega
    have hHigh : Nat.size ((n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hCoord : Nat.size (input.2.lo + (n + 1) * input.2.hi) ≤ K := by dsimp [K]; omega
    have hScaled : Nat.size (M * (input.2.lo + (n + 1) * input.2.hi)) ≤ K := by dsimp [K]; omega
    have c1 := queryNaturalAdd_cost n 1 K hN h1
    have c2 := queryNaturalMul_cost (n + 1) input.2.hi K hW hH
    have c3 := queryNaturalAdd_cost input.2.lo ((n + 1) * input.2.hi) K hL hHigh
    have c4 := queryNaturalMul_cost M (input.2.lo + (n + 1) * input.2.hi) K hM' hCoord
    have c5 := queryNaturalAdd_cost input.1.val (M * (input.2.lo + (n + 1) * input.2.hi)) K hI hScaled
    simp only [queryChildCodeWithWork, binaryNaturalAddWithWork_value, binaryNaturalMulWithWork_value]
    dsimp only [K] at c1 c2 c3 c4 c5
    nlinarith only [c1, c2, c3, c4, c5, Nat.zero_le B]

theorem queryChildOrderWithWork_cost {M n : ℕ} (a b : Fin M × TargetInterval n)
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryEncodedLEWithWork queryChildCodeWithWork a b).2 ≤ 201000 * (B + 1) ^ 2 := by
  have ha := queryChildCodeWithWork_bounds a B hM hn
  have hb := queryChildCodeWithWork_bounds b B hM hn
  have h := queryEncodedLEWithWork_cost queryChildCodeWithWork a b
    (100000 * (B + 1) ^ 2) (8 * (B + 1)) ha.2 hb.2 ha.1 hb.1
  nlinarith only [h, Nat.zero_le B]

theorem queryOrderedChildInputsWithWork_cost {M n : ℕ} (inputs : List (Fin M × TargetInterval n))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryOrderedChildInputsWithWork inputs).2 ≤
      (inputs.length + 1) ^ 2 * (202000 * (B + 1) ^ 2) := by
  have h := queryOrderedInputsWithWork_cost childInputCode coordinateEqualWithWork
    (queryEncodedLEWithWork queryChildCodeWithWork)
    (fun a b => by simp only [queryEncodedLEWithWork_value, queryChildCodeWithWork_value])
    (24 * B + 8) (201000 * (B + 1) ^ 2)
    (fun a b => coordinateEqualWithWork_cost a b B hM hn)
    (fun a b => queryChildOrderWithWork_cost a b B hM hn) inputs
  apply h.trans
  gcongr
  nlinarith only [Nat.zero_le B]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialSupport
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.triangularMassWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Executed Boolean construction of the first adaptive refinement lists.
Their values are the original lists, including ordering and repetitions. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryRawCentersWithWork_value {n : ℕ} (N P F : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryRawCentersWithWork N P F a value q).1 =
      rawRefinementCenters N P F a.value value.value q := by
  have hg (b : ℕ) : (gridStateBoxWithWork n (seedGridSpacing b P)
      ⌈value.value⌉₊ q.lo q.hi).1 = localTargetStates n (seedGridSpacing b P) ⌈value.value⌉₊ q := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ (by unfold seedGridSpacing; omega)]
    rfl
  simp only [queryRawCentersWithWork, queryEraseWithWork_value _ queryIntervalEqualWithWork_value,
    arithmeticFlatMapWithWork_value, seedGridSpacingWithWork_value _ _ hP,
    naturalCeilingWithWork_value, hg, queryScalesWithWork_value, rawRefinementCenters]



@[simp] theorem queryInitialSupportWithWork_value {n : ℕ} (N P F exponent : ℕ) (hP : 0 < P)
    (a value : BinaryFraction) (q : TargetInterval n) :
    (queryInitialSupportWithWork N P F exponent hP a value q).1 =
      refinementInitialSupport N P F exponent a.value value.value q := by
  simp only [queryInitialSupportWithWork, queryRawCentersWithWork_value _ _ _ hP,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value _ _ hP, canonicalMulWithWork_value, inversePowerTwo_value,
    nat_value, queryGroupKeysWithWork_value, queryOnlineKeysWithWork_value,
    localOnlineSourceKeys, List.map_map, refinementInitialSupport]
  rfl

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRepresentatives
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryOrderedChildInputsWithWork_value _root_.OAI.EditApproximation.queryOrderedHistoryInputsWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted representative and child-coordinate lists for adaptive band
data gathers. All initial-table lookups are included in the work counter. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryWideInputsWithWork_value {nx ny : ℕ} (M : ℕ)
    (parent : TargetInterval nx) (P : ℕ) (hP : 0 < P)
    (representatives : List (ℕ × TargetInterval ny)) :
    (queryWideInputsWithWork M parent P representatives).1 = wideWarmupInputs parent P representatives := by
  simp only [queryWideInputsWithWork, queryEraseWithWork_value _ coordinateEqualWithWork_value,
    arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    wideChildGridWithWork_value _ _ _ _ _ hP, wideWarmupInputs]



end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryActionInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds for the final adaptive child gather.  The temporary list and
its sorting work depend on emitted actions, rather than the full table. -/

namespace EditApproximation

theorem queryActionInputsWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (queryActionInputsWithWork actions).1.length = actions.length * M ∧
    (queryActionInputsWithWork actions).2 ≤ actions.length * (5 * M + 3) + M + 1 := by
  let run := fun action : BinaryBellmanAction Parent Child M =>
    arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M)
  have hlen (action : BinaryBellmanAction Parent Child M) : (run action).1.length = M := by
    simp only [run, arithmeticMapWithWork_value, List.length_map, List.length_finRange]
  have hc (action : BinaryBellmanAction Parent Child M) : (run action).2 ≤ 4 * M := by
    have h := arithmeticMapWithWork_cost (fun i : Fin M => (action.childState i, 1))
      (List.finRange M) 1 (fun _ _ => le_rfl)
    simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using h
  constructor
  · simp only [queryActionInputsWithWork, arithmeticFlatMapWithWork_value, List.length_flatMap,
      arithmeticMapWithWork_value, List.length_map, List.length_finRange, List.map_const',
      List.sum_replicate, smul_eq_mul]
  · have h := arithmeticFlatMapWithWork_cost run actions (4 * M) M
      (fun action _ => hc action) (fun action _ => (hlen action).le)
    change (arithmeticFlatMapWithWork run actions).2 + M + 1 ≤ _
    have heq : 4 * M + M + 3 = 5 * M + 3 := by omega
    rw [heq] at h
    omega

theorem queryOrderedChildInputsWithWork_length {M n : ℕ} (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1.length ≤ inputs.length := by
  rw [queryOrderedChildInputsWithWork_value, orderedInputs_length]
  exact List.toFinset_card_le inputs

theorem queryNeededInputsWithWork_bounds {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryNeededInputsWithWork selected online).1.length ≤ (selected.length + online.length) * M ∧
    (queryNeededInputsWithWork selected online).2 ≤
      queryNeededInputsBitBudget (selected.length + online.length) M B := by
  let first := queryActionInputsWithWork selected
  let second := queryActionInputsWithWork online
  have hf := queryActionInputsWithWork_bounds selected
  have hs := queryActionInputsWithWork_bounds online
  have hl : (first.1 ++ second.1).length = (selected.length + online.length) * M := by
    rw [List.length_append, hf.1, hs.1, Nat.add_mul]
  have hsort := queryOrderedChildInputsWithWork_cost (first.1 ++ second.1) B hM hn
  rw [hl] at hsort
  constructor
  · exact (queryOrderedChildInputsWithWork_length (first.1 ++ second.1)).trans_eq hl
  · change first.2 + second.2 + first.1.length +
      (queryOrderedChildInputsWithWork (first.1 ++ second.1)).2 + 2 ≤ _
    have hfc : first.2 ≤ selected.length * (5 * M + 3) + M + 1 := hf.2
    have hsc : second.2 ≤ online.length * (5 * M + 3) + M + 1 := hs.2
    unfold queryNeededInputsBitBudget
    rw [Nat.add_mul]
    have hfl : first.1.length ≤ (selected.length + online.length) * M := by
      rw [hf.1, Nat.add_mul]
      omega
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryDataBuffers
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Counted local data buffers for the adaptive gathers. Bounds depend on
stored keys and the requested key, not on an unbounded ambient key type. -/

namespace EditApproximation
namespace BinaryFraction

theorem gatheredWordLookupWithWork_cost_on {κ : Type*}
    (equal : κ → κ → Bool × ℕ) (C : ℕ) (keys : List κ)
    (values : List BinaryFraction) (query : κ)
    (hC : ∀ key ∈ keys, (equal query key).2 ≤ C) :
    (gatheredWordLookupWithWork equal keys values query).2 ≤
      1 + keys.length * (C + 1) := by
  induction keys generalizing values with
  | nil => simp only [gatheredWordLookupWithWork, List.length_nil, Nat.zero_mul, Nat.add_zero, le_rfl]
  | cons key keys ih =>
    have hc := hC key List.mem_cons_self
    have ht := ih (values.drop 1) (fun k hk => hC k (List.mem_cons_of_mem _ hk))
    cases values with
    | nil => simp only [gatheredWordLookupWithWork]; omega
    | cons value values =>
      simp only [List.drop_succ_cons, List.drop_zero] at ht
      simp only [gatheredWordLookupWithWork]
      split_ifs <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega



theorem queryHistoryReadWithWork_cost {M n : ℕ}
    (keys : List (Fin M × ℕ × TargetInterval n)) (values : List BinaryFraction)
    (s : ℕ) (input : Fin M × TargetInterval n) (B : ℕ)
    (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) (hs : Nat.size s ≤ B)
    (ht : ∀ key ∈ keys, Nat.size key.2.1 ≤ B) :
    (queryHistoryReadWithWork keys values s input).2 ≤
      1 + keys.length * (32 * B + 12) := by
  apply gatheredWordLookupWithWork_cost_on queryHistoryEqualWithWork (32 * B + 11)
  intro key hk
  have hc := coordinateEqualWithWork_cost input (key.1, key.2.2) B hM hn
  have he := naturalEqualWithWork_cost s key.2.1 B hs (ht key hk)
  change (coordinateEqualWithWork input (key.1, key.2.2)).2 +
    (naturalEqualWithWork s key.2.1).2 + 1 ≤ _
  omega

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryInputCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryRawHistoryInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (P history : ℕ) (hP : 0 < P) (representatives : List (ℕ × TargetInterval ny))
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryRawHistoryInputsWithWork M parent P history representatives).1) :
    input.2.1 < history := by
  rw [queryRawHistoryInputsWithWork_value M parent P history hP] at hi
  obtain ⟨br, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨t, ht, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
  exact List.mem_range.mp ht

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryHistoryBufferCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.BinaryFraction

theorem queryEarlierInputsWithWork_time {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (N P F exponent history : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny)
    (hi : input ∈ (queryEarlierInputsWithWork M parent N P F exponent history hP a initial q).1) :
    input.2.1 < history := by
  simp only [queryEarlierInputsWithWork, queryOrderedHistoryInputsWithWork_value] at hi
  have hm := (mem_orderedInputs historyInputCode (historyInputCode_injective M ny) _ input).mp hi
  rw [List.mem_toFinset] at hm
  exact queryRawHistoryInputsWithWork_time M parent P history hP _ input hm

end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementGather
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The last three adaptive gathers of a refinement request. Each request
list is constructed after the answers on which it depends. The selected
actions, list construction, sorting and buffer cells all carry work. -/

namespace EditApproximation

section Gather
variable {ι β α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ)
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)




theorem queryRefinementGather_work (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
    let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
    let actions := online earlier.1 earlierWords
    let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
      parent a (initial q).1 q draw
    let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
    let groups := selected shared.1 sharedWords
    let current := queryNeededInputsWithWork groups.1 actions.1
    let currentWords := current.1.map fun key => (readCurrent key).value oracle
    (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
      a t initial draw q readEarlier readCurrent online selected next).work oracle readWork =
      earlier.2 + (earlier.1.map fun key => (readEarlier key).work oracle readWork + 3).sum +
      actions.2 + (initial q).2 + shared.2 +
      (shared.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
      groups.2 + current.2 +
      (current.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
      (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork := by
  simp only [queryRefinementGather, BitQuery.work_bind, BitQuery.compute,
    BitQuery.work, BitQuery.value, BitQuery.work_collect,
    Nat.add_zero, Nat.add_assoc]

end Gather

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryRefinementWorkBound
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Composition of the seven executed refinement stages. Recursive reads,
list construction, sorting, both selectors and the final continuation are
all included in this counter. -/

namespace EditApproximation

private theorem query_sum_map_bound {κ : Type*} (xs : List κ) (f : κ → ℕ) (C : ℕ)
    (h : ∀ x ∈ xs, f x ≤ C) : (xs.map f).sum ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

section Work
variable {ι β α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (a : BinaryFraction) (t : ℕ)
  (initial : TargetInterval target.length → BinaryFraction × ℕ)
  (draw : CountedCellGroupDraws M F Q) (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (online : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ)
  (selected : List (Fin M × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) × ℕ)
  (next : List (Fin M × ℕ × TargetInterval target.length) → List BinaryFraction →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (BinaryBellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M) →
    List (Fin M × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)

theorem queryRefinementGather_work_bound (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (B W EL EC OL OC SL SC groupLen GC FC PC : ℕ)
    (hMb : Nat.size M ≤ B) (hny : Nat.size target.length ≤ B) :
    let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
    let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
    let actions := online earlier.1 earlierWords
    let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
      parent a (initial q).1 q draw
    let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
    let groups := selected shared.1 sharedWords
    let current := queryNeededInputsWithWork groups.1 actions.1
    let currentWords := current.1.map fun key => (readCurrent key).value oracle
    earlier.1.length ≤ EL → earlier.2 ≤ EC → actions.1.length ≤ OL → actions.2 ≤ OC →
    shared.1.length ≤ SL → shared.2 ≤ SC → groups.1.length ≤ groupLen → groups.2 ≤ GC →
    (∀ key ∈ earlier.1, (readEarlier key).work oracle readWork ≤ W) →
    (∀ key, (readCurrent key).work oracle readWork ≤ W) →
    (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ FC →
    (initial q).2 ≤ PC →
    (queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF
      a t initial draw q readEarlier readCurrent online selected next).work oracle readWork ≤
      BinaryFraction.queryRefinementStagesBudget M B W EL EC OL OC SL SC groupLen GC PC FC := by
  let earlier := BinaryFraction.queryEarlierInputsWithWork M parent N P F exponent t hP a initial q
  let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
  let actions := online earlier.1 earlierWords
  let shared := BinaryFraction.querySharedInputsWithWork M N F Q exponent eM eF hM hF
    parent a (initial q).1 q draw
  let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
  let groups := selected shared.1 sharedWords
  let current := queryNeededInputsWithWork groups.1 actions.1
  let currentWords := current.1.map fun key => (readCurrent key).value oracle
  dsimp only
  intro heL heC hoL hoC hsL hsC hgL hgC heR hcR hfinish hparent
  change earlier.1.length ≤ EL at heL
  change earlier.2 ≤ EC at heC
  change actions.1.length ≤ OL at hoL
  change actions.2 ≤ OC at hoC
  change shared.1.length ≤ SL at hsL
  change shared.2 ≤ SC at hsC
  change groups.1.length ≤ groupLen at hgL
  change groups.2 ≤ GC at hgC
  change (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ FC at hfinish
  have heRead := (query_sum_map_bound earlier.1 (fun key => (readEarlier key).work oracle readWork + 3)
    (W + 3) (fun key hk => Nat.add_le_add_right (heR key hk) 3)).trans (Nat.mul_le_mul_right _ heL)
  have hsRead := (query_sum_map_bound shared.1 (fun key => (readCurrent key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hcR key) 3)).trans (Nat.mul_le_mul_right _ hsL)
  have hc := queryNeededInputsWithWork_bounds groups.1 actions.1 B hMb hny
  have hcL : current.1.length ≤ (groupLen + OL) * M :=
    hc.1.trans (Nat.mul_le_mul_right M (Nat.add_le_add hgL hoL))
  have hcC : current.2 ≤ queryNeededInputsBitBudget (groupLen + OL) M B := by
    apply hc.2.trans
    unfold queryNeededInputsBitBudget
    gcongr
  have hcRead := (query_sum_map_bound current.1 (fun key => (readCurrent key).work oracle readWork + 3)
    (W + 3) (fun key _ => Nat.add_le_add_right (hcR key) 3)).trans (Nat.mul_le_mul_right _ hcL)
  rw [queryRefinementGather_work]
  change earlier.2 + (earlier.1.map fun key => (readEarlier key).work oracle readWork + 3).sum +
    actions.2 + (initial q).2 + shared.2 +
    (shared.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
    groups.2 + current.2 + (current.1.map fun key => (readCurrent key).work oracle readWork + 3).sum +
    (next earlier.1 earlierWords groups.1 actions.1 current.1 currentWords).work oracle readWork ≤ _
  unfold BinaryFraction.queryRefinementStagesBudget
  omega

end Work
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryReadBoundIrrelevance
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read budgets certify fixed buffer algorithms. Enlarging the
budget changes proof arguments only, and preserves both values and work. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R R' : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (hc' : ∀ i r, (child i r).2 ≤ R') (hi' : ∀ i r, (initial i r).2 ≤ R')

theorem queryGroupSelectWithWork_readBound_irrel (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi draw keys words q =
    queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R' hc' hi' draw keys words q := by
  rfl

theorem queryOnlineSelectWithWork_readBound_irrel (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q =
    queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R' hc' hi' t integer keys words q := by
  rfl

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QuerySelectorCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selector bounds for the actual separate history and shared-current
buffers. The original child-reader budget is preserved in the program. -/

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R U : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (hcU : ∀ i r, (child i r).2 ≤ U) (hiU : ∀ i r, (initial i r).2 ≤ U)
  (hp : ∀ r, (parentInitial r).2 ≤ U)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (earlierKeys : List (Fin M × ℕ × TargetInterval target.length)) (earlierWords : List BinaryFraction)
  (sharedKeys : List (Fin M × TargetInterval target.length)) (sharedWords : List BinaryFraction)
  (q : TargetInterval target.length)
  (hb : PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
    tau a eta kappa delta (fun r => (parentInitial r).1)
    (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun input => (queryHistoryReadWithWork earlierKeys earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork sharedKeys sharedWords input.1 input.2).1)
    (fun s input => (queryHistoryReadWithWork earlierKeys earlierWords s input).1)
    (fun b r => (integer b r).1))

include hb hp hcU hiU in
theorem queryGroupSelectWithWork_bounds (hPdyadic : ∃ j : ℕ, P = 2 ^ j)
    (hshared : ∀ i r, (queryChildReadWithWork sharedKeys sharedWords i r).2 ≤ U) (D : ℕ)
    (hd : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ D) :
    let selected := queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw sharedKeys sharedWords q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    selected.2 ≤ preparedLocalGroupsBitBudget N M P F exponent eM eF B * tableReadFactor U * (D + 4) := by
  have h := preparedLocalCellGroupsSourceWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta parentInitial child initial
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork sharedKeys sharedWords input.1 input.2)
    (queryHistoryReadWithWork earlierKeys earlierWords) U hcU hiU (t - 1) draw integer q hb hp hPdyadic
    (fun input => hshared input.1 input.2) D hd
  rw [queryGroupSelectWithWork_readBound_irrel source target parent N P F exponent Q eM eF hP hM hF
    tau a parentInitial child initial R U hc hi hcU hiU draw sharedKeys sharedWords q]
  simpa only [queryGroupSelectWithWork] using h

include hb hp hcU hiU hM in
theorem queryOnlineSelectWithWork_bounds
    (hh : ∀ s ≤ t - 1 + 1, ∀ input, (queryHistoryReadWithWork earlierKeys earlierWords s input).2 ≤ U)
    (D : ℕ)
    (hd : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ D) :
    let selected := queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer earlierKeys earlierWords q
    selected.1.length ≤ B + 1 ∧
    selected.2 ≤ preparedLocalOnlineBitBudget M P B S * tableReadFactor U * (D + 4) := by
  have h := preparedLocalOnlineActionsSourceWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM tau a eta kappa delta parentInitial child initial
    (queryHistoryReadWithWork earlierKeys earlierWords (t - 1))
    (fun input => queryChildReadWithWork sharedKeys sharedWords input.1 input.2)
    (queryHistoryReadWithWork earlierKeys earlierWords) U hcU hiU (t - 1) integer q hb hp hh D hd
  rw [queryOnlineSelectWithWork_readBound_irrel source target parent N P F exponent H hP
    tau a eta kappa parentInitial child initial R U hc hi hcU hiU t integer earlierKeys earlierWords q]
  simpa only [queryOnlineSelectWithWork] using h

end Selectors
end EditApproximation.BinaryFraction

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryLocalRefinementCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF B E S : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (oracle : ι → BinaryFraction) (readWork : ι → ℕ)

open BinaryFraction

theorem queryLocalRefinement_work_bound_oai (Rp W Dg Do : ℕ)
    (htime : 0 < t) (ht : Nat.size t ≤ B) (hPd : ∃ j : ℕ, P = 2 ^ j)
    (hp : ∀ r, (parentInitial r).2 ≤ Rp)
    (heW : ∀ key, ((readEarlier key).value oracle).width ≤ B)
    (hcW : ∀ key, ((readCurrent key).value oracle).width ≤ B)
    (heR : ∀ key ∈ (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1,
      (readEarlier key).work oracle readWork ≤ W)
    (hcR : ∀ key, (readCurrent key).work oracle readWork ≤ W)
    (hdg : ∀ eb ∈ List.range (max 1 N.bits.length),
      (refinementScaleGuardWithWork F (2 ^ eb) a (parentInitial q).1).1 = true →
      ∀ cell ∈ (targetCellsWithWork
        (canonicalMulWithWork (inversePowerTwo exponent) (nat (2 ^ eb))).1
        (bitWordValue (naturalCeilingWithWork (parentInitial q).1).1) q).1,
      ∀ scale sample, (draw (2 ^ eb) cell scale sample).2 ≤ Dg)
    (hdo : ∀ e ∈ (queryExponentsWithWork N F a (parentInitial q).1).1,
      (centerEligibilityWithWork (2 ^ e) F a
        (parentInitial (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).1).1 = true →
        (integer (2 ^ e) (roundStateWithWork (bitWordValue (seedGridSpacingWithWork (2 ^ e) P).1)
          (seedGridSpacingWithWork_pos (2 ^ e) P hP) q).1).2 ≤ Do)
    (hb :
      let earlier := (queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q).1
      let earlierWords := earlier.map fun key => (readEarlier key).value oracle
      let shared := (querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a
        (parentInitial q).1 q draw).1
      let sharedWords := shared.map fun key => (readCurrent key).value oracle
      PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
        tau a eta kappa delta (fun r => (parentInitial r).1)
        (fun i r => (child i r).1) (fun i r => (initial i r).1)
        (fun input => (queryHistoryReadWithWork earlier earlierWords (t - 1) input).1)
        (fun input => (queryChildReadWithWork shared sharedWords input.1 input.2).1)
        (fun s input => (queryHistoryReadWithWork earlier earlierWords s input).1)
        (fun b r => (integer b r).1)) :
    (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      parentInitial child initial R hc hi draw integer q readEarlier readCurrent).work oracle readWork ≤
      queryLocalRefinementBitBudget M N P F exponent eM eF B S t Rp R W Dg Do := by
  let earlier := queryEarlierInputsWithWork M parent N P F exponent t hP a parentInitial q
  let earlierWords := earlier.1.map fun key => (readEarlier key).value oracle
  let shared := querySharedInputsWithWork M N F Q exponent eM eF hM hF parent a (parentInitial q).1 q draw
  let sharedWords := shared.1.map fun key => (readCurrent key).value oracle
  let EL := queryHistoryInputsLength M P t (queryEarlierRepresentativesLength P F exponent B)
  let SL := querySharedInputsLength M F exponent eM eF B
  let G := (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2
  let U := queryRefinementReadBudget B Rp R EL SL
  change PreparedKernelInputBounds (nx := source.length) N P F exponent H Q eM eF B E S (t - 1)
    tau a eta kappa delta (fun r => (parentInitial r).1) (fun i r => (child i r).1) (fun i r => (initial i r).1)
    (fun input => (queryHistoryReadWithWork earlier.1 earlierWords (t - 1) input).1)
    (fun input => (queryChildReadWithWork shared.1 sharedWords input.1 input.2).1)
    (fun s input => (queryHistoryReadWithWork earlier.1 earlierWords s input).1) (fun b r => (integer b r).1) at hb
  have hB : 10 ≤ B := hb.largeBits
  have hFpos : 1 ≤ F := by rw [hF]; exact Nat.one_le_two_pow
  have hnx : Nat.size source.length ≤ B := by have := hb.sourceSize; omega
  have hny : Nat.size target.length ≤ B := by have := hb.targetSize; omega
  have hMb : Nat.size M ≤ B := by have := hb.aritySize; omega
  have hE := queryEarlierInputsWithWork_bounds M N P F exponent t B Rp parent hP a parentInitial q
    (by omega) hb.inputSize hb.factorSize hFpos hb.precisionSize hnx hny hMb ht hb.thetaSize
    hb.factorWidth hb.parentSize hp (hb.parentNonneg q) hPd
  have hSh := querySharedInputsWithWork_bounds_on M N F Q exponent eM eF B Dg hM hF parent a
    (parentInitial q).1 q draw (by omega) hb.inputSize hb.factorSize hb.aritySize hb.sampleSize hb.scaleSizes
    hb.thetaSize hnx hny hb.factorWidth (hb.parentSize q) (hb.parentNonneg q) (by
      intro eb heb cell hcell
      have hmem := heb
      simp only [queryExponentsWithWork, filterWithWork_value, List.mem_filter] at hmem
      exact hdg eb hmem.1 hmem.2 cell hcell)
  have hEU : ∀ s ≤ t - 1 + 1, ∀ input,
      (queryHistoryReadWithWork earlier.1 earlierWords s input).2 ≤ U := by
    intro s hs input
    have hs' : s ≤ t := by omega
    have hr := queryHistoryReadWithWork_cost earlier.1 earlierWords s input B hMb hny
      ((Nat.size_le_size hs').trans ht) (fun key hk =>
        (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht)
    have hm := Nat.mul_le_mul_right (32 * B + 12) hE.1
    change earlier.1.length * (32 * B + 12) ≤ EL * (32 * B + 12) at hm
    dsimp only [U, queryRefinementReadBudget]
    omega
  have hSU : ∀ i r, (queryChildReadWithWork shared.1 sharedWords i r).2 ≤ U := by
    intro i r
    have hr := queryChildReadWithWork_cost shared.1 sharedWords i r B hMb hny
    have hm := Nat.mul_le_mul_right (24 * B + 9) hSh.1
    change shared.1.length * (24 * B + 9) ≤ SL * (24 * B + 9) at hm
    dsimp only [U, queryRefinementReadBudget]
    omega
  have hRU : R ≤ U := by dsimp only [U, queryRefinementReadBudget]; omega
  have hpU : ∀ r, (parentInitial r).2 ≤ U := by
    intro r
    exact (hp r).trans (by dsimp only [U, queryRefinementReadBudget]; omega)
  have hcU : ∀ i r, (child i r).2 ≤ U := fun i r => (hc i r).trans hRU
  have hiU : ∀ i r, (initial i r).2 ≤ U := fun i r => (hi i r).trans hRU
  have hg := queryGroupSelectWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM hF tau a eta kappa delta t parentInitial child initial R U hc hi hcU hiU hpU draw integer
    earlier.1 earlierWords shared.1 sharedWords q hb hPd hSU Dg hdg
  have ho := queryOnlineSelectWithWork_bounds source target parent N P F exponent H Q eM eF B E S
    hP hM tau a eta kappa delta t parentInitial child initial R U hc hi hcU hiU hpU integer
    earlier.1 earlierWords shared.1 sharedWords q hb hEU Do hdo
  have heWords : ∀ w ∈ earlierWords, w.width ≤ B := by
    intro w hw
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
    exact heW key
  have heTimes : ∀ key ∈ earlier.1, Nat.size key.2.1 ≤ B := by
    intro key hk
    exact (Nat.size_le_size (queryEarlierInputsWithWork_time M parent N P F exponent t hP a parentInitial q key hk).le).trans ht
  unfold queryLocalRefinement
  apply queryRefinementGather_work_bound source target parent N P F exponent Q eM eF hP hM hF a t
    parentInitial draw q readEarlier readCurrent _ _ _ oracle readWork B W EL _ (B + 1) _ SL _ G _ _ Rp hMb hny
  · exact hE.1
  · exact hE.2
  · exact ho.1
  · exact ho.2
  · exact hSh.1
  · exact hSh.2
  · exact hg.1
  · exact hg.2
  · exact heR
  · exact hcR
  · let current := queryNeededInputsWithWork
      (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
        parentInitial child initial R hc hi draw shared.1 sharedWords q).1
      (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
        parentInitial child initial R hc hi t integer earlier.1 earlierWords q).1
    have hw : ∀ w ∈ current.1.map (fun key => (readCurrent key).value oracle), w.width ≤ B := by
      intro w hw
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hw
      exact hcW key
    have hf := queryLocalRefinement_finish_bounds source target parent N P F exponent H Q eM eF
      hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi draw integer
      earlier.1 earlierWords shared.1 sharedWords (current.1.map fun key => (readCurrent key).value oracle) q
      B Rp EL hB hb.inputSize hnx hb.targetSize hMb hb.precisionSize hb.factorSize ht hb.factorWidth
      hb.decrementSize hb.parentSize hp (hb.parentNonneg q) heWords hw heTimes hE.1
    simpa only [BitQuery.compute, BitQuery.work, Nat.add_zero] using hf.2
  · exact hp q

end Local
end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.queryLocalRefinement_work_bound_oai.{u_1, u_2} := @OAI.EditApproximation.queryLocalRefinement_work_bound_oai.{u_1, u_2}
