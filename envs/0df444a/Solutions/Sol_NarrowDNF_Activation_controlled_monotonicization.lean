-- Prove2me | solution 1 for NarrowDNF.Activation.controlled_monotonicization
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:25:50.904627+00:00
-- url     : https://prove2.me/submissions/68c99b52-1377-44d8-87b0-62eae31064cf

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_AdaptiveShift
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_FiberShift
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_ShiftProbability
import Theorems.Thm_NarrowDNF_Activation_load_forcing_le
import Theorems.Thm_NarrowDNF_Activation_sameAtom_of_active_subset_of_agree
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split
import Theorems.Thm_NarrowDNF_ProductMeasure_forcing_mass
import Theorems.Thm_NarrowDNF_ShiftProbability_one_coordinate_error_le
import Theorems.Thm_NarrowDNF_Weighted_select_two_budgets
import Theorems.Thm_NarrowDNF_monotone_of_coordinateMonotone

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability

section


/-! Local activation families and their adaptive atoms. The global-input encoding
of a local activation carries an explicit locality proof, so it does not grant
an activation access to coordinates outside its indexing set. -/
namespace NarrowDNF





namespace Activation
variable {ι : Type*} [DecidableEq ι]









omit [DecidableEq ι] in
private theorem active_mono {J : Activation ι} (hJ : J.Increasing) : Monotone J.active := by
  intro x y hxy i hi
  obtain ⟨S, hiS, hS⟩ := hi
  exact ⟨S, hiS, hJ S hxy hS⟩











end Activation
end NarrowDNF


end

section


namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









namespace Activation





omit [DecidableEq ι] in
@[simp] private theorem mem_activeFinset (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.activeFinset x ↔ i ∈ J.active x := by
  classical
  simp [activeFinset]

omit [DecidableEq ι] in
@[simp] private theorem mem_certificate (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.certificate x ↔ i ∈ J.active x ∧ x i = true := by
  classical
  simp [certificate]

















end Activation
end NarrowDNF


end

section


/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] private theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl









private theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg hp0 hp1 (x i)

private theorem bitWeight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    0 < bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_pos.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : ι → Bool) :
    0 < weight p x :=
  Finset.prod_pos fun i _ => bitWeight_pos hp0 hp1 (x i)

/-- Finite distributivity for independently chosen coordinates. -/
private theorem sum_prod_coordinates {α : Type*} [Fintype α] (F : ι → α → ℝ) :
    (∑ x : ι → α, ∏ i, F i (x i)) = ∏ i, ∑ a, F i a := by
  classical
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) F).symm

@[simp] private theorem sum_weight (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [sum_prod_coordinates]
  simp

@[simp] private theorem expectation_const (p c : ℝ) : expectation (ι := ι) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

@[simp] private theorem expectation_zero (p : ℝ) : expectation (ι := ι) p (fun _ => 0) = 0 :=
  expectation_const p 0

@[simp] private theorem expectation_one (p : ℝ) : expectation (ι := ι) p (fun _ => 1) = 1 :=
  expectation_const p 1



private theorem expectation_mul_const (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => F x * c) = expectation p F * c := by
  simp [expectation, mul_assoc, Finset.sum_mul]

private theorem expectation_const_mul (p c : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => c * F x) = c * expectation p F := by
  simpa [mul_comm] using expectation_mul_const p c F

private theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)

private theorem expectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : (ι → Bool) → ℝ} (hFG : ∀ x, F x ≤ G x) :
    expectation p F ≤ expectation p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hFG x) (weight_nonneg hp0 hp1 x)

private theorem probability_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : (ι → Bool) → Prop) [DecidablePred P] : 0 ≤ probability p P := by
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> norm_num





@[simp] private theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]









omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]









/-- Change of variables for a finite weighted pushforward, including noninjective maps. -/
private theorem weighted_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (g : α → β) (F : β → ℝ) :
    (∑ a, w a * F (g a)) = ∑ b, (∑ a, if g a = b then w a else 0) * F b := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

/-- The exact OR/forcing distribution law for every real-valued observable. -/
private theorem forcing_expectation (p : ℝ) (F : (ι → Bool) → ℝ) :
    expectation p (fun x => expectation p (fun d => F (fun i => x i || d i))) =
      expectation (2*p-p^2) F := by
  unfold expectation
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type'
    (fun (x d : ι → Bool) => weight p x * weight p d * F (fun i => x i || d i))]
  rw [weighted_pushforward
    (fun t : (ι → Bool) × (ι → Bool) => weight p t.1 * weight p t.2)
    (fun t : (ι → Bool) × (ι → Bool) => fun i => t.1 i || t.2 i) F]
  simp_rw [Fintype.sum_prod_type, forcing_mass]

/-- Interchange an expectation and a finite sum. -/
private theorem expectation_sum {κ : Type*} [Fintype κ] (p : ℝ)
    (F : κ → (ι → Bool) → ℝ) :
    expectation p (fun x => ∑ a, F a x) = ∑ a, expectation p (F a) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite expectations with respect to independent cubes commute. -/
private theorem expectation_comm (p q : ℝ) (F : (ι → Bool) → (ι → Bool) → ℝ) :
    expectation p (fun x => expectation q (F x)) =
      expectation q (fun y => expectation p (fun x => F x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring







omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem extendFalse_on (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : {i // P i}) : extendFalse P z i = z i := by
  simp [extendFalse, i.property]

omit [Fintype ι] [DecidableEq ι] in
@[simp] private theorem extendFalse_off (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) (i : ι) (hi : ¬ P i) : extendFalse P z i = false := by
  simp [extendFalse, hi]



end NarrowDNF.ProductMeasure

end

end

section


namespace NarrowDNF
namespace Activation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





private theorem activeFinset_eq_biUnion (J : Activation ι) (x : Cube ι) :
    J.activeFinset x = (Finset.univ.filter fun S : Finset ι => J.fires S x).biUnion id := by
  classical
  ext i
  simp [active, and_comm]

private theorem active_card_le_sum (J : Activation ι) (x : Cube ι) :
    ((J.activeFinset x).card : ℝ) ≤
      ∑ S : Finset ι, (S.card : ℝ) * (if J.fires S x then 1 else 0) := by
  classical
  rw [activeFinset_eq_biUnion]
  have h := Finset.card_biUnion_le (s := Finset.univ.filter fun S : Finset ι => J.fires S x)
    (t := id)
  have hr : (((Finset.univ.filter fun S : Finset ι => J.fires S x).biUnion id).card : ℝ) ≤
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => J.fires S x), (S.card : ℝ) := by
    exact_mod_cast h
  simpa [Finset.sum_filter, mul_ite] using hr

private theorem expected_active_le_load (J : Activation ι) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProductMeasure.expectation p (fun x => ((J.activeFinset x).card : ℝ)) ≤ J.load p := by
  classical
  apply (ProductMeasure.expectation_mono hp0 hp1 (fun x => active_card_le_sum J x)).trans_eq
  simp only [ProductMeasure.expectation, load, ProductMeasure.probability, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro x _
  ring

end Activation
end NarrowDNF


end

section


/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide











/-- An upper-shifted fiber is nondecreasing. -/
private theorem upper_monotone (v : Fiber) : (upper v).1 ≤ (upper v).2 := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> decide

/-- A lower-shifted fiber is nondecreasing. -/
private theorem lower_monotone (v : Fiber) : (lower v).1 ≤ (lower v).2 := by
  rcases v with ⟨v0, v1⟩
  cases v0 <;> cases v1 <;> decide





/-- The upper shift preserves componentwise ordering between two fibers.
This is the local fact needed to preserve monotonicity in another coordinate. -/
private theorem upper_preserves_order (v w : Fiber)
    (h0 : v.1 ≤ w.1) (h1 : v.2 ≤ w.2) :
    (upper v).1 ≤ (upper w).1 ∧ (upper v).2 ≤ (upper w).2 := by
  rcases v with ⟨v0, v1⟩
  rcases w with ⟨w0, w1⟩
  cases v0 <;> cases v1 <;> cases w0 <;> cases w1 <;>
    simp_all [upper]

/-- The lower shift preserves componentwise ordering between two fibers.
This is the local fact needed to preserve monotonicity in another coordinate. -/
private theorem lower_preserves_order (v w : Fiber)
    (h0 : v.1 ≤ w.1) (h1 : v.2 ≤ w.2) :
    (lower v).1 ≤ (lower w).1 ∧ (lower v).2 ≤ (lower w).2 := by
  rcases v with ⟨v0, v1⟩
  rcases w with ⟨w0, w1⟩
  cases v0 <;> cases v1 <;> cases w0 <;> cases w1 <;>
    simp_all [lower]





end NarrowDNF.FiberShift


end

section


/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
the shift definitions preceding Lemma 3.1 of the 2026-11-06 STOC revision, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]









@[simp] private theorem upperShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (lowerInput i x) = v (lowerInput i x) := by
  simp [upperShift, lowerInput]

@[simp] private theorem upperShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (upperInput i x) = (v (lowerInput i x) || v (upperInput i x)) := by
  simp [upperShift, lowerInput, upperInput, Bool.or_comm]

@[simp] private theorem lowerShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (lowerInput i x) = (v (lowerInput i x) && v (upperInput i x)) := by
  simp [lowerShift, lowerInput, upperInput]

@[simp] private theorem lowerShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (upperInput i x) = v (upperInput i x) := by
  simp [lowerShift, upperInput]

private theorem lowerInput_le (i : ι) (x : Cube ι) : lowerInput i x ≤ x := by
  intro j
  by_cases hji : j = i
  · subst j
    simp [lowerInput]
  · simp [lowerInput, hji]





private theorem upperShift_coordinateMonotone (i : ι) (v : Cube ι → Bool) :
    CoordinateMonotone i (upperShift i v) := by
  intro x
  simpa [upperShift, lowerInput, upperInput, FiberShift.upper, Bool.or_comm] using
    FiberShift.upper_monotone (v (lowerInput i x), v (upperInput i x))

private theorem lowerShift_coordinateMonotone (i : ι) (v : Cube ι → Bool) :
    CoordinateMonotone i (lowerShift i v) := by
  intro x
  simpa [lowerShift, lowerInput, upperInput, FiberShift.lower] using
    FiberShift.lower_monotone (v (lowerInput i x), v (upperInput i x))

private theorem upperShift_preserves_coordinateMonotone {i j : ι} (hij : i ≠ j)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (upperShift i v) := by
  intro x
  have h1 : v (lowerInput i (lowerInput j x)) ≤
      v (lowerInput i (upperInput j x)) := by
    simpa only [lowerInput, upperInput, Function.update_comm hij] using
      hv (lowerInput i x)
  exact (FiberShift.upper_preserves_order
    (v (lowerInput j x), v (lowerInput i (lowerInput j x)))
    (v (upperInput j x), v (lowerInput i (upperInput j x))) (hv x) h1).2

private theorem lowerShift_preserves_coordinateMonotone {i j : ι} (hij : i ≠ j)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (lowerShift i v) := by
  intro x
  have h1 : v (upperInput i (lowerInput j x)) ≤
      v (upperInput i (upperInput j x)) := by
    simpa only [lowerInput, upperInput, Function.update_comm hij] using
      hv (upperInput i x)
  exact (FiberShift.lower_preserves_order
    (v (lowerInput j x), v (upperInput i (lowerInput j x)))
    (v (upperInput j x), v (upperInput i (upperInput j x))) (hv x) h1).1













private theorem shiftChoice_coordinateMonotone (i : ι) (b : Bool) (v : Cube ι → Bool) :
    CoordinateMonotone i (shiftChoice i b v) := by
  cases b
  · exact upperShift_coordinateMonotone i v
  · exact lowerShift_coordinateMonotone i v

/-- Each chosen shift preserves monotonicity in any already monotone
coordinate, including its own coordinate. -/
private theorem shiftChoice_preserves_coordinateMonotone (i j : ι) (b : Bool)
    {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (shiftChoice i b v) := by
  by_cases hij : i = j
  · subst i
    exact shiftChoice_coordinateMonotone j b v
  · cases b
    · exact upperShift_preserves_coordinateMonotone hij hv
    · exact lowerShift_preserves_coordinateMonotone hij hv

private theorem applyShifts_preserves_coordinateMonotone (shifts : List (ι × Bool))
    (j : ι) {v : Cube ι → Bool} (hv : CoordinateMonotone j v) :
    CoordinateMonotone j (applyShifts shifts v) := by
  induction shifts generalizing v with
  | nil => exact hv
  | cons a rest ih =>
    exact ih (shiftChoice_preserves_coordinateMonotone a.1 j a.2 hv)

/-- Once a coordinate has been processed, it is monotone in the final output. -/
private theorem applyShifts_coordinateMonotone_of_mem (shifts : List (ι × Bool))
    (j : ι) (hj : j ∈ shifts.map Prod.fst) (v : Cube ι → Bool) :
    CoordinateMonotone j (applyShifts shifts v) := by
  induction shifts generalizing v with
  | nil => simp at hj
  | cons a rest ih =>
    rcases a with ⟨i, b⟩
    simp only [List.map_cons, List.mem_cons] at hj
    rcases hj with hji | hj
    · subst j
      exact applyShifts_preserves_coordinateMonotone rest i
        (shiftChoice_coordinateMonotone i b v)
    · exact ih hj (shiftChoice i b v)

/-- Processing every coordinate yields an increasing function, regardless
of processing order, shift choices, or repetitions of coordinates. -/
private theorem applyShifts_monotone [Fintype ι] (shifts : List (ι × Bool))
    (hcovers : ∀ i, i ∈ shifts.map Prod.fst) (v : Cube ι → Bool) :
    Monotone (applyShifts shifts v) := by
  apply monotone_of_coordinateMonotone
  intro i
  exact applyShifts_coordinateMonotone_of_mem shifts i (hcovers i) v

end NarrowDNF


end

section


/-!
# Adaptive atoms under shifts

The precise content of Lemma 3.2 of the 2026-11-06 STOC revision, including its
atom-recovery proof (formerly in Appendix B of arXiv:2609.00240v1).
All activations carry the locality field from `Activation`; no decoder or atom
recovery oracle is assumed. The unbranched formulas for shifts are equivalent
to the paper's two-slice formulas by Boolean idempotence.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]



private theorem le_forceInput (D : Finset ι) (x : Cube ι) : x ≤ forceInput D x := by
  intro i
  simp only [forceInput]
  split <;> simp_all

private theorem forceInput_mono (D : Finset ι) : Monotone (forceInput D) := by
  intro x y hxy i
  simp only [forceInput]
  split
  · exact le_rfl
  · exact hxy i

private theorem forceInput_singleton (i : ι) (x : Cube ι) :
    forceInput {i} x = upperInput i x := by
  funext j
  simp [forceInput, upperInput, Function.update_apply]

namespace Activation



/-- Lowering a fixed coordinate is a well-defined map on adaptive atoms. This
includes the case where the atom does not record that coordinate. -/
private theorem sameAtom_lowerInput {J : Activation ι} (hJ : J.Increasing)
    {x y : Cube ι} (hxy : J.SameAtom x y) (i : ι) :
    J.SameAtom (lowerInput i x) (lowerInput i y) := by
  apply sameAtom_of_active_subset_of_agree
    (B := J.active x) (active_mono hJ (lowerInput_le i x))
  · rw [hxy.1]
    exact active_mono hJ (lowerInput_le i y)
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp [lowerInput]
    · simpa [lowerInput, Function.update_apply, hji] using hxy.2 j hj

/-- An upper shift needs no refinement of the adaptive partition. -/
private theorem measurable_upperShift {J : Activation ι} (hJ : J.Increasing)
    {v : Cube ι → Bool} (hv : J.Measurable v) (i : ι) :
    J.Measurable (upperShift i v) := by
  intro x y hxy
  unfold upperShift
  rw [hv x y hxy, hv _ _ (sameAtom_lowerInput hJ hxy i)]



private theorem force_active (J : Activation ι) (D : Finset ι) (x : Cube ι) :
    (J.force D).active x = J.active (forceInput D x) := rfl

private theorem force_increasing {J : Activation ι} (hJ : J.Increasing) (D : Finset ι) :
    (J.force D).Increasing := by
  intro S x y hxy
  exact hJ S (forceInput_mono D hxy)

/-- A forced atom determines the original atom at the unforced input. -/
private theorem force_refines {J : Activation ι} (hJ : J.Increasing) (D : Finset ι)
    {x y : Cube ι} (hxy : (J.force D).SameAtom x y) : J.SameAtom x y := by
  apply sameAtom_of_active_subset_of_agree
    (B := J.active (forceInput D x)) (active_mono hJ (le_forceInput D x))
  · rw [← force_active, hxy.1, force_active]
    exact active_mono hJ (le_forceInput D y)
  · exact hxy.2

/-- A forced atom also determines the original atom at the forced input.
The proof explicitly changes its recorded actual labels to forced labels. -/
private theorem sameAtom_forceInput {J : Activation ι} (D : Finset ι)
    {x y : Cube ι} (hxy : (J.force D).SameAtom x y) :
    J.SameAtom (forceInput D x) (forceInput D y) := by
  constructor
  · exact hxy.1
  · intro i hi
    simp only [forceInput]
    split
    · rfl
    · exact hxy.2 i hi

/-- A lower shift is measurable for the one-coordinate forced refinement. -/
private theorem measurable_lowerShift {J : Activation ι} (hJ : J.Increasing)
    {v : Cube ι → Bool} (hv : J.Measurable v) (i : ι) :
    (J.force {i}).Measurable (lowerShift i v) := by
  intro x y hxy
  have horiginal : v x = v y := hv x y (force_refines hJ {i} hxy)
  have hupper : J.SameAtom (upperInput i x) (upperInput i y) := by
    simpa only [forceInput_singleton] using sameAtom_forceInput {i} hxy
  unfold lowerShift
  rw [horiginal, hv _ _ hupper]

private theorem forceInput_union (D E : Finset ι) (x : Cube ι) :
    forceInput D (forceInput E x) = forceInput (D ∪ E) x := by
  funext i
  by_cases hiD : i ∈ D <;> by_cases hiE : i ∈ E <;>
    simp [forceInput, hiD, hiE]

private theorem force_force (J : Activation ι) (D E : Finset ι) :
    (J.force D).force E = J.force (D ∪ E) := by
  cases J with
  | mk fires hlocal =>
    simp only [force, forceInput_union]

private theorem force_empty (J : Activation ι) : J.force ∅ = J := by
  have hinput : ∀ x : Cube ι, forceInput ∅ x = x := by
    intro x
    funext i
    simp [forceInput]
  cases J with
  | mk fires hlocal =>
    simp only [force, hinput]



/-- The complete finite-sequence closure statement of Lemma 3.2. It permits
arbitrary interleavings and repetitions, with no commutativity assumption. -/
private theorem measurable_applyShifts (steps : List (ι × Bool)) {J : Activation ι}
    (hJ : J.Increasing) {v : Cube ι → Bool} (hv : J.Measurable v) :
    (J.force (lowerCoordinates steps)).Measurable (applyShifts steps v) := by
  induction steps generalizing J v with
  | nil => simpa only [lowerCoordinates, force_empty, applyShifts] using hv
  | cons step rest ih =>
    rcases step with ⟨i, b⟩
    cases b
    · simpa only [lowerCoordinates, Bool.false_eq_true, if_false, applyShifts,
        shiftChoice] using ih hJ (measurable_upperShift hJ hv i)
    · simpa only [lowerCoordinates, if_true, applyShifts, shiftChoice, force_force,
        Finset.singleton_union] using
        ih (force_increasing hJ {i}) (measurable_lowerShift hJ hv i)

end Activation
end NarrowDNF


end

section


/-!
# Load transport under random forcing

Point-mass and expectation bounds at effective bias `2*p-p^2`. Bounds are stated
without division by point masses, so they hold also for degenerate biases.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











end NarrowDNF.ProductMeasure

namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



private theorem forceInput_forcingCoordinates (d x : Cube ι) :
    forceInput (forcingCoordinates d) x = fun i => x i || d i := by
  funext i
  cases hdi : d i <;> simp [forceInput, forcingCoordinates, hdi]

namespace Activation

open ProductMeasure
attribute [local instance] Classical.propDecidable









/-- Exact mean activation probability after independent Bernoulli forcing. -/
private theorem probability_forced_mean (J : Activation ι) (p : ℝ) (S : Finset ι) :
    expectation p (fun d : Cube ι =>
      probability p ((J.force (forcingCoordinates d)).fires S)) =
        probability (2*p-p^2) (J.fires S) := by
  unfold probability force
  simp only [forceInput_forcingCoordinates]
  rw [expectation_comm]
  exact forcing_expectation p (fun x => if J.fires S x then 1 else 0)

/-- The equality in Lemma 3.4, with a Bernoulli cube encoding the random set D. -/
private theorem load_forced_mean (J : Activation ι) (p : ℝ) :
    expectation p (fun d : Cube ι => (J.force (forcingCoordinates d)).load p) =
      J.load (2*p-p^2) := by
  unfold load
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [expectation_const_mul, probability_forced_mean]







end Activation
end NarrowDNF

end

end

section


/-!
# Randomized coordinate shifting under the biased product measure

This file proves the full error inequality of Lemma 3.1 and the iterated
expectation inequality following Lemma 3.1 in the 2026-11-06 STOC revision. Random choices form an
explicit Bernoulli product cube; the independence needed by iteration is
derived from the finite-sum Fubini formula.
-/

noncomputable section

namespace NarrowDNF.ShiftProbability

open ProductMeasure

variable {ι : Type*} [DecidableEq ι]

private theorem update_insertBit (i : ι) (a b : Bool) (z : {j // j ≠ i} → Bool) :
    Function.update (insertBit i a z) i b = insertBit i b z := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simpa only [Function.update_of_ne hji] using
      (insertBit_away i a z ⟨j, hji⟩).trans (insertBit_away i b z ⟨j, hji⟩).symm

@[simp] private theorem lowerInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    lowerInput i (insertBit i b z) = insertBit i false z :=
  update_insertBit i b false z

@[simp] private theorem upperInput_insertBit (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    upperInput i (insertBit i b z) = insertBit i true z :=
  update_insertBit i b true z

variable [Fintype ι]





/-- An observable unchanged by coordinate updates has the same expectation
after fixing that coordinate to either value. This is proved from Fubini. -/
private theorem expectation_of_ignores_coordinate (p : ℝ) (i : ι) (b : Bool)
    (F : Cube ι → ℝ) (hF : ∀ x c, F (Function.update x i c) = F x) :
    expectation p F = expectation p (fun z => F (insertBit i b z)) := by
  have heq (c : Bool) : (fun z => F (insertBit i c z)) =
      (fun z => F (insertBit i b z)) := by
    funext z
    simpa only [update_insertBit] using (hF (insertBit i c z) b).symm
  rw [expectation_split p i, heq false, heq true]
  ring

/-- Exact independence of a selected Bernoulli bit from an observable of
the remaining coordinates. There is no independence assumption in this lemma. -/
private theorem expectation_coordinate_bind (p : ℝ) (i : ι) (F : Bool → Cube ι → ℝ)
    (hF : ∀ b x c, F b (Function.update x i c) = F b x) :
    expectation p (fun d => F (d i) d) =
      (1-p) * expectation p (F false) + p * expectation p (F true) := by
  rw [expectation_split p i]
  simp only [insertBit_at]
  rw [expectation_of_ignores_coordinate p i false (F false) (hF false),
    expectation_of_ignores_coordinate p i true (F true) (hF true)]



omit [Fintype ι] in
@[simp] private theorem shiftByChoices_nil (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices [] d v = v := rfl

omit [Fintype ι] in
@[simp] private theorem shiftByChoices_cons (i : ι) (order : List ι)
    (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices (i :: order) d v =
      shiftByChoices order d (shiftChoice i (d i) v) := rfl

omit [Fintype ι] in
private theorem shiftByChoices_congr (order : List ι) (d e : Cube ι)
    (hde : ∀ i ∈ order, d i = e i) (v : Cube ι → Bool) :
    shiftByChoices order d v = shiftByChoices order e v := by
  induction order generalizing v with
  | nil => rfl
  | cons i rest ih =>
    rw [shiftByChoices_cons, shiftByChoices_cons, hde i (by simp)]
    exact ih (fun j hj => hde j (by simp [hj])) (shiftChoice i (e i) v)

omit [Fintype ι] in
private theorem shiftByChoices_update_of_not_mem (order : List ι) (i : ι) (hi : i ∉ order)
    (d : Cube ι) (b : Bool) (v : Cube ι → Bool) :
    shiftByChoices order (Function.update d i b) v = shiftByChoices order d v := by
  apply shiftByChoices_congr
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [hji]

/-- Fubini recursion for the exact expected error. Nonrepetition makes the
remaining shifts independent of the bit controlling the first shift. -/
private theorem expected_error_cons (p : ℝ) (i : ι) (order : List ι) (hi : i ∉ order)
    (f v : Cube ι → Bool) :
    expectation p (fun d => ProductMeasure.error p f (shiftByChoices (i :: order) d v)) =
      (1-p) * expectation p (fun d => ProductMeasure.error p f
        (shiftByChoices order d (upperShift i v))) +
      p * expectation p (fun d => ProductMeasure.error p f
        (shiftByChoices order d (lowerShift i v))) := by
  simpa only [shiftByChoices_cons, shiftChoice, Bool.false_eq_true, if_false, if_true] using
    expectation_coordinate_bind p i
      (fun b d => ProductMeasure.error p f (shiftByChoices order d (shiftChoice i b v)))
      (fun b d c => congrArg (ProductMeasure.error p f)
        (shiftByChoices_update_of_not_mem order i hi d c (shiftChoice i b v)))

/-- Equation (8)'s error inequality, strengthened to any nonrepeating partial
coordinate order. The random choice cube has the explicit product law `μ_p`. -/
private theorem iterated_error_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (order : List ι) (hnodup : order.Nodup) (f v : Cube ι → Bool) (hf : Monotone f) :
    expectation p (fun d => ProductMeasure.error p f (shiftByChoices order d v)) ≤
      ProductMeasure.error p f v := by
  induction order generalizing v with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨hi, hrest⟩ := List.nodup_cons.mp hnodup
    rw [expected_error_cons p i rest hi]
    apply le_trans _ (one_coordinate_error_le p hp0 hp1 i f v hf)
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih hrest (upperShift i v)) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih hrest (lowerShift i v)) hp0)



private theorem shiftByChoices_monotone (order : List ι) (hcovers : ∀ i, i ∈ order)
    (d : Cube ι) (v : Cube ι → Bool) : Monotone (shiftByChoices order d v) := by
  apply applyShifts_monotone
  intro i
  rw [List.map_map]
  change i ∈ List.map id order
  simpa only [List.map_id] using hcovers i



end NarrowDNF.ShiftProbability

end

end

section


noncomputable section
namespace NarrowDNF
namespace Activation
open ProductMeasure ShiftProbability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The set of lower shifts along a covering coordinate order is exactly the
set represented by the Bernoulli choice vector. -/
private theorem lowerCoordinates_map_choices (order : List ι) (D : Cube ι) (i : ι) :
    i ∈ lowerCoordinates (order.map fun j => (j, D j)) ↔ i ∈ order ∧ D i = true := by
  induction order with
  | nil => simp [lowerCoordinates]
  | cons j rest ih =>
    cases hj : D j <;> by_cases hij : i = j <;>
      simp_all [lowerCoordinates]

private theorem lowerCoordinates_cover (order : List ι) (horder : ∀ i, i ∈ order) (D : Cube ι) :
    lowerCoordinates (order.map fun i => (i, D i)) = forcingCoordinates D := by
  ext i
  simp [lowerCoordinates_map_choices, horder, forcingCoordinates]



end Activation
end NarrowDNF

end

end

noncomputable section
open NarrowDNF
open NarrowDNF
open NarrowDNF.Activation
open ProductMeasure ShiftProbability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Theorem 3.5 of the 2026-11-06 STOC revision, with explicit finite random choices,
full adaptive measurability, and the zero-load edge case included. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {d : ℕ} {e L : ℝ} (_he0 : 0 ≤ e) (hL0 : 0 ≤ L)
    {f : Cube ι → Bool} (hf : Monotone f)
    {J : Activation ι} (hJ : J.Increasing) (hd : J.ArityLE d)
    {h : Cube ι → Bool} (hh : J.Measurable h)
    (he : error p f h ≤ e) (hL : J.load p ≤ L)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ (D : Finset ι) (u : Cube ι → Bool),
      Monotone u ∧ (J.force D).Measurable u ∧ error p f u ≤ e + τ ∧
      expectation p (fun x => (((J.force D).activeFinset x).card : ℝ)) ≤
        (2-p)^d * L * (1 + e / τ) := by
  classical
  let order := (Finset.univ : Finset ι).toList
  have hn : order.Nodup := Finset.nodup_toList _
  have hc : ∀ i, i ∈ order := by intro i; simp [order]
  let H := fun D : Cube ι => shiftByChoices order D h
  let cost := fun D : Cube ι =>
    expectation p (fun x => (((J.force (forcingCoordinates D)).activeFinset x).card : ℝ))
  have hcost : ∀ D, 0 ≤ cost D := by
    intro D
    exact expectation_nonneg hp0.le hp1.le (fun x => Nat.cast_nonneg _)
  have hcostMean : expectation p cost ≤ (2-p)^d * L := by
    calc
      expectation p cost ≤ expectation p (fun D : Cube ι =>
          (J.force (forcingCoordinates D)).load p) :=
        expectation_mono hp0.le hp1.le (fun D => expected_active_le_load _ hp0.le hp1.le)
      _ = J.load (2*p-p^2) := load_forced_mean J p
      _ ≤ (2-p)^d * J.load p := load_forcing_le J hp0.le hp1.le hd
      _ ≤ (2-p)^d * L := mul_le_mul_of_nonneg_left hL (pow_nonneg (by linarith : (0:ℝ) ≤ 2-p) d)
  have herrMean : expectation p (fun D => error p f (H D)) ≤ e :=
    (iterated_error_le p hp0.le hp1.le order hn f h hf).trans he
  obtain ⟨D, hDe, hDc⟩ := Weighted.select_two_budgets
    (weight p) (weight_pos hp0 hp1) (sum_weight p)
    (fun D => error p f (H D)) cost
    (fun D => probability_nonneg hp0.le hp1.le _) hcost
    e ((2-p)^d * L) τ (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ 2-p) d) hL0) hτ herrMean hcostMean
  refine ⟨forcingCoordinates D, H D, shiftByChoices_monotone order hc D h, ?_, hDe, hDc⟩
  have hm := measurable_applyShifts (order.map fun i => (i, D i)) hJ hh
  rw [lowerCoordinates_cover order hc D] at hm
  exact hm
