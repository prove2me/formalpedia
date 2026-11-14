-- Prove2me | solution 1 for NarrowDNF.ConditionalExpectation.local_conditional_independence
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:23:49.35621+00:00
-- url     : https://prove2.me/submissions/8426212c-6ea6-4331-82e9-edf187109b94

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_merge
import Theorems.Thm_NarrowDNF_ConditionalExpectation_expectation_mul_of_complement_local
import Theorems.Thm_NarrowDNF_ConditionalExpectation_moment_restriction
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_restrict

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

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

















@[simp] private theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]









omit [Fintype ι] in
@[simp] private theorem insertBit_at (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool) :
    insertBit i b z i = b := by simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] in
@[simp] private theorem insertBit_away (i : ι) (b : Bool) (z : {j // j ≠ i} → Bool)
    (j : {j // j ≠ i}) : insertBit i b z j = z j := by
  simp [insertBit, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

















omit [DecidableEq ι] in
/-- Product weights factor over a coordinate predicate and its complement. -/
private theorem weight_partition (p : ℝ) (P : ι → Prop) [DecidablePred P] (x : ι → Bool) :
    weight p x = weight p (fun i : {i // P i} => x i) *
      weight p (fun i : {i // ¬ P i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => bitWeight p (x i))).symm





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


/-!
# Conditional expectation on a finite partition

A partition is represented by a map `φ : α → β`; each realized fiber has
positive mass when the input weights are strictly positive. This file derives
least-squares projection and Boolean threshold rounding from finite sums. It
does not assume Hatami's construction-specific residual bound.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ConditionalExpectation

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]









omit [Fintype β] [DecidableEq β] in
/-- Conditional means are independent of the implementation of label equality. -/
private theorem mean_decidableEq_irrel (d₁ d₂ : DecidableEq β) (φ : α → β) (w F : α → ℝ) (b : β) :
    @mean α β _ d₁ φ w F b = @mean α β _ d₂ φ w F b := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  rw [hd]









































section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]













end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- Exact probability of a coordinate restriction. -/
private theorem mass_restriction (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (z : {i // P i} → Bool) :
    mass (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) z =
      ProductMeasure.weight p z := by
  unfold mass
  rw [Fintype.sum_equiv (restrictionFiberEquiv P z)
    (fun x => ProductMeasure.weight p x.val)
    (fun y => ProductMeasure.weight p z * ProductMeasure.weight p y)
    (fun x => by
      change ProductMeasure.weight p x.val = ProductMeasure.weight p z *
        ProductMeasure.weight p (fun i : {i // ¬ P i} => x.val i)
      rw [ProductMeasure.weight_partition p P x.val, x.property])]
  rw [← Finset.mul_sum, ProductMeasure.sum_weight, mul_one]



/-- Conditioning a product law on some coordinates leaves its complementary
coordinates independent with their original bias. -/
private theorem mean_restriction {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (P : ι → Prop) [DecidablePred P] (F : Cube ι → ℝ) (z : {i // P i} → Bool) :
    mean (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) F z =
      ProductMeasure.expectation p (fun y => F (merge P z y)) := by
  unfold mean
  rw [mass_restriction, moment_restriction]
  have hn := (ProductMeasure.weight_pos hp0 hp1 z).ne'
  field_simp









end CoordinatePartition
section Localization





variable {ι : Type*} [Fintype ι] [DecidableEq ι]











end Localization
end NarrowDNF.ConditionalExpectation

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Two local functions become independent after conditioning on the coordinates
in the intersection of their supports. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (S R : Finset ι) (F G : Cube ι → ℝ)
    (hF : ∀ x y, (∀ i ∈ S, x i = y i) → F x = F y)
    (hG : ∀ x y, (∀ i ∈ R, x i = y i) → G x = G y) :
    expectation p (fun x => F x * G x) =
      expectation p (fun x =>
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) F x *
        conditional (fun x : Cube ι => fun i : {i // i ∈ S ∩ R} => x i) (weight p) G x) := by
  let T : ι → Prop := fun i => i ∈ S ∩ R
  have hfactor (z : {i // T i} → Bool) :
      expectation p (fun y => F (merge T z y) * G (merge T z y)) =
        expectation p (fun y => F (merge T z y)) *
          expectation p (fun y => G (merge T z y)) := by
    apply expectation_mul_of_complement_local p (fun i : {i // ¬ T i} => i.val ∈ S)
    · intro x y hxy
      apply hF
      intro i hiS
      by_cases hiT : T i
      · simp [merge, hiT]
      · simpa [merge, hiT] using hxy (⟨i,hiT⟩ : {i // ¬ T i}) hiS
    · intro x y hxy
      apply hG
      intro i hiR
      by_cases hiT : T i
      · simp [merge, hiT]
      · have hiS : i ∉ S := by
          intro his
          exact hiT (Finset.mem_inter.mpr ⟨his,hiR⟩)
        simpa [merge, hiT] using hxy (⟨i,hiT⟩ : {i // ¬ T i}) hiS
  rw [expectation_merge p T (fun x => F x * G x)]
  simp_rw [hfactor]
  symm
  change expectation p (fun x : Cube ι => mean (fun x : Cube ι => fun i : {i // T i} => x i)
    (weight p) F (fun i => x i) *
      mean (fun x : Cube ι => fun i : {i // T i} => x i) (weight p) G (fun i => x i)) = _
  trans expectation p (fun x : Cube ι =>
    expectation p (fun y => F (merge T (fun i => x i) y)) *
    expectation p (fun y => G (merge T (fun i => x i) y)))
  · apply congrArg (expectation p)
    funext x
    apply congrArg₂ (fun a b : ℝ => a*b)
    · apply Eq.trans ?_ (mean_restriction (ι := ι) hp0 hp1 T F (fun i => x i))
      exact mean_decidableEq_irrel _ _ _ _ _ _
    · apply Eq.trans ?_ (mean_restriction (ι := ι) hp0 hp1 T G (fun i => x i))
      exact mean_decidableEq_irrel _ _ _ _ _ _
  · exact expectation_restrict p T (fun z => expectation p (fun y => F (merge T z y)) *
      expectation p (fun y => G (merge T z y)))
