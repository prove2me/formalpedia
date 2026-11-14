-- Prove2me | solution 1 for NarrowDNF.Fourier.eq_mean_of_variance_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:12:24.158925+00:00
-- url     : https://prove2.me/submissions/e73a2782-9514-4e6f-a21b-63fc05527821

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

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





































































end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Fourier
section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- With full-support Bernoulli weights, zero variance forces pointwise constancy. -/
theorem solution {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → ℝ) (hf : Influence.variance p f ≤ 0) (x : ι → Bool) :
    f x = ProductMeasure.expectation p f := by
  have hnon (y : ι → Bool) : 0 ≤ ProductMeasure.weight p y *
      (f y - ProductMeasure.expectation p f) ^ 2 :=
    mul_nonneg (ProductMeasure.weight_nonneg hp0.le hp1.le y) (sq_nonneg _)
  have hle := Finset.single_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (ι → Bool))) => hnon y)
    (Finset.mem_univ x)
  have hz : ProductMeasure.weight p x * (f x - ProductMeasure.expectation p f) ^ 2 = 0 := by
    apply le_antisymm _ (hnon x)
    exact hle.trans hf
  have hs : (f x - ProductMeasure.expectation p f) ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (ne_of_gt (ProductMeasure.weight_pos hp0 hp1 x))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
