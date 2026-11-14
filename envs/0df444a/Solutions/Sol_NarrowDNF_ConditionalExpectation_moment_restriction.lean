-- Prove2me | solution 1 for NarrowDNF.ConditionalExpectation.moment_restriction
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:50.766659+00:00
-- url     : https://prove2.me/submissions/b77ef650-f9e7-4a67-b182-6bc5a001a461

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














































































omit [DecidableEq ι] in
/-- Product weights factor over a coordinate predicate and its complement. -/
private theorem weight_partition (p : ℝ) (P : ι → Prop) [DecidablePred P] (x : ι → Bool) :
    weight p x = weight p (fun i : {i // P i} => x i) *
      weight p (fun i : {i // ¬ P i} => x i) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => bitWeight p (x i))).symm











end NarrowDNF.ProductMeasure

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.ConditionalExpectation
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The coordinate conditional moment factors into the fixed assignment's mass
and the product average over the remaining coordinates. -/
theorem solution (p : ℝ) (P : ι → Prop) [DecidablePred P]
    (F : Cube ι → ℝ) (z : {i // P i} → Bool) :
    moment (fun x : Cube ι => fun i : {i // P i} => x i) (ProductMeasure.weight p) F z =
      ProductMeasure.weight p z * ProductMeasure.expectation p (fun y => F (merge P z y)) := by
  unfold moment ProductMeasure.expectation
  rw [Fintype.sum_equiv (restrictionFiberEquiv P z)
    (fun x => ProductMeasure.weight p x.val * F x.val)
    (fun y => ProductMeasure.weight p z * (ProductMeasure.weight p y * F (merge P z y)))
    (fun x => by
      have hx : merge P z (fun i : {i // ¬ P i} => x.val i) = x.val :=
        congrArg Subtype.val ((restrictionFiberEquiv P z).symm_apply_apply x)
      change ProductMeasure.weight p x.val * F x.val = ProductMeasure.weight p z *
        (ProductMeasure.weight p (fun i : {i // ¬ P i} => x.val i) *
          F (merge P z (fun i => x.val i)))
      rw [hx, ProductMeasure.weight_partition p P x.val, x.property]
      ring)]
  rw [← Finset.mul_sum]
