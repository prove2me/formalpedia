-- Prove2me | solution 1 for NarrowDNF.Hypercontractivity.cross_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:15:03.226212+00:00
-- url     : https://prove2.me/submissions/468dd669-367e-4188-8c07-fc6435f9906f

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_UniformHypercontractivity

namespace NarrowDNF.Hypercontractivity
end NarrowDNF.Hypercontractivity


noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.Hypercontractivity
attribute [local instance] Classical.decEq
variable {α β : Type*} [Fintype α] [Fintype β]
/-- Cauchy-Schwarz with arbitrary nonnegative finite weights, applied to
the squared outputs of an L2-to-L4 contraction. -/
theorem solution {w : α → ℝ} (hw : ∀ x, 0 ≤ w x)
    {T : (α → ℝ) → α → ℝ} (hT : Contract24 w T) (f g : α → ℝ) :
    (∑ x, w x * (T f x)^2 * (T g x)^2) ≤
      (∑ x, w x * (f x)^2) * (∑ x, w x * (g x)^2) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.univ : Finset α)
    (r := fun x => w x * (T f x)^2 * (T g x)^2)
    (f := fun x => w x * (T f x)^4)
    (g := fun x => w x * (T g x)^4)
    (fun x _ => mul_nonneg (hw x) (by positivity))
    (fun x _ => mul_nonneg (hw x) (by positivity))
    (fun x _ => by ring)
  have hf0 : 0 ≤ ∑ x, w x * (f x)^2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hg0 : 0 ≤ ∑ x, w x * (g x)^2 :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hprod := mul_le_mul (hT f) (hT g)
    (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (by positivity)) (sq_nonneg _)
  have hbound := hcs.trans hprod
  have hnonneg := mul_nonneg hf0 hg0
  nlinarith [sq_nonneg
    ((∑ x, w x * (T f x)^2 * (T g x)^2) -
      (∑ x, w x * (f x)^2) * (∑ x, w x * (g x)^2))]
