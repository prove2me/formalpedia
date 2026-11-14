-- Prove2me | solution 1 for NarrowDNF.ConditionalExpectation.residual_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:11:52.566198+00:00
-- url     : https://prove2.me/submissions/41875a2e-b0aa-447f-b65e-808761fa5c2d

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



@[simp] private theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] private theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl

















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























omit [Fintype β] in
private theorem mass_pos (φ : α → β) (w : α → ℝ) (hw : ∀ a, 0 < w a)
    (a : α) : 0 < mass φ w (φ a) := by
  have hle : w a ≤ mass φ w (φ a) := by
    unfold mass
    exact Finset.single_le_sum (f := fun y : {x // φ x = φ a} => w y)
      (fun y _ => (hw y).le) (Finset.mem_univ (⟨a,rfl⟩ : {x // φ x = φ a}))
  exact (hw a).trans_le hle

omit [Fintype β] in
/-- The mean satisfies its defining weighted first-moment equation on every atom,
including unrealized ones. -/
private theorem mean_mul_mass (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 < w a) (b : β) :
    mean φ w F b * mass φ w b = moment φ w F b := by
  by_cases hb : ∃ a, φ a = b
  · obtain ⟨a, rfl⟩ := hb
    exact div_mul_cancel₀ _ (mass_pos φ w hw a).ne'
  · haveI : IsEmpty {a // φ a = b} := ⟨fun a => hb ⟨a,a.property⟩⟩
    simp [mean, mass, moment]

























section Adaptive
variable {ι : Type*} [Fintype ι] [DecidableEq ι]













end Adaptive

section CoordinatePartition
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



















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
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
/-- The residual has zero weighted inner product with every atom-constant function. -/
theorem solution (φ : α → β) (w F : α → ℝ) (hw : ∀ a, 0 < w a)
    (G : β → ℝ) :
    (∑ a, w a * (F a - conditional φ w F a) * G (φ a)) = 0 := by
  rw [← Fintype.sum_fiberwise φ]
  apply Finset.sum_eq_zero
  intro b _
  have h : ∀ a : {a // φ a = b}, conditional φ w F a = mean φ w F b := by
    intro a
    simp [conditional, a.property]
  simp_rw [h]
  calc
    (∑ a : {a // φ a = b}, w a * (F a - mean φ w F b) * G (φ a)) =
        (moment φ w F b - mean φ w F b * mass φ w b) * G b := by
      simp_rw [show ∀ a : {a // φ a = b}, φ a = b from fun a => a.property]
      unfold moment mass
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [mean_mul_mass φ w F hw b]; ring
