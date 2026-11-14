-- Prove2me | solution 1 for NarrowDNF.HatamiActivation.threshold_load_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:08.120221+00:00
-- url     : https://prove2.me/submissions/d889887a-5f33-48da-9388-fca06c1d2a97

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiActivation_threshold_probability_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

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
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide



























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
# Finite Bernoulli variance and resampling influence

The one-coordinate identities in this file use the paper's resampling
normalization: a pivotal Boolean fiber has influence `2 * p * (1 - p)`.
The endpoints `p = 0` and `p = 1` are included in the algebraic identities.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Influence




















/-- The square of a Boolean numerical value is itself. -/
@[simp] private theorem boolValue_sq (b : Bool) : boolValue b ^ 2 = boolValue b := by
  cases b <;> norm_num [boolValue]



section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

































end Cube
end NarrowDNF.Influence


end

end

section


/-!
# Finite biased Fourier expansion

A basis index is a Boolean support mask. Its true coordinates are exactly the
usual subset index. All expectations use Bernoulli product weights, and the
normalization of influence is independent resampling rather than bit flipping.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.Fourier











section Cube
variable {ι : Type*} [Fintype ι] [DecidableEq ι]































































/-- The constant Fourier coefficient is the mean. -/
@[simp] private theorem coefficient_zeroMask (p : ℝ) (f : (ι → Bool) → ℝ) :
    coefficient p f (fun _ => false) = ProductMeasure.expectation p f := by
  simp [coefficient, character, bitBasis]














@[simp] private theorem degree_maskEquivFinset_symm (S : Finset ι) :
    degree (maskEquivFinset.symm S) = S.card :=
  congrArg Finset.card (maskEquivFinset.apply_symm_apply S)


























end Cube
end NarrowDNF.Fourier







end

end

section


/-!
# Hatami's threshold activation family

The local activations and multiplicity-counted load calculation from Appendix A
of the 2026-11-06 STOC revision. The cutoff is real, as in the source. All threshold masses
are explicit finite sums; no activation-load guarantee is assumed.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiActivation

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

























omit [Fintype ι] in
@[simp] private theorem localMass_extendLocal (p : ℝ) (T : Finset ι) (z : T → Bool) :
    localMass p T (Activation.extendLocal T z) = weight p z := by
  unfold localMass
  congr 1
  funext i
  simp [Activation.extendLocal, i.property]



omit [Fintype ι] [DecidableEq ι] in
/-- Summing `2^|T|` over subsets gives `3^|S|`, rather than an ambient-dimension factor. -/
private theorem sum_powerset_two_pow (S : Finset ι) :
    (∑ T ∈ S.powerset, (2 : ℝ)^T.card) = (3 : ℝ)^S.card := by
  have h := (Finset.prod_add_one (f := fun _ : ι => (2 : ℝ)) S).symm
  norm_num at h
  exact h

private theorem sum_subsets_eq (S : Finset ι) (F : Finset ι → ℝ) :
    (∑ T : Finset ι, if T ⊆ S then F T else 0) = ∑ T ∈ S.powerset, F T := by
  have hs : (Finset.univ.filter fun T : Finset ι => T ⊆ S) = S.powerset := by
    ext T
    simp
  rw [← Finset.sum_filter, hs]

omit [Fintype ι] [DecidableEq ι] in
private theorem powerset_multiplicity_le {k : ℝ} (hk0 : 0 ≤ k) (S : Finset ι)
    (hS : (S.card : ℝ) ≤ k) :
    (∑ T ∈ S.powerset, (T.card : ℝ) * (2 : ℝ)^T.card) ≤ k * (2 : ℝ)^(2*k) := by
  have hpow : (3 : ℝ)^S.card ≤ (2 : ℝ)^(2*k) := by
    calc
      (3 : ℝ)^S.card ≤ (4 : ℝ)^S.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = (2 : ℝ)^(2 * (S.card : ℝ)) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        norm_num
      _ ≤ (2 : ℝ)^(2*k) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ ∑ T ∈ S.powerset, k * (2 : ℝ)^T.card := by
      apply Finset.sum_le_sum
      intro T hT
      have hc : (T.card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (Finset.mem_powerset.mp hT)
      exact mul_le_mul_of_nonneg_right (hc.trans hS) (by positivity)
    _ = k * (3 : ℝ)^S.card := by rw [← Finset.mul_sum, sum_powerset_two_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hk0























































end NarrowDNF.HatamiActivation

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiActivation
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Multiplicity-counted activation load, reduced to the retained input masses. -/
theorem solution {k p δ : ℝ} (hk0 : 0 ≤ k) (hδ : 0 < δ)
    (retained : Finset (Finset ι)) (m : Finset ι → ℝ)
    (hm : ∀ S ∈ retained, 0 ≤ m S)
    (hcard : ∀ S ∈ retained, (S.card : ℝ) ≤ k) :
    (thresholdActivation k p δ retained m).load p ≤
      (k * (2 : ℝ)^(2*k) / δ) * ∑ S ∈ retained, m S := by
  unfold Activation.load
  calc
    _ ≤ ∑ T : Finset ι, (T.card : ℝ) *
        ((2 : ℝ)^T.card * bMass retained m T / δ) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (threshold_probability_le hδ retained m hm T)
        (Nat.cast_nonneg _)
    _ = ∑ T : Finset ι, ∑ S ∈ retained,
        if T ⊆ S then ((T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) else 0 := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [bMass, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> simp_all; ring
    _ = ∑ S ∈ retained, ∑ T : Finset ι,
        if T ⊆ S then ((T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) else 0 :=
      Finset.sum_comm
    _ = ∑ S ∈ retained,
        (∑ T ∈ S.powerset, (T.card : ℝ) * (2 : ℝ)^T.card) * (m S / δ) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [sum_subsets_eq, Finset.sum_mul]
    _ ≤ ∑ S ∈ retained, (k * (2 : ℝ)^(2*k)) * (m S / δ) := by
      apply Finset.sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_right (powerset_multiplicity_le hk0 S (hcard S hS))
        (div_nonneg (hm S hS) hδ.le)
    _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_div]; ring
