-- Prove2me | solution 1 for NarrowDNF.HatamiCrossTerms.crossEnvelope_le_corrected
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:47:39.361042+00:00
-- url     : https://prove2.me/submissions/269d6718-98c7-48ba-9704-91689b264ae1

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
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiActivation_localMass_le_componentTailMass
import Theorems.Thm_NarrowDNF_HatamiActivation_sum_componentTailMass_le
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_kernel_sum
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_intersection_kernel_sum_le

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

namespace NarrowDNF.HatamiCrossTerms
end NarrowDNF.HatamiCrossTerms

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

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























private theorem significantSets_card (p : ℝ) (f : Cube ι → ℝ) (k η : ℝ)
    (S : Finset ι) (hS : S ∈ significantSets p f k η) : (S.card : ℝ) ≤ k :=
  (Finset.mem_filter.mp hS).2.1





omit [Fintype ι] [DecidableEq ι] in
/-- Every local input has mass at least `p^|S|` in the low-bias range. -/
private theorem pow_le_localMass {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (S : Finset ι) (x : Cube ι) : p^S.card ≤ localMass p S x := by
  calc
    _ = ∏ i : S, p := by simp
    _ ≤ ∏ i : S, bitWeight p (x i) := by
      apply Finset.prod_le_prod
      · intro _ _
        exact hp0
      · intro i _
        cases x i <;> simp [bitWeight]; linarith

/-- A significant component has a tail event with mass at least `p^|S|`. -/
private theorem pow_le_componentTailMass_of_significant {k p η : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (f : Cube ι → ℝ) (S : Finset ι)
    (hS : S ∈ significantSets p f k η) : p^S.card ≤ componentTailMass p f η S := by
  obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hS).2.2
  exact (pow_le_localMass hp0 hp S x).trans
    (localMass_le_componentTailMass hp0 (by linarith) f η S x hx.le)































end NarrowDNF.HatamiActivation

end

end

section


/-!
# Hatami's corrected cross-term estimate

Finite cross-term estimates for the exact restricted-activation conditional
components. The repaired coefficient factor is retained explicitly.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiCrossTerms

open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]































omit [Fintype ι] [DecidableEq ι] in
/-- The powerset factor is at most `2^(2k)` for every retained set. -/
private theorem three_pow_card_le {k : ℝ} (S : Finset ι) (hS : (S.card : ℝ) ≤ k) :
    (3:ℝ)^S.card ≤ (2:ℝ)^(2*k) := by
  calc
    (3:ℝ)^S.card ≤ (4:ℝ)^S.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (2:ℝ)^(2*(S.card:ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)



















end NarrowDNF.HatamiCrossTerms





end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiCrossTerms
open ProductMeasure HatamiResidual HatamiActivation
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The repaired complete cross envelope bound, before the final rank factor.
Every activation and retained set is the exact one from Hatami's construction. -/
theorem solution {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hδ : 0 ≤ δ) (hη : 0 < η) (f : Cube ι → Bool) :
    crossEnvelope p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
      (fun x => Influence.boolValue (f x))
      (significantSets p (fun x => Influence.boolValue (f x)) k η) ≤
        (2:ℝ)^(8*k) * δ / η^2 := by
  have hp1 : p < 1 := by linarith
  let F := fun x => Influence.boolValue (f x)
  let A := significantSets p F k η
  have hcard : ∀ S ∈ A, (S.card : ℝ) ≤ k := significantSets_card p F k η
  have ha : ∀ S ∈ A, 0 ≤ p^S.card := fun S _ => pow_nonneg hp0.le _
  have ham : ∀ S ∈ A, p^S.card ≤ componentTailMass p F η S :=
    fun S hS => pow_le_componentTailMass_of_significant hp0.le hp F S hS
  have hsum : (∑ S ∈ A, p^S.card) ≤ 1 / η^2 := by
    apply le_trans (Finset.sum_le_sum (fun S hS => ham S hS))
    exact sum_componentTailMass_le hp0 hp1 hη f A
  have hweighted : (∑ S ∈ A, (3:ℝ)^S.card * p^S.card) ≤
      (2:ℝ)^(2*k) / η^2 := by
    calc
      _ ≤ ∑ S ∈ A, (2:ℝ)^(2*k) * p^S.card := by
        apply Finset.sum_le_sum
        intro S hS
        exact mul_le_mul_of_nonneg_right (three_pow_card_le S (hcard S hS)) (ha S hS)
      _ = (2:ℝ)^(2*k) * ∑ S ∈ A, p^S.card := (Finset.mul_sum ..).symm
      _ ≤ (2:ℝ)^(2*k) * (1 / η^2) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by ring
  have hkernel := intersection_kernel_sum_le hp0 hp1 hδ A (fun S => p^S.card)
    (componentTailMass p F η) ha ham hcard
  have hcross := crossEnvelope_le_kernel_sum hp0 hp1 (fourierActivation k p δ η F) f A hcard
  apply hcross.trans
  calc
    _ ≤ (2:ℝ)^(6*k) * (δ * ∑ S ∈ A, (3:ℝ)^S.card * p^S.card) :=
      mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg (by norm_num) _)
    _ ≤ (2:ℝ)^(6*k) * (δ * ((2:ℝ)^(2*k) / η^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hweighted hδ) (Real.rpow_nonneg (by norm_num) _)
    _ = (2:ℝ)^(8*k) * δ / η^2 := by
      have hpow : (2:ℝ)^(6*k) * (2:ℝ)^(2*k) = (2:ℝ)^(8*k) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc
        _ = ((2:ℝ)^(6*k) * (2:ℝ)^(2*k)) * δ / η^2 := by ring
        _ = _ := by rw [hpow]
