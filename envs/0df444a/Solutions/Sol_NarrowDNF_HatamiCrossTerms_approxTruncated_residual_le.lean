-- Prove2me | solution 1 for NarrowDNF.HatamiCrossTerms.approxTruncated_residual_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:50:01.938688+00:00
-- url     : https://prove2.me/submissions/7b8fbad5-4539-46cb-bafa-bff82ad29209

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
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiCrossTerms
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_crossEnvelope_le_corrected
import Theorems.Thm_NarrowDNF_HatamiCrossTerms_residual_le_rank_factor
import Theorems.Thm_NarrowDNF_HatamiResidual_sum_diagonal_le_small_mass

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









private theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg hp0 hp1 (x i)





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







private theorem expectation_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F : (ι → Bool) → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ expectation p F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (weight_nonneg hp0 hp1 x) (hF x)









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







































end NarrowDNF.HatamiActivation

end

end

section


/-!
# Hatami's actual restricted-activation conditional components

This file formalizes the Step III/IV construction using actual adaptive atom
labels. `approxComponent` is conditional expectation onto the family retaining
only activations whose index is contained in the component's support. Generic
projection and diagonal estimates are proved here. Construction-specific
cross-term bounds are stated only when proved; no analytic estimate is an axiom.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiResidual

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





























section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]





end Generic


















section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound






/-- Finite-subfamily linearity of product expectation. -/
private theorem expectation_finset_sum {κ : Type*} (p : ℝ) (s : Finset κ)
    (F : κ → Cube ι → ℝ) :
    expectation p (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, expectation p (F j) := by
  unfold expectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm














section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]







end GenericMeanBound











end NarrowDNF.HatamiResidual




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











































/-- The rank-count factor is simultaneously at most `2k` and `2^k` for real `k >= 1`. -/
private theorem rankCount_bounds {k : ℝ} (hk : 1 ≤ k) :
    ((Nat.floor k + 1 : ℕ) : ℝ) ≤ 2*k ∧ ((Nat.floor k + 1 : ℕ) : ℝ) ≤ (2:ℝ)^k := by
  have hfloor : (Nat.floor k : ℝ) ≤ k := Nat.floor_le (by linarith)
  constructor
  · push_cast
    linarith
  · calc
      ((Nat.floor k + 1 : ℕ) : ℝ) ≤ (2:ℝ)^(Nat.floor k) := by
        exact_mod_cast (Nat.succ_le_iff.mpr (Nat.floor k).lt_two_pow_self)
      _ = (2:ℝ)^((Nat.floor k):ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor

/-- The low-degree small-component mass is nonnegative. -/
private theorem smallMassReal_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : Cube ι → ℝ) (k η : ℝ) : 0 ≤ FourierTruncation.smallMassReal p f k η := by
  apply Finset.sum_nonneg
  intro S _
  apply expectation_nonneg hp0 hp1
  intro x
  split_ifs <;> positivity

/-- Match the diagonal quantity to the source's exact real-cutoff Step II mass. -/
private theorem diagonal_sum_le_smallMassReal {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ) :
    (∑ S ∈ significantSets p f k η,
      ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
        (approxComponent p (fourierActivation k p δ η f) f S)) ≤
      FourierTruncation.smallMassReal p f k η := by
  have h := sum_diagonal_le_small_mass (k := k) (η := η) hp0 hp1 hδ f
  apply h.trans_eq
  rw [HatamiResidual.expectation_finset_sum, Finset.sum_filter]
  unfold FourierTruncation.smallMassReal
  apply Finset.sum_congr rfl
  intro S _
  by_cases hdeg : (S.card : ℝ) ≤ k <;> simp [hdeg]



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
/-- Hatami's complete Step III residual estimate for the exact threshold
construction, with the repaired cross-term exponent. The only remaining
analytic quantity is the explicitly defined small-component mass. -/
theorem solution {p k δ η : ℝ}
    (hp0 : 0 < p) (hp : p ≤ 1/2) (hk : 1 ≤ k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hη : 0 < η) (f : Cube ι → Bool) :
    ConditionalExpectation.squaredError (weight p)
      (truncated p (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η))
      (approxTruncated p (fourierActivation k p δ η (fun x => Influence.boolValue (f x)))
        (fun x => Influence.boolValue (f x))
        (significantSets p (fun x => Influence.boolValue (f x)) k η)) ≤
      2*k*FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k η +
        (2:ℝ)^(9*k)*δ/η^2 := by
  have hp1 : p < 1 := by linarith
  let F := fun x => Influence.boolValue (f x)
  let A := significantSets p F k η
  let J := fourierActivation k p δ η F
  let ranks := Finset.range (Nat.floor k + 1)
  have hcover : ∀ S ∈ A, S.card ∈ ranks := by
    intro S hS
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_iff.mpr (Nat.le_floor (significantSets_card p F k η S hS))
  have h := residual_le_rank_factor hp0.le hp1.le J F A ranks hcover
  have hdiag := diagonal_sum_le_smallMassReal (k := k) (η := η) hp0 hp1 hδ1 F
  have hcross := crossEnvelope_le_corrected (k := k) hp0 hp hδ0 hη f
  have hsmall0 := smallMassReal_nonneg hp0.le hp1.le F k η
  have hcross0 : 0 ≤ (2:ℝ)^(8*k)*δ/η^2 := by positivity
  have hn := rankCount_bounds hk
  have hcard : (ranks.card : ℝ) = ((Nat.floor k + 1 : ℕ) : ℝ) := by simp [ranks]
  rw [hcard] at h
  apply h.trans
  calc
    _ ≤ ((Nat.floor k + 1 : ℕ) : ℝ) *
        (FourierTruncation.smallMassReal p F k η + (2:ℝ)^(8*k)*δ/η^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hdiag hcross) (Nat.cast_nonneg _)
    _ = ((Nat.floor k + 1 : ℕ) : ℝ) * FourierTruncation.smallMassReal p F k η +
        ((Nat.floor k + 1 : ℕ) : ℝ) * ((2:ℝ)^(8*k)*δ/η^2) := by ring
    _ ≤ (2*k)*FourierTruncation.smallMassReal p F k η +
        (2:ℝ)^k * ((2:ℝ)^(8*k)*δ/η^2) :=
      add_le_add (mul_le_mul_of_nonneg_right hn.1 hsmall0)
        (mul_le_mul_of_nonneg_right hn.2 hcross0)
    _ = _ := by
      have hpow : (2:ℝ)^k * (2:ℝ)^(8*k) = (2:ℝ)^(9*k) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      calc
        _ = 2*k*FourierTruncation.smallMassReal p F k η +
          ((2:ℝ)^k * (2:ℝ)^(8*k))*δ/η^2 := by ring
        _ = _ := by rw [hpow]
