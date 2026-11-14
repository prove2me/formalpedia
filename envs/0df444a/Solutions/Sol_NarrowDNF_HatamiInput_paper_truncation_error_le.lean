-- Prove2me | solution 1 for NarrowDNF.HatamiInput.paper_truncation_error_le
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:56:34.392273+00:00
-- url     : https://prove2.me/submissions/c9ef8802-db97-418a-bef2-7436ed2e519a

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_FourierTruncation
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiParameters
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_BourgainEstimate_paper_smallComponentMass_bound
import Theorems.Thm_NarrowDNF_FourierTruncation_significant_remainder_le
import Theorems.Thm_NarrowDNF_HatamiInput_highDegreeReal_mass_le

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.BourgainEstimate
end NarrowDNF.BourgainEstimate

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

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































































end NarrowDNF.HatamiActivation

end

end

section


/-!
# Bourgain's small-component estimate with the paper's threshold

The estimates in this module are fully discharged. No Fourier, square-function,
noise, hypercontractive, or small-component estimate is an assumed hypothesis.
Only the stated bound on the Boolean function's total resampling influence is
an input, as required by Hatami's theorem.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainEstimate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]







/-- The weaker Section 4 error budget follows from the proved Section 5
small-component estimate and `e ≤ 1`. -/
private theorem paper_smallComponentMass_bound_section4 {p k e : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → Bool) (C : ℕ)
    (hk : 5 ≤ k) (he : 0 < e) (he1 : e ≤ 1)
    (hC : (C : ℝ) ≤ k) (hI : Influence.totalInfluence p f ≤ C) :
    FourierTruncation.smallMassReal p (fun x => Influence.boolValue (f x)) k
      (HatamiParameters.epsilonOne k e) ≤ e/k := by
  refine (paper_smallComponentMass_bound hp0 hp1 f C hk he he1 hC hI).trans ?_
  exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1)])
    (by linarith)

end NarrowDNF.BourgainEstimate

end

end

section


/-!
# Hatami's quantitative activation input

Assembly of the actual Fourier truncation, the reconstructed Bourgain estimate,
the repaired adaptive residual proof, and threshold decoding for Lemma 2.1.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]





/-- The paper's exact parameter multiplication identity. -/
private theorem paper_parameter_product {a : ℝ} (ha : 0 < a) (C : ℝ) :
    (1000*C/a)*(a/1000) = C := by
  field_simp

/-- In the nonconstant case the paper's cutoff is at least 1000. -/
private theorem paper_cutoff_ge {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C) :
    (1000 : ℝ) ≤ 1000*C/a := by
  apply (le_div_iff₀ ha).mpr
  linarith























end NarrowDNF.HatamiInput

end

end

noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The two pruning steps have squared error at most two epsilon-zero for
exactly the retained family appearing in the source activation construction. -/
theorem solution {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (f : Cube ι → Bool) (C : ℕ)
    (hC : 1 ≤ C) (hI : Influence.totalInfluence p f ≤ C) :
    ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (HatamiResidual.truncated p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          (1000*(C : ℝ)/a) (HatamiParameters.epsilonOne (1000*(C : ℝ)/a) (a/1000)))) ≤
            2*(a/1000) := by
  let k := 1000*(C : ℝ)/a
  let e := a/1000
  have hCr : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk1000 : 1000 ≤ k := paper_cutoff_ge ha ha1 hCr
  have hk0 : 0 < k := by linarith
  have he0 : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by dsimp [e]; linarith
  have hke : k*e = C := paper_parameter_product ha (C : ℝ)
  have hCk : (C : ℝ) ≤ k := by nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr he1)]
  have htrunc := FourierTruncation.significant_remainder_le hp0 hp1
    (fun x => Influence.boolValue (f x)) k (HatamiParameters.epsilonOne k e)
  have hhigh := highDegreeReal_mass_le hp0 hp1 hk0 f
  have hhigh' : Influence.totalInfluence p f/(2*k) ≤ e := by
    apply (div_le_iff₀ (by positivity : 0 < 2*k)).mpr
    nlinarith
  have hsmall := BourgainEstimate.paper_smallComponentMass_bound_section4
    hp0 hp1 f C (by linarith) he0 he1 hCk hI
  have hsmall' : e/k ≤ e := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith
  change ConditionalExpectation.squaredError (ProductMeasure.weight p)
      (fun x => Influence.boolValue (f x))
      (FourierTruncation.partialSum p (fun x => Influence.boolValue (f x))
        (HatamiActivation.significantSets p (fun x => Influence.boolValue (f x))
          k (HatamiParameters.epsilonOne k e))) ≤ 2*e
  linarith
