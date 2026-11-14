-- Prove2me | solution 1 for NarrowDNF.narrowDNF_of_hatami
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:35:26.135205+00:00
-- url     : https://prove2.me/submissions/e600cb1d-f2d8-4292-b4ae-ab724608c73e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Definitions.Def_NarrowDNF_ShiftProbability
import Definitions.Def_NarrowDNF_WidthBound
import Theorems.Thm_NarrowDNF_WidthBound_width_le_exponential
import Theorems.Thm_NarrowDNF_adaptive_approximation_to_dnf

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

namespace NarrowDNF.ShiftProbability
end NarrowDNF.ShiftProbability

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound

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


namespace NarrowDNF
namespace Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem truncatedDNF_eq_true (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) :
    J.truncatedDNF u w x = true ↔ DNFHolds (J.truncatedTerms u w) x := by
  classical simp [truncatedDNF]









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











omit [Fintype ι] in
@[simp] private theorem shiftByChoices_nil (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices [] d v = v := rfl

omit [Fintype ι] in
@[simp] private theorem shiftByChoices_cons (i : ι) (order : List ι)
    (d : Cube ι) (v : Cube ι → Bool) :
    shiftByChoices (i :: order) d v =
      shiftByChoices order d (shiftChoice i (d i) v) := rfl















end NarrowDNF.ShiftProbability

end

end

section


/-!
# Explicit width and error-budget arithmetic

These are the final arithmetic estimates in the proof of Theorem 1.2 of
the 2026-11-06 STOC revision. The source's numerical constants are retained. This
module does not assume or assert the structural theorem supplying the
approximator and activation family.
-/

noncomputable section

namespace NarrowDNF.WidthBound











private theorem absoluteConstant_pos : 0 < absoluteConstant := by norm_num [absoluteConstant]















end NarrowDNF.WidthBound

end

end

noncomputable section
open NarrowDNF
/-- Complete low-bias main-theorem assembly from the exact, separately stated
Hatami existence proposition. The proposition is not postulated as an axiom. -/
theorem solution (hHatami : HatamiArityLoad) : NarrowDNFApproximation := by
  refine ⟨WidthBound.absoluteConstant, WidthBound.absoluteConstant_pos, ?_⟩
  intro n hn K p ε hK hp0 hpHalf hε hε1 f hf hI
  have hp1 : p < 1 := by linarith
  have ha : 0 < ε/4 := by positivity
  have ha1 : ε/4 ≤ 1 := by linarith
  obtain ⟨J, h, hJ, herr, hm, harity, hload⟩ := hHatami n p hp0 hpHalf f (ε/4) ha ha1
  have hc : Nat.ceil (Influence.totalInfluence p f) ≤ Nat.ceil K := Nat.ceil_mono hI
  have hcr : (Nat.ceil (Influence.totalInfluence p f) : ℝ) ≤ (Nat.ceil K : ℝ) := by
    exact_mod_cast hc
  have hd : Nat.ceil (1000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / (ε/4)) ≤
      WidthBound.degree K ε := by
    apply Nat.ceil_mono
    change 1000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / (ε/4) ≤
      4000 * (Nat.ceil K : ℝ) / ε
    calc
      _ = 4000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ) / ε := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcr (by norm_num)) hε.le
  have hdJ : J.ArityLE (WidthBound.degree K ε) := by
    intro S hS x
    exact harity S (hd.trans_lt hS) x
  have hloadJ : J.load p ≤ WidthBound.loadBound K ε := by
    apply hload.trans
    apply Real.exp_le_exp.mpr
    change 10000000000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ)^2 / (ε/4)^2 ≤
      160000000000 * (Nat.ceil K : ℝ)^2 / ε^2
    calc
      _ = 160000000000 * (Nat.ceil (Influence.totalInfluence p f) : ℝ)^2 / ε^2 := by ring
      _ ≤ _ := by gcongr
  have hL0 : 0 ≤ WidthBound.loadBound K ε := (Real.exp_pos _).le
  obtain ⟨terms, hw, he⟩ := adaptive_approximation_to_dnf hp0 hp1 hε hL0 hf hJ hdJ hm herr hloadJ
  refine ⟨terms, ?_, he⟩
  intro T hT
  have ht : (T.card : ℝ) ≤ (WidthBound.width K ε : ℝ) := by
    have htNat : T.card ≤ WidthBound.width K ε := by
      simpa only [WidthBound.width] using hw T hT
    exact_mod_cast htNat
  exact ht.trans (WidthBound.width_le_exponential hK hε hε1)
