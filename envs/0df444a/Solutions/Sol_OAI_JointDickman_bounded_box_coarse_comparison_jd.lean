-- Prove2me | solution 1 for OAI.JointDickman.bounded_box_coarse_comparison_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:05:53.342197+00:00
-- url     : https://prove2.me/submissions/ba8232da-e5b4-46cb-aa49-41265fd98e69

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_geometric_sampled_integral_error_sum_jd
import Theorems.Thm_OAI_JointDickman_geometric_singularSeries_error_jd
import Theorems.Thm_OAI_JointDickman_groupedManuscriptChannel_square_bound_jd
import Theorems.Thm_OAI_JointDickman_primeChannelMarginal_upper_jd
import Theorems.Thm_OAI_JointDickman_primeCommonLogCell_upper_jd
import Theorems.Thm_OAI_JointDickman_primeRampProfile_from_published_jd

section
-- module Solutions.OAIQ083_JD.Compat
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OscillatoryTests
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth oscillatory tests used in the coefficient estimate -/

namespace JointDickman

theorem norm_additivePhase (x : ℝ) : ‖additivePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_additivePhase (x : ℝ) :
    HasDerivAt additivePhase (additivePhase x * ((2 * Real.pi : ℝ) * Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul (2 * Real.pi)).ofReal_comp.mul_const Complex.I).cexp
  simpa only [mul_one, id_eq] using! h

theorem continuous_additivePhase : Continuous additivePhase :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_additivePhase x).continuousAt)

theorem oscillatoryTest_norm (w : ℝ → ℝ) (ξ t : ℝ) :
    ‖oscillatoryTest w ξ t‖ = |w t| := by
  simp only [oscillatoryTest, norm_mul, norm_additivePhase, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primitive-root sums and the Ramanujan factor -/

namespace JointDickman

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

theorem stdAddChar_natCast {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = Complex.exp (2 * Real.pi * Complex.I * n / q) := by
  simpa only [Int.cast_natCast] using
    ZMod.stdAddChar_coe (N := q) (n : ℤ)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RamanujanSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact unit-frequency Ramanujan sum -/

namespace JointDickman

open Finset
open scoped ArithmeticFunction.Moebius

theorem norm_stdAddChar {q : ℕ} [NeZero q] (r : ZMod q) :
    ‖ZMod.stdAddChar r‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact (ZMod.toCircle r).norm_coe

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditivePhaseBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relating real exponential notation to residue characters -/

namespace JointDickman

theorem additivePhase_add (s t : ℝ) :
    additivePhase (s + t) = additivePhase s * additivePhase t := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem stdAddChar_as_additivePhase {q : ℕ} [NeZero q] (n : ℕ) :
    ZMod.stdAddChar (n : ZMod q) = additivePhase ((n : ℝ) / q) := by
  rw [stdAddChar_natCast]
  unfold additivePhase
  congr 1
  push_cast
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Compatible parameters and elementary asymptotics

The strict inequalities here are the weight margins of `arithmetic.tex`.
The subsequent limits account for the sampling entropy and the logarithmic
factors in the prime cutoff and amplification parameters.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSetWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite prime-selection and fair-split weights

The independent prime-set model and its fair splits satisfy exact finite
identities without prime asymptotics or analytic equidistribution premises.
-/

namespace JointDickman

open scoped BigOperators

theorem bernoulliSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    0 ≤ bernoulliSubsetMass P q S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun p hp => (hq p (hS hp)).1)
  · exact Finset.prod_nonneg (fun p hp => sub_nonneg.mpr (hq p
      (Finset.mem_sdiff.mp hp).1).2)

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

/-- The exact finite product formula for a multiplicative tilt. -/
theorem bernoulliSubsetMass_tilt {α : Type*} [DecidableEq α]
    (P : Finset α) (q v : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, (1 - q p + q p * v p) := by
  calc
    _ = ∑ S ∈ P.powerset,
        (∏ p ∈ S, q p * v p) * ∏ p ∈ P \ S, (1 - q p) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib]
      unfold bernoulliSubsetMass
      ring
    _ = _ := by rw [← Finset.prod_add]; congr 1; ext p; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_BernoulliComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Mutually exclusive site hits versus independent Bernoulli hits

At one prime the actual site hits are mutually exclusive. Their categorical
law differs from independent Bernoulli hits by at most twice the square of
the sum of the site probabilities in `L¹`. Everything here is a finite-sum
proof; no coupling estimate is assumed.
-/

namespace JointDickman

open scoped BigOperators

private theorem sum_singleton_kernel {α : Type*} [DecidableEq α]
    (P : Finset α) (w : α → ℝ) :
    (∑ S ∈ P.powerset, ∑ i ∈ P, if S = {i} then w i else 0) = ∑ i ∈ P, w i := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_powerset, Finset.singleton_subset_iff, hi]

theorem categoricalSubsetMass_singleton {α : Type*} [DecidableEq α]
    {P : Finset α} (q : α → ℝ) {i : α} (hi : i ∈ P) :
    categoricalSubsetMass P q {i} = q i := by
  classical
  simp [categoricalSubsetMass, Finset.singleton_inj, hi]

theorem categoricalSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, categoricalSubsetMass P q S = 1 := by
  classical
  unfold categoricalSubsetMass
  rw [Finset.sum_add_distrib, sum_singleton_kernel]
  simp

theorem categoricalSubsetMass_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i)
    (hsum : ∑ i ∈ P, q i ≤ 1) : 0 ≤ categoricalSubsetMass P q S := by
  unfold categoricalSubsetMass
  apply add_nonneg
  · split_ifs <;> linarith
  · exact Finset.sum_nonneg (fun i hi => by split_ifs <;> simp_all)

private theorem complement_product_lower {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    1 - ∑ i ∈ P, q i ≤ ∏ i ∈ P, (1 - q i) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert i P hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hqi := hq i (Finset.mem_insert_self _ _)
    have hqP : ∀ j ∈ P, 0 ≤ q j ∧ q j ≤ 1 := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hmul := mul_le_mul_of_nonneg_left (ih hqP) (sub_nonneg.mpr hqi.2)
    have hsum0 : 0 ≤ ∑ j ∈ P, q j := Finset.sum_nonneg (fun j hj => (hqP j hj).1)
    nlinarith

private theorem bernoulli_singleton_le {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1)
    {i : α} (hi : i ∈ P) : bernoulliSubsetMass P q {i} ≤ q i := by
  have hp : (∏ j ∈ P \ {i}, (1 - q j)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j hj
      exact sub_nonneg.mpr (hq j (Finset.mem_sdiff.mp hj).1).2
    · intro j hj
      linarith [(hq j (Finset.mem_sdiff.mp hj).1).1]
  simpa [bernoulliSubsetMass] using mul_le_mul_of_nonneg_left hp (hq i hi).1

private theorem singleton_deficit_le {α : Type*} [DecidableEq α]
    {P : Finset α} {q : α → ℝ} (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1)
    {i : α} (hi : i ∈ P) :
    q i - bernoulliSubsetMass P q {i} ≤ q i * (∑ j ∈ P, q j) := by
  have hqsub : ∀ j ∈ P \ {i}, 0 ≤ q j ∧ q j ≤ 1 :=
    fun j hj => hq j (Finset.mem_sdiff.mp hj).1
  have hprod := complement_product_lower (P \ {i}) q hqsub
  have hsum : (∑ j ∈ P \ {i}, q j) ≤ ∑ j ∈ P, q j :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun j hj _ => (hq j hj).1)
  have hmul := mul_le_mul_of_nonneg_left hprod (hq i hi).1
  have hmul' := mul_le_mul_of_nonneg_left hsum (hq i hi).1
  simp only [bernoulliSubsetMass, Finset.prod_singleton] at *
  nlinarith

/-- An exact identity: twice the total singleton deficit is the entire
`L¹` discrepancy. The empty-set excess and multi-hit mass balance it. -/
theorem categorical_bernoulli_l1_eq {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ S ∈ P.powerset, |categoricalSubsetMass P q S - bernoulliSubsetMass P q S|) =
      2 * ∑ i ∈ P, (q i - bernoulliSubsetMass P q {i}) := by
  classical
  have hpoint (S : Finset α) (hS : S ∈ P.powerset) :
      |categoricalSubsetMass P q S - bernoulliSubsetMass P q S| =
      2 * (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) -
        (categoricalSubsetMass P q S - bernoulliSubsetMass P q S) := by
    by_cases hS0 : S = ∅
    · subst S
      have he := complement_product_lower P q hq
      simp only [categoricalSubsetMass_empty, bernoulliSubsetMass, Finset.prod_empty,
        Finset.sdiff_empty, one_mul] at *
      rw [abs_of_nonpos (by linarith)]
      simp
    · by_cases hs : ∃ i ∈ P, S = {i}
      · obtain ⟨i, hi, rfl⟩ := hs
        rw [categoricalSubsetMass_singleton q hi,
          abs_of_nonneg (sub_nonneg.mpr (bernoulli_singleton_le hq hi))]
        simp only [Finset.singleton_inj]
        simp [hi]
        ring
      · have hne (i : α) (hi : i ∈ P) : S ≠ {i} := fun heq => hs ⟨i, hi, heq⟩
        have hcat : categoricalSubsetMass P q S = 0 := by
          simp only [categoricalSubsetMass, ite_eq_right hS0, zero_add]
          exact Finset.sum_eq_zero (fun i hi => by simp [hne i hi])
        have hd : (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) = 0 :=
          Finset.sum_eq_zero (fun i hi => by simp [hne i hi])
        rw [hcat, hd, zero_sub, abs_neg,
          abs_of_nonneg (bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp hS) hq)]
        ring
  calc
    _ = ∑ S ∈ P.powerset,
        (2 * (∑ i ∈ P, if S = {i} then q i - bernoulliSubsetMass P q {i} else 0) -
          (categoricalSubsetMass P q S - bernoulliSubsetMass P q S)) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_singleton_kernel]
      simp only [Finset.sum_sub_distrib, categoricalSubsetMass_sum, bernoulliSubsetMass_sum]
      ring

/-- The finite categorical-to-independent comparison used at a single
prime. Its error is quadratic in the sum of the hit probabilities. -/
theorem categorical_bernoulli_l1_le {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) :
    (∑ S ∈ P.powerset, |categoricalSubsetMass P q S - bernoulliSubsetMass P q S|) ≤
      2 * (∑ i ∈ P, q i) ^ 2 := by
  rw [categorical_bernoulli_l1_eq P q hq]
  have h := Finset.sum_le_sum (s := P) (fun i hi => singleton_deficit_le hq hi)
  rw [← Finset.sum_mul] at h
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Comparing finite product laws

Replacing one independent coordinate at a time bounds the `L¹` distance
of two finite product probability laws by the sum of their coordinate
distances. Applied to the mutually exclusive prime-site law, this gives
the accumulated quadratic error for arbitrary bounded complex tests.
All identities and inequalities here are proved by finite sums.
-/

namespace JointDickman

open scoped BigOperators

theorem finiteProductMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    (a : ∀ i, Ω i → ℝ) (ha : ∀ i x, 0 ≤ a i x) (x : ∀ i, Ω i) :
    0 ≤ finiteProductMass a x :=
  Finset.prod_nonneg (fun i _ => ha i (x i))

theorem finiteProductMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a : ∀ i, Ω i → ℝ)
    (ha : ∀ i, ∑ x, a i x = 1) : ∑ x, finiteProductMass a x = 1 := by
  classical
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  simp only [ha, Finset.prod_const_one]

private theorem finiteProductMass_coordinate_l1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (a b : ∀ i, Ω i → ℝ) (i : ι)
    (ha : ∀ j x, 0 ≤ a j x) (ha1 : ∀ j, ∑ x, a j x = 1)
    (hab : ∀ j, j ≠ i → ∀ x, a j x = b j x) :
    (∑ x, |finiteProductMass a x - finiteProductMass b x|) =
      ∑ y, |a i y - b i y| := by
  classical
  let c : ∀ j, Ω j → ℝ := fun j y => if j = i then |a j y - b j y| else a j y
  have hp (x : ∀ j, Ω j) :
      |finiteProductMass a x - finiteProductMass b x| = finiteProductMass c x := by
    have hr : (∏ j ∈ Finset.univ.erase i, a j (x j)) =
        ∏ j ∈ Finset.univ.erase i, b j (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hab j (Finset.ne_of_mem_erase hj) (x j)
    have hcr : (∏ j ∈ Finset.univ.erase i, c j (x j)) =
        ∏ j ∈ Finset.univ.erase i, a j (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [c, Finset.ne_of_mem_erase hj]
    unfold finiteProductMass
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => b j (x j)) (Finset.mem_univ i), ← hr,
      ← sub_mul, abs_mul, abs_of_nonneg (Finset.prod_nonneg (fun j _ => ha j (x j))),
      ← Finset.mul_prod_erase _ (fun j => c j (x j)) (Finset.mem_univ i), hcr]
    simp [c]
  simp_rw [hp]
  unfold finiteProductMass
  rw [← Fintype.prod_sum]
  have hc (j : ι) : (∑ y, c j y) = if j = i then (∑ y, |a j y - b j y|) else 1 := by
    by_cases hj : j = i
    · simp [c, hj]
    · simp [c, hj, ha1]
  simp_rw [hc]
  exact Fintype.prod_ite_eq' i (fun j => ∑ y, |a j y - b j y|)

/-- The `L¹` discrepancy of product probability masses is at most the
sum of the coordinate discrepancies. No order on the coordinates is needed. -/
theorem finiteProductMass_l1_le {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a b : ∀ i, Ω i → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hb : ∀ i x, 0 ≤ b i x)
    (ha1 : ∀ i, ∑ x, a i x = 1) (hb1 : ∀ i, ∑ x, b i x = 1) :
    (∑ x, |finiteProductMass a x - finiteProductMass b x|) ≤
      ∑ i, ∑ y, |a i y - b i y| := by
  classical
  let mix (s : Finset ι) : ∀ i, Ω i → ℝ := fun i y => if i ∈ s then a i y else b i y
  have hm (s : Finset ι) (i : ι) (y : Ω i) : 0 ≤ mix s i y := by
    dsimp [mix]
    split_ifs <;> [exact ha i y; exact hb i y]
  have hm1 (s : Finset ι) (i : ι) : ∑ y, mix s i y = 1 := by
    by_cases hi : i ∈ s <;> simp [mix, hi, ha1, hb1]
  have h (s : Finset ι) :
      (∑ x, |finiteProductMass (mix s) x - finiteProductMass b x|) ≤
        ∑ i ∈ s, ∑ y, |a i y - b i y| := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s hi ih =>
      have heq := finiteProductMass_coordinate_l1 (mix (insert i s)) (mix s) i
        (hm _) (hm1 _) (by
          intro j hji y
          simp [mix, hji])
      have ht : (∑ x, |finiteProductMass (mix (insert i s)) x - finiteProductMass b x|) ≤
          (∑ x, |finiteProductMass (mix (insert i s)) x - finiteProductMass (mix s) x|) +
            ∑ x, |finiteProductMass (mix s) x - finiteProductMass b x| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        exact abs_sub_le _ _ _
      rw [heq] at ht
      simp only [mix, Finset.mem_insert_self, ↓reduceIte, hi] at ht
      rw [Finset.sum_insert hi]
      linarith
  simpa [mix] using h Finset.univ

/-- A bounded complex test sees no more than its bound times the sum
of the coordinate `L¹` errors. -/
theorem finiteProductMass_test_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (a b : ∀ i, Ω i → ℝ)
    (ha : ∀ i x, 0 ≤ a i x) (hb : ∀ i x, 0 ≤ b i x)
    (ha1 : ∀ i, ∑ x, a i x = 1) (hb1 : ∀ i, ∑ x, b i x = 1)
    (F : (∀ i, Ω i) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (finiteProductMass a x : ℂ) * F x) -
      (∑ x, (finiteProductMass b x : ℂ) * F x)‖ ≤
      L * ∑ i, ∑ y, |a i y - b i y| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, ‖(finiteProductMass a x : ℂ) * F x -
        (finiteProductMass b x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |finiteProductMass a x - finiteProductMass b x| * L := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = L * ∑ x, |finiteProductMass a x - finiteProductMass b x| := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteProductMass_l1_le a b ha hb ha1 hb1) hL

theorem categoricalProduct_test_bound {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (P : Finset α) (q : ι → α → ℝ)
    (hq : ∀ i j, j ∈ P → 0 ≤ q i j ∧ q i j ≤ 1)
    (hsum : ∀ i, ∑ j ∈ P, q i j ≤ 1)
    (F : (ι → P.powerset) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (categoricalProductMass P q x : ℂ) * F x) -
      (∑ x, (bernoulliProductMass P q x : ℂ) * F x)‖ ≤
      2 * L * ∑ i, (∑ j ∈ P, q i j) ^ 2 := by
  classical
  have h := finiteProductMass_test_bound
    (fun i (S : P.powerset) => categoricalSubsetMass P (q i) S.val)
    (fun i (S : P.powerset) => bernoulliSubsetMass P (q i) S.val)
    (fun i _ => categoricalSubsetMass_nonneg (fun j hj => (hq i j hj).1) (hsum i))
    (fun i S => bernoulliSubsetMass_nonneg (Finset.mem_powerset.mp S.property) (hq i))
    (fun i => by simpa only [Finset.sum_coe_sort] using categoricalSubsetMass_sum P (q i))
    (fun i => by simpa only [Finset.sum_coe_sort] using bernoulliSubsetMass_sum P (q i))
    F hL hF
  refine h.trans ?_
  calc
    _ ≤ L * ∑ i, 2 * (∑ j ∈ P, q i j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hL
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = ∑ S ∈ P.powerset, |categoricalSubsetMass P (q i) S -
            bernoulliSubsetMass P (q i) S| := Finset.sum_coe_sort _ _
        _ ≤ _ := categorical_bernoulli_l1_le P (q i) (hq i)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem bernoulliBitMass_sum (q : ℝ) : ∑ b, bernoulliBitMass q b = 1 := by
  simp [bernoulliBitMass]

theorem bernoulliBitMass_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) :
    0 ≤ bernoulliBitMass q b := by
  cases b <;> simp only [bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hq.2
  · exact hq.1

theorem bernoulliSubsetMass_eq_product {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (S : P.powerset) :
    finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) (subsetHitEquiv P S) =
      bernoulliSubsetMass P q S.val := by
  classical
  have hp : finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val))
      (subsetHitEquiv P S) = ∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val := by
    unfold finiteProductMass
    apply Finset.prod_congr rfl
    intro i _
    simp [bernoulliBitMass, subsetHitEquiv]
  rw [hp, show (∏ i : P, if i.val ∈ S.val then q i.val else 1 - q i.val) =
    ∏ i ∈ P, if i ∈ S.val then q i else 1 - q i from
      Finset.prod_coe_sort P (fun i => if i ∈ S.val then q i else 1 - q i), Finset.prod_ite]
  have hs : P.filter (fun i => i ∈ S.val) = S.val := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => Finset.mem_powerset.mp S.property hi)
  have hc : P.filter (fun i => i ∉ S.val) = P \ S.val := by
    ext i
    simp
  rw [hs, hc]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSplitLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two fair splits of the same prime site

The local law is constructed by first selecting a Bernoulli site and then,
conditional on that hit, taking two independent fair splits. Its common and
exclusive categories have mass `q/4` each. Finite product comparison gives
the independent common/exclusive model without assuming a coupling.
-/

namespace JointDickman

open scoped BigOperators

theorem finitePushMass_test {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℝ) (f : A → B) (F : B → ℂ) :
    (∑ y, (finitePushMass a f y : ℂ) * F y) = ∑ x, (a x : ℂ) * F (f x) := by
  classical
  calc
    _ = ∑ y, ∑ x, if f x = y then (a x : ℂ) * F y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [finitePushMass, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ x, ∑ y, if f x = y then (a x : ℂ) * F y else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp

/-- Pushforward commutes with finite independent products. -/
theorem finiteProductMass_pushforward {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (y : ∀ i, B i) :
    finiteProductMass (fun i => finitePushMass (a i) (f i)) y =
      finitePushMass (finiteProductMass a) (fun x i => f i (x i)) y := by
  classical
  unfold finiteProductMass finitePushMass
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f i (x i)) = y
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    rw [ite_eq_left (congrFun h i)]
  · rw [ite_eq_right h]
    have hne : ∃ i, f i (x i) ≠ y i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem finiteProductMass_pushforward_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (a : ∀ i, A i → ℝ) (f : ∀ i, A i → B i) (F : (∀ i, B i) → ℂ) :
    (∑ y, (finiteProductMass (fun i => finitePushMass (a i) (f i)) y : ℂ) * F y) =
      ∑ x, (finiteProductMass a x : ℂ) * F (fun i => f i (x i)) := by
  simp_rw [finiteProductMass_pushforward]
  exact finitePushMass_test _ _ _

theorem sameSiteTwoSplitMass_formula (q : ℝ) (b : Bool × Bool) :
    sameSiteTwoSplitMass q b = if b = (false, false) then 1 - 3 * q / 4 else q / 4 := by
  rcases b with ⟨b₁, b₂⟩
  cases b₁ <;> cases b₂ <;>
    simp [sameSiteTwoSplitMass, conditionalFairSplitMass, bernoulliBitMass] <;> ring

/-- This identifies the categorical law from the actual conditional split
construction, including its empty-set mass. -/
theorem sameSiteTwoSplitMass_categories (q : ℝ) (S : SplitCategories) :
    finitePushMass (sameSiteTwoSplitMass q) splitCategory S =
      categoricalSubsetMass Finset.univ (fun _ : Fin 3 => q / 4) S.val := by
  simp [finitePushMass, sameSiteTwoSplitMass_formula, splitCategory,
    categoricalSubsetMass, Fintype.sum_prod_type, Fin.sum_univ_succ, Subtype.ext_iff, eq_comm]
  ring_nf

theorem threeCategoryBernoulli_factor (q : ℝ) (S : SplitCategories) :
    bernoulliSubsetMass Finset.univ (fun _ : Fin 3 => q) S.val =
      bernoulliBitMass q (decide ((0 : Fin 3) ∈ S.val)) *
      bernoulliBitMass q (decide ((1 : Fin 3) ∈ S.val)) *
      bernoulliBitMass q (decide ((2 : Fin 3) ∈ S.val)) := by
  have h := bernoulliSubsetMass_eq_product (Finset.univ : Finset (Fin 3)) (fun _ => q) S
  change (∏ i : (Finset.univ : Finset (Fin 3)),
    bernoulliBitMass q (decide (i.val ∈ S.val))) = _ at h
  rw [show (∏ i : (Finset.univ : Finset (Fin 3)),
      bernoulliBitMass q (decide (i.val ∈ S.val))) =
        ∏ i : Fin 3, bernoulliBitMass q (decide (i ∈ S.val)) from
          Finset.prod_coe_sort (Finset.univ : Finset (Fin 3))
            (fun i => bernoulliBitMass q (decide (i ∈ S.val))), Fin.prod_univ_three] at h
  exact h.symm

/-- The comparison law really is a product of the three category vectors,
each of which is itself a product of Bernoulli coordinates. -/
theorem independentCategoryProductMass_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → SplitCategories) :
    bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y =
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((0 : Fin 3) ∈ (y i).val)) *
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((1 : Fin 3) ∈ (y i).val)) *
      finiteProductMass (fun i => bernoulliBitMass (q i)) (fun i => decide ((2 : Fin 3) ∈ (y i).val)) := by
  unfold bernoulliProductMass finiteProductMass
  simp_rw [threeCategoryBernoulli_factor]
  simp only [Finset.prod_mul_distrib]

theorem sameSiteTwoSplitProduct_categories {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (F : (ι → SplitCategories) → ℂ) :
    (∑ x, (sameSiteTwoSplitProductMass q x : ℂ) * F (fun i => splitCategory (x i))) =
      ∑ y, (categoricalProductMass Finset.univ (fun i (_ : Fin 3) => q i / 4) y : ℂ) * F y := by
  have h := finiteProductMass_pushforward_test (fun i => sameSiteTwoSplitMass (q i))
    (fun _ => splitCategory) F
  unfold finiteProductMass at h
  simp_rw [sameSiteTwoSplitMass_categories] at h
  exact h.symm

/-- Comparing the actual two-split law to three independent category bits. -/
theorem sameSiteTwoSplitProduct_test_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (F : (ι → SplitCategories) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ y, ‖F y‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass q x : ℂ) * F (fun i => splitCategory (x i))) -
      (∑ y, (bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i / 4) y : ℂ) * F y)‖ ≤
      (9 / 8 : ℝ) * L * ∑ i, (q i) ^ 2 := by
  rw [sameSiteTwoSplitProduct_categories]
  have hq' (i : ι) (j : Fin 3) (_hj : j ∈ (Finset.univ : Finset (Fin 3))) :
      0 ≤ q i / 4 ∧ q i / 4 ≤ 1 := by
    constructor <;> linarith [(hq i).1, (hq i).2]
  have hs (i : ι) : (∑ _j ∈ (Finset.univ : Finset (Fin 3)), q i / 4) ≤ 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    linarith [(hq i).2]
  have h := categoricalProduct_test_bound Finset.univ (fun i (_ : Fin 3) => q i / 4)
    hq' hs F hL hF
  have he (i : ι) : (∑ _j ∈ (Finset.univ : Finset (Fin 3)), q i / 4) ^ 2 =
      (9 / 16 : ℝ) * (q i) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  simp_rw [he] at h
  rw [← Finset.mul_sum] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Prime-site specialization with the explicit `9/8` coefficient. -/
theorem sameSiteTwoSplitPrime_test_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (F : (Q → SplitCategories) → ℂ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ y, ‖F y‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x : ℂ) *
        F (fun p => splitCategory (x p))) -
      (∑ y, (bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y : ℂ) * F y)‖ ≤
      (9 / 8 : ℝ) * L * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  have hq (p : Q) : 0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have hp := hQ p.val p.property
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  have h := sameSiteTwoSplitProduct_test_bound (fun p : Q => 1 / (p.val : ℝ)) hq F hL hF
  have hs : (∑ p : Q, (1 / (p.val : ℝ)) ^ 2) = ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
    simp only [div_pow, one_pow]
    exact Finset.sum_coe_sort Q (fun p => 1 / (p : ℝ) ^ 2)
  rw [hs] at h
  simpa only [div_div, mul_comm _ (4 : ℝ)] using h

theorem independentSplitProducts_of_actual (Q : Finset ℕ) (x : Q → Bool × Bool) :
    independentSplitProducts Q (fun p => splitCategory (x p)) = actualSplitProducts Q x := by
  apply Prod.ext
  · change (∏ p : Q, if (0 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) *
        (∏ p : Q, if (1 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rcases x p with ⟨a, b⟩
    cases a <;> cases b <;> simp [splitCategory]
  · change (∏ p : Q, if (0 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) *
        (∏ p : Q, if (2 : Fin 3) ∈ (splitCategory (x p)).val then p.val else 1) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    rcases x p with ⟨a, b⟩
    cases a <;> cases b <;> simp [splitCategory]

/-- The manuscript's two-split comparison, directly for arbitrary bounded
tests of the resulting pair of prime products. It applies in particular to
every pair of cells used in the step kernel. -/
theorem twoSplitPrimeProducts_test_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : ℕ × ℕ → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ z, ‖F z‖ ≤ L) :
    ‖(∑ x, (sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x : ℂ) *
        F (actualSplitProducts Q x)) -
      (∑ y, (bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y : ℂ) *
          F (independentSplitProducts Q y))‖ ≤
      (9 / 8 : ℝ) * L * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  have h := sameSiteTwoSplitPrime_test_bound Q hQ (fun y => F (independentSplitProducts Q y))
    hL (fun y => hF _)
  simpa only [independentSplitProducts_of_actual] using h

open Classical in
/-- The cell-pair probability estimate used to compare step kernels. -/
theorem twoSplitPrimeProducts_cell_bound (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (A B : Set ℕ) :
    |(∑ x, if (actualSplitProducts Q x).1 ∈ A ∧ (actualSplitProducts Q x).2 ∈ B then
        sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) -
      (∑ y, if (independentSplitProducts Q y).1 ∈ A ∧ (independentSplitProducts Q y).2 ∈ B then
        bernoulliProductMass Finset.univ
          (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0)| ≤
      (9 / 8 : ℝ) * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  let F : ℕ × ℕ → ℂ := fun z => if z.1 ∈ A ∧ z.2 ∈ B then 1 else 0
  have hF (z : ℕ × ℕ) : ‖F z‖ ≤ (1 : ℝ) := by
    dsimp [F]
    split_ifs <;> norm_num
  have h := twoSplitPrimeProducts_test_bound Q hQ F (by norm_num : (0 : ℝ) ≤ 1) hF
  simp only [F, mul_ite, mul_one, mul_zero] at h
  have hc (P : Prop) [Decidable P] (a : ℝ) :
      (if P then (a : ℂ) else 0) = ((if P then a else 0 : ℝ) : ℂ) := by
    split_ifs <;> rfl
  simp_rw [hc] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  simpa only [mul_one] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative reciprocal-square tails

The error in the independent-product replacement is controlled by the tail
of all integers; no prime number theorem is needed here.
-/

namespace JointDickman

open Finset

theorem sum_reciprocal_square_tail (Q : Finset ℕ) {N : ℕ} (hN : N ≠ 0)
    (hQ : ∀ q ∈ Q, N < q) : (∑ q ∈ Q, 1 / (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  let M := max N (Q.sup id)
  have hsub : Q ⊆ Ioc N M := by
    intro q hq
    exact mem_Ioc.mpr ⟨hQ q hq, (le_sup (f := id) hq).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ q ∈ Ioc N M, 1 / (q : ℝ) ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      simpa only [one_div] using (sum_Ioc_inv_sq_le_sub (α := ℝ) hN (le_max_left _ _))
    _ ≤ _ := sub_le_self _ (by positivity)

open Classical in
/-- The cell probability comparison has error at most `9/(8N)` when all
allowed primes exceed `N`. -/
theorem twoSplitPrimeProducts_cell_tail_bound (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (A B : Set ℕ) :
    |(∑ x, if (actualSplitProducts Q x).1 ∈ A ∧ (actualSplitProducts Q x).2 ∈ B then
        sameSiteTwoSplitProductMass (fun p : Q => 1 / (p.val : ℝ)) x else 0) -
      (∑ y, if (independentSplitProducts Q y).1 ∈ A ∧ (independentSplitProducts Q y).2 ∈ B then
        bernoulliProductMass univ
          (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0)| ≤
      9 / (8 * N : ℝ) := by
  calc
    _ ≤ (9 / 8 : ℝ) * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 :=
      twoSplitPrimeProducts_cell_bound Q hQ A B
    _ ≤ (9 / 8 : ℝ) * (1 / N) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail Q hN hcut) (by norm_num)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogProductBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite logarithmic errors for prime-product normalizations

The quadratic logarithmic error is summable above the lower prime cutoff.
The inverse factors in the exact Bernoulli product mass are controlled
separately by a reciprocal sum over the selected primes.
-/

namespace JointDickman

open Finset

theorem log_one_sub_add_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  have hbase : |Real.log (1 - x) + x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx, add_comm] using h
  have hden : 0 < 1 - x := by linarith
  apply hbase.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem finite_log_product_error {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    |Real.log (∏ i ∈ P, (1 - x i)) + ∑ i ∈ P, x i| ≤ 2 * ∑ i ∈ P, (x i) ^ 2 := by
  rw [Real.log_prod (fun i hi => by linarith [(hx i hi).2]), ← sum_add_distrib]
  calc
    _ ≤ ∑ i ∈ P, |Real.log (1 - x i) + x i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, 2 * (x i) ^ 2 := sum_le_sum fun i hi =>
      log_one_sub_add_error (hx i hi).1 (hx i hi).2
    _ = _ := (mul_sum _ _ _).symm

/-- A selected-prime normalizer differs logarithmically from the linear
reciprocal-prime sum by at most the reciprocal-square tail. -/
theorem prime_log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ P, N < p) :
    |Real.log (∏ p ∈ P, (1 - z / (p : ℝ))) + z * ∑ p ∈ P, 1 / (p : ℝ)| ≤
      2 * z ^ 2 / (N : ℝ) := by
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have h := finite_log_product_error P (fun p => z / (p : ℝ)) hx
  have heq : (∑ p ∈ P, (z / (p : ℝ)) ^ 2) = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    simp only [div_pow, mul_one_div]
  rw [heq] at h
  have hlin : (∑ p ∈ P, z / (p : ℝ)) = z * ∑ p ∈ P, 1 / (p : ℝ) := by
    simp only [mul_sum, mul_one_div]
  rw [hlin] at h
  calc
    _ ≤ 2 * (z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := h
    _ ≤ 2 * (z ^ 2 * (1 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z))
        (by norm_num)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normalization of the independent prime-product law

The logarithm of the all-absent probability is its linear prime sum up to
a reciprocal-square error. Mertens' second theorem therefore determines
the normalization for a moving lower and upper cutoff.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Both endpoint Mertens remainders control the prime-interval remainder. -/
theorem prime_interval_mertens_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X Y : ℝ, 2 ≤ X → X ≤ Y →
      |(∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) -
        (Real.log (Real.log Y) - Real.log (Real.log X))| ≤
        C / Real.log Y + C / Real.log X := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨C, hC, fun X Y hX hXY => ?_⟩
  have hY : 2 ≤ Y := hX.trans hXY
  have h₁ : |primeReciprocalSum X - Real.log (Real.log X) - M| ≤ C / Real.log X := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound X hX
  have h₂ : |primeReciprocalSum Y - Real.log (Real.log Y) - M| ≤ C / Real.log Y := by
    simpa [primeReciprocalSum, primesLE_eq_filter] using hbound Y hY
  rw [largePrimeSet_reciprocal_eq (by linarith) hXY]
  calc
    _ = |(primeReciprocalSum Y - Real.log (Real.log Y) - M) -
        (primeReciprocalSum X - Real.log (Real.log X) - M)| := by congr 1; ring
    _ ≤ |primeReciprocalSum Y - Real.log (Real.log Y) - M| +
        |primeReciprocalSum X - Real.log (Real.log X) - M| := abs_sub _ _
    _ ≤ _ := add_le_add h₂ h₁

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The manuscript's auxiliary prime scale

The lower cutoff is `B^1000`, the upper cutoff is `exp (4 B)`, and
`R = B / log (B^1000)`. The normalizing constant below is derived from
the published reciprocal-prime Mertens estimate.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem auxiliaryCutoff_tendsto : Tendsto auxiliaryCutoff atTop atTop :=
  tendsto_pow_atTop (by norm_num : (1000 : ℕ) ≠ 0)

theorem auxiliaryCutoff_le_upper :
    ∀ᶠ B in atTop, (auxiliaryCutoff B : ℝ) ≤ auxiliaryUpper B := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by norm_num : (0 : ℝ) < 4)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
  have hpow : (0 : ℝ) ≤ (B : ℝ) ^ 1000 := pow_nonneg (Nat.cast_nonneg B) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpow,
    abs_of_pos (Real.exp_pos _), one_mul, auxiliaryCutoff, auxiliaryUpper,
    Nat.cast_pow] using hB

theorem auxiliaryRatio_pos {B : ℕ} (hB : 1 < B) : 0 < auxiliaryRatio B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  exact div_pos (by linarith) (mul_pos (by norm_num) (Real.log_pos hBreal))

theorem auxiliaryRatio_tendsto : Tendsto auxiliaryRatio atTop atTop := by
  have hlim : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul 1000
  have hpos : ∀ᶠ B : ℕ in atTop, 0 < 1000 * (Real.log B / (B : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
    exact mul_pos (by norm_num) (div_pos (Real.log_pos hBreal) (by linarith))
  have hgt : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ)))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hlim, hpos⟩
  convert hgt.inv_tendsto_nhdsGT_zero using 1
  all_goals try with_reducible_and_instances rfl
  ext B
  simp only [auxiliaryRatio, Pi.inv_apply, mul_inv_rev, inv_div]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteAdditiveOrthogonality
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite additive orthogonality for the arithmetic kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped ComplexConjugate

theorem additivePhase_conj (t : ℝ) : conj (additivePhase t) = additivePhase (-t) := by
  unfold additivePhase
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ScaledRoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients in the limiting prime-product density

The zeroth normalized coefficient has the stated limit, and every fixed
higher coefficient vanishes. No residue-distribution assertion is assumed.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteChannels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite smoothing channels

Nonnegative transition probabilities and a uniform output mass bound
imply the weighted square-norm estimate for finite smoothing channels.
-/

namespace JointDickman

open Finset

section Channel

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

/-- Exact weighted adjoint identity, before any norm estimate. -/
theorem finiteChannel_adjoint (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (hμ : ∀ a, μ a ≠ 0) (f : Ω → ℝ) (g : A → ℝ) :
    (∑ a, μ a * finiteChannel w μ p f a * g a) =
      ∑ s, w s * f s * finiteChannelAdjoint p g s := by
  unfold finiteChannel finiteChannelAdjoint
  simp_rw [mul_div_cancel₀ _ (hμ _), sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro a _
  ring

private theorem channel_cell_square (w : Ω → ℝ) (p : Ω → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hp : ∀ s, 0 ≤ p s) (f : Ω → ℝ) :
    (∑ s, w s * p s * f s) ^ 2 ≤
      (∑ s, w s * p s) * ∑ s, w s * p s * f s ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (hw s) (hp s)
  · intro s _
    exact mul_nonneg (mul_nonneg (hw s) (hp s)) (sq_nonneg _)
  · intro s _
    ring_nf
    exact le_rfl

omit [Fintype A] in
theorem finiteTwoSplitKernel_symm (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (a b : A) :
    finiteTwoSplitKernel w μ p a b = finiteTwoSplitKernel w μ p b a := by
  unfold finiteTwoSplitKernel
  congr 1
  · apply sum_congr rfl
    intro s _
    ring
  · ring

/-- The two-split kernel is exactly the channel followed by its adjoint. -/
theorem finiteTwoSplitKernel_action (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (hμ : ∀ a, μ a ≠ 0) (g : A → ℝ) (a : A) :
    finiteKernelAction μ (finiteTwoSplitKernel w μ p) g a =
      finiteChannel w μ p (finiteChannelAdjoint p g) a := by
  unfold finiteKernelAction finiteTwoSplitKernel finiteChannel finiteChannelAdjoint
  simp only [sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro b _
  field_simp [hμ a, hμ b]

omit [Fintype Ω] in
/-- Two weighted absolute row/column estimates give a finite Schur bound.
This form also applies to signed differences of probability kernels. -/
theorem finiteKernelAction_square_bound (μ : A → ℝ) (K : A → A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b * |K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a * |K a b|) ≤ C) (g : A → ℝ) :
    (∑ a, μ a * finiteKernelAction μ K g a ^ 2) ≤
      C ^ 2 * ∑ a, μ a * g a ^ 2 := by
  have hcell (a : A) : finiteKernelAction μ K g a ^ 2 ≤
      C * ∑ b, μ b * |K a b| * g b ^ 2 := by
    have habs : |finiteKernelAction μ K g a| ≤ ∑ b, μ b * |K a b| * |g b| := by
      unfold finiteKernelAction
      calc
        _ ≤ ∑ b, |μ b * K a b * g b| := abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hμ _)]
    have hsum : 0 ≤ ∑ b, μ b * |K a b| * |g b| :=
      sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hμ b) (abs_nonneg _)) (abs_nonneg _)
    have hsq := (sq_le_sq₀ (abs_nonneg _) hsum).2 habs
    rw [sq_abs] at hsq
    have hcs := channel_cell_square μ (fun b => |K a b|) hμ
      (fun b => abs_nonneg _) (fun b => |g b|)
    simp_rw [sq_abs] at hcs
    exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right (hrow a)
      (sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hμ b) (abs_nonneg _)) (sq_nonneg _))))
  calc
    _ ≤ ∑ a, μ a * (C * ∑ b, μ b * |K a b| * g b ^ 2) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hcell a) (hμ a)
    _ = C * ∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b| := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ C * ∑ b, μ b * g b ^ 2 * C := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hcol b)
        (mul_nonneg (hμ b) (sq_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

end Channel


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual finite fair-split channel

A site is a vector of independent Bernoulli bits. Conditional on that site,
each present prime is retained independently with probability one half and
each absent prime stays absent. Integrating two conditionally independent
retentions gives exactly the same-site two-split law, including for arbitrary
output cells. This connects that law to the actual finite channel kernel.
-/

namespace JointDickman

open scoped BigOperators

/-- This is the conditional independence in the definition of two fair splits. -/
theorem conditionalFairSplitMass_factor (hit b c : Bool) :
    conditionalFairSplitMass hit (b, c) =
      fairRetentionBitMass hit b * fairRetentionBitMass hit c := by
  cases hit <;> cases b <;> cases c <;>
    norm_num [conditionalFairSplitMass, fairRetentionBitMass, bernoulliBitMass]

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

theorem bernoulliSiteMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) : ∑ x, bernoulliSiteMass q x = 1 :=
  finiteProductMass_sum _ (fun i => bernoulliBitMass_sum (q i))

theorem bernoulliSiteMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliSiteMass q x :=
  finiteProductMass_nonneg _ (fun i => bernoulliBitMass_nonneg (hq i)) x

/-- Summing out the shared site gives the actual joint retention law. -/
theorem fairRetentionMass_joint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y z : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z) =
      sameSiteTwoSplitProductMass q (fun i => (y i, z i)) := by
  classical
  have hp (x : ι → Bool) :
      bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z =
        ∏ i, bernoulliBitMass (q i) (x i) * fairRetentionBitMass (x i) (y i) *
          fairRetentionBitMass (x i) (z i) := by
    simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, Finset.prod_mul_distrib]
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i) * fairRetentionBitMass hit (z i))]
  unfold sameSiteTwoSplitProductMass finiteProductMass
  apply Finset.prod_congr rfl
  intro i _
  unfold sameSiteTwoSplitMass
  apply Finset.sum_congr rfl
  intro hit _
  rw [conditionalFairSplitMass_factor]
  ring

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

theorem fairSplitAverage_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    (∑ x, bernoulliSiteMass q x * fairSplitAverage x f * fairSplitAverage x g) =
      ∑ z, sameSiteTwoSplitProductMass q z * f (fun i => (z i).1) * g (fun i => (z i).2) := by
  classical
  calc
    _ = ∑ z, ∑ y, (∑ x, bernoulliSiteMass q x * fairRetentionMass x y * fairRetentionMass x z) *
        f y * g z := by
      unfold fairSplitAverage
      simp only [mul_assoc]
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ z, ∑ y, sameSiteTwoSplitProductMass q (fun i => (y i, z i)) * f y * g z := by
      simp_rw [fairRetentionMass_joint]
    _ = ∑ y, ∑ z, sameSiteTwoSplitProductMass q (fun i => (y i, z i)) * f y * g z :=
      Finset.sum_comm
    _ = ∑ yz : (ι → Bool) × (ι → Bool),
        sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2 :=
      (Fintype.sum_prod_type (fun yz : (ι → Bool) × (ι → Bool) =>
        sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2)).symm
    _ = _ := ((Equiv.arrowProdEquivProdArrow ι (fun _ => Bool) (fun _ => Bool)).sum_comp
      (fun yz => sameSiteTwoSplitProductMass q (fun i => (yz.1 i, yz.2 i)) * f yz.1 * g yz.2)).symm

theorem fairSplitTransition_eq_average {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (cell : (ι → Bool) → A) (x : ι → Bool) (a : A) :
    fairSplitTransition cell x a = fairSplitAverage x (fun y => if cell y = a then 1 else 0) := by
  classical
  unfold fairSplitTransition fairSplitAverage
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp_all

theorem fairSplitTransition_twoSplit_mass {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (q : ι → ℝ) (cell : (ι → Bool) → A) (a b : A) :
    (∑ x, bernoulliSiteMass q x * fairSplitTransition cell x a * fairSplitTransition cell x b) =
      ∑ z, if cell (fun i => (z i).1) = a ∧ cell (fun i => (z i).2) = b then
        sameSiteTwoSplitProductMass q z else 0 := by
  classical
  simp_rw [fairSplitTransition_eq_average]
  rw [fairSplitAverage_bilinear]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : cell (fun i => (z i).1) = a <;>
    by_cases hb : cell (fun i => (z i).2) = b <;> simp [ha, hb]

/-- Consequently the actual finite channel's two-split kernel is the cell
mass of the explicit two-split law divided by the two output atom weights. -/
theorem fairSplitTransition_twoSplitKernel {ι A : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq A]
    (q : ι → ℝ) (cell : (ι → Bool) → A) (μ : A → ℝ) (a b : A) :
    finiteTwoSplitKernel (bernoulliSiteMass q) μ (fairSplitTransition cell) a b =
      (∑ z, if cell (fun i => (z i).1) = a ∧ cell (fun i => (z i).2) = b then
        sameSiteTwoSplitProductMass q z else 0) / (μ a * μ b) := by
  unfold finiteTwoSplitKernel
  rw [fairSplitTransition_twoSplit_mass]

open Classical in
/-- Kernel identity for any finite partition of the retained prime product.
This is the direct bridge from the actual channel to two-split cell estimates. -/
theorem fairPrimeTransition_twoSplitKernel {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → A) (μ : A → ℝ) (a b : A) :
    finiteTwoSplitKernel (bernoulliSiteMass q) μ
      (fairSplitTransition (fun y => cell (retainedPrimeProduct Q y))) a b =
      (∑ z, if cell (actualSplitProducts Q z).1 = a ∧ cell (actualSplitProducts Q z).2 = b then
        sameSiteTwoSplitProductMass q z else 0) / (μ a * μ b) := by
  rw [fairSplitTransition_twoSplitKernel]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetThinning
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair thinning of an independently selected prime set -/

namespace JointDickman

open Finset

theorem fairRetentionMass_subsets {α : Type*} [DecidableEq α]
    (P : Finset α) (S T : P.powerset) :
    fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      subsetRetentionMass S.val T.val := by
  classical
  have heq : fairRetentionMass (subsetHitEquiv P S) (subsetHitEquiv P T) =
      ∏ p ∈ P, if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1 := by
    unfold fairRetentionMass finiteProductMass
    calc
      _ = ∏ p : P, if p.val ∈ S.val then (1 / 2 : ℝ) else if p.val ∈ T.val then 0 else 1 := by
        apply prod_congr rfl
        intro p _
        by_cases hs : p.val ∈ S.val <;> by_cases ht : p.val ∈ T.val <;>
          norm_num [subsetHitEquiv, fairRetentionBitMass, bernoulliBitMass, hs, ht]
      _ = _ := prod_coe_sort P (fun p => if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1)

  rw [heq]
  by_cases ht : T.val ⊆ S.val
  · rw [subsetRetentionMass, ite_eq_left ht]
    have hp (p : α) : (if p ∈ S.val then (1 / 2 : ℝ) else if p ∈ T.val then 0 else 1) =
        if p ∈ S.val then (1 / 2 : ℝ) else 1 := by
      by_cases hs : p ∈ S.val
      · simp [hs]
      · have hn : p ∉ T.val := fun h => hs (ht h)
        simp [hs, hn]
    simp_rw [hp]
    rw [← prod_filter]
    have hf : P.filter (fun p => p ∈ S.val) = S.val := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hp => (mem_powerset.mp S.property) hp)
    rw [hf, prod_const]
  · rw [subsetRetentionMass, ite_eq_right ht]
    obtain ⟨p, hpT, hpS⟩ := not_subset.mp ht
    apply prod_eq_zero (mem_powerset.mp T.property hpT)
    simp only [hpT, hpS, ite_false, if_false, ite_true, if_true]

theorem subsetRetentionMass_marginal {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) {T : Finset α} (hT : T ⊆ P) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * subsetRetentionMass S T) =
      bernoulliSubsetMass P (fun p => q p / 2) T := by
  classical
  let t : P.powerset := ⟨T, mem_powerset.mpr hT⟩
  have h := fairRetentionMass_marginal (fun p : P => q p.val) (subsetHitEquiv P t)
  rw [← (subsetHitEquiv P).sum_comp] at h
  change (∑ s : P.powerset,
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val)) (subsetHitEquiv P s) *
      fairRetentionMass (subsetHitEquiv P s) (subsetHitEquiv P t)) =
    finiteProductMass (fun p : P => bernoulliBitMass (q p.val / 2)) (subsetHitEquiv P t) at h
  simp_rw [bernoulliSubsetMass_eq_product, fairRetentionMass_subsets] at h
  rw [bernoulliSubsetMass_eq_product P (fun p => q p / 2) t] at h
  exact (sum_coe_sort P.powerset (fun S => bernoulliSubsetMass P q S * subsetRetentionMass S T)).symm.trans h

/-- Integrating both the first remaining set and its fair second coins
leaves precisely the independent addition law with halved parameters. -/
theorem subsetRetentionMass_expectation {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S *
      ∑ T ∈ P.powerset, subsetRetentionMass S T * F T) =
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) T * F T := by
  classical
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  rw [← sum_mul, subsetRetentionMass_marginal P q (mem_powerset.mp hT)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedSplitProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed fair-split product law used by the kernel -/

namespace JointDickman
open Finset

theorem splitProductMass_nonneg (P S : Finset ℕ) (n : ℕ) :
    0 ≤ splitProductMass P S n := by
  classical
  apply sum_nonneg
  intro A _
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem signedSplitProductMass_one (P : Finset ℕ) (n : ℕ) :
    signedSplitProductMass P (fun _ => 1) n = primeProductMass P (1/2) n := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp only [mul_one]
  rw [subsetRetentionMass_expectation]
  unfold primeProductMass
  apply sum_congr rfl
  intro A _
  have hq : (fun p : ℕ => (1/(p : ℝ))/2) = (fun p : ℕ => (1/2 : ℝ)/(p : ℝ)) := by
    funext p
    ring
  rw [hq]
  split_ifs <;> simp

theorem signedSplitProductMass_abs_le {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {g : Finset ℕ → ℝ} (hg : ∀ S ⊆ P, |g S| ≤ 1) (n : ℕ) :
    |signedSplitProductMass P g n| ≤ primeProductMass P (1/2) n := by
  classical
  rw [← signedSplitProductMass_one]
  unfold signedSplitProductMass
  calc
    _ ≤ ∑ S ∈ P.powerset,
        |bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S * splitProductMass P S n| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro S hS
      have hmass : 0 ≤ bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S := by
        apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
        intro p hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
        exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
      rw [abs_mul,abs_mul,abs_of_nonneg hmass,abs_of_nonneg (splitProductMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hg S (mem_powerset.mp hS)) hmass)
        (splitProductMass_nonneg _ _ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFourierReflection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflecting the second endpoint in the Fourier integral -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem finiteAdditiveSum_neg_real (s : Finset ℕ) (c : ℕ → ℝ) (θ : ℝ) :
    finiteAdditiveSum s (fun n => (c n : ℂ)) (-θ) =
      conj (finiteAdditiveSum s (fun n => (c n : ℂ)) θ) := by
  unfold finiteAdditiveSum
  rw [map_sum]
  apply sum_congr rfl
  intro n _
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueFourierParseval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact unit-residue Parseval identity for the fine histograms -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem stdAddChar_conj {q : ℕ} [NeZero q] (r : ZMod q) :
    conj (ZMod.stdAddChar r) = ZMod.stdAddChar (-r) := by
  rw [← Complex.inv_eq_conj (norm_stdAddChar r),AddChar.map_neg_eq_inv]

theorem unitResidue_fourier_pair {q : ℕ} [NeZero q]
    (r s : (ZMod q)ˣ) (v w : ℂ) :
    (∑ h : ZMod q, (ZMod.stdAddChar (h*(r : ZMod q))*v)*
      conj (ZMod.stdAddChar (h*(s : ZMod q))*w)) =
      if r = s then (q : ℂ)*v*conj w else 0 := by
  have he (h : ZMod q) : (ZMod.stdAddChar (h*(r : ZMod q))*v)*
      conj (ZMod.stdAddChar (h*(s : ZMod q))*w) =
      (v*conj w)*ZMod.stdAddChar (h*((r : ZMod q)-(s : ZMod q))) := by
    rw [map_mul (starRingEnd ℂ),stdAddChar_conj,mul_sub,AddChar.map_sub_eq_div,AddChar.map_neg_eq_inv]
    ring
  simp_rw [he]
  rw [← mul_sum,AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  have hz : (r : ZMod q)-(s : ZMod q) = 0 ↔ r = s := by
    rw [sub_eq_zero]
    exact Units.val_injective.eq_iff
  simp only [hz,ZMod.card]
  by_cases hrs : r = s
  · simp [hrs]
    ring
  · simp [hrs]

theorem unitResidue_fourier_parseval {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier v h‖^2) =
      (q : ℝ)*∑ r : (ZMod q)ˣ, ‖v r‖^2 := by
  have he : (∑ h : ZMod q, unitResidueFourier v h*conj (unitResidueFourier v h)) =
      ∑ r : (ZMod q)ˣ, ∑ s : (ZMod q)ˣ, ∑ h : ZMod q,
        (ZMod.stdAddChar (h*(r : ZMod q))*v r)*conj (ZMod.stdAddChar (h*(s : ZMod q))*v s) := by
    simp only [unitResidueFourier,map_sum,mul_sum,sum_mul]
    rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro s _
    rw [sum_comm]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_pow]
  simp_rw [← Complex.mul_conj']
  rw [he]
  simp_rw [unitResidue_fourier_pair]
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  rw [sum_eq_single r]
  · simp [mul_assoc]
  · intro s _ hsr
    simp [Ne.symm hsr]
  · simp

/-- Dividing the transform by phi gives the manuscript's probability normalization. -/
theorem normalizedUnitResidue_fourier_parseval {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier v h/(q.totient : ℂ)‖^2) =
      ((q : ℝ)/(q.totient : ℝ))*((1/(q.totient : ℝ))*∑ r : (ZMod q)ˣ, ‖v r‖^2) := by
  simp only [norm_div,Complex.norm_natCast,div_pow,← sum_div,unitResidue_fourier_parseval]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CellAverageOscillation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Complex cell averages and oscillation bounds -/

namespace JointDickman
open MeasureTheory

theorem complexCellAverage_norm_le {a b M : ℝ} {F : ℝ → ℂ}
    (hab : a < b) (hF : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ M) :
    ‖complexCellAverage a b F‖ ≤ M := by
  rw [complexCellAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := F) (C := M) (fun x hx =>
      hF x (Set.uIcc_of_le hab.le ▸ Set.uIoc_subset_uIcc hx))
  simpa only [abs_of_pos (sub_pos.mpr hab)] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogOscillatoryTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Oscillation of the actual major-arc tests in logarithmic coordinates -/

namespace JointDickman
open MeasureTheory

theorem logOscillatoryTest_norm (w : ℝ → ℝ) (B N ω x : ℝ) :
    ‖logOscillatoryTest w B N ω x‖ = |w (Real.exp (B*x)/N)| :=
  oscillatoryTest_norm w ω _

/-- Exact major-arc phase after the logarithmic change of variables. -/
theorem logOscillatoryTest_majorArc (w : ℝ → ℝ) {B N j X k ξ : ℝ}
    (hB : B ≠ 0) (hN : N ≠ 0) (hk : 0 < k) :
    logOscillatoryTest w B N (ξ*N/(j*X)) (Real.log k/B) =
      (w (k/N) : ℂ)*additivePhase (ξ*k/(j*X)) := by
  unfold logOscillatoryTest oscillatoryTest
  rw [mul_div_cancel₀ _ hB,Real.exp_log hk]
  congr 2
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeNormalizerUpper
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform upper bounds for prime-interval normalizers

The reciprocal-prime Mertens remainder gives one constant for all real
cutoffs. This is the analytic input to the small-product tail estimate.
-/

namespace JointDickman

open Finset

theorem primeNormalizer_upper
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (X Y z : ℝ), 2 ≤ X → X ≤ Y → 0 ≤ z → z ≤ 1 →
      primeNormalizer (largePrimeSet Y X) z ≤ A * (Real.log X / Real.log Y) ^ z := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨Real.exp (2 + 2 * C / Real.log 2), Real.exp_pos _, ?_⟩
  intro X Y z hX hXY hz hz1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hQ : ∀ p ∈ largePrimeSet Y X, p.Prime :=
    fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y X, 1 < p :=
    fun p hp => (hQ p hp).one_lt
  have hlocal := prime_log_product_error (largePrimeSet Y X) hQ hz hz1 (by decide : (1 : ℕ) ≠ 0) hcut
  have hsum := hinterval X Y hX hXY
  have hlogratio : Real.log (Real.log Y / Real.log X) = Real.log (Real.log Y) - Real.log (Real.log X) :=
    Real.log_div hlogY.ne' hlogX.ne'
  have hdivX : C / Real.log X ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) hX)
  have hdivY : C / Real.log Y ≤ C / Real.log 2 :=
    div_le_div_of_nonneg_left hC hlog2 (Real.log_le_log (by norm_num) (hX.trans hXY))
  have hsumlow := (abs_le.mp hsum).1
  have hlocalup := (abs_le.mp hlocal).2
  have hzsq : z ^ 2 ≤ 1 := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hsumlow hz
  have hsumerr : z * (C / Real.log Y + C / Real.log X) ≤ 2 * C / Real.log 2 := by
    calc
      _ ≤ 1 * (C / Real.log Y + C / Real.log X) :=
        mul_le_mul_of_nonneg_right hz1 (by positivity)
      _ = C / Real.log Y + C / Real.log X := one_mul _
      _ ≤ C / Real.log 2 + C / Real.log 2 := add_le_add hdivY hdivX
      _ = _ := by ring
  have hlogbound : Real.log (primeNormalizer (largePrimeSet Y X) z) ≤
      2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X) := by
    change Real.log (primeNormalizer (largePrimeSet Y X) z) +
      z * (∑ p ∈ largePrimeSet Y X, 1 / (p : ℝ)) ≤ 2 * z ^ 2 / (1 : ℕ) at hlocalup
    rw [hlogratio]
    norm_num only [Nat.cast_one, div_one] at hlocalup
    nlinarith
  have hpositive : 0 < primeNormalizer (largePrimeSet Y X) z := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (hQ p hp).one_lt
    have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (hz1.trans_lt hp1)
    linarith
  calc
    _ = Real.exp (Real.log (primeNormalizer (largePrimeSet Y X) z)) := (Real.exp_log hpositive).symm
    _ ≤ Real.exp (2 + 2 * C / Real.log 2 - z * Real.log (Real.log Y / Real.log X)) :=
      Real.exp_le_exp.mpr hlogbound
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos (div_pos hlogX hlogY),
        Real.log_div hlogX.ne' hlogY.ne', Real.log_div hlogY.ne' hlogX.ne']
      congr 2
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductSmallTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Small prime products and absent large primes

A small product must omit every prime above its size. Independence turns
this observation into an exact all-absent product bound.
-/

namespace JointDickman

open Finset

open Classical in
theorem bernoulliSubsetMass_subset_sum (P A : Finset ℕ) (q : ℕ → ℝ) :
    (∑ S ∈ P.powerset, if S ⊆ A then bernoulliSubsetMass P q S else 0) =
      ∏ p ∈ P \ A, (1 - q p) := by
  let v := fun p : ℕ => if p ∈ A then (1 : ℝ) else 0
  have hv (S : Finset ℕ) : (∏ p ∈ S, v p) = if S ⊆ A then 1 else 0 := by
    by_cases hS : S ⊆ A
    · simp only [ite_eq_left hS]
      exact prod_eq_one (fun p hp => ite_eq_left (hS hp))
    · rw [ite_eq_right hS]
      obtain ⟨p, hpS, hpA⟩ := not_subset.mp hS
      exact prod_eq_zero hpS (ite_eq_right hpA)
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * ∏ p ∈ S, v p := by
      apply sum_congr rfl
      intro S _
      rw [hv]
      split_ifs <;> simp
    _ = ∏ p ∈ P, (1 - q p + q p * v p) := bernoulliSubsetMass_tilt P q v
    _ = ∏ p ∈ P, if p ∈ A then 1 else (1 - q p) := by
      apply prod_congr rfl
      intro p _
      dsimp [v]
      split_ifs <;> ring
    _ = _ := by
      rw [prod_ite]
      simp only [prod_const_one, one_mul]
      congr 1
      ext p
      simp

open Classical in
theorem primeProduct_small_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {z X : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∑ S ∈ P.powerset, if (∏ p ∈ S, p : ℕ) ≤ X then
      bernoulliSubsetMass P (fun p => z / p) S else 0) ≤
      primeNormalizer (P.filter (fun p => X < (p : ℝ))) z := by
  let A : Finset ℕ := P.filter (fun (p : ℕ) => (p : ℝ) ≤ X)
  have hq : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨div_nonneg hz hp0.le, (div_le_one hp0).mpr (hz1.trans hp1)⟩
  calc
    _ ≤ ∑ S ∈ P.powerset, if S ⊆ A then bernoulliSubsetMass P (fun p => z / p) S else 0 := by
      apply sum_le_sum
      intro S hSP
      have hS := mem_powerset.mp hSP
      by_cases hsmall : (∏ p ∈ S, p : ℕ) ≤ X
      · have hSA : S ⊆ A := by
          intro p hp
          have hprod : p ≤ ∏ q ∈ S, q := single_le_prod' (fun q hq => (hP q (hS hq)).one_le) hp
          exact mem_filter.mpr ⟨hS hp, (by exact_mod_cast hprod : (p : ℝ) ≤ ∏ q ∈ S, q).trans hsmall⟩
        rw [ite_eq_left hsmall, ite_eq_left hSA]
      · rw [ite_eq_right hsmall]
        split_ifs
        · exact bernoulliSubsetMass_nonneg hS hq
        · rfl
    _ = ∏ p ∈ P \ A, (1 - z / (p : ℝ)) := bernoulliSubsetMass_subset_sum P A _
    _ = _ := by
      unfold primeNormalizer
      congr 1
      ext p
      simp [A]
      tauto

open Filter
open scoped Topology

open Classical in
/-- The manuscript's uniform small-log-product tail, including the empty product. -/
theorem primeProduct_small_log_tail
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        if Real.log (∏ p ∈ S, p : ℕ) / B ≤ δ then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0) ≤
        C * (δ + 1 / auxiliaryRatio B) ^ z := by
  obtain ⟨C, hC, hnormalizer⟩ := primeNormalizer_upper hM
  refine ⟨C, hC, ?_⟩
  have hN : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  filter_upwards [hN, auxiliaryCutoff_le_upper, eventually_gt_atTop 1] with B hNB hupper hB
  intro δ hδ hδ1
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hNreal : (2 : ℝ) ≤ auxiliaryCutoff B := by exact_mod_cast hNB
  let X := max (auxiliaryCutoff B : ℝ) (Real.exp (δ * B))
  have hX : 2 ≤ X := hNreal.trans (le_max_left _ _)
  have hXY : X ≤ auxiliaryUpper B := by
    apply max_le hupper
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfilter : (auxiliaryPrimes B).filter (fun (p : ℕ) => Real.exp (δ * B) < (p : ℝ)) =
      largePrimeSet (auxiliaryUpper B) X := by
    ext p
    simp [auxiliaryPrimes, largePrimeSet, X, max_lt_iff, and_assoc]
  have hsmall := primeProduct_small_bound (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (X := Real.exp (δ * B)) hz hz1
  rw [hfilter] at hsmall
  have hevent : (∑ S ∈ (auxiliaryPrimes B).powerset,
      if Real.log (∏ p ∈ S, p : ℕ) / B ≤ δ then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, if (∏ p ∈ S, p : ℕ) ≤ Real.exp (δ * B) then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => z / p) S else 0 := by
    apply sum_congr rfl
    intro S hS
    have hpos : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_powerset.mp hS hp)).pos)
    simp only [div_le_iff₀ hB0, Real.log_le_iff_le_exp hpos]
  have hloginv : Real.log (auxiliaryCutoff B) / (B : ℝ) = 1 / auxiliaryRatio B := by
    have hR := auxiliaryRatio_mul_log hB
    have hR0 : auxiliaryRatio B ≠ 0 := (auxiliaryRatio_pos hB).ne'
    field_simp
    nlinarith [hR]
  have hlogX : Real.log X ≤ Real.log (auxiliaryCutoff B) + δ * B := by
    by_cases h : (auxiliaryCutoff B : ℝ) ≤ Real.exp (δ * B)
    · dsimp only [X]
      rw [max_eq_right h, Real.log_exp]
      linarith [Real.log_natCast_nonneg (auxiliaryCutoff B)]
    · dsimp only [X]
      rw [max_eq_left (le_of_not_ge h)]
      nlinarith
  have hratio : Real.log X / Real.log (auxiliaryUpper B) ≤ δ + 1 / auxiliaryRatio B := by
    rw [auxiliaryUpper, Real.log_exp, ← hloginv]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)).mpr
    have hNlog := Real.log_natCast_nonneg (auxiliaryCutoff B)
    have hcancel : (Real.log (auxiliaryCutoff B) / (B : ℝ)) * B = Real.log (auxiliaryCutoff B) :=
      div_mul_cancel₀ _ hB0.ne'
    nlinarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlogY0 : 0 ≤ Real.log (auxiliaryUpper B) := by
    rw [auxiliaryUpper, Real.log_exp]
    positivity
  rw [hevent]
  exact hsmall.trans ((hnormalizer X (auxiliaryUpper B) z hX hXY hz hz1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hlogX0 hlogY0) hratio hz) hC.le))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteChannelSchur
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From two-split kernels to channel estimates

The channel input may be signed: the estimates here therefore also apply
when the transition probabilities have been centered in their residue
coordinate. No probabilistic or analytic estimate is assumed implicitly.
-/

namespace JointDickman

open Finset

private theorem weighted_product_cauchy {Ω : Type*} [Fintype Ω]
    (w f g : Ω → ℝ) (hw : ∀ s, 0 ≤ w s) :
    (∑ s, w s * f s * g s) ^ 2 ≤
      (∑ s, w s * f s ^ 2) * ∑ s, w s * g s ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (hw s) (sq_nonneg _)
  · intro s _
    exact mul_nonneg (hw s) (sq_nonneg _)
  · intro s _
    ring_nf
    exact le_rfl

/-- The quadratic-form version of the weighted Schur bound. -/
theorem finiteKernelAction_quadratic_bound {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hrow : ∀ a, (∑ b, μ b * |K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a * |K a b|) ≤ C) (g : A → ℝ) :
    (∑ a, μ a * g a * finiteKernelAction μ K g a) ≤
      C * ∑ a, μ a * g a ^ 2 := by
  have hpoint (a b : A) :
      2 * (μ a * g a * (μ b * K a b * g b)) ≤
        μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2) := by
    have habs : K a b * g a * g b ≤ |K a b| * |g a| * |g b| := by
      simpa only [abs_mul] using le_abs_self (K a b * g a * g b)
    have hsq := sq_nonneg (|g a| - |g b|)
    rw [sub_sq, sq_abs, sq_abs] at hsq
    have hbase : 2 * (K a b * g a * g b) ≤ |K a b| * (g a ^ 2 + g b ^ 2) := by
      nlinarith [mul_nonneg (abs_nonneg (K a b)) hsq]
    first | (convert mul_le_mul_of_nonneg_left hbase (mul_nonneg (hμ a) (hμ b)) using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_of_nonneg_left hbase (mul_nonneg (hμ a) (hμ b))).trans (le_of_eq (by ring)))
  have hdouble :
      2 * (∑ a, μ a * g a * finiteKernelAction μ K g a) ≤
        ∑ a, ∑ b, μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2) := by
    simp only [finiteKernelAction, mul_sum]
    exact sum_le_sum fun a _ => sum_le_sum fun b _ => hpoint a b
  have hsplit :
      (∑ a, ∑ b, μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2)) =
        (∑ a, μ a * g a ^ 2 * ∑ b, μ b * |K a b|) +
        ∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b| := by
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    · simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    · rw [sum_comm]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      ring
  rw [hsplit] at hdouble
  have hr : (∑ a, μ a * g a ^ 2 * ∑ b, μ b * |K a b|) ≤
      C * ∑ a, μ a * g a ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => by
      simpa [mul_comm C] using mul_le_mul_of_nonneg_left (hrow a)
        (mul_nonneg (hμ a) (sq_nonneg _))
  have hc : (∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b|) ≤
      C * ∑ b, μ b * g b ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun b _ => by
      simpa [mul_comm C] using mul_le_mul_of_nonneg_left (hcol b)
        (mul_nonneg (hμ b) (sq_nonneg _))
  linarith

/-- A bound for the two-split kernel controls the original channel.
Unlike a marginal estimate, this applies to signed, centered channels. -/
theorem finiteChannel_square_of_kernel_rows {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hμ : ∀ a, 0 < μ a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b * |finiteTwoSplitKernel w μ p a b|) ≤ C)
    (f : Ω → ℝ) :
    (∑ a, μ a * finiteChannel w μ p f a ^ 2) ≤ C * ∑ s, w s * f s ^ 2 := by
  let g := finiteChannel w μ p f
  let h := finiteChannelAdjoint p g
  let E := ∑ a, μ a * g a ^ 2
  let F := ∑ s, w s * f s ^ 2
  let H := ∑ s, w s * h s ^ 2
  have hμ0 : ∀ a, μ a ≠ 0 := fun a => ne_of_gt (hμ a)
  have hE : 0 ≤ E := sum_nonneg fun a _ => mul_nonneg (hμ a).le (sq_nonneg _)
  have hF : 0 ≤ F := sum_nonneg fun s _ => mul_nonneg (hw s) (sq_nonneg _)
  have hpair : E = ∑ s, w s * f s * h s := by
    calc
      E = ∑ a, μ a * finiteChannel w μ p f a * g a := by
        apply sum_congr rfl
        intro a _
        dsimp [g]
        ring
      _ = _ := finiteChannel_adjoint w μ p hμ0 f g
  have hcauchy : E ^ 2 ≤ F * H := by
    rw [hpair]
    exact weighted_product_cauchy w f h hw
  have hcol : ∀ b, (∑ a, μ a * |finiteTwoSplitKernel w μ p a b|) ≤ C := by
    intro b
    simpa only [finiteTwoSplitKernel_symm w μ p] using hrow b
  have hquad := finiteKernelAction_quadratic_bound μ (finiteTwoSplitKernel w μ p)
    (fun a => (hμ a).le) hrow hcol g
  have hkernel : H = ∑ a, μ a * g a *
      finiteKernelAction μ (finiteTwoSplitKernel w μ p) g a := by
    calc
      H = ∑ a, μ a * finiteChannel w μ p h a * g a := by
        rw [finiteChannel_adjoint w μ p hμ0 h g]
        apply sum_congr rfl
        intro s _
        dsimp [h]
        ring
      _ = _ := by
        apply sum_congr rfl
        intro a _
        rw [finiteTwoSplitKernel_action w μ p hμ0]
        change μ a * finiteChannel w μ p h a * g a =
          μ a * g a * finiteChannel w μ p h a
        ring
  rw [← hkernel] at hquad
  have hmain : E ^ 2 ≤ F * (C * E) :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hquad hF)
  change E ≤ C * F
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hC hF
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueCentering
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centering finite channels in the residue coordinate

All residues above the same base cell carry the same atom weight. Thus
subtracting the residue average of the transition subtracts exactly the
residue average of the channel. The corresponding two-split kernel is
centered in both coordinates. A residue-independent approximation cancels,
at a loss of at most four in its uniform error.
-/

namespace JointDickman

open scoped BigOperators

theorem finiteResidueAverage_add {R : Type*} [Fintype R] (f g : R → ℝ) :
    finiteResidueAverage (fun r => f r + g r) =
      finiteResidueAverage f + finiteResidueAverage g := by
  simp [finiteResidueAverage, Finset.sum_add_distrib, add_div]

theorem finiteResidueAverage_sub {R : Type*} [Fintype R] (f g : R → ℝ) :
    finiteResidueAverage (fun r => f r - g r) =
      finiteResidueAverage f - finiteResidueAverage g := by
  simp [finiteResidueAverage, Finset.sum_sub_distrib, sub_div]

theorem finiteResidueAverage_mul_const {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => f r * c) = finiteResidueAverage f * c := by
  simp only [finiteResidueAverage, ← Finset.sum_mul]
  ring

theorem finiteResidueAverage_const_mul {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => c * f r) = c * finiteResidueAverage f := by
  simp only [finiteResidueAverage, ← Finset.mul_sum]
  ring

theorem finiteResidueAverage_div_const {R : Type*} [Fintype R] (f : R → ℝ) (c : ℝ) :
    finiteResidueAverage (fun r => f r / c) = finiteResidueAverage f / c := by
  simp only [finiteResidueAverage, ← Finset.sum_div]
  ring

theorem finiteResidueAverage_sum {S R : Type*} [Fintype S] [Fintype R] (f : S → R → ℝ) :
    finiteResidueAverage (fun r => ∑ s, f s r) = ∑ s, finiteResidueAverage (f s) := by
  unfold finiteResidueAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteResidueAverage_const {R : Type*} [Fintype R] [Nonempty R] (c : ℝ) :
    finiteResidueAverage (fun _ : R => c) = c := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [finiteResidueAverage, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hn

theorem finiteResidueAverage_abs_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) {ε : ℝ} (hf : ∀ r, |f r| ≤ ε) : |finiteResidueAverage f| ≤ ε := by
  have hn : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  calc
    |finiteResidueAverage f| = |∑ r, f r| / (Fintype.card R : ℝ) := by
      simp only [finiteResidueAverage, abs_div, abs_of_pos hn]
    _ ≤ (∑ r, |f r|) / (Fintype.card R : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ (∑ _r : R, ε) / (Fintype.card R : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun r _ => hf r)) hn.le
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ ε hn.ne'

/-- Equal cell weights make transition centering exactly channel centering.
The identity also holds at zero weights, under the usual totalized division. -/
theorem finiteChannel_residueCentered {Ω D R : Type*} [Fintype Ω] [Fintype D] [Fintype R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ) (f : Ω → ℝ) (d : D) (r : R) :
    finiteChannel w (fun a : D × R => μ a.1) (residueCenteredTransition p) f (d, r) =
      finiteChannel w (fun a : D × R => μ a.1) p f (d, r) -
        finiteResidueAverage (fun t => finiteChannel w (fun a : D × R => μ a.1) p f (d, t)) := by
  have hp (s : Ω) : w s * residueCenteredTransition p s (d, r) * f s =
      w s * p s (d, r) * f s - finiteResidueAverage (fun t => w s * p s (d, t) * f s) := by
    rw [finiteResidueAverage_mul_const, finiteResidueAverage_const_mul]
    unfold residueCenteredTransition
    ring
  unfold finiteChannel
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, sub_div, finiteResidueAverage_div_const, finiteResidueAverage_sum]

/-- The kernel of the centered channel is the actual four-term centered
two-split kernel. No nonzero-weight assumption is needed for this identity. -/
theorem finiteTwoSplitKernel_residueCentered {Ω D R : Type*}
    [Fintype Ω] [Fintype R] (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ)
    (d e : D) (r s : R) :
    finiteTwoSplitKernel w (fun a : D × R => μ a.1) (residueCenteredTransition p) (d, r) (e, s) =
      residueCenteredKernel (finiteTwoSplitKernel w (fun a : D × R => μ a.1) p) (d, r) (e, s) := by
  have hp (x : Ω) : w x * residueCenteredTransition p x (d, r) *
      residueCenteredTransition p x (e, s) =
      w x * p x (d, r) * p x (e, s) -
        finiteResidueAverage (fun t => w x * p x (d, t) * p x (e, s)) -
        finiteResidueAverage (fun u => w x * p x (d, r) * p x (e, u)) +
        finiteResidueAverage (fun t => finiteResidueAverage (fun u => w x * p x (d, t) * p x (e, u))) := by
    simp only [finiteResidueAverage_mul_const, finiteResidueAverage_const_mul]
    unfold residueCenteredTransition
    ring
  unfold finiteTwoSplitKernel residueCenteredKernel
  simp_rw [hp, finiteResidueAverage_div_const, finiteResidueAverage_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, add_div, sub_div]

theorem residueCenteredKernel_sub_base {D R : Type*} [Fintype R] [Nonempty R]
    (K : D × R → D × R → ℝ) (G : D → D → ℝ) (d e : D) (r s : R) :
    residueCenteredKernel K (d, r) (e, s) =
      residueCenteredKernel (fun a b => K a b - G a.1 b.1) (d, r) (e, s) := by
  unfold residueCenteredKernel
  simp_rw [finiteResidueAverage_sub, finiteResidueAverage_const]
  ring

/-- A residue-independent approximating kernel disappears after centering;
the four remaining averages each contribute at most the uniform error. -/
theorem residueCenteredKernel_abs_le {D R : Type*} [Fintype R] [Nonempty R]
    (K : D × R → D × R → ℝ) (G : D → D → ℝ) {ε : ℝ}
    (hK : ∀ d e r s, |K (d, r) (e, s) - G d e| ≤ ε) (d e : D) (r s : R) :
    |residueCenteredKernel K (d, r) (e, s)| ≤ 4 * ε := by
  rw [residueCenteredKernel_sub_base K G]
  unfold residueCenteredKernel
  have h₀ := hK d e r s
  have h₁ := finiteResidueAverage_abs_le (fun t => K (d, t) (e, s) - G d e)
    (fun t => hK d e t s)
  have h₂ := finiteResidueAverage_abs_le (fun u => K (d, r) (e, u) - G d e)
    (fun u => hK d e r u)
  have h₃ := finiteResidueAverage_abs_le
    (fun t => finiteResidueAverage (fun u => K (d, t) (e, u) - G d e))
    (fun t => finiteResidueAverage_abs_le _ (fun u => hK d e t u))
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h₀ h₁)) h₂)) h₃).trans
      (by ring_nf; exact le_rfl))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CenteredKernelRows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centered rows after discarding a small part of a kernel

Uniform averaging in a residue coordinate preserves weighted sums because
all residues over a base cell have the same weight. A nonnegative discarded
kernel therefore costs at most four times its row bound after centering.
The remaining kernel can be compared with a residue-independent kernel.
-/

namespace JointDickman

open scoped BigOperators

theorem finiteResidueAverage_nonneg {R : Type*} [Fintype R]
    (f : R → ℝ) (hf : ∀ r, 0 ≤ f r) : 0 ≤ finiteResidueAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun r _ => hf r) (Nat.cast_nonneg _)

theorem finiteResidueAverage_mono {R : Type*} [Fintype R]
    (f g : R → ℝ) (hfg : ∀ r, f r ≤ g r) :
    finiteResidueAverage f ≤ finiteResidueAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun r _ => hfg r)
    (Nat.cast_nonneg _)

theorem finiteResidueAverage_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) {C : ℝ} (hf : ∀ r, f r ≤ C) : finiteResidueAverage f ≤ C := by
  simpa only [finiteResidueAverage_const] using
    finiteResidueAverage_mono f (fun _ => C) hf

theorem sum_finiteResidueAverage {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) : (∑ _r : R, finiteResidueAverage f) = ∑ r, f r := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, finiteResidueAverage]
  field_simp

/-- Averaging within an equal-weight residue fibre preserves total mass. -/
theorem weighted_sum_residueAverage {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] (μ : D → ℝ) (f : D × R → ℝ) :
    (∑ a : D × R, μ a.1 * finiteResidueAverage (fun t => f (a.1, t))) =
      ∑ a : D × R, μ a.1 * f a := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  simp_rw [← finiteResidueAverage_const_mul]
  exact sum_finiteResidueAverage (fun t => μ d * f (d, t))

theorem residueCenteredKernel_add {D R : Type*} [Fintype R]
    (K L : D × R → D × R → ℝ) (a b : D × R) :
    residueCenteredKernel (fun a b => K a b + L a b) a b =
      residueCenteredKernel K a b + residueCenteredKernel L a b := by
  unfold residueCenteredKernel
  simp only [finiteResidueAverage_add]
  ring

/-- All four nonnegative terms of the centering formula have controlled
weighted row sums. Only equality of weights inside each fibre is used. -/
theorem residueCenteredKernel_nonneg_rows {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R]
    (μ : D → ℝ) (K : D × R → D × R → ℝ)
    (hμ : ∀ d, 0 ≤ μ d) (hK : ∀ a b, 0 ≤ K a b) {C : ℝ}
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * K a b) ≤ C) (a : D × R) :
    (∑ b : D × R, μ b.1 * |residueCenteredKernel K a b|) ≤ 4 * C := by
  have hfirst : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun t => K (a.1, t) b)) ≤ C := by
    simp_rw [← finiteResidueAverage_const_mul]
    rw [← finiteResidueAverage_sum]
    exact finiteResidueAverage_le _ (fun t => hrow (a.1, t))
  have hsecond : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun u => K a (b.1, u))) ≤ C := by
    rw [weighted_sum_residueAverage]
    exact hrow a
  have hboth : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun t =>
        finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))) ≤ C := by
    simp_rw [← finiteResidueAverage_const_mul]
    rw [← finiteResidueAverage_sum]
    apply finiteResidueAverage_le
    intro t
    simp_rw [finiteResidueAverage_const_mul]
    rw [weighted_sum_residueAverage]
    exact hrow (a.1, t)
  have hp (b : D × R) : |residueCenteredKernel K a b| ≤
      K a b + finiteResidueAverage (fun t => K (a.1, t) b) +
        finiteResidueAverage (fun u => K a (b.1, u)) +
          finiteResidueAverage (fun t =>
            finiteResidueAverage (fun u => K (a.1, t) (b.1, u))) := by
    have h₀ := hK a b
    have h₁ := finiteResidueAverage_nonneg _ (fun t => hK (a.1, t) b)
    have h₂ := finiteResidueAverage_nonneg _ (fun u => hK a (b.1, u))
    have h₃ := finiteResidueAverage_nonneg _ (fun t =>
      finiteResidueAverage_nonneg _ (fun u => hK (a.1, t) (b.1, u)))
    unfold residueCenteredKernel
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ ∑ b : D × R, μ b.1 *
        (K a b + finiteResidueAverage (fun t => K (a.1, t) b) +
          finiteResidueAverage (fun u => K a (b.1, u)) +
            finiteResidueAverage (fun t =>
              finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hp b) (hμ b.1)
    _ ≤ 4 * C := by
      simp only [mul_add, Finset.sum_add_distrib]
      linarith [hrow a]

/-- Decompose the actual kernel into a nonnegative discarded part with
small row mass and a part uniformly close to a residue-independent kernel. -/
theorem residueCenteredKernel_rows_of_discarded {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R]
    (μ : D → ℝ) (K L H : D × R → D × R → ℝ) (G : D → D → ℝ)
    (hμ : ∀ d, 0 ≤ μ d) (hL : ∀ a b, 0 ≤ L a b)
    (hdecomp : ∀ a b, K a b = L a b + H a b) {C ε : ℝ}
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * L a b) ≤ C)
    (hflat : ∀ d e r s, |H (d, r) (e, s) - G d e| ≤ ε) (a : D × R) :
    (∑ b : D × R, μ b.1 * |residueCenteredKernel K a b|) ≤
      4 * C + 4 * ε * ∑ b : D × R, μ b.1 := by
  have hKeq : K = fun a b => L a b + H a b := by
    funext a b
    exact hdecomp a b
  rw [hKeq]
  simp_rw [residueCenteredKernel_add]
  calc
    _ ≤ ∑ b : D × R, μ b.1 *
        (|residueCenteredKernel L a b| + |residueCenteredKernel H a b|) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (abs_add_le _ _) (hμ b.1)
    _ = (∑ b : D × R, μ b.1 * |residueCenteredKernel L a b|) +
        ∑ b : D × R, μ b.1 * |residueCenteredKernel H a b| := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ 4 * C + ∑ b : D × R, μ b.1 * (4 * ε) := by
      apply add_le_add (residueCenteredKernel_nonneg_rows μ L hμ hL hrow a)
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
        (residueCenteredKernel_abs_le H G hflat a.1 b.1 a.2 b.2) (hμ b.1)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The discarded-plus-flat kernel estimate controls the entire centered
channel, uniformly for every real input. -/
theorem residueChannel_square_of_discarded {Ω D R : Type*}
    [Fintype Ω] [Fintype D] [Fintype R] [Nonempty R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ)
    (L H : D × R → D × R → ℝ) (G : D → D → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hμ : ∀ d, 0 < μ d) (hL : ∀ a b, 0 ≤ L a b)
    (hdecomp : ∀ a b, finiteTwoSplitKernel w (fun a : D × R => μ a.1) p a b =
      L a b + H a b) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * L a b) ≤ C)
    (hflat : ∀ d e r s, |H (d, r) (e, s) - G d e| ≤ ε) (f : Ω → ℝ) :
    (∑ a : D × R, μ a.1 *
      (finiteChannel w (fun a : D × R => μ a.1) p f a -
        finiteResidueAverage (fun t =>
          finiteChannel w (fun a : D × R => μ a.1) p f (a.1, t))) ^ 2) ≤
      (4 * C + 4 * ε * ∑ a : D × R, μ a.1) * ∑ x, w x * f x ^ 2 := by
  have hrows (a : D × R) :
      (∑ b : D × R, μ b.1 * |finiteTwoSplitKernel w (fun a : D × R => μ a.1)
        (residueCenteredTransition p) a b|) ≤
        4 * C + 4 * ε * ∑ b : D × R, μ b.1 := by
    have hk (a b : D × R) :
        finiteTwoSplitKernel w (fun a : D × R => μ a.1)
          (residueCenteredTransition p) a b =
          residueCenteredKernel (finiteTwoSplitKernel w (fun a : D × R => μ a.1) p) a b := by
      rcases a with ⟨d, r⟩
      rcases b with ⟨e, s⟩
      exact finiteTwoSplitKernel_residueCentered w μ p d e r s
    simp_rw [hk]
    exact residueCenteredKernel_rows_of_discarded μ _ L H G
      (fun d => (hμ d).le) hL hdecomp hrow hflat a
  have hbound := finiteChannel_square_of_kernel_rows w (fun a : D × R => μ a.1)
    (residueCenteredTransition p) hw (fun a => hμ a.1)
    (add_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg (mul_nonneg (by norm_num) hε)
        (Finset.sum_nonneg fun a _ => (hμ a.1).le))) hrows f
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteChannel_residueCentered]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_LowExclusiveKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite low-exclusive kernel

The common variable and the two exclusive variables have independent
finite masses. Cells are specified by an `Option`-valued map, allowing
discarded outputs. Restricting the second exclusive variable to `low`
has separate row and column estimates, proved from these actual masses.
-/

namespace JointDickman

open scoped BigOperators

section

variable {C E A : Type*} [Fintype C] [Fintype E] [Fintype A] [DecidableEq A]

omit [Fintype A] in
theorem optionCellMass_nonneg (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) (a : A) : 0 ≤ optionCellMass v cell a := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> [exact hv e; exact le_rfl]

theorem optionCellMass_sum_le (v : E → ℝ) (cell : E → Option A)
    (hv : ∀ e, 0 ≤ v e) : (∑ a, optionCellMass v cell a) ≤ ∑ e, v e := by
  unfold optionCellMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  cases h : cell e with
  | none => simpa [h] using hv e
  | some a => simp

theorem lowExclusiveProbability_nonneg (v : E → ℝ) (low : E → Prop)
    [DecidablePred low] (hv : ∀ e, 0 ≤ v e) : 0 ≤ lowExclusiveProbability v low := by
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> [exact hv e; exact le_rfl]

omit [Fintype A] in
/-- This factorized definition is precisely the restricted independent
triple law; it includes no assumption about its row or column behavior. -/
theorem lowExclusiveMass_eq_triple (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) :
    lowExclusiveMass w v cell low a b =
      ∑ c, ∑ e₂, ∑ e₁, if low e₂ ∧ cell c e₁ = some a ∧ cell c e₂ = some b then
        w c * v e₁ * v e₂ else 0 := by
  unfold lowExclusiveMass optionCellMass
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e₂ _
  apply Finset.sum_congr rfl
  intro e₁ _
  by_cases hlow : low e₂ <;> by_cases ha : cell c e₁ = some a <;>
    by_cases hb : cell c e₂ = some b <;> simp [hlow, ha, hb]

/-- The row estimate uses the fact that an exclusive output belongs to
at most one retained cell. -/
theorem lowExclusiveMass_row (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a : A) :
    (∑ b, lowExclusiveMass w v cell low a b) ≤
      lowExclusiveProbability v low * independentCellMarginal w v cell a := by
  have hlow : ∀ e, 0 ≤ if low e then v e else 0 := by
    intro e
    split_ifs <;> [exact hv e; exact le_rfl]
  calc
    _ = ∑ c, (w c * optionCellMass v (cell c) a) *
        (∑ b, optionCellMass (fun e => if low e then v e else 0) (cell c) b) := by
      unfold lowExclusiveMass
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ c, (w c * optionCellMass v (cell c) a) * lowExclusiveProbability v low := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left (optionCellMass_sum_le _ (cell c) hlow)
        (mul_nonneg (hw c) (optionCellMass_nonneg v (cell c) hv a))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

omit [Fintype A] in
/-- Integrating the common variable after conditioning on the restricted
exclusive variable. This is the precise conditional mass used for columns. -/
theorem lowExclusiveMass_integrate_common (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (b : A) :
    (∑ c, w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b) =
      ∑ e, if low e then v e * optionCellMass w (fun c => cell c e) b else 0 := by
  unfold optionCellMass
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : low e
  · simp only [hl, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : cell c e = some b <;> simp [hc, mul_comm]
  · simp [hl]

/-- The column estimate uses the normalized first exclusive law and a
uniform conditional common-variable cell estimate at every low exclusive. -/
theorem lowExclusiveMass_column (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {H : ℝ} (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H)
    (b : A) : (∑ a, lowExclusiveMass w v cell low a b) ≤ lowExclusiveProbability v low * H := by
  have hlow : ∀ e, 0 ≤ if low e then v e else 0 := by
    intro e
    split_ifs <;> [exact hv e; exact le_rfl]
  calc
    _ = ∑ c, (w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b) *
        (∑ a, optionCellMass v (cell c) a) := by
      unfold lowExclusiveMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ c, w c * optionCellMass (fun e => if low e then v e else 0) (cell c) b := by
      apply Finset.sum_le_sum
      intro c _
      have hsum := optionCellMass_sum_le v (cell c) hv
      rw [hv1] at hsum
      simpa using mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (hw c) (optionCellMass_nonneg _ (cell c) hlow b))
    _ = ∑ e, if low e then v e * optionCellMass w (fun c => cell c e) b else 0 :=
      lowExclusiveMass_integrate_common w v cell low b
    _ ≤ ∑ e, if low e then v e * H else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · exact mul_le_mul_of_nonneg_left (hcommon e he b) (hv e)
      · exact le_rfl
    _ = _ := by simp only [lowExclusiveProbability, Finset.sum_mul, ite_mul, zero_mul]

end

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_IndependentKernelSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The independent common/exclusive model and its cutoff

The three independent category bits are reindexed as three independent
Boolean prime subsets. Their products are the common product and the two
exclusive products. The low-exclusive union is separated exactly; the
complement is the product of the two high-exclusive cell probabilities.
-/

namespace JointDickman

open scoped BigOperators

/-- The independent category weight factors into the three actual
Bernoulli subset weights, without a coupling assumption. -/
theorem independentCategoryMass_triple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → SplitCategories) :
    bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y =
      bernoulliSiteMass q ((categoryTripleEquiv ι y).1) *
      bernoulliSiteMass q ((categoryTripleEquiv ι y).2.1) *
      bernoulliSiteMass q ((categoryTripleEquiv ι y).2.2) :=
  independentCategoryProductMass_factor q y

/-- Exact real-test pushforward to the independent triple law. -/
theorem independentCategory_triple_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (F : (ι → Bool) → (ι → Bool) → (ι → Bool) → ℝ) :
    (∑ y, bernoulliProductMass Finset.univ (fun i (_ : Fin 3) => q i) y *
      F ((categoryTripleEquiv ι y).1) ((categoryTripleEquiv ι y).2.1)
        ((categoryTripleEquiv ι y).2.2)) =
      ∑ c, ∑ e₁, ∑ e₂,
        bernoulliSiteMass q c * bernoulliSiteMass q e₁ * bernoulliSiteMass q e₂ * F c e₁ e₂ := by
  simp_rw [independentCategoryMass_triple]
  rw [(categoryTripleEquiv ι).sum_comp
    (fun x => bernoulliSiteMass q x.1 * bernoulliSiteMass q x.2.1 *
      bernoulliSiteMass q x.2.2 * F x.1 x.2.1 x.2.2)]
  simp only [Fintype.sum_prod_type]

theorem categoryPrimeProduct_eq_retained (Q : Finset ℕ) (y : Q → SplitCategories) :
    independentSplitProducts Q y =
      (retainedPrimeProduct Q ((categoryTripleEquiv Q y).1) *
        retainedPrimeProduct Q ((categoryTripleEquiv Q y).2.1),
       retainedPrimeProduct Q ((categoryTripleEquiv Q y).1) *
        retainedPrimeProduct Q ((categoryTripleEquiv Q y).2.2)) := by
  simp [independentSplitProducts, categoryPrimeProduct, retainedPrimeProduct,
    categoryTripleEquiv, categoryToTriple]

section Cutoff

variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

theorem independentPairMass_eq_triple (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (a b : A) :
    independentPairMass w v cell a b =
      ∑ c, ∑ e₁, ∑ e₂,
        if cell c e₁ = some a ∧ cell c e₂ = some b then w c * v e₁ * v e₂ else 0 := by
  unfold independentPairMass optionCellMass
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e₁ _
  apply Finset.sum_congr rfl
  intro e₂ _
  by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [ha, hb]

/-- The low union is dominated by the two one-sided low kernels. -/
theorem lowUnionExclusiveMass_le_sides (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a b : A) :
    lowUnionExclusiveMass w v cell low a b ≤
      lowExclusiveMass w v cell low a b + lowExclusiveMass w v cell low b a := by
  rw [lowExclusiveMass_eq_triple, lowExclusiveMass_eq_triple]
  unfold lowUnionExclusiveMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.sum_comm (f := fun e₂ e₁ =>
    if low e₂ ∧ cell c e₁ = some a ∧ cell c e₂ = some b then w c * v e₁ * v e₂ else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e₂ _
  have h := mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)
  by_cases hl₁ : low e₁ <;> by_cases hl₂ : low e₂ <;>
    by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [hl₁, hl₂, ha, hb] <;> nlinarith

/-- Local marginal and conditional common-cell bounds control the actual
union kernel, including the overlap of its two low-exclusive events. -/
theorem lowUnionExclusiveKernel_weighted_rows [Fintype A]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    {m H : ℝ} (hm : 0 < m)
    (hmarginal : ∀ a, independentCellMarginal w v cell a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ b, optionCellMass w (fun c => cell c e) b ≤ H * m)
    (a : A) :
    (∑ b, m * lowUnionExclusiveKernel w v cell low (fun _ => m) a b) ≤
      2 * lowExclusiveProbability v low * H := by
  have hσ := lowExclusiveProbability_nonneg v low hv
  have he (b : A) : m * lowUnionExclusiveKernel w v cell low (fun _ => m) a b =
      lowUnionExclusiveMass w v cell low a b / m := by
    unfold lowUnionExclusiveKernel
    field_simp
  simp_rw [he]
  rw [← Finset.sum_div]
  have hsum : (∑ b, lowUnionExclusiveMass w v cell low a b) ≤
      lowExclusiveProbability v low * independentCellMarginal w v cell a +
        lowExclusiveProbability v low * (H * m) := by
    calc
      _ ≤ ∑ b, (lowExclusiveMass w v cell low a b + lowExclusiveMass w v cell low b a) :=
        Finset.sum_le_sum fun b _ => lowUnionExclusiveMass_le_sides w v cell low hw hv a b
      _ = (∑ b, lowExclusiveMass w v cell low a b) +
          ∑ b, lowExclusiveMass w v cell low b a := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (lowExclusiveMass_row w v cell low hw hv a)
        (lowExclusiveMass_column w v cell low hw hv hv1 hcommon a)
  calc
    _ ≤ (lowExclusiveProbability v low * independentCellMarginal w v cell a +
        lowExclusiveProbability v low * (H * m)) / m := div_le_div_of_nonneg_right hsum hm.le
    _ ≤ (lowExclusiveProbability v low * (H * m) +
        lowExclusiveProbability v low * (H * m)) / m :=
      div_le_div_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left (hmarginal a) hσ) le_rfl) hm.le
    _ = _ := by field_simp <;> ring

end Cutoff

/-- Exact cell-pair probabilities under the independent prime-category law. -/
theorem independentPrimeCellMass_eq_pair {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (q : Q → ℝ) (cell : ℕ → Option A) (a b : A) :
    (∑ y, if cell (independentSplitProducts Q y).1 = some a ∧
        cell (independentSplitProducts Q y).2 = some b then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) =
      independentPairMass (bernoulliSiteMass q) (bernoulliSiteMass q)
        (primeProductCell Q cell) a b := by
  have h := independentCategory_triple_test q
    (fun c e₁ e₂ => if primeProductCell Q cell c e₁ = some a ∧
      primeProductCell Q cell c e₂ = some b then 1 else 0)
  rw [independentPairMass_eq_triple]
  convert h using 1
  · apply Finset.sum_congr rfl
    intro y _
    rw [categoryPrimeProduct_eq_retained]
    change (if primeProductCell Q cell ((categoryTripleEquiv Q y).1)
        ((categoryTripleEquiv Q y).2.1) = some a ∧
      primeProductCell Q cell ((categoryTripleEquiv Q y).1)
        ((categoryTripleEquiv Q y).2.2) = some b then
      bernoulliProductMass Finset.univ (fun p (_ : Fin 3) => q p) y else 0) = _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro e₁ _
    apply Finset.sum_congr rfl
    intro e₂ _
    simp only [mul_ite, mul_one, mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeResidueChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite residue estimate for the actual fair-prime channel

This combines the actual two-split comparison, the independent low/high
decomposition, and the exclusive local law. The conclusion concerns the
original fair-split channel and every real input simultaneously.
-/

namespace JointDickman

open scoped BigOperators

theorem fullPrimeMass_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 ≤ fullPrimeMass Q x := by
  apply bernoulliSiteMass_nonneg
  intro p
  have hp := hQ p.val p.property
  have hp₀ : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
  exact ⟨by positivity, (div_le_one hp₀).mpr hp₁⟩

theorem quarterPrimeMass_nonneg (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 ≤ quarterPrimeMass Q x := by
  apply bernoulliSiteMass_nonneg
  intro p
  have hp := hQ p.val p.property
  have hp₀ : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
  have hp₁ : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
  refine ⟨by positivity, (div_le_one (mul_pos (by norm_num) hp₀)).mpr ?_⟩
  linarith

theorem quarterPrimeMass_sum (Q : Finset ℕ) : ∑ x, quarterPrimeMass Q x = 1 :=
  bernoulliSiteMass_sum _

/-- The actual fair-split channel kernel and the independent triple kernel
are compared through their real cell-pair probabilities. -/
theorem fairPrimeKernel_independent_error {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → A) {m : ℝ} (hm : 0 < m) (a b : A) :
    |finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (fairPrimeTransition Q cell) a b -
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeOutputCell Q cell) a b / (m * m)| ≤ (9 / (8 * N : ℝ)) / (m * m) := by
  classical
  have hprob := twoSplitPrimeProducts_cell_tail_bound Q hQ hN hcut
    {n | cell n = a} {n | cell n = b}
  simp only [Set.mem_ofPred_eq] at hprob
  have hi : (∑ y, if cell (independentSplitProducts Q y).1 = a ∧
        cell (independentSplitProducts Q y).2 = b then
      bernoulliProductMass Finset.univ
        (fun (p : Q) (_ : Fin 3) => 1 / (4 * (p.val : ℝ))) y else 0) =
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeOutputCell Q cell) a b := by
    simpa only [Option.some.injEq, quarterPrimeMass, primeOutputCell] using independentPrimeCellMass_eq_pair Q
      (fun p : Q => 1 / (4 * (p.val : ℝ))) (fun n => some (cell n)) a b
  change |finiteTwoSplitKernel
      (bernoulliSiteMass (fun p : Q => 1 / (p.val : ℝ))) (fun _ => m)
      (fairSplitTransition (fun x => cell (retainedPrimeProduct Q x))) a b - _| ≤ _
  rw [fairPrimeTransition_twoSplitKernel, ← hi, ← sub_div, abs_div,
    abs_of_pos (mul_pos hm hm)]
  apply div_le_div_of_nonneg_right _ (mul_pos hm hm).le
  convert hprob using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ => x - y)
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteBridge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact equivalence of prime-site and prime-subset probabilities -/

namespace JointDickman

open Finset

theorem selectedPrimeSubset_subset (Q : Finset ℕ) (x : Q → Bool) :
    selectedPrimeSubset Q x ⊆ Q := filter_subset _ _

theorem selectedPrimeSubset_injective (Q : Finset ℕ) : Function.Injective (selectedPrimeSubset Q) := by
  intro x y hxy
  funext p
  have h : x p = true ↔ y p = true := by
    rw [← selectedPrimeSubset_mem Q x p, ← selectedPrimeSubset_mem Q y p, hxy]
  cases hx : x p <;> cases hy : y p <;> simp_all

open Classical in
theorem selectedPrimeSubset_surjective (Q S : Finset ℕ) (hS : S ⊆ Q) :
    ∃ x : Q → Bool, selectedPrimeSubset Q x = S := by
  refine ⟨fun p => decide (p.val ∈ S), ?_⟩
  ext p
  by_cases hp : p ∈ Q
  · simp [selectedPrimeSubset, hp]
  · have hpS : p ∉ S := fun h => hp (hS h)
    simp [selectedPrimeSubset, hp, hpS]

theorem retainedPrimeProduct_selected (Q : Finset ℕ) (x : Q → Bool) :
    retainedPrimeProduct Q x = ∏ p ∈ selectedPrimeSubset Q x, p := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then p.val else 1 := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then p else 1 :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then p else 1)
    _ = _ := by rw [prod_ite, hfilter]; simp

theorem bernoulliSiteMass_selected (Q : Finset ℕ) (q : ℕ → ℝ) (x : Q → Bool) :
    bernoulliSiteMass (fun p : Q => q p.val) x = bernoulliSubsetMass Q q (selectedPrimeSubset Q x) := by
  have hfilter : Q.filter (fun p => p ∈ selectedPrimeSubset Q x) = selectedPrimeSubset Q x := by
    ext p
    simp only [mem_filter, and_iff_right_iff_imp]
    exact fun h => selectedPrimeSubset_subset Q x h
  have hfilter' : Q.filter (fun p => p ∉ selectedPrimeSubset Q x) = Q \ selectedPrimeSubset Q x := by
    ext p
    simp
  calc
    _ = ∏ p : Q, if p.val ∈ selectedPrimeSubset Q x then q p.val else 1 - q p.val := by
      apply prod_congr rfl
      intro p _
      simp only [selectedPrimeSubset_mem]
      cases x p <;> rfl
    _ = ∏ p ∈ Q, if p ∈ selectedPrimeSubset Q x then q p else 1 - q p :=
      prod_coe_sort Q (fun p : ℕ => if p ∈ selectedPrimeSubset Q x then q p else 1 - q p)
    _ = _ := by rw [prod_ite, hfilter, hfilter']; rfl

open Classical in
/-- This equality transfers every event, not just an interval or a residue class. -/
theorem bernoulliPrimeSite_event (Q : Finset ℕ) (q : ℕ → ℝ) (A : ℕ → Prop) :
    (∑ x : Q → Bool, if A (retainedPrimeProduct Q x) then
      bernoulliSiteMass (fun p : Q => q p.val) x else 0) =
      ∑ S ∈ Q.powerset, if A (∏ p ∈ S, p) then bernoulliSubsetMass Q q S else 0 := by
  apply sum_bij (fun x _ => selectedPrimeSubset Q x)
  · intro x _
    exact mem_powerset.mpr (selectedPrimeSubset_subset Q x)
  · intro x _ y _ h
    exact selectedPrimeSubset_injective Q h
  · intro S hS
    obtain ⟨x, hx⟩ := selectedPrimeSubset_surjective Q S (mem_powerset.mp hS)
    exact ⟨x, mem_univ _, hx⟩
  · intro x _
    rw [retainedPrimeProduct_selected, bernoulliSiteMass_selected]

open Classical in
theorem quarterPrimeMass_small_log_tail
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop, ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      (∑ x : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ≤ δ then
          quarterPrimeMass (auxiliaryPrimes B) x else 0) ≤
        C * (δ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := primeProduct_small_log_tail hM
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with B hB
  intro δ hδ hδ1
  have heq (x : auxiliaryPrimes B → Bool) :
      quarterPrimeMass (auxiliaryPrimes B) x =
        bernoulliSiteMass (fun p : auxiliaryPrimes B => (1 / 4 : ℝ) / p.val) x := by
    unfold quarterPrimeMass
    congr 1
    funext p
    ring
  simp_rw [heq]
  rw [bernoulliPrimeSite_event (auxiliaryPrimes B) (fun p : ℕ => (1 / 4 : ℝ) / p)
    (fun n : ℕ => Real.log n / B ≤ δ)]
  exact hB δ hδ hδ1


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductLogCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual logarithmic and residue cells, with partial output -/

namespace JointDickman

open Finset

open Classical in
theorem logResidueCell_eq_some {D : Type*} (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (d : D) (r : (ZMod q)ˣ) :
    logResidueCell B q lower upper n = some (d, r) ↔
      Real.log n / B ∈ Set.Ioc (lower d) (upper d) ∧ (n : ZMod q) = r := by
  unfold logResidueCell
  by_cases hn : n.Coprime q
  · rw [dite_eq_left hn]
    by_cases hi : ∃ e, Real.log n / B ∈ Set.Ioc (lower e) (upper e)
    · rw [dite_eq_left hi, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hd, hr⟩
        subst d
        exact ⟨hi.choose_spec, by rw [← hr]; rfl⟩
      · rintro ⟨hd, hr⟩
        exact ⟨hdisjoint hi.choose d _ hi.choose_spec hd, Units.ext hr⟩
    · rw [dite_eq_right hi]
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun hd => False.elim (hi ⟨d, hd⟩)
  · rw [dite_eq_right hn]
    simp only [reduceCtorEq, false_iff, not_and]
    intro _ hr
    have hu : IsUnit (n : ZMod q) := hr ▸ r.isUnit
    exact hn ((ZMod.isUnit_iff_coprime n q).mp hu)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PartialPrimeChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fair-prime channels restricted to a collection of output cells -/

namespace JointDickman

open scoped BigOperators

/-- The same actual two-split comparison applies when outputs outside
all cells are discarded. -/
theorem partialFairPrimeKernel_independent_error {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option A) {m : ℝ} (hm : 0 < m) (a b : A) :
    |finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
      independentPairMass (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) a b / (m * m)| ≤ (9 / (8 * N : ℝ)) / (m * m) := by
  have h := fairPrimeKernel_independent_error Q hQ hN hcut cell hm (some a) (some b)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [finiteTwoSplitKernel, partialFairPrimeTransition, fairPrimeTransition,
      fairSplitTransition, independentPairMass, primeOutputCell, primeProductCell,
      optionCellMass, Option.some.injEq]
  congr 6

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueChannelDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Decay of the residue-channel error at polynomial cell scales -/

namespace JointDickman

open Filter
open scoped Topology

theorem primeComparisonError_power {B : ℕ} (hB : 0 < B) :
    9 / (8 * (auxiliaryCutoff B : ℝ)) = (9 / 8 : ℝ) * (B : ℝ) ^ (-(1000 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Real.rpow_neg hB0.le]
  norm_num [auxiliaryCutoff, Real.rpow_natCast]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ChannelGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's refining logarithmic grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem channelFineCount_pos {m₁ B : ℕ} (hm : 0 < m₁) (hB : 0 < B) :
    0 < channelFineCount m₁ B := by
  apply Nat.mul_pos hm
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by exact_mod_cast hB) _))
    (by exact_mod_cast hm)

theorem channelFineCount_upper {m₁ : ℕ} (hm : 0 < m₁) (B : ℕ) :
    (channelFineCount m₁ B : ℝ) ≤ (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) + m₁ := by
  have hm0 : (0 : ℝ) < m₁ := by exact_mod_cast hm
  have h := (Nat.ceil_lt_add_one (show 0 ≤ ((5 / 2 : ℝ) *
      (B : ℝ) ^ (11 / 10 : ℝ)) / m₁ by positivity)).le
  have h' := mul_le_mul_of_nonneg_left h hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_add, mul_one,
    mul_div_cancel₀ _ hm0.ne'] using h'

theorem channelFineCount_eventually_le_square {m₁ : ℕ} (hm : 0 < m₁) :
    ∀ᶠ B : ℕ in atTop, (channelFineCount m₁ B : ℝ) ≤ (B : ℝ) ^ 2 := by
  have hsmall : Tendsto (fun B : ℕ =>
      ((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) + m₁) / (B : ℝ) ^ 2) atTop (𝓝 0) := by
    have h₁ := ((power_div_power_tendsto_zero (by norm_num : (11 / 10 : ℝ) < 2)).comp
      tendsto_natCast_atTop_atTop).const_mul (5 / 2 : ℝ)
    have h₂ : Tendsto (fun B : ℕ => (m₁ : ℝ) / (B : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, Real.rpow_two, add_div, mul_div_assoc, add_zero, mul_zero] using h₁.add h₂
  filter_upwards [hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  exact (channelFineCount_upper hm B).trans
    ((div_lt_one (by positivity : (0 : ℝ) < (B : ℝ) ^ 2)).mp hsmallB).le

theorem channelMesh_pos {n : ℕ} (hn : 0 < n) : 0 < channelMesh n :=
  div_pos (by norm_num) (by exact_mod_cast hn)

theorem channel_width (n : ℕ) (i : Fin n) : channelUpper n i - channelLower n i = channelMesh n := by
  unfold channelUpper channelLower
  ring

theorem channelLower_ge (n : ℕ) (i : Fin n) : 1 / 2 ≤ channelLower n i := by
  unfold channelLower channelMesh
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by positivity))

theorem channelUpper_le {n : ℕ} (hn : 0 < n) (i : Fin n) : channelUpper n i ≤ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  have h := mul_le_mul_of_nonneg_right hi (channelMesh_pos hn).le
  have heq : (n : ℝ) * channelMesh n = 5 / 2 := by
    unfold channelMesh
    field_simp
  unfold channelUpper
  linarith

theorem channelCells_disjoint {n : ℕ} (hn : 0 < n) (i j : Fin n) (s : ℝ)
    (hi : s ∈ Set.Ioc (channelLower n i) (channelUpper n i))
    (hj : s ∈ Set.Ioc (channelLower n j) (channelUpper n j)) : i = j := by
  apply Fin.ext
  have hmesh := channelMesh_pos hn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hij : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hlt
    have hle : channelUpper n i ≤ channelLower n j := by
      unfold channelUpper channelLower
      nlinarith
    exact (not_lt_of_ge (hi.2.trans hle)) hj.1
  · have hji : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hgt
    have hle : channelUpper n j ≤ channelLower n i := by
      unfold channelUpper channelLower
      nlinarith
    exact (not_lt_of_ge (hj.2.trans hle)) hi.1

theorem channel_atom_lower {n q B : ℕ} [NeZero q] (hB : 0 < B)
    (hn : 0 < n) (hnB : (n : ℝ) ≤ (B : ℝ) ^ 2) (hqB : q ≤ B) :
    (B : ℝ) ^ (-(3 : ℝ)) ≤ channelMesh n / (q.totient : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hφ : (q.totient : ℝ) ≤ B := by exact_mod_cast (Nat.totient_le q).trans hqB
  have hprod : (n : ℝ) * q.totient ≤ (B : ℝ) ^ 3 := by
    calc
      _ ≤ (B : ℝ) ^ 2 * B := mul_le_mul hnB hφ hq0.le (by positivity)
      _ = _ := by ring
  rw [Real.rpow_neg hB0.le]
  rw [Real.rpow_ofNat]
  unfold channelMesh
  rw [div_div, ← one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ 3)
    (mul_pos hn0 hq0)).mpr
  nlinarith [pow_pos hB0 3]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedChannelMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact identification of signed split masses and the actual channel -/

namespace JointDickman
open Finset

theorem retainedPrimeProduct_subset (P : Finset ℕ) (S : P.powerset) :
    retainedPrimeProduct P (subsetHitEquiv P S) = ∏ p ∈ S.val, p := by
  rw [retainedPrimeProduct_selected]
  congr 1
  ext p
  by_cases hp : p ∈ P
  · simp [selectedPrimeSubset, subsetHitEquiv, hp]
  · have hs : p ∉ S.val := fun hs => hp (mem_powerset.mp S.property hs)
    simp [selectedPrimeSubset, hp, hs]

theorem fullPrimeMass_subset (P : Finset ℕ) (S : P.powerset) :
    fullPrimeMass P (subsetHitEquiv P S) =
      bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S.val :=
by
  simpa only [fullPrimeMass, bernoulliSiteMass] using
    bernoulliSubsetMass_eq_product P (fun p : ℕ => 1/(p : ℝ)) S

/-- Push the finite signed split measure forward to its integer product. -/
theorem signedSplitProductMass_sum (P : Finset ℕ) (g : Finset ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, signedSplitProductMass P g n * F n) =
      ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S * g S *
        ∑ A ∈ P.powerset, subsetRetentionMass S A * F (∏ p ∈ A, p) := by
  classical
  unfold signedSplitProductMass splitProductMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  rw [sum_eq_single (∏ p ∈ A, p)]
  · simp
    ring
  · intro n _ hn
    simp [Ne.symm hn]
  · intro hn
    exact False.elim (hn (mem_image.mpr ⟨A, hA, rfl⟩))

/-- The signed integer-product law is exactly the original fair-split expectation. -/
theorem signedSplitProductMass_expectation (P : Finset ℕ)
    (g : (P → Bool) → ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P,
      signedSplitProductMass P (subsetSiteTest P g) n * F n) =
      ∑ x : P → Bool, fullPrimeMass P x * g x *
        ∑ y : P → Bool, fairRetentionMass x y * F (retainedPrimeProduct P y) := by
  classical
  rw [signedSplitProductMass_sum]
  rw [← (subsetHitEquiv P).sum_comp]
  simp_rw [← (subsetHitEquiv P).sum_comp
    (fun y => fairRetentionMass _ y * F (retainedPrimeProduct P y))]
  simp_rw [fullPrimeMass_subset, fairRetentionMass_subsets, retainedPrimeProduct_subset]
  rw [← sum_coe_sort P.powerset]
  apply sum_congr rfl
  intro S _
  rw [sum_coe_sort P.powerset
    (fun A => subsetRetentionMass S.val A * F (∏ p ∈ A, p))]
  rfl

/-- A channel cell contains exactly the corresponding signed integer masses. -/
theorem signedSplitProductMass_channel {A : Type*} [Fintype A] [DecidableEq A]
    (P : Finset ℕ) (g : (P → Bool) → ℝ) (cell : ℕ → Option A)
    (μ : A → ℝ) (a : A) (hμ : μ a ≠ 0) :
    (∑ n ∈ primeSplitProductSupport P, if cell n = some a then
      signedSplitProductMass P (subsetSiteTest P g) n else 0) =
      μ a * finiteChannel (fullPrimeMass P) μ (partialFairPrimeTransition P cell) g a := by
  classical
  have h := signedSplitProductMass_expectation P g
    (fun n => if cell n = some a then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [h, finiteChannel, mul_div_cancel₀ _ hμ]
  apply sum_congr rfl
  intro x _
  unfold partialFairPrimeTransition optionCellMass
  ring

/-- The manuscript normalization is delta/phi, with no approximation. -/
theorem manuscriptChannel_cell_mass {m₁ B q : ℕ} [NeZero q]
    (hm : 0 < m₁) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ) :
    (∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      if logResidueCell B q (channelLower (channelFineCount m₁ B))
        (channelUpper (channelFineCount m₁ B)) n = some a then
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n
      else 0) =
      (channelMesh (channelFineCount m₁ B)/(q.totient : ℝ))*
        manuscriptChannel m₁ B q g a := by
  apply signedSplitProductMass_channel
  exact (div_pos (channelMesh_pos (channelFineCount_pos hm hB))
    (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))).ne'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EndpointResiduePartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue decomposition of the endpoint exponential sums -/

namespace JointDickman
open Finset

theorem residue_nat_phase {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (h*(n : ZMod q)) = additivePhase ((n : ℝ)*h.val/q) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val h,← Nat.cast_mul,stdAddChar_as_additivePhase]
  push_cast
  congr 1
  ring

/-- The residue phase is kept exactly when integers are assigned to cells.
Only the slowly varying archimedean factor is averaged later. -/
theorem endpoint_residue_partition {D : Type*} [Fintype D] [DecidableEq D]
    {B q : ℕ} [NeZero q] (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (s : Finset ℕ) (J : Finset D) (c : ℕ → ℂ) (h : ZMod q) (ν : ℝ)
    (hsupp : ∀ n ∈ s, c n ≠ 0 → ∃ i ∈ J, ∃ r : (ZMod q)ˣ,
      logResidueCell B q lower upper n = some (i,r)) :
    (∑ n ∈ s, c n*additivePhase ((n : ℝ)*(h.val/(q : ℝ)+ν))) =
      unitResidueFourier (fun r => ∑ i ∈ J, ∑ n ∈ s,
        if logResidueCell B q lower upper n = some (i,r)
        then c n*additivePhase ((n : ℝ)*ν) else 0) h := by
  classical
  unfold unitResidueFourier
  simp only [mul_sum]
  simp_rw [sum_comm (s := J) (t := s)]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  by_cases hc : c n = 0
  · simp [hc]
  obtain ⟨i,hi,r,hr⟩ := hsupp n hn hc
  have hmod := ((logResidueCell_eq_some B q lower upper hdisjoint n i r).mp hr).2
  have hone : (∑ t : (ZMod q)ˣ, ∑ j ∈ J,
      ZMod.stdAddChar (h*(t : ZMod q))*
        (if logResidueCell B q lower upper n = some (j,t)
        then c n*additivePhase ((n : ℝ)*ν) else 0)) =
        ZMod.stdAddChar (h*(r : ZMod q))*(c n*additivePhase ((n : ℝ)*ν)) := by
    simp only [hr,Option.some.injEq,Prod.mk.injEq]
    rw [sum_eq_single r]
    · rw [sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · exact fun hni => False.elim (hni hi)
    · intro t _ htr
      simp [Ne.symm htr]
    · simp
  rw [hone,← hmod,residue_nat_phase]
  rw [show (n : ℝ)*(h.val/(q : ℝ)+ν) = (n : ℝ)*h.val/q+(n : ℝ)*ν by ring,
    additivePhase_add]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteHistogramFourier
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local histogram Fourier bound in finite-cell form -/

namespace JointDickman
open Finset

/-- The local window length is card(J)*delta. It is retained explicitly,
so summing boxes can use bounded overlap rather than their number. -/
theorem finite_histogram_fourier_bound {ι : Type*} [DecidableEq ι]
    {q : ℕ} [NeZero q] (J : Finset ι) {δ M : ℝ}
    (_hδ : 0 ≤ δ) (_hM : 0 ≤ M) (U : ι → (ZMod q)ˣ → ℝ)
    (v : (ZMod q)ˣ → ℂ)
    (hv : ∀ r, ‖v r‖ ≤ δ*M*(∑ i ∈ J, U i r)) :
    (∑ h : ZMod q, ‖unitResidueFourier v h/(q.totient : ℂ)‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*δ)*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (δ/(q.totient : ℝ))*U i r^2) := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hper (r : (ZMod q)ˣ) : ‖v r‖^2 ≤
      δ^2*M^2*(J.card : ℝ)*(∑ i ∈ J, U i r^2) := by
    have hupper : 0 ≤ δ*M*(∑ i ∈ J, U i r) := (norm_nonneg _).trans (hv r)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hupper).mpr (hv r)
    have hc : (∑ i ∈ J, U i r)^2 ≤ (J.card : ℝ)*(∑ i ∈ J, U i r^2) := by
      simpa using sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) (fun i => U i r)
    calc
      ‖v r‖^2 ≤ (δ*M)^2*(∑ i ∈ J, U i r)^2 := by simpa only [mul_pow] using hsq
      _ ≤ (δ*M)^2*((J.card : ℝ)*(∑ i ∈ J, U i r^2)) :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
      _ = _ := by ring
  rw [normalizedUnitResidue_fourier_parseval]
  calc
    _ ≤ ((q : ℝ)/(q.totient : ℝ))*((1/(q.totient : ℝ))*
        ∑ r : (ZMod q)ˣ, δ^2*M^2*(J.card : ℝ)*(∑ i ∈ J, U i r^2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hper r)) (by positivity))
        (by positivity)
    _ = _ := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro r _
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SignedHistogramError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Histogram replacement for the actual signed fair-split measure -/

namespace JointDickman
open Finset MeasureTheory

/-- Replacing a test on one cell only costs its oscillation times the
positive half-prime mass of that cell. -/
theorem signedSplitProductMass_cell_error {A : Type*} [DecidableEq A]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : Finset ℕ → ℝ) (hg : ∀ S ⊆ P, |g S| ≤ 1)
    (cell : ℕ → Option A) (a : A) (F : ℕ → ℂ) (c : ℂ) (E : ℝ)
    (hosc : ∀ n ∈ primeSplitProductSupport P, cell n = some a → ‖F n-c‖ ≤ E) :
    ‖(∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*F n else 0) -
      ((∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        signedSplitProductMass P g n else 0) : ℝ)*c‖ ≤
      E * ∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        primeProductMass P (1/2) n else 0 := by
  classical
  have he : (∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*F n else 0) -
      ((∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        signedSplitProductMass P g n else 0) : ℝ)*c =
      ∑ n ∈ primeSplitProductSupport P, if cell n = some a then
        (signedSplitProductMass P g n : ℂ)*(F n-c) else 0 := by
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,
      sum_mul,← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    by_cases hn : cell n = some a
    · simp only [hn,ite_true, if_true]
      ring
    · simp only [hn,ite_false, if_false,zero_mul,sub_self]
  rw [he,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  by_cases hcell : cell n = some a
  · simp only [hcell,ite_true, if_true,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (signedSplitProductMass_abs_le hP hg n) (hosc n hn hcell)
      (norm_nonneg _) ((abs_nonneg _).trans (signedSplitProductMass_abs_le hP hg n))).trans_eq
        (mul_comm _ _)
  · simp [hcell]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EndpointHistogramIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact endpoint-to-histogram identity on the actual grid -/

namespace JointDickman
open Finset

theorem channelCells_cover {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Ioc (1/2 : ℝ) 3) :
    ∃ i : Fin n, x ∈ Set.Ioc (channelLower n i) (channelUpper n i) := by
  let f := fun i : ℕ => (1/2 : ℝ)+(i : ℝ)*channelMesh n
  have hend : f n = 3 := by
    dsimp [f,channelMesh]
    field_simp
    ring
  have hstart : f 0 = 1/2 := by simp [f]
  have hx' : x ∈ Set.Ioc (f 0) (f n) := by rwa [hstart,hend]
  obtain ⟨i,hi,hcell⟩ := Set.mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n f hx')
  refine ⟨⟨i,mem_range.mp hi⟩,?_⟩
  simpa only [f,channelLower,channelUpper,Nat.cast_add,Nat.cast_one] using hcell

theorem primeSplitProductSupport_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {k : ℕ} (hk : k ∈ primeSplitProductSupport P) : 0 < k := by
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hk
  exact prod_pos (fun p hp => (hP p (mem_powerset.mp hA hp)).pos)

theorem primeSplitProductSupport_coprime {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {q k : ℕ} (hq : q ≠ 0) (hcut : ∀ p ∈ P, q < p)
    (hk : k ∈ primeSplitProductSupport P) : k.Coprime q := by
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hk
  rw [Nat.coprime_prod_left_iff]
  intro p hp
  have hpP := mem_powerset.mp hA hp
  apply (hP p hpP).coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt (hcut p hpP)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdiv)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the manuscript grid into equal coarse cells -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem grouped_width (m k : ℕ) (a : Fin m × Fin k) :
    groupedUpper m k a - groupedLower m k a = channelMesh (m * k) := channel_width _ _

theorem groupedLower_ge (m k : ℕ) (a : Fin m × Fin k) :
    1 / 2 ≤ groupedLower m k a := channelLower_ge _ _

theorem groupedUpper_le {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (a : Fin m × Fin k) :
    groupedUpper m k a ≤ 3 := channelUpper_le (Nat.mul_pos hm hk) _

theorem groupedCells_disjoint {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a b : Fin m × Fin k) (s : ℝ)
    (ha : s ∈ Set.Ioc (groupedLower m k a) (groupedUpper m k a))
    (hb : s ∈ Set.Ioc (groupedLower m k b) (groupedUpper m k b)) : a = b :=
  finProdFinEquiv.injective (channelCells_disjoint (Nat.mul_pos hm hk) _ _ s ha hb)

theorem groupedLower_diameter {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m) (i j : Fin k) :
    |groupedLower m k (d, i) - groupedLower m k (d, j)| ≤ channelMesh m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi : (i.val : ℝ) ≤ k := by exact_mod_cast i.isLt.le
  have hj : (j.val : ℝ) ≤ k := by exact_mod_cast j.isLt.le
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have heq : groupedLower m k (d, i) - groupedLower m k (d, j) =
      ((i.val : ℝ) - j.val) * channelMesh (m * k) := by
    change (1 / 2 + ((i.val + k * d.val : ℕ) : ℝ) * channelMesh (m * k)) -
      (1 / 2 + ((j.val + k * d.val : ℕ) : ℝ) * channelMesh (m * k)) = _
    push_cast
    ring
  have hmul : (k : ℝ) * channelMesh (m * k) = channelMesh m := by
    unfold channelMesh
    rw [Nat.cast_mul]
    field_simp
  rw [heq, abs_mul, abs_of_pos (channelMesh_pos (Nat.mul_pos hm hk))]
  calc
    _ ≤ (k : ℝ) * channelMesh (m * k) := by
      apply mul_le_mul_of_nonneg_right _ (channelMesh_pos (Nat.mul_pos hm hk)).le
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = _ := hmul

theorem grouped_total_mass {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (∑ _a : Fin m × Fin k, channelMesh (m * k)) = 5 / 2 := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  unfold channelMesh
  field_simp

theorem channelFineCount_lower {m B : ℕ} (hm : 0 < m) :
    (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) ≤ channelFineCount m B := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left
    (Nat.le_ceil (((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m)) hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_div_cancel₀ _ hm0.ne'] using h

theorem channelMesh_fine_upper {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B) :
    channelMesh (channelFineCount m B) ≤ (5 / 2 : ℝ) / B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hr : (B : ℝ) ≤ (B : ℝ) ^ (11 / 10 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (B : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
  have hn : (B : ℝ) ≤ channelFineCount m B := by
    calc
      _ ≤ (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) := by nlinarith
      _ ≤ _ := channelFineCount_lower hm
  unfold channelMesh
  exact div_le_div_of_nonneg_left (by norm_num) hB0 hn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientLogBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Totient denominators on the major arcs -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem totient_eq_prime_product_real (q : ℕ) :
    (q.totient : ℝ) = q*∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  simpa only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_prod,Rat.cast_sub,
    Rat.cast_one,Rat.cast_inv,one_div] using h

/-- Only moduli up to the fixed B^15 major-arc cutoff are needed. -/
theorem totient_log_bound (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ q : ℕ,
      0 < q → q ≤ B^15 → (q : ℝ) ≤ K*Real.log B*q.totient := by
  let κ := Real.exp (-Real.eulerMascheroniConstant)/2
  have hκ : 0 < κ := half_pos (Real.exp_pos _)
  have hlim := hMP.comp ((tendsto_pow_atTop (by decide : (15 : ℕ) ≠ 0)).comp
    tendsto_natCast_atTop_atTop)
  have hsmall := hlim.eventually (eventually_ge_nhds (show κ < Real.exp (-Real.eulerMascheroniConstant) by
    dsimp [κ] <;> linarith [Real.exp_pos (-Real.eulerMascheroniConstant)]))
  refine ⟨15/κ,by positivity,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop 2] with B hproduct hB
  intro q hq hqB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hlog : 0 ≤ Real.log ((B : ℝ)^15) := Real.log_nonneg (one_le_pow₀ hB1)
  have hset : q.primeFactors ⊆ Nat.primesLE (B^15) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hqB,Nat.prime_of_mem_primeFactors hp⟩
  have hprod : (∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ))) ≤
      ∏ p ∈ q.primeFactors, (1-1/(p : ℝ)) := by
    apply prod_le_prod_of_subset_of_le_one hset
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hp1)
    · intro p _ _
      exact sub_le_self _ (by positivity)
  have hprod' : κ ≤ Real.log ((B : ℝ)^15)*
      ∏ p ∈ Nat.primesLE (B^15), (1-1/(p : ℝ)) := by
    simpa only [Function.comp_def,← Nat.cast_pow,Nat.floor_natCast,← primesLE_eq_filter] using hproduct
  have hh := hprod'.trans (mul_le_mul_of_nonneg_left hprod hlog)
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hh'' : (q : ℝ)*κ ≤ (15*Real.log B)*q.totient := by
    refine hh'.trans_eq ?_
    rw [totient_eq_prime_product_real,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  calc
    _ ≤ ((15*Real.log B)*q.totient)/κ := (le_div_iff₀ hκ).mpr hh''
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_KernelDenominatorSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient subpower bound for the kernel denominator sum

Mertens' product theorem and the harmonic sum bound suffice here. A
polylogarithmic bound is enough to absorb either of the manuscript's
positive power savings, so no additional mean-value theorem is assumed.
-/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem kernelDenominatorSum_log_bound
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ j Q : ℕ,
      0 < j → 0 < Q → j*Q ≤ B^15 →
      kernelDenominatorSum j Q ≤ K^2*(Real.log B)^2*(1+15*Real.log B) := by
  obtain ⟨K,hK,hbound⟩ := totient_log_bound hMP
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with B hboundB hB
  intro j Q hj hQ hscale
  have hlog : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hQscale : Q ≤ B^15 := (Nat.le_mul_of_pos_left Q hj).trans hscale
  have hterm (q : ℕ) (hq : q ∈ Icc 1 Q) :
      (1/(q.totient : ℝ))*((j*q : ℕ)/(Nat.totient (j*q) : ℝ)) ≤
        (K^2*(Real.log B)^2)*(1/(q : ℝ)) := by
    have hq0 : 0 < q := (mem_Icc.mp hq).1
    have hjq : 0 < j*q := Nat.mul_pos hj hq0
    have hqB : q ≤ B^15 := (mem_Icc.mp hq).2.trans hQscale
    have hjqB : j*q ≤ B^15 := (Nat.mul_le_mul_left j (mem_Icc.mp hq).2).trans hscale
    have hqφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr hq0)
    have hjqφ : (0 : ℝ) < (j*q).totient := by exact_mod_cast (Nat.totient_pos.mpr hjq)
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hq0
    have hfirst : 1/(q.totient : ℝ) ≤ K*Real.log B/q := by
      apply (div_le_div_iff₀ hqφ hqreal).mpr
      simpa only [one_mul] using hboundB q hq0 hqB
    have hsecond : ((j*q : ℕ) : ℝ)/(Nat.totient (j*q) : ℝ) ≤ K*Real.log B :=
      (div_le_iff₀ hjqφ).mpr (hboundB (j*q) hjq hjqB)
    exact (mul_le_mul hfirst hsecond (by positivity) (div_nonneg (mul_nonneg hK.le hlog) (Nat.cast_nonneg q))).trans_eq (by ring)
  have hsum : (∑ q ∈ Icc 1 Q, 1/(q : ℝ)) ≤ 1+Real.log Q := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div] using
      harmonic_le_one_add_log Q
  have hlogQ : Real.log (Q : ℝ) ≤ 15*Real.log B := by
    have hh := Real.log_le_log (by exact_mod_cast hQ : (0 : ℝ) < Q)
      (show (Q : ℝ) ≤ (B : ℝ)^15 by exact_mod_cast hQscale)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, (K^2*(Real.log B)^2)*(1/(q : ℝ)) := sum_le_sum hterm
    _ = (K^2*(Real.log B)^2)*(∑ q ∈ Icc 1 Q, 1/(q : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.trans (by linarith)) (by positivity)

theorem kernelDenominatorSum_subpower
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ j Q : ℕ, 0 < j → 0 < Q → j*Q ≤ B^15 →
      kernelDenominatorSum j Q ≤ (B : ℝ)^ε := by
  obtain ⟨K,hK,hbound⟩ := kernelDenominatorSum_log_bound hMP
  have hlim := (((log_power_div_power_tendsto_zero 2 hε).add
    ((log_power_div_power_tendsto_zero 3 hε).const_mul 15)).const_mul (K^2)).comp
      tendsto_natCast_atTop_atTop
  simp only [mul_zero,add_zero] at hlim
  filter_upwards [hbound,hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with B hboundB hsmall hB
  intro j Q hj hQ hscale
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  refine (hboundB j Q hj hQ hscale).trans ?_
  apply (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp
  convert hsmall using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_def,Real.rpow_ofNat]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramScaleDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the histogram and residue denominator losses -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem channelMesh_scale_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    (B : ℝ)*channelMesh (channelFineCount m B) ≤ (B : ℝ)^(-(1/10 : ℝ)) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn := channelFineCount_pos hm hB
  have hn0 : (0 : ℝ) < channelFineCount m B := by exact_mod_cast hn
  have hp := Real.rpow_pos_of_pos hB0 (11/10 : ℝ)
  have hmesh : channelMesh (channelFineCount m B) ≤ 1/(B : ℝ)^(11/10 : ℝ) := by
    unfold channelMesh
    apply (div_le_div_iff₀ hn0 hp).mpr
    simpa only [one_mul] using channelFineCount_lower (B := B) hm
  calc
    _ ≤ (B : ℝ)*(1/(B : ℝ)^(11/10 : ℝ)) := mul_le_mul_of_nonneg_left hmesh hB0.le
    _ = _ := by
      rw [mul_one_div]
      calc
        (B : ℝ)/(B : ℝ)^(11/10 : ℝ) = (B : ℝ)^(1 : ℝ)/(B : ℝ)^(11/10 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hB0]; norm_num

/-- After summing denominators, both actual small losses still tend to zero,
uniformly for eta*T <= j and the required polynomial modulus range. -/
theorem histogram_residue_denominator_decay
    (hMP : PublishedInputs.PrimeProductMertensInput) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ (j Q : ℕ) (T : ℝ), 0 < j → 0 < Q → 0 ≤ T → η*T ≤ j → j*Q ≤ B^15 →
      (T/j)*kernelDenominatorSum j Q*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) ≤ ε B := by
  let ε := fun B : ℕ => (1/η)*((B : ℝ)^(-(1/20 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)))
  refine ⟨ε, ?_, ?_⟩
  · have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/20)).comp tendsto_natCast_atTop_atTop
    have h₂ := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/400)).comp tendsto_natCast_atTop_atTop
    simpa only [ε,Function.comp_def,add_zero,mul_zero] using (h₁.add h₂).const_mul (1/η)
  · intro m hm
    filter_upwards [kernelDenominatorSum_subpower hMP (by norm_num : (0 : ℝ) < 1/400),
      eventually_ge_atTop 1] with B hden hB
    intro j Q T hj hQ hT hlag hscale
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hratio : T/(j : ℝ) ≤ 1/η := by
      apply (div_le_div_iff₀ hj0 hη).mpr
      nlinarith
    have hloss : (B : ℝ)^(1/400 : ℝ)*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) ≤
        (B : ℝ)^(-(1/20 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)) := by
      calc
        _ ≤ (B : ℝ)^(1/400 : ℝ)*
            ((B : ℝ)^(-(1/10 : ℝ))+(B : ℝ)^(-(1/200 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hB0.le _)
          exact add_le_add (channelMesh_scale_bound (B := B) hm (by omega)) (le_refl _)
        _ = (B : ℝ)^(-(39/400 : ℝ))+(B : ℝ)^(-(1/400 : ℝ)) := by
          rw [mul_add,← Real.rpow_add hB0,← Real.rpow_add hB0]
          norm_num
        _ ≤ _ := add_le_add (Real.rpow_le_rpow_of_exponent_le hB1
          (by norm_num : (-(39/400 : ℝ)) ≤ -(1/20))) (le_refl _)
    have hden0 : 0 ≤ kernelDenominatorSum j Q := by
      unfold kernelDenominatorSum
      positivity
    have hmesh0 : 0 ≤ (B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)) := by
      unfold channelMesh
      positivity
    calc
      _ ≤ (1/η)*(B : ℝ)^(1/400 : ℝ)*
          ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hratio (hden j Q hj hQ hscale) hden0 (by positivity)) hmesh0
      _ ≤ ε B := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hloss (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local collections of fine cells for an endpoint box -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem mem_histogramWindowCells {n : ℕ} {l u x : ℝ} {i : Fin n}
    (hx : x ∈ Set.Icc l u) (hi : x ∈ Set.Ioc (channelLower n i) (channelUpper n i)) :
    i ∈ histogramWindowCells n l u := by
  simp only [histogramWindowCells,mem_filter,mem_univ,true_and]
  exact ⟨hi.1.le.trans hx.2,hx.1.trans hi.2⟩

theorem histogramWindowCells_length {n : ℕ} (hn : 0 < n) {l u : ℝ} (hlu : l ≤ u) :
    ((histogramWindowCells n l u).card : ℝ)*channelMesh n ≤ u-l+2*channelMesh n := by
  classical
  let J := histogramWindowCells n l u
  have hδ := channelMesh_pos hn
  by_cases hJ : J.Nonempty
  · let a := J.min' hJ
    let b := J.max' hJ
    have ha : a ∈ J := min'_mem J hJ
    have hb : b ∈ J := max'_mem J hJ
    have hab : a ≤ b := min'_le J b hb
    have hcard : J.card ≤ b.val+1-a.val := by
      have hsubset : J.image Fin.val ⊆ Icc a.val b.val := by
        intro k hk
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
        exact mem_Icc.mpr ⟨min'_le J i hi,le_max' J i hi⟩
      have hc := card_le_card hsubset
      rwa [card_image_of_injective J Fin.val_injective,Nat.card_Icc] at hc
    have hcR : (J.card : ℝ) ≤ (b.val : ℝ)+1-a.val := by
      calc
        (J.card : ℝ) ≤ ((b.val+1-a.val : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = _ := by rw [Nat.cast_sub (show a.val ≤ b.val+1 by omega),Nat.cast_add,Nat.cast_one]
    have ha' : l ≤ channelUpper n a := (mem_filter.mp ha).2.2
    have hb' : channelLower n b ≤ u := (mem_filter.mp hb).2.1
    have hlen := mul_le_mul_of_nonneg_right hcR hδ.le
    dsimp [channelLower,channelUpper] at ha' hb'
    dsimp [J] at hlen
    nlinarith
  · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hJ
    change (J.card : ℝ)*channelMesh n ≤ _
    rw [he,card_empty,Nat.cast_zero,zero_mul]
    linarith

/-- Every retained integer in a fixed endpoint support lies in the interior
of the manuscript's logarithmic interval for sufficiently large B. -/
theorem endpoint_support_log_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ᶠ B : ℕ in atTop, ∀ N : ℝ, 0 < N →
      Real.log N ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) →
      ∀ k : ℕ, a < (k : ℝ)/N → (k : ℝ)/N ≤ b →
        Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3 := by
  have hb : 0 < b := ha.trans_le hab
  have hlo : ∀ᶠ B : ℕ in atTop, -Real.log a < (3/10 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 3/10)).eventually_gt_atTop _
  have hhi : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (1/2 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually_ge_atTop _
  filter_upwards [hlo,hhi,eventually_gt_atTop 0] with B hloB hhiB hB
  intro N hN hlog k hklo hkhi
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hk0 : (0 : ℝ) < k := (mul_pos ha hN).trans ((lt_div_iff₀ hN).mp hklo)
  have hloK := Real.log_lt_log (mul_pos ha hN) ((lt_div_iff₀ hN).mp hklo)
  have hhiK := Real.log_le_log hk0 ((div_le_iff₀ hN).mp hkhi)
  rw [Real.log_mul ha.ne' hN.ne'] at hloK
  rw [Real.log_mul hb.ne' hN.ne'] at hhiK
  exact ⟨(lt_div_iff₀ hB0).mpr (by nlinarith [hlog.1]),
    (div_le_iff₀ hB0).mpr (by nlinarith [hlog.2])⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointWindowIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact localization of the endpoint Fourier sum to its log window -/

namespace JointDickman
open Finset

theorem endpoint_histogram_window_identity {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {N l u : ℝ} (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ) (h : ZMod q) (ν : ℝ)
    (hsupp : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3 ∩ Set.Icc l u) :
    (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B),
      (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) k*w (k/N) : ℝ)*
        additivePhase ((k : ℝ)*(h.val/(q : ℝ)+ν))) =
      unitResidueFourier (fun r => ∑ i ∈ histogramWindowCells (channelFineCount m B) l u,
        manuscriptCellSum m B q g (logOscillatoryTest w B N (ν*N)) i r) h := by
  classical
  let n := channelFineCount m B
  let P := auxiliaryPrimes B
  let γ := signedSplitProductMass P (subsetSiteTest P g)
  have hn := channelFineCount_pos hm hB
  have hsupport (k : ℕ) (hk : k ∈ primeSplitProductSupport P)
      (hc : (γ k*w (k/N) : ℝ) ≠ (0 : ℂ)) :
      ∃ i ∈ histogramWindowCells n l u, ∃ r : (ZMod q)ˣ,
        logResidueCell B q (channelLower n) (channelUpper n) k = some (i,r) := by
    have hw : w (k/N) ≠ 0 := by intro hw; simp [hw] at hc
    obtain ⟨i,hi⟩ := channelCells_cover hn (hsupp k hk hw).1
    have hcop := primeSplitProductSupport_coprime (auxiliaryPrimes_prime B) (NeZero.ne q)
      (fun p hp => hcut.trans_lt (by exact_mod_cast (mem_filter.mp hp).2)) hk
    refine ⟨i,mem_histogramWindowCells (hsupp k hk hw).2 hi,ZMod.unitOfCoprime k hcop,?_⟩
    exact (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
      (channelCells_disjoint hn) k i _).mpr ⟨hi,rfl⟩
  have he := endpoint_residue_partition (B := B) (channelLower n) (channelUpper n)
    (channelCells_disjoint hn) (primeSplitProductSupport P) (histogramWindowCells n l u)
    (fun k => ((γ k*w (k/N) : ℝ) : ℂ)) h ν hsupport
  rw [he]
  congr 1
  funext r
  apply sum_congr rfl
  intro i _
  unfold manuscriptCellSum
  apply sum_congr rfl
  intro k hk
  dsimp only [n,P,γ]
  by_cases hc : logResidueCell B q (channelLower (channelFineCount m B))
    (channelUpper (channelFineCount m B)) k = some (i,r)
  · simp only [hc,ite_true, if_true]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast primeSplitProductSupport_pos (auxiliaryPrimes_prime B) hk
    have hlog := logOscillatoryTest_majorArc w (B := (B : ℝ)) (N := N)
      (j := 1) (X := 1) (k := (k : ℝ)) (ξ := ν) (by exact_mod_cast hB.ne') hN.ne' hk0
    simp only [mul_one,div_one] at hlog
    rw [hlog,Complex.ofReal_mul]
    ring_nf
  · simp only [hc,ite_false, if_false]


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramAmplitudeBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive cell domination for both endpoint Fourier amplitudes -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptCellSum_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (F : ℝ → ℂ) (M : ℝ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ)
    (hF : ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    ‖manuscriptCellSum m B q g F i r‖ ≤
      M*(channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r) := by
  let n := channelFineCount m B
  let cell := logResidueCell B q (channelLower n) (channelUpper n)
  have hh := signedSplitProductMass_cell_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (subsetSiteTest (auxiliaryPrimes B) g) (fun _ _ => hg _) cell (i,r)
    (fun k => F (Real.log k/B)) 0 M (by
      intro k _ hk
      have hx := (logResidueCell_eq_some B q (channelLower n) (channelUpper n)
        (channelCells_disjoint (channelFineCount_pos hm hB)) k i r).mp hk
      simpa only [sub_zero] using hF _ (Set.Ioc_subset_Icc_self hx.1))
  have hone := manuscriptChannel_cell_mass hm hB (fun _ => 1) (i,r)
  change (∑ k ∈ primeSplitProductSupport (auxiliaryPrimes B), if cell k = some (i,r) then
    signedSplitProductMass (auxiliaryPrimes B) (fun _ => 1) k else 0) = _ at hone
  simp only [signedSplitProductMass_one] at hone
  rw [hone] at hh
  simpa only [mul_zero,sub_zero,manuscriptCellSum,n,cell,mul_assoc] using hh

theorem manuscriptCellApprox_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (F : ℝ → ℂ) (M : ℝ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ)
    (hF : ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
        (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    ‖manuscriptCellApprox m B q g F i r‖ ≤
      M*(channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r) := by
  let A := complexCellAverage (channelLower (channelFineCount m B) i)
    (channelUpper (channelFineCount m B) i) F
  have hwidth := channel_width (channelFineCount m B) i
  have hi : channelLower (channelFineCount m B) i < channelUpper (channelFineCount m B) i := by
    linarith [channelMesh_pos (channelFineCount_pos hm hB)]
  have hA : ‖A‖ ≤ M := complexCellAverage_norm_le hi hF
  have he : manuscriptCellSum m B q g (fun _ => A) i r = manuscriptCellApprox m B q g F i r := by
    unfold manuscriptCellSum manuscriptCellApprox
    rw [← manuscriptChannel_cell_mass hm hB g (i,r)]
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero,sum_mul]
    apply sum_congr rfl
    intro k _
    split_ifs <;> simp [A]
  rw [← he]
  exact manuscriptCellSum_norm_le hm hB g hg (fun _ => A) M i r (fun _ _ => hA)

theorem cellAmplitude_fourier_bound {ι : Type*} [DecidableEq ι] {q : ℕ} [NeZero q]
    (J : Finset ι) {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (U : ι → (ZMod q)ˣ → ℝ) (A : ι → (ZMod q)ˣ → ℂ)
    (hA : ∀ i ∈ J, ∀ r, ‖A i r‖ ≤ M*(δ/(q.totient : ℝ))*U i r) :
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, A i r) h‖^2) ≤
      ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*δ)*M^2*
        (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (δ/(q.totient : ℝ))*U i r^2) := by
  let v := fun r => (q.totient : ℂ)*(∑ i ∈ J, A i r)
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hv (r : (ZMod q)ˣ) : ‖v r‖ ≤ δ*M*(∑ i ∈ J, U i r) := by
    calc
      _ = (q.totient : ℝ)*‖∑ i ∈ J, A i r‖ := by simp only [v,norm_mul,Complex.norm_natCast]
      _ ≤ (q.totient : ℝ)*(∑ i ∈ J, ‖A i r‖) :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hφ.le
      _ ≤ (q.totient : ℝ)*(∑ i ∈ J, M*(δ/(q.totient : ℝ))*U i r) :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i hi => hA i hi r)) hφ.le
      _ = _ := by rw [← mul_sum]; field_simp
  have hh := finite_histogram_fourier_bound J hδ hM U v hv
  have hid (h : ZMod q) : unitResidueFourier v h/(q.totient : ℂ) =
      unitResidueFourier (fun r => ∑ i ∈ J, A i r) h := by
    unfold unitResidueFourier
    rw [sum_div]
    apply sum_congr rfl
    intro r _
    dsimp [v]
    have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    field_simp
  simpa only [hid] using hh

theorem manuscript_amplitude_fourier_bounds {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) :
    let bound := ((q : ℝ)/(q.totient : ℝ))*((J.card : ℝ)*channelMesh (channelFineCount m B))*M^2*
      (∑ i ∈ J, ∑ r : (ZMod q)ˣ, (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
        manuscriptChannel m B q (fun _ => 1) (i,r)^2)
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellSum m B q g F i r) h‖^2) ≤ bound ∧
    (∑ h : ZMod q, ‖unitResidueFourier (fun r => ∑ i ∈ J, manuscriptCellApprox m B q g F i r) h‖^2) ≤ bound := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  exact ⟨cellAmplitude_fourier_bound J hδ hM _ _
    (fun i hi r => manuscriptCellSum_norm_le hm hB g hg F M i r (hF i hi)),
    cellAmplitude_fourier_bound J hδ hM _ _
    (fun i hi r => manuscriptCellApprox_norm_le hm hB g hg F M i r (hF i hi))⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramProductError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product error for the actual two endpoint histograms -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptAmplitudeEnergy_nonneg {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B))) :
    0 ≤ manuscriptAmplitudeEnergy m B q J := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  unfold manuscriptAmplitudeEnergy
  positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointSupportSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing between the finite integer window and the full split support -/

namespace JointDickman
open Finset

theorem signedSplitProductMass_eq_zero_of_not_mem (P : Finset ℕ) (g : Finset ℕ → ℝ)
    {n : ℕ} (hn : n ∉ primeSplitProductSupport P) : signedSplitProductMass P g n = 0 := by
  classical
  have hp : ∀ A ∈ P.powerset, (∏ p ∈ A, p) ≠ n := by
    intro A hA hprod
    exact hn (mem_image.mpr ⟨A,hA,hprod⟩)
  have hz (S : Finset ℕ) : splitProductMass P S n = 0 := by
    unfold splitProductMass
    apply sum_eq_zero
    intro A hA
    simp only [hp A hA,ite_false, if_false,mul_zero]
  simp only [signedSplitProductMass,hz,mul_zero,sum_const_zero]

theorem endpointFourierSum_eq_support {B : ℕ} {a b N : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0) (θ : ℝ) :
    endpointFourierSum B a b N g w θ =
      ∑ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
        (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/N) : ℝ)*additivePhase ((n : ℝ)*θ) := by
  classical
  let S := Ioc ⌊a*N⌋₊ ⌊b*N⌋₊
  let P := primeSplitProductSupport (auxiliaryPrimes B)
  let f := fun n : ℕ => (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/N) : ℝ)*
    additivePhase ((n : ℝ)*θ)
  have hzero (n : ℕ) (hn : n ∉ S) : w (n/N) = 0 := by
    apply hsupp
    by_contra! hc
    apply hn
    have hb := ha.trans_le hab
    exact mem_Ioc.mpr ⟨(Nat.floor_lt (mul_pos ha hN).le).mpr ((lt_div_iff₀ hN).mp hc.1),
      (Nat.le_floor_iff (mul_pos hb hN).le).mpr ((div_le_iff₀ hN).mp hc.2)⟩
  change (∑ n ∈ S, f n) = ∑ n ∈ P, f n
  calc
    _ = ∑ n ∈ S ∩ P, f n := by
      symm
      apply sum_subset inter_subset_left
      intro n hn hnot
      have hnP : n ∉ P := fun hnP => hnot (mem_inter.mpr ⟨hn,hnP⟩)
      simp [f,signedSplitProductMass_eq_zero_of_not_mem _ _ hnP]
    _ = ∑ n ∈ P, f n := by
      apply sum_subset inter_subset_right
      intro n hn hnot
      have hnS : n ∉ S := fun hnS => hnot (mem_inter.mpr ⟨hnS,hn⟩)
      simp [f,hzero n hnS]

theorem endpointFourierSum_histogram {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0)
    (hlog : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (h : ZMod q) (ν : ℝ) :
    endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w (h.val/(q : ℝ)+ν) =
      manuscriptFourier m B q
        (histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B))
        g (logOscillatoryTest w B N (ν*N)) h := by
  rw [endpointFourierSum_eq_support ha hab hN _ w hsupp]
  apply endpoint_histogram_window_identity hm hB hcut hN
  intro k hk hw
  refine ⟨hlog k hk hw,?_⟩
  have hb := ha.trans_le hab
  have hx : a < (k : ℝ)/N ∧ (k : ℝ)/N ≤ b := by
    constructor
    · by_contra he
      exact hw (hsupp _ (Or.inl (le_of_not_gt he)))
    · by_contra he
      exact hw (hsupp _ (Or.inr (lt_of_not_ge he)))
  have hk0 : (0 : ℝ) < k := (mul_pos ha hN).trans ((lt_div_iff₀ hN).mp hx.1)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  exact ⟨div_le_div_of_nonneg_right
    (Real.log_le_log (mul_pos ha hN) ((lt_div_iff₀ hN).mp hx.1).le) hB0.le,
    div_le_div_of_nonneg_right
      (Real.log_le_log hk0 ((div_le_iff₀ hN).mp hx.2)) hB0.le⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramConjugation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative endpoint has the opposite residue and continuous frequency -/

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem logOscillatoryTest_conj (w : ℝ → ℝ) (B N ω x : ℝ) :
    conj (logOscillatoryTest w B N ω x) = logOscillatoryTest w B N (-ω) x := by
  unfold logOscillatoryTest oscillatoryTest
  rw [map_mul,Complex.conj_ofReal,additivePhase_conj]
  congr 2
  ring

theorem manuscriptCellSum_conj (m B q : ℕ) [NeZero q]
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) :
    conj (manuscriptCellSum m B q g F i r) =
      manuscriptCellSum m B q g (fun x => conj (F x)) i r := by
  classical
  unfold manuscriptCellSum
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  split_ifs <;> simp only [map_mul,Complex.conj_ofReal,map_zero]

theorem manuscriptFourier_conj (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℂ) (h : ZMod q) :
    conj (manuscriptFourier m B q J g F h) =
      manuscriptFourier m B q J g (fun x => conj (F x)) (-h) := by
  unfold manuscriptFourier unitResidueFourier
  rw [map_sum]
  apply sum_congr rfl
  intro r _
  rw [map_mul,stdAddChar_conj,map_sum]
  simp only [neg_mul,manuscriptCellSum_conj]

theorem endpointFourierSum_histogram_neg {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ a ∨ b < x → w x = 0)
    (hlog : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (h : ZMod q) (ν : ℝ) :
    endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w (-(h.val/(q : ℝ)+ν)) =
      manuscriptFourier m B q
        (histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B))
        g (logOscillatoryTest w B N (-(ν*N))) (-h) := by
  change finiteAdditiveSum _ _ (-(h.val/(q : ℝ)+ν)) = _
  rw [finiteAdditiveSum_neg_real]
  change conj (endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w _) = _
  rw [endpointFourierSum_histogram hm hB hcut ha hab hN g w hsupp hlog h ν,
    manuscriptFourier_conj]
  simp_rw [logOscillatoryTest_conj]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramWindowOverlap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded overlap of logarithmic windows along a geometric scale -/

namespace JointDickman
open Finset

/-- The integer lattice has at most length+1 points in any real interval. -/
theorem integer_interval_card_le (S : Finset ℤ) {a b : ℝ} (hab : a ≤ b)
    (hS : ∀ m ∈ S, a ≤ (m : ℝ) ∧ (m : ℝ) ≤ b) :
    (S.card : ℝ) ≤ b-a+1 := by
  classical
  by_cases hne : S.Nonempty
  · let lo := S.min' hne
    let hi := S.max' hne
    have hlo : lo ∈ S := min'_mem S hne
    have hhi : hi ∈ S := max'_mem S hne
    have hord : lo ≤ hi := min'_le S hi hhi
    have hc : S.card ≤ (hi-lo+1).toNat := by
      have hs : S ⊆ Icc lo hi := fun m hm => mem_Icc.mpr ⟨min'_le S m hm,le_max' S m hm⟩
      have he : hi+1-lo = hi-lo+1 := by ring
      simpa only [Int.card_Icc,he] using card_le_card hs
    have hz : 0 ≤ hi-lo+1 := by omega
    have hcast : (S.card : ℝ) ≤ (hi : ℝ)-(lo : ℝ)+1 := by
      have hh : (S.card : ℤ) ≤ hi-lo+1 := by
        have hh := Int.ofNat_le.mpr hc
        simpa only [Int.toNat_of_nonneg hz] using hh
      exact_mod_cast hh
    exact hcast.trans (by linarith [(hS lo hlo).1,(hS hi hhi).2])
  · have he := not_nonempty_iff_eq_empty.mp hne
    simp only [he,card_empty,Nat.cast_zero]
    linarith

/-- For X=exp(m*t), the local cell windows have bounded overlap. The
constant depends only on their fixed width, with B*mesh displayed. -/
theorem histogramWindow_overlap {B t L U : ℝ} (hB : 0 < B) (ht : 0 < t)
    (hLU : L ≤ U) {n : ℕ} (hn : 0 < n) (S : Finset ℤ) (i : Fin n) :
    ((S.filter (fun (m : ℤ) => i ∈ histogramWindowCells n
      (((m : ℝ)*t+L)/B) (((m : ℝ)*t+U)/B))).card : ℝ) ≤
        (B*channelMesh n+U-L)/t+1 := by
  classical
  let a := (B*channelLower n i-U)/t
  let b := (B*channelUpper n i-L)/t
  have hab : a ≤ b := by
    apply (div_le_div_iff_of_pos_right ht).mpr
    have hwidth := channel_width n i
    nlinarith [channelMesh_pos hn]
  have hbnd := integer_interval_card_le
    (S.filter (fun (m : ℤ) => i ∈ histogramWindowCells n (((m : ℝ)*t+L)/B) (((m : ℝ)*t+U)/B))) hab
    (by
      intro m hm
      have hh := (mem_filter.mp (mem_filter.mp hm).2).2
      have hu := (le_div_iff₀ hB).mp hh.1
      have hl := (div_le_iff₀ hB).mp hh.2
      constructor
      · apply (div_le_iff₀ ht).mpr
        nlinarith
      · apply (le_div_iff₀ ht).mpr
        nlinarith)
  refine hbnd.trans_eq ?_
  dsimp [a,b]
  have hw := channel_width n i
  field_simp
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MajorArcFiniteSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite major-arc identity for the actual Fourier integrand -/

namespace JointDickman
open Filter MeasureTheory Set Function Finset
open scoped Topology

theorem mem_positiveDenominators (N : ℕ) (q : ℕ+) :
    q ∈ positiveDenominators N ↔ (q : ℕ) ≤ N := by
  exact (Finset.mem_subtype (p := fun n : ℕ => 0 < n) (s := range (N+1)) (a := q)).trans
    (by simp only [Finset.mem_range,Nat.lt_succ_iff]; rfl)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SchwartzFourierProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier inversion and polynomial moments for the fixed smooth profile -/

namespace JointDickman
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem testFourierTransform_eq_fourier (w : ℝ → ℝ) :
    testFourierTransform w = 𝓕 (fun s => (w s : ℂ)) := by
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    dsimp [additivePhase]
    have he : ((2*Real.pi*(-ξ*s) : ℝ) : ℂ)*Complex.I =
        ((-2*Real.pi*s*ξ : ℝ) : ℂ)*Complex.I := by push_cast <;> ring
    rw [he]
    ring)

theorem schwartz_testFourier_integrable (w : 𝓢(ℝ, ℝ)) :
    Integrable (testFourierTransform w) := by
  let f : 𝓢(ℝ, ℂ) := w.postcompCLM Complex.ofRealCLM
  have he : testFourierTransform w = (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
    rw [testFourierTransform_eq_fourier,SchwartzMap.fourier_coe]
    rfl
  rw [he]
  exact (𝓕 f : 𝓢(ℝ, ℂ)).integrable

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueFourierProjection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite residue-average projection is an L2 contraction -/

namespace JointDickman
open Finset

theorem complexResidueMean_square_le {q : ℕ} [NeZero q] (v : (ZMod q)ˣ → ℂ) :
    (q.totient : ℝ)*‖complexResidueMean v‖^2 ≤ ∑ r, ‖v r‖^2 := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hn := norm_sum_le univ v
  have hsq : ‖∑ r, v r‖^2 ≤ (∑ r, ‖v r‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (sum_nonneg (fun r _ => norm_nonneg _))).mpr hn
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun _ : (ZMod q)ˣ => (1 : ℝ)) (fun r => ‖v r‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient] at hcs
  have hh := hsq.trans hcs
  rw [complexResidueMean,norm_div,Complex.norm_natCast,div_pow]
  have he : (q.totient : ℝ)*(‖∑ r, v r‖^2/(q.totient : ℝ)^2) =
      ‖∑ r, v r‖^2/(q.totient : ℝ) := by field_simp
  rw [he]
  exact (div_le_iff₀ hφ).mpr (by simpa only [mul_comm] using hh)

theorem unitResidueFourier_projection_contract {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) :
    (∑ h : ZMod q, ‖unitResidueFourier (fun _ => complexResidueMean v) h‖^2) ≤
      ∑ h : ZMod q, ‖unitResidueFourier v h‖^2 := by
  rw [unitResidue_fourier_parseval,unitResidue_fourier_parseval]
  simp only [sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient]
  exact mul_le_mul_of_nonneg_left (complexResidueMean_square_le v) (Nat.cast_nonneg q)

theorem unitResidueFourier_projected {q : ℕ} [NeZero q]
    (v : (ZMod q)ˣ → ℂ) (h : ZMod q) :
    unitResidueFourier (fun _ => complexResidueMean v) h =
      (ramanujanSum q h/(q.totient : ℂ))*(∑ r, v r) := by
  unfold unitResidueFourier complexResidueMean ramanujanSum
  rw [← sum_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramCellCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing histogram cell averages by a chosen cell value -/

namespace JointDickman
open Finset MeasureTheory

theorem manuscriptChannel_cell_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (i : Fin (channelFineCount m B)) (r : (ZMod q)ˣ) :
    ‖((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ)‖ ≤
      (channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q (fun _ => 1) (i,r) := by
  have hh := manuscriptCellSum_norm_le hm hB g hg (fun _ => 1) 1 i r (by simp)
  have he : manuscriptCellSum m B q g (fun _ => 1) i r =
      (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*manuscriptChannel m B q g (i,r) : ℝ) : ℂ) := by
    unfold manuscriptCellSum
    simp only [mul_one]
    rw [← manuscriptChannel_cell_mass hm hB g (i,r)]
    simp only [Complex.ofReal_sum,apply_ite,Complex.ofReal_zero]
  rw [he,Complex.norm_real] at hh
  simpa only [one_mul] using hh

theorem cellCoefficientFourier_square_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖cellCoefficientFourier m B q J g F h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*M^2 := by
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  have hh := cellAmplitude_fourier_bound J hδ hM
    (fun i r => manuscriptChannel m B q (fun _ => 1) (i,r))
    (fun i r => (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i) (by
      intro i hi r
      have hw := manuscriptChannel_cell_norm_le hm hB g hg i r
      rw [norm_mul,Complex.norm_real]
      exact (mul_le_mul hw (hF i hi) (norm_nonneg _)
        ((norm_nonneg _).trans hw)).trans_eq (by ring))
  exact hh.trans_eq (by unfold manuscriptAmplitudeEnergy; ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SampledHistogram
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residue projection of the sampled endpoint histogram -/

namespace JointDickman
open Finset MeasureTheory

theorem sampledProjectedValue_eq_sum (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) :
    sampledProjectedValue m B q J g F =
      ∑ r : (ZMod q)ˣ, ∑ i ∈ J,
        (((channelMesh (channelFineCount m B)/(q.totient : ℝ))*
          manuscriptChannel m B q g (i,r) : ℝ) : ℂ)*F i := by
  unfold sampledProjectedValue finiteResidueAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [ZMod.card_units_eq_totient,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_natCast,Complex.ofReal_mul]
  rw [← sum_mul,← mul_sum]
  ring

theorem sampledProjectedFourier_eq (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ)
    (F : Fin (channelFineCount m B) → ℂ) (h : ZMod q) :
    sampledProjectedFourier m B q J g F h =
      (ramanujanSum q h/(q.totient : ℂ))*sampledProjectedValue m B q J g F := by
  rw [sampledProjectedFourier,unitResidueFourier_projected,sampledProjectedValue_eq_sum]

theorem sampledProjectedFourier_square_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) :
    (∑ h : ZMod q, ‖sampledProjectedFourier m B q J g F h‖^2) ≤
      manuscriptAmplitudeEnergy m B q J*M^2 :=
  (unitResidueFourier_projection_contract _).trans
    (cellCoefficientFourier_square_le hm hB J g hg F hM hF)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An averaged sharp cutoff for the coarse channel -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

theorem averagingRamp_bounds {a b : ℝ} (hab : a < b) (x : ℝ) :
    0 ≤ averagingRamp a b x ∧ averagingRamp a b x ≤ 1 := by
  have hlo : a ≤ min b (max a x) := le_min hab.le (le_max_left _ _)
  have hhi : min b (max a x) ≤ b := min_le_left _ _
  unfold averagingRamp
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (sub_pos.mpr hab).le
  · apply (div_le_one (sub_pos.mpr hab)).mpr
    linarith

theorem averagingRamp_one {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    averagingRamp a b x = 1 := by
  rw [averagingRamp, min_eq_left (hx.trans (le_max_right _ _))]
  exact div_self (sub_pos.mpr hab).ne'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CellAverageProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lipschitz control of normalized cell integrals -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

theorem cellAverage_profile_error {f : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L f)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    |(∫ x in a..b, f (x - t)) / (b - a) - f (a - t)| ≤ L * (b - a) := by
  have hint : IntervalIntegrable (fun x => f (x - t)) volume a b :=
    (hLip.continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have heq : (∫ x in a..b, f (x - t)) / (b - a) - f (a - t) =
      (∫ x in a..b, f (x - t) - f (a - t)) / (b - a) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [(sub_pos.mpr hab).ne']
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f (x - t) - f (a - t))
    (C := (L : ℝ) * (b - a)) (fun x hx => by
      rw [Set.uIoc_of_le hab.le] at hx
      rcases hx with ⟨hxa, hxb⟩
      have hh := hLip.dist_le_mul (x - t) (a - t)
      rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right, abs_of_nonneg (by linarith : 0 ≤ x - a)] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : x - a ≤ b - a) L.coe_nonneg))
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] using h

/-- Normalize the probability error by the actual cell mass, then add
only the Lipschitz oscillation across that cell. -/
theorem normalizedCell_profile_error {f : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L f)
    {a b P φ ε : ℝ} (hab : a < b) (hφ : 0 < φ) (t : ℝ)
    (hlocal : |P - (∫ x in a..b, f (x - t)) / φ| ≤ ε) :
    |P / ((b - a) / φ) - f (a - t)| ≤ ε / ((b - a) / φ) + L * (b - a) := by
  have hm : 0 < (b - a) / φ := div_pos (sub_pos.mpr hab) hφ
  have heq : P / ((b - a) / φ) - f (a - t) =
      (P - (∫ x in a..b, f (x - t)) / φ) / ((b - a) / φ) +
      ((∫ x in a..b, f (x - t)) / (b - a) - f (a - t)) := by
    field_simp [hφ.ne', (sub_pos.mpr hab).ne']
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right hlocal hm.le
  · exact cellAverage_profile_error hLip hab t

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PublishedRampProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smoothed prime channel profile from published inputs -/

namespace JointDickman

open Filter MeasureTheory
open scoped Topology NNReal

/-- The integral profile can be evaluated at a cell endpoint after
normalization, with explicit local-law and mesh errors. -/
theorem primeRampCell_normalized_error {D : Type*} [DecidableEq D]
    {v : ℕ → ℝ} {H B q : ℕ} {lower upper : D → ℝ} {lo hi : ℝ} {L : ℝ≥0} {ε : ℝ}
    (hφ : 0 < (q.totient : ℝ))
    (hLip : LipschitzWith L (rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi))
    (c : auxiliaryPrimes B → Bool) (d : D) (r : (ZMod q)ˣ)
    (horder : lower d < upper d)
    (hlocal : |primeRampCell B q lower upper lo hi c (d, r) -
      (∫ x in lower d..upper d,
        rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
          (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)) / q.totient| ≤ ε) :
    |primeRampCell B q lower upper lo hi c (d, r) / ((upper d - lower d) / q.totient) -
      rampDensity (scaledRoughDensity v (1 / 4) H B) lo hi
        (lower d - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)| ≤
      ε / ((upper d - lower d) / q.totient) + L * (upper d - lower d) :=
  normalizedCell_profile_error hLip horder hφ _ hlocal

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CoarseChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse centering of a smooth mixture kernel

A bounded Lipschitz profile changes little inside each coarse cell. Its
common-variable mixture is consequently close to a kernel depending only
on the coarse indices. Combining this fact with a discarded row bound
gives the finite coarse-channel estimate.
-/

namespace JointDickman

open scoped BigOperators NNReal

/-- Oscillation of the genuine mixture follows from the Lipschitz
profiles, rather than from an assumed kernel oscillation estimate. -/
theorem smoothMixtureKernel_oscillation {C A : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : A → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {M mesh : ℝ} {L₀ : ℝ≥0} (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (a a' b b' : A) (ha : |location a - location a'| ≤ mesh)
    (hb : |location b - location b'| ≤ mesh) :
    |smoothMixtureKernel w f location a b - smoothMixtureKernel w f location a' b'| ≤
      2 * M * (L₀ : ℝ) * mesh := by
  have hLM : 0 ≤ (L₀ : ℝ) * mesh := mul_nonneg L₀.coe_nonneg hmesh
  have hpoint (c : C) :
      |f c (location a) * f c (location b) - f c (location a') * f c (location b')| ≤
        2 * M * (L₀ : ℝ) * mesh := by
    have ha' : |f c (location a) - f c (location a')| ≤ (L₀ : ℝ) * mesh := by
      have h := (hLip c).dist_le_mul (location a) (location a')
      rw [Real.dist_eq, Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left ha L₀.coe_nonneg)
    have hb' : |f c (location b) - f c (location b')| ≤ (L₀ : ℝ) * mesh := by
      have h := (hLip c).dist_le_mul (location b) (location b')
      rw [Real.dist_eq, Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left hb L₀.coe_nonneg)
    calc
      _ = |(f c (location a) - f c (location a')) * f c (location b) +
          f c (location a') * (f c (location b) - f c (location b'))| := by congr 1; ring
      _ ≤ |(f c (location a) - f c (location a')) * f c (location b)| +
          |f c (location a') * (f c (location b) - f c (location b'))| := abs_add_le _ _
      _ = |f c (location a) - f c (location a')| * |f c (location b)| +
          |f c (location a')| * |f c (location b) - f c (location b')| := by
        rw [abs_mul, abs_mul]
      _ ≤ ((L₀ : ℝ) * mesh) * M + M * ((L₀ : ℝ) * mesh) := add_le_add
        (mul_le_mul ha' (hf c _) (abs_nonneg _) hLM)
        (mul_le_mul (hf c _) hb' (abs_nonneg _) hM)
      _ = _ := by ring
  calc
    _ = |∑ c, w c *
        (f c (location a) * f c (location b) - f c (location a') * f c (location b'))| := by
      unfold smoothMixtureKernel
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c, |w c *
        (f c (location a) * f c (location b) - f c (location a') * f c (location b'))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, w c *
        |f c (location a) * f c (location b) - f c (location a') * f c (location b')| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ c, w c * (2 * M * (L₀ : ℝ) * mesh) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hpoint c) (hw c)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A chosen representative in each coarse fibre gives a genuinely
coarse-only kernel, with the derived oscillation error. -/
theorem smoothMixtureKernel_coarse_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : D × R → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {M mesh : ℝ} {L₀ : ℝ≥0} (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (r₀ : R) (d e : D) (r s : R) :
    |smoothMixtureKernel w f location (d, r) (e, s) -
      smoothMixtureKernel w f location (d, r₀) (e, r₀)| ≤ 2 * M * (L₀ : ℝ) * mesh :=
  smoothMixtureKernel_oscillation w f location hw hw1 hM hmesh hf hLip
    (d, r) (d, r₀) (e, s) (e, r₀) (hdiam d r r₀) (hdiam e s r₀)

/-- The finite coarse-channel estimate. The channel kernel is actually
decomposed, and only its retained part is approximated by the displayed
smooth mixture. Centering is in the fine index inside each coarse cell. -/
theorem coarseChannel_square_bound {Ω C D R : Type*}
    [Fintype Ω] [Fintype C] [Fintype D] [Fintype R] [Nonempty R]
    (wΩ : Ω → ℝ) (p : Ω → D × R → ℝ) (w : C → ℝ)
    (f : C → ℝ → ℝ) (location : D × R → ℝ)
    (discarded retained : D × R → D × R → ℝ)
    (hwΩ : ∀ x, 0 ≤ wΩ x) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {m B ε M mesh : ℝ} {L₀ : ℝ≥0}
    (hm : 0 < m) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (hdiscarded : ∀ a b, 0 ≤ discarded a b)
    (hrows : ∀ a, (∑ b : D × R, m * discarded a b) ≤ B)
    (hdecomp : ∀ a b, finiteTwoSplitKernel wΩ (fun _ => m) p a b =
      discarded a b + retained a b)
    (happrox : ∀ a b, |retained a b - smoothMixtureKernel w f location a b| ≤ ε)
    (g : Ω → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel wΩ (fun _ => m) p g a - finiteResidueAverage (fun r =>
        finiteChannel wΩ (fun _ => m) p g (a.1, r))) ^ 2) ≤
      (4 * B + 4 * (ε + 2 * M * (L₀ : ℝ) * mesh) * ∑ _a : D × R, m) *
        ∑ x, wΩ x * g x ^ 2 := by
  let r₀ : R := Classical.choice inferInstance
  let G : D → D → ℝ := fun d e => smoothMixtureKernel w f location (d, r₀) (e, r₀)
  have hflat (d e : D) (r s : R) : |retained (d, r) (e, s) - G d e| ≤
      ε + 2 * M * (L₀ : ℝ) * mesh := by
    have hosc := smoothMixtureKernel_coarse_error w f location hw hw1 hM hmesh hf hLip
      hdiam r₀ d e r s
    calc
      _ = |(retained (d, r) (e, s) - smoothMixtureKernel w f location (d, r) (e, s)) +
          (smoothMixtureKernel w f location (d, r) (e, s) - G d e)| := by congr 1; ring
      _ ≤ |retained (d, r) (e, s) - smoothMixtureKernel w f location (d, r) (e, s)| +
          |smoothMixtureKernel w f location (d, r) (e, s) - G d e| := abs_add_le _ _
      _ ≤ _ := add_le_add (happrox (d, r) (e, s)) hosc
  exact residueChannel_square_of_discarded wΩ (fun _ : D => m) p discarded retained G
    hwΩ (fun _ => hm) hdiscarded hdecomp hB
    (add_nonneg hε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM)
      L₀.coe_nonneg) hmesh)) hrows hflat g

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCoarseChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coarse approximation of the actual fair-prime channel

Normalized high-exclusive cell probabilities are compared directly with
bounded Lipschitz profiles. Their product yields the smooth mixture kernel;
the actual two-split comparison and the low-union estimate then transfer
the coarse approximation to the original fair-prime channel.
-/

namespace JointDickman

open scoped BigOperators NNReal

/-- The approximating factors are bounded; the actual factors acquire
their bounds from the local errors. -/
theorem product_error_of_bounded_profile {a b u v M η : ℝ}
    (hM : 0 ≤ M) (hη : 0 ≤ η) (hu : |u| ≤ M) (hv : |v| ≤ M)
    (ha : |a - u| ≤ η) (hb : |b - v| ≤ η) :
    |a * b - u * v| ≤ 2 * M * η + η ^ 2 := by
  have hbabs : |b| ≤ M + η := by
    calc
      |b| = |v + (b - v)| := by congr 1; ring
      _ ≤ |v| + |b - v| := abs_add_le _ _
      _ ≤ M + η := add_le_add hv hb
  calc
    |a * b - u * v| = |(a - u) * b + u * (b - v)| := by congr 1; ring
    _ ≤ |(a - u) * b| + |u * (b - v)| := abs_add_le _ _
    _ = |a - u| * |b| + |u| * |b - v| := by rw [abs_mul, abs_mul]
    _ ≤ η * (M + η) + M * η := add_le_add
      (mul_le_mul ha hbabs (abs_nonneg _) hη)
      (mul_le_mul hu hb (abs_nonneg _) hM)
    _ = _ := by ring

/-- Dividing the cell probabilities before taking their product gives
exactly the normalized exclusive-product kernel. -/
theorem exclusiveProductKernel_eq_normalized {C D R : Type*} [Fintype C]
    (w : C → ℝ) (p : C → D × R → ℝ) {m : ℝ} (hm : m ≠ 0) (a b : D × R) :
    exclusiveProductKernel w (fun _ => m) p a b =
      ∑ c, w c * (p c a / m) * (p c b / m) := by
  unfold exclusiveProductKernel
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  field_simp

/-- The smooth mixture follows from the normalized cellwise local law;
no kernel-approximation premise is needed. -/
theorem exclusiveProductKernel_smooth_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (p : C → D × R → ℝ) (f : C → ℝ → ℝ)
    (location : D × R → ℝ) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {m M η : ℝ} (hm : m ≠ 0) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ c x, |f c x| ≤ M)
    (hlocal : ∀ c a, |p c a / m - f c (location a)| ≤ η) (a b : D × R) :
    |exclusiveProductKernel w (fun _ => m) p a b - smoothMixtureKernel w f location a b| ≤
      2 * M * η + η ^ 2 := by
  rw [exclusiveProductKernel_eq_normalized w p hm]
  unfold smoothMixtureKernel
  calc
    _ = |∑ c, w c * ((p c a / m) * (p c b / m) - f c (location a) * f c (location b))| := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c, |w c * ((p c a / m) * (p c b / m) - f c (location a) * f c (location b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, w c * |(p c a / m) * (p c b / m) - f c (location a) * f c (location b)| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ c, w c * (2 * M * η + η ^ 2) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (product_error_of_bounded_profile hM hη (hf c _) (hf c _)
          (hlocal c a) (hlocal c b)) (hw c)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_WeightedKernelCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a bounded weight only discards the low-exclusive union -/

namespace JointDickman

open scoped BigOperators

section
variable {C E A : Type*} [Fintype C] [Fintype E] [DecidableEq A]

theorem weightedDiscardedMass_eq (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ) (a b : A) :
    weightedDiscardedMass w v cell weight a b =
      ∑ c, ∑ e₁, ∑ e₂, if cell c e₁ = some a ∧ cell c e₂ = some b then
        w c * v e₁ * v e₂ * (1 - weight e₁ * weight e₂) else 0 := by
  unfold weightedDiscardedMass
  simp only [independentPairMass_eq_triple, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e₁ _
  apply Finset.sum_congr rfl
  intro e₂ _
  split_ifs <;> ring

theorem weightedDiscardedMass_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1) (a b : A) :
    0 ≤ weightedDiscardedMass w v cell weight a b := by
  rw [weightedDiscardedMass_eq]
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro e₁ _
  apply Finset.sum_nonneg
  intro e₂ _
  split_ifs
  · have hp : weight e₁ * weight e₂ ≤ 1 := by
      nlinarith [(hweight e₁).1, (hweight e₁).2, (hweight e₂).1, (hweight e₂).2]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)) (sub_nonneg.mpr hp)
  · exact le_rfl

theorem weightedDiscardedMass_le_lowUnion (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1) (a b : A) :
    weightedDiscardedMass w v cell weight a b ≤ lowUnionExclusiveMass w v cell low a b := by
  rw [weightedDiscardedMass_eq]
  unfold lowUnionExclusiveMass
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro e₁ _
  apply Finset.sum_le_sum
  intro e₂ _
  by_cases hc : cell c e₁ = some a ∧ cell c e₂ = some b
  · simp only [hc, and_true, ↓reduceIte]
    by_cases hl : low e₁ ∨ low e₂
    · rw [ite_eq_left hl]
      have hp : 0 ≤ weight e₁ * weight e₂ := mul_nonneg (hweight e₁).1 (hweight e₂).1
      have hm := mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂)
      nlinarith
    · rw [ite_eq_right hl]
      have hl' := not_or.mp hl
      rw [hhigh e₁ hl'.1, hhigh e₂ hl'.2]
      simp
  · have hc' : ¬((low e₁ ∨ low e₂) ∧ cell c e₁ = some a ∧ cell c e₂ = some b) := by tauto
    rw [ite_eq_right hc, ite_eq_right hc']

theorem weightedDiscardedKernel_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1) {m : ℝ} (hm : 0 ≤ m) (a b : A) :
    0 ≤ weightedDiscardedKernel w v cell weight m a b :=
  div_nonneg (weightedDiscardedMass_nonneg w v cell weight hw hv hweight a b) (mul_nonneg hm hm)

theorem weightedDiscardedKernel_le_lowUnion (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (weight : E → ℝ)
    (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e)
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1) {m : ℝ} (hm : 0 ≤ m) (a b : A) :
    weightedDiscardedKernel w v cell weight m a b ≤
      lowUnionExclusiveKernel w v cell low (fun _ => m) a b :=
  div_le_div_of_nonneg_right (weightedDiscardedMass_le_lowUnion w v cell weight low hw hv
    hweight hhigh a b) (mul_nonneg hm hm)

end
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PartialWeightedChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse approximation for the partially retained weighted prime channel -/

namespace JointDickman

open scoped BigOperators NNReal

theorem independentPairKernel_weighted {C E D R : Type*} [Fintype C] [Fintype E]
    [DecidableEq D] [DecidableEq R]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option (D × R)) (weight : E → ℝ)
    (m : ℝ) (a b : D × R) :
    independentPairMass w v cell a b / (m * m) =
      weightedDiscardedKernel w v cell weight m a b +
        exclusiveProductKernel w (fun _ => m)
          (fun c => optionCellMass (fun e => v e * weight e) (cell c)) a b := by
  unfold weightedDiscardedKernel weightedDiscardedMass exclusiveProductKernel independentPairMass
  ring

theorem partialFairPrimeKernel_weighted_smooth_error {D R : Type*}
    [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (weight : (Q → Bool) → ℝ) (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m M η : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hf : ∀ c x, |f c x| ≤ M)
    (hlocal : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c) a / m -
        f c (location a)| ≤ η) (a b : D × R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
        weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) weight m a b) -
      smoothMixtureKernel (quarterPrimeMass Q) f location a b| ≤
        2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by
  have herr := partialFairPrimeKernel_independent_error Q hQ hN hcut cell hm a b
  rw [independentPairKernel_weighted _ _ _ weight] at herr
  have hhigh := exclusiveProductKernel_smooth_error (quarterPrimeMass Q)
    (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c))
    f location (quarterPrimeMass_nonneg Q hQ) (quarterPrimeMass_sum Q) hm.ne' hM hη hf hlocal a b
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) a b -
      weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) weight m a b) - smoothMixtureKernel (quarterPrimeMass Q) f location a b =
      (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) a b -
        (weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) weight m a b +
        exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
          (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c)) a b)) +
      (exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
          (fun c => optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c)) a b -
        smoothMixtureKernel (quarterPrimeMass Q) f location a b) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- The discarded weighted mass is controlled by the low union. This
proves the coarse estimate for the actual partial-output channel. -/
theorem partialFairPrimeWeightedCoarse_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (weight : (Q → Bool) → ℝ) (low : (Q → Bool) → Prop) [DecidablePred low]
    (hweight : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1)
    (hhigh : ∀ e, ¬low e → weight e = 1)
    (f : (Q → Bool) → ℝ → ℝ) (location : D × R → ℝ)
    {m H M η mesh : ℝ} {L₀ : ℝ≥0}
    (hm : 0 < m) (hH : 0 ≤ H) (hM : 0 ≤ M) (hη : 0 ≤ η) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeProductCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass Q e * weight e) (primeProductCell Q cell c) a / m -
        f c (location a)| ≤ η)
    (g : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) g a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) g (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * (2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) +
          2 * M * (L₀ : ℝ) * mesh) * ∑ _a : D × R, m) *
            ∑ x, fullPrimeMass Q x * g x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
  let W := weightedDiscardedKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) weight m
  have hW (a b : D × R) : 0 ≤ W a b :=
    weightedDiscardedKernel_nonneg _ _ _ weight hquarter hquarter hweight hm.le a b
  have hrows (a : D × R) : (∑ b : D × R, m * W a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H := by
    calc
      _ ≤ ∑ b : D × R, m * lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
          (primeProductCell Q cell) low (fun _ => m) a b := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left
          (weightedDiscardedKernel_le_lowUnion _ _ _ weight low hquarter hquarter
            hweight hhigh hm.le a b) hm.le
      _ ≤ _ := lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
        (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hsmooth := partialFairPrimeKernel_weighted_smooth_error Q hQ hN hcut cell weight f location
    hm hM hη hf hlocal
  have hε : 0 ≤ 2 * M * η + η ^ 2 + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := coarseChannel_square_bound (fullPrimeMass Q) (partialFairPrimeTransition Q cell)
    (quarterPrimeMass Q) f location W (fun a b => K a b - W a b)
    (fullPrimeMass_nonneg Q hQ) hquarter (quarterPrimeMass_sum Q)
    hm (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hM hmesh hf hLip hdiam hW hrows
    (fun a b => by dsimp [K] <;> ring) hsmooth g
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReindexedCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing partial output cells -/

namespace JointDickman

open scoped BigOperators

theorem optionCellMass_map_equiv {E A B : Type*} [Fintype E] [DecidableEq A] [DecidableEq B]
    (v : E → ℝ) (cell : E → Option A) (e : A ≃ B) (a : A) :
    optionCellMass v (fun x => (cell x).map e) (e a) = optionCellMass v cell a := by
  unfold optionCellMass
  apply Finset.sum_congr rfl
  intro x _
  cases h : cell x with
  | none => simp [h]
  | some b => simp only [h, Option.map_some, Option.some.injEq, e.injective.eq_iff]

theorem independentCellMarginal_map_equiv {C E A B : Type*}
    [Fintype C] [Fintype E] [DecidableEq A] [DecidableEq B]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option A) (e : A ≃ B) (a : A) :
    independentCellMarginal w v (fun c x => (cell c x).map e) (e a) =
      independentCellMarginal w v cell a := by
  unfold independentCellMarginal
  simp only [optionCellMass_map_equiv]

theorem logarithmicCell_mass {E A : Type*} [Fintype E] [DecidableEq A]
    (v : E → ℝ) (n : E → ℕ) (B : ℕ) (lower upper : A → ℝ) (a : A) :
    optionCellMass v (fun x => logarithmicCell B lower upper (n x)) a =
      optionCellMass v (fun x => logResidueCell B 1 lower upper (n x)) (a, 1) :=
  optionCellMass_map_equiv v _ (trivialResidueEquiv A) (a, 1)

theorem logarithmicCell_primeProduct_mass {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (B : ℕ) (lower upper : A → ℝ)
    (v : (Q → Bool) → ℝ) (c : Q → Bool) (a : A) :
    optionCellMass v (primeProductCell Q (logarithmicCell B lower upper) c) a =
      optionCellMass v (primeProductCell Q (logResidueCell B 1 lower upper) c) (a, 1) :=
  logarithmicCell_mass v _ B lower upper a

theorem logarithmicCell_marginal {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (B : ℕ) (lower upper : A → ℝ) (a : A) :
    independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q (logarithmicCell B lower upper)) a =
      independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q (logResidueCell B 1 lower upper)) (a, 1) :=
  independentCellMarginal_map_equiv _ _ _ (trivialResidueEquiv A) (a, 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PublishedCoarseChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic coarse channel bound from published inputs -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

open Classical in
theorem primeLogCoarse_from_published
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A C T : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < T ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 → ∃ M L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      ∀ (D R : Type*) [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R],
      ∀ lower upper : D × R → ℝ,
      (∀ a b s, s ∈ Set.Ioc (lower a) (upper a) → s ∈ Set.Ioc (lower b) (upper b) → a = b) →
      (∀ a, 1 / 2 ≤ lower a) → (∀ a, upper a ≤ 16 / 5) →
      ∀ δ mesh : ℝ, 0 < δ → 0 ≤ mesh → (∀ a, upper a - lower a = δ) →
      (∀ d r s, |lower (d, r) - lower (d, s)| ≤ mesh) →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      let U := finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => δ)
        (partialFairPrimeTransition (auxiliaryPrimes B) (logarithmicCell B lower upper)) f
      (∑ a : D × R, δ * (U a - finiteResidueAverage (fun r => U (a.1, r))) ^ 2) ≤
        coarseChannelError A C T M L θ B δ mesh (∑ _a : D × R, δ) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨v, _, H, C₀, hC₀, hprofile⟩ := primeRampProfile_from_published_jd hSD hSW hM hMP
  obtain ⟨A₁, C₁, hA₁, hC₁, hcommon⟩ := primeCommonLogCell_upper_jd hSD hSW hM hMP
  obtain ⟨A₂, C₂, hA₂, hC₂, hmarginal⟩ := primeChannelMarginal_upper_jd hSD hSW hM hMP
  obtain ⟨T, hT, htail⟩ := quarterPrimeMass_small_log_tail hM
  let A := A₁ + A₂
  let C := C₀ + C₁ + C₂
  have hA : 0 ≤ A := add_nonneg hA₁ hA₂
  have hC : 0 < C := by dsimp [C] <;> positivity
  refine ⟨A, C, T, hA, hC, hT, ?_⟩
  intro θ hθ hθmax
  obtain ⟨M, L, hprof⟩ := hprofile θ (2 * θ) hθ (by linarith)
  refine ⟨M, L, ?_⟩
  filter_upwards [hprof, hcommon, hmarginal, htail, eventually_ge_atTop 2]
    with B hprofB hcommonB hmarginalB htailB hB
  intro D R _ _ _ _ _ lower upper hdisjoint hlower hupper δ mesh hδ hmesh hwidth hdiam f
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let A₀ := A + (E + κ) / δ
  let η := E / δ + (L : ℝ) * δ
  let low := lowPrimeLog (auxiliaryPrimes B) B (2 * θ)
  let weight (e : auxiliaryPrimes B → Bool) :=
    averagingRamp θ (2 * θ) (Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B)
  let profile (c : auxiliaryPrimes B → Bool) (x : ℝ) :=
    rampDensity (scaledRoughDensity v (1 / 4) H B) θ (2 * θ)
      (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
  have horder (a : D × R) : lower a < upper a := by linarith [hwidth a]
  have hq : ((1 : ℕ) : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) := by
    simpa only [Nat.cast_one] using
      (Real.one_le_rpow (by exact_mod_cast (show 1 ≤ B by omega)) (by norm_num : (0 : ℝ) ≤ 100))
  have hE : 0 ≤ E := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  have hκ : 0 ≤ κ := by dsimp [κ] <;> positivity
  have hA₀ : 0 ≤ A₀ := add_nonneg hA (div_nonneg (add_nonneg hE hκ) hδ.le)
  have hη : 0 ≤ η := add_nonneg (div_nonneg hE hδ.le) (mul_nonneg L.coe_nonneg hδ.le)
  have hAmul : A₀ * δ = A * δ + E + κ := by dsimp [A₀]; field_simp <;> ring
  have hN : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have hcut : ∀ p ∈ auxiliaryPrimes B, auxiliaryCutoff B < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have hweight (e) : 0 ≤ weight e ∧ weight e ≤ 1 := averagingRamp_bounds (by linarith) _
  have hhigh (e) (he : ¬low e) : weight e = 1 := by
    apply averagingRamp_one (by linarith)
    exact le_of_lt (lt_of_not_ge he)
  have hmar : ∀ a : D × R,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B)) (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper)) a ≤ A₀ * δ := by
    intro a
    rw [logarithmicCell_marginal]
    have hb := hmarginalB (D × R) 1 hq lower upper hdisjoint
      (fun a => by linarith [hlower a]) (fun a => (horder a).le) hupper a 1
    simp only [Nat.totient_one, Nat.cast_one, div_one, hwidth] at hb
    have hAC : A₂ * δ ≤ A * δ := mul_le_mul_of_nonneg_right (by dsimp [A] <;> linarith) hδ.le
    have hEC : C₂ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C] <;> linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    rw [hAmul]
    linarith
  have hcom : ∀ e, low e → ∀ a : D × R,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c e) a ≤ A₀ * δ := by
    intro e he a
    have he' : lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e := by
      exact le_trans he (by linarith)
    have hcomm : (fun c => primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c e) =
        primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) e := by
      funext c
      simp only [primeProductCell, Nat.mul_comm]
    rw [hcomm, logarithmicCell_primeProduct_mass]
    have hb := hcommonB (D × R) 1 hq lower upper hdisjoint hlower
      (fun a => (horder a).le) hupper e he' a 1
    have hcomm' : (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B 1 lower upper) c e) =
        primeProductCell (auxiliaryPrimes B) (logResidueCell B 1 lower upper) e := by
      funext c
      simp only [primeProductCell, Nat.mul_comm]
    rw [hcomm'] at hb
    simp only [Nat.totient_one, Nat.cast_one, div_one, hwidth] at hb
    have hAC : A₁ * δ ≤ A * δ := mul_le_mul_of_nonneg_right (by dsimp [A] <;> linarith) hδ.le
    have hEC : C₁ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C] <;> linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    rw [hAmul]
    linarith
  have hloc : ∀ c a,
      |optionCellMass (fun e => quarterPrimeMass (auxiliaryPrimes B) e * weight e)
          (primeProductCell (auxiliaryPrimes B) (logarithmicCell B lower upper) c) a / δ -
        profile c (lower a)| ≤ η := by
    intro c a
    rw [logarithmicCell_primeProduct_mass]
    have hb := hprofB.2.2 (D × R) 1 hq lower upper hdisjoint horder hupper c a 1
    have hEC : C₀ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E :=
      mul_le_mul_of_nonneg_right (by dsimp [C] <;> linarith) (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    have hh := primeRampCell_normalized_error (by norm_num : (0 : ℝ) < Nat.totient 1)
      hprofB.2.1 c a 1 (horder a) (hb.trans hEC)
    simpa only [primeRampCell, weight, profile, Nat.totient_one, Nat.cast_one, div_one, hwidth] using hh
  have hplip (c) : LipschitzWith L (profile c) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hprofB.2.1.dist_le_mul
      (x - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
      (y - Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B)
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right, profile] using h
  have hout := partialFairPrimeWeightedCoarse_square_bound (auxiliaryPrimes B)
    (auxiliaryPrimes_prime B) hN hcut (logarithmicCell B lower upper) weight low hweight hhigh
    profile lower hδ hA₀ M.coe_nonneg hη hmesh (fun c x => hprofB.1 _) hplip hdiam hmar hcom hloc f
  have hσ : lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low ≤
      T * (2 * θ + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) :=
    htailB (2 * θ) (by positivity) (by linarith)
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  refine hout.trans (mul_le_mul_of_nonneg_right ?_ hin)
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 8)) hA₀) le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseErrorLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing fine-grid errors in the coarse channel -/

namespace JointDickman

open Filter
open scoped Topology

theorem polynomial_error_div_tendsto {δ : ℕ → ℝ} {C p s : ℝ}
    (hC : 0 ≤ C) (hps : s < p)
    (hδ : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-s) ≤ δ B) :
    Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-p) / δ B) atTop (𝓝 0) := by
  have hlim : Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-(p - s))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (sub_pos.mpr hps)).comp tendsto_natCast_atTop_atTop).const_mul C
  have hb : ∀ᶠ B : ℕ in atTop,
      0 ≤ C * (B : ℝ) ^ (-p) / δ B ∧
        C * (B : ℝ) ^ (-p) / δ B ≤ C * (B : ℝ) ^ (-(p - s)) := by
    filter_upwards [hδ, eventually_gt_atTop 0] with B hδB hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have hlow : 0 < (B : ℝ) ^ (-s) := Real.rpow_pos_of_pos hB0 _
    have hn : 0 ≤ C * (B : ℝ) ^ (-p) := mul_nonneg hC (Real.rpow_nonneg hB0.le _)
    refine ⟨div_nonneg hn (hlow.trans_le hδB).le, ?_⟩
    calc
      _ ≤ C * (B : ℝ) ^ (-p) / (B : ℝ) ^ (-s) := div_le_div_of_nonneg_left hn hlow hδB
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_sub hB0]
        congr 2
        ring
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hlim

theorem channelMesh_fine_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun B : ℕ => channelMesh (channelFineCount m B)) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℕ => (5 / 2 : ℝ) / B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun B => by unfold channelMesh; positivity) _ ht
  filter_upwards [eventually_ge_atTop 1] with B hB
  exact channelMesh_fine_upper hm hB

theorem channelMesh_fine_lower {m : ℕ} (hm : 0 < m) :
    ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(3 : ℝ)) ≤ channelMesh (channelFineCount m B) := by
  filter_upwards [channelFineCount_eventually_le_square hm, eventually_gt_atTop 0] with B hn hB
  simpa only [Nat.totient_one, Nat.cast_one, div_one] using
    (channel_atom_lower (q := 1) hB (channelFineCount_pos hm hB) hn (by omega : 1 ≤ B))

theorem coarseChannelError_fine_tendsto (A T M L θ mesh : ℝ) {C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun B : ℕ => coarseChannelError A C T M L θ B
      (channelMesh (channelFineCount m B)) mesh (5 / 2)) atTop
      (𝓝 (8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A + 20 * M * L * mesh)) := by
  let δ : ℕ → ℝ := fun B => channelMesh (channelFineCount m B)
  have hδ := channelMesh_fine_tendsto hm
  have hlow := channelMesh_fine_lower hm
  have hδsq : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(6 : ℝ)) ≤ δ B * δ B := by
    filter_upwards [hlow, eventually_gt_atTop 0] with B hlowB hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have heq : (B : ℝ) ^ (-(6 : ℝ)) = (B : ℝ) ^ (-(3 : ℝ)) * (B : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq]
    exact mul_self_le_mul_self (Real.rpow_nonneg hB0.le _) hlowB
  have hE := polynomial_error_div_tendsto hC (by norm_num : (3 : ℝ) < 80) hlow
  have hκ : Tendsto (fun B : ℕ => (9 / (8 * (auxiliaryCutoff B : ℝ))) / δ B) atTop (𝓝 0) := by
    apply (polynomial_error_div_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 8)
      (by norm_num : (3 : ℝ) < 1000) hlow).congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    rw [primeComparisonError_power hB]
  have hκsq : Tendsto (fun B : ℕ => (9 / (8 * (auxiliaryCutoff B : ℝ))) / (δ B * δ B)) atTop (𝓝 0) := by
    apply (polynomial_error_div_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 8)
      (by norm_num : (6 : ℝ) < 1000) hδsq).congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    rw [primeComparisonError_power hB]
  have hη : Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-(80 : ℝ)) / δ B + L * δ B) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hE.add (hδ.const_mul L)
  have hrow : Tendsto (fun B : ℕ => A +
      (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) / δ B)
      atTop (𝓝 A) := by
    simpa only [add_div, add_zero] using (hE.add hκ).const_add A
  have hinv : Tendsto (fun B : ℕ => 1 / auxiliaryRatio B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryRatio_tendsto
  have htail := (hinv.const_add (2 * θ)).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hfirst := ((htail.const_mul T).const_mul 8).mul hrow
  have hsecond := (((hη.const_mul (2 * M)).add (hη.pow 2)).add hκsq).const_add (2 * M * L * mesh)
  convert hfirst.add ((hsecond.const_mul 4).mul_const (5 / 2)) using 1
  · funext B
    unfold coarseChannelError
    dsimp only [δ]
    ring
  · norm_num
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformCoarseChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's coarse channel on its refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology NNReal

open Classical in
theorem groupedManuscriptChannel_coarse_bound
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ A C T : ℝ, 0 ≤ A ∧ 0 < C ∧ 0 < T ∧
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 → ∃ M L : ℝ≥0,
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B) *
        (groupedManuscriptChannel m B f a -
          finiteResidueAverage (fun r => groupedManuscriptChannel m B f (a.1, r))) ^ 2) ≤
        coarseChannelError A C T M L θ B (channelMesh (channelFineCount m B)) (channelMesh m) (5 / 2) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨A, C, T, hA, hC, hT, hbound⟩ := primeLogCoarse_from_published hSD hSW hM hMP
  refine ⟨A, C, T, hA, hC, hT, ?_⟩
  intro θ hθ hθmax
  obtain ⟨M, L, hbound⟩ := hbound θ hθ hθmax
  refine ⟨M, L, ?_⟩
  intro m hm
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro f
  let k := channelBlockCount m B
  have hk : 0 < k := by
    have hn := channelFineCount_pos hm hB
    change 0 < m * k at hn
    by_contra h
    have hk0 : k = 0 := by omega
    simp [hk0] at hn
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hh := hboundB (Fin m) (Fin k) (groupedLower m k) (groupedUpper m k)
    (groupedCells_disjoint hm hk) (groupedLower_ge m k)
    (fun a => (groupedUpper_le hm hk a).trans (by norm_num))
    (channelMesh (m * k)) (channelMesh m) (channelMesh_pos (Nat.mul_pos hm hk))
    (channelMesh_pos hm).le (grouped_width m k) (groupedLower_diameter hm hk) f
  rw [grouped_total_mass hm hk] at hh
  exact hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseCompactness
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse compactness of the manuscript channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem exists_small_coarse_cutoff (A T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A < ε := by
  let θ : ℕ → ℝ := fun n => (1 / 8) * (1 / ((n : ℝ) + 1))
  have hθ : Tendsto θ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 8 : ℝ)
  have ht : Tendsto (fun n => 8 * T * (2 * θ n) ^ (1 / 4 : ℝ) * A) atTop (𝓝 0) := by
    have hh := (hθ.const_mul 2).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
    simpa using (hh.const_mul (8 * T)).mul_const A
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  refine ⟨θ n, ?_, ?_, hn⟩
  · dsimp [θ]
    positivity
  · have hinv : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [θ]
    linarith

open Classical in
/-- The coarse partition is fixed before B grows and works uniformly for
all real input functions, including inputs depending on B. -/
theorem groupedManuscriptChannel_coarse_compactness
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B) *
        (groupedManuscriptChannel m B f a -
          finiteResidueAverage (fun r => groupedManuscriptChannel m B f (a.1, r))) ^ 2) ≤
        ε * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨A, C, T, _, hC, _, hbound⟩ := groupedManuscriptChannel_coarse_bound hSD hSW hM hMP
  obtain ⟨θ, hθ, hθmax, htail⟩ := exists_small_coarse_cutoff A T (half_pos hε)
  obtain ⟨M, L, hbound⟩ := hbound θ hθ hθmax
  have hmesh : Tendsto (fun m : ℕ => 20 * (M : ℝ) * L * channelMesh m) atTop (𝓝 0) := by
    have hh : Tendsto (fun m : ℕ => (5 / 2 : ℝ) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [channelMesh, mul_zero] using hh.const_mul (20 * (M : ℝ) * L)
  obtain ⟨m, hm, hsmall⟩ := ((eventually_gt_atTop 0).and
    (hmesh.eventually (eventually_lt_nhds (half_pos hε)))).exists
  refine ⟨m, hm, ?_⟩
  have hlim := coarseChannelError_fine_tendsto A T M L θ (channelMesh m) hC.le hm
  have hlimit : 8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A + 20 * (M : ℝ) * L * channelMesh m < ε := by
    linarith
  filter_upwards [hbound m hm, hlim.eventually (eventually_lt_nhds hlimit)] with B hb he
  intro f
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  exact (hb f).trans (mul_le_mul_of_nonneg_right he.le hin)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LogarithmicMarginal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic marginal is the channel used by coarse compactness -/

namespace JointDickman
open Finset Filter

open Classical in
theorem logarithmicCell_eq_some {D : Type*} [DecidableEq D]
    (B : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (i : D) :
    logarithmicCell B lower upper n = some i ↔
      Real.log n/B ∈ Set.Ioc (lower i) (upper i) := by
  unfold logarithmicCell
  constructor
  · intro he
    obtain ⟨⟨d,r⟩,hc,hi⟩ := Option.map_eq_some_iff.mp he
    change d = i at hi
    subst d
    exact ((logResidueCell_eq_some B 1 lower upper hdisjoint n i r).mp hc).1
  · intro hi
    have hc : logResidueCell B 1 lower upper n = some (i,1) :=
      (logResidueCell_eq_some B 1 lower upper hdisjoint n i 1).mpr
        ⟨hi,Subsingleton.elim _ _⟩
    simp [hc,trivialResidueEquiv]

theorem groupedManuscriptChannel_log_mass {m B : ℕ}
    (hm : 0 < m) (hB : 0 < B) (g : (auxiliaryPrimes B → Bool) → ℝ)
    (a : Fin m × Fin (channelBlockCount m B)) :
    channelMesh (channelFineCount m B)*groupedManuscriptChannel m B g a =
      logCellSignedMass m B g (finProdFinEquiv a) := by
  classical
  have hk : 0 < channelBlockCount m B := by
    have hh := channelFineCount_pos hm hB
    change 0 < m*channelBlockCount m B at hh
    exact Nat.pos_of_ne_zero (by intro he; simp [he] at hh)
  have he := signedSplitProductMass_channel (auxiliaryPrimes B) g
    (logarithmicCell B (groupedLower m (channelBlockCount m B))
      (groupedUpper m (channelBlockCount m B)))
    (fun _ => channelMesh (channelFineCount m B)) a
    (channelMesh_pos (channelFineCount_pos hm hB)).ne'
  change _ = channelMesh (channelFineCount m B)*groupedManuscriptChannel m B g a at he
  rw [← he]
  unfold logCellSignedMass
  apply sum_congr rfl
  intro n _
  simp only [logarithmicCell_eq_some B _ _ (groupedCells_disjoint hm hk)]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteKernelBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear stability of a finite kernel under square-norm approximation -/

namespace JointDickman
open Finset

theorem finiteKernelBilinear_bound {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v : A → ℝ) :
    |finiteKernelBilinear μ K u v| ≤
      C*Real.sqrt (∑ a, μ a*u a^2)*Real.sqrt (∑ a, μ a*v a^2) := by
  have hu : 0 ≤ ∑ a, μ a*u a^2 := sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hv : 0 ≤ ∑ a, μ a*v a^2 := sum_nonneg (fun a _ => mul_nonneg (hμ a) (sq_nonneg _))
  have hs : finiteKernelBilinear μ K u v ^ 2 ≤
      (∑ a, μ a*u a^2)*(∑ a, μ a*finiteKernelAction μ K v a^2) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro a _
      exact mul_nonneg (hμ a) (sq_nonneg _)
    · intro a _
      exact mul_nonneg (hμ a) (sq_nonneg _)
    · intro a _
      ring_nf
      exact le_rfl
  have haction := finiteKernelAction_square_bound μ K hμ hC hrow hcol v
  have hh := hs.trans (mul_le_mul_of_nonneg_left haction hu)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  rw [sq_abs,mul_pow,mul_pow,Real.sq_sqrt hu,Real.sq_sqrt hv]
  exact hh.trans_eq (by ring)

theorem finiteKernelBilinear_bound_of_energies {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v : A → ℝ)
    {U V : ℝ} (hu : (∑ a, μ a*u a^2) ≤ U) (hv : (∑ a, μ a*v a^2) ≤ V) :
    |finiteKernelBilinear μ K u v| ≤ C*Real.sqrt U*Real.sqrt V := by
  apply (finiteKernelBilinear_bound μ K hμ hC hrow hcol u v).trans
  gcongr

theorem finiteKernelBilinear_sub {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (u v s t : A → ℝ) :
    finiteKernelBilinear μ K u v-finiteKernelBilinear μ K s t =
      finiteKernelBilinear μ K (fun a => u a-s a) v+
        finiteKernelBilinear μ K s (fun a => v a-t a) := by
  simp only [finiteKernelBilinear,finiteKernelAction,mul_sum,mul_sub,sub_mul,
    sum_sub_distrib]
  ring

theorem finiteKernelBilinear_stability {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b*|K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a*|K a b|) ≤ C) (u v s t : A → ℝ)
    {e₁ e₂ U V : ℝ}
    (he₁ : (∑ a, μ a*(u a-s a)^2) ≤ e₁)
    (he₂ : (∑ a, μ a*(v a-t a)^2) ≤ e₂)
    (hU : (∑ a, μ a*s a^2) ≤ U) (hV : (∑ a, μ a*v a^2) ≤ V) :
    |finiteKernelBilinear μ K u v-finiteKernelBilinear μ K s t| ≤
      C*(Real.sqrt e₁*Real.sqrt V+Real.sqrt U*Real.sqrt e₂) := by
  rw [finiteKernelBilinear_sub]
  exact (abs_add_le _ _).trans ((add_le_add
    (finiteKernelBilinear_bound_of_energies μ K hμ hC hrow hcol _ _ he₁ hV)
    (finiteKernelBilinear_bound_of_energies μ K hμ hC hrow hcol _ _ hU he₂)).trans_eq (by ring))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CoarseKernelComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform coarse replacement of both bounded endpoint tests -/

namespace JointDickman
open Finset Filter

theorem finiteResidueAverage_square_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) :
    (Fintype.card R : ℝ)*finiteResidueAverage f^2 ≤ ∑ r, f r^2 := by
  have hn : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hh := sum_mul_sq_le_sq_mul_sq univ (fun _ : R => (1 : ℝ)) f
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
  have he : (Fintype.card R : ℝ)*finiteResidueAverage f^2 =
      (∑ r, f r)^2/(Fintype.card R : ℝ) := by
    unfold finiteResidueAverage
    field_simp
  rw [he]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hh)

theorem coarseGroupAverage_energy {D R : Type*} [Fintype D] [Fintype R] [Nonempty R]
    (u : D × R → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ a : D × R, δ*coarseGroupAverage u a^2) ≤ ∑ a : D × R, δ*u a^2 := by
  simp only [Fintype.sum_prod_type,coarseGroupAverage]
  apply sum_le_sum
  intro d _
  have hh := mul_le_mul_of_nonneg_left (finiteResidueAverage_square_le (fun r => u (d,r))) hδ
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_sum,mul_assoc,mul_left_comm] using hh

theorem fullPrimeMass_unit_energy (B : ℕ)
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1) :
    (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) ≤ 1 := by
  calc
    _ ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x*1 := by
      apply sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (show g x^2 ≤ 1 by have hx := abs_le.mp (hg x); nlinarith)
        (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x)
    _ = 1 := by simpa only [mul_one,fullPrimeMass] using
      bernoulliSiteMass_sum (fun p : auxiliaryPrimes B => 1/(p.val : ℝ))

/-- A fixed coarse partition works for all bounded endpoint tests and every
kernel with a prescribed weighted absolute row and column bound. -/
theorem groupedManuscriptChannel_bilinear_coarse
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ K : (Fin m × Fin (channelBlockCount m B)) →
        (Fin m × Fin (channelBlockCount m B)) → ℝ,
      ∀ A : ℝ, 0 ≤ A →
      (∀ a, (∑ b, channelMesh (channelFineCount m B)*|K a b|) ≤ A) →
      (∀ b, (∑ a, channelMesh (channelFineCount m B)*|K a b|) ≤ A) →
      |finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B)) K
          (groupedManuscriptChannel m B g) (groupedManuscriptChannel m B h)-
        finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B)) K
          (coarseGroupAverage (groupedManuscriptChannel m B g))
          (coarseGroupAverage (groupedManuscriptChannel m B h))| ≤ A*ε := by
  obtain ⟨C,hC,hbound⟩ := groupedManuscriptChannel_square_bound_jd hSD hSW hM hMP
  let η := (ε/(2*Real.sqrt C))^2
  have hroot : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hη : 0 < η := sq_pos_of_pos (div_pos hε (mul_pos (by norm_num) hroot))
  obtain ⟨m,hm,hcoarse⟩ := groupedManuscriptChannel_coarse_compactness hSD hSW hM hMP hη
  refine ⟨m,hm,?_⟩
  filter_upwards [hcoarse,hbound m hm,eventually_gt_atTop 0] with B he hb hB
  have hk : 0 < channelBlockCount m B := by
    have hp := channelFineCount_pos hm hB
    change 0 < m*channelBlockCount m B at hp
    exact Nat.pos_of_ne_zero (by intro he; simp [he] at hp)
  let : NeZero (channelBlockCount m B) := ⟨hk.ne'⟩
  intro g h hg hh K A hA hrow hcol
  have hδ := (channelMesh_pos (channelFineCount_pos hm hB)).le
  have hge := (he g).trans (mul_le_of_le_one_right hη.le (fullPrimeMass_unit_energy B g hg))
  have hhe := (he h).trans (mul_le_of_le_one_right hη.le (fullPrimeMass_unit_energy B h hh))
  have hgn := (hb g).trans (mul_le_of_le_one_right hC.le (fullPrimeMass_unit_energy B g hg))
  have hhn := (hb h).trans (mul_le_of_le_one_right hC.le (fullPrimeMass_unit_energy B h hh))
  have hgcn := (coarseGroupAverage_energy (groupedManuscriptChannel m B g) hδ).trans hgn
  have hs := finiteKernelBilinear_stability (fun _ => channelMesh (channelFineCount m B))
    K (fun _ => hδ) hA hrow hcol (groupedManuscriptChannel m B g)
    (groupedManuscriptChannel m B h) (coarseGroupAverage (groupedManuscriptChannel m B g))
    (coarseGroupAverage (groupedManuscriptChannel m B h)) hge hhe hgcn hhn
  have hηroot : Real.sqrt η = ε/(2*Real.sqrt C) :=
    Real.sqrt_sq (div_nonneg hε.le (by positivity))
  have hconst : Real.sqrt η*Real.sqrt C+Real.sqrt C*Real.sqrt η = ε := by
    rw [hηroot]
    field_simp
    ring
  exact hs.trans_eq (by rw [hconst])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramFourierRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability for exact finite-sum rearrangements of the histogram error -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem manuscriptFourier_frequency_continuous (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℝ → ℂ)
    (hF : ∀ x, Continuous (fun ξ => F ξ x)) (r : ZMod q) :
    Continuous (fun ξ => manuscriptFourier m B q J g (F ξ) r) := by
  classical
  unfold manuscriptFourier unitResidueFourier manuscriptCellSum
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro n _
  split_ifs
  · exact continuous_const.mul (hF _)
  · exact continuous_const

theorem sampledProjectedFourier_frequency_continuous (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → Fin (channelFineCount m B) → ℂ)
    (hF : ∀ i, Continuous (fun ξ => F ξ i)) (r : ZMod q) :
    Continuous (fun ξ => sampledProjectedFourier m B q J g (F ξ) r) := by
  simp_rw [sampledProjectedFourier_eq]
  apply continuous_const.mul
  unfold sampledProjectedValue
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (hF i)

theorem norm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) (i : ι)
    {C : ℝ} (hC : 0 ≤ C) (hs : ∑ j, ‖f j‖^2 ≤ C) : ‖f i‖ ≤ Real.sqrt C := by
  have hle : ‖f i‖^2 ≤ C :=
    (single_le_sum (fun j _ => sq_nonneg ‖f j‖) (mem_univ i)).trans hs
  nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (f i)]

theorem manuscriptFourier_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) (r : ZMod q) :
    ‖manuscriptFourier m B q J g F r‖ ≤ Real.sqrt (manuscriptAmplitudeEnergy m B q J*M^2) := by
  apply norm_le_sqrt_sum_sq _ r (mul_nonneg (manuscriptAmplitudeEnergy_nonneg hm hB J) (sq_nonneg M))
  exact (manuscript_amplitude_fourier_bounds hm hB J g hg F hM hF).1.trans_eq
    (by unfold manuscriptAmplitudeEnergy; ring)

theorem sampledProjectedFourier_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) (r : ZMod q) :
    ‖sampledProjectedFourier m B q J g F r‖ ≤ Real.sqrt (manuscriptAmplitudeEnergy m B q J*M^2) :=
  norm_le_sqrt_sum_sq _ r (mul_nonneg (manuscriptAmplitudeEnergy_nonneg hm hB J) (sq_nonneg M))
    (sampledProjectedFourier_square_le hm hB J g hg F hM hF)

theorem schwartz_bounded_product_integrable (w : 𝓢(ℝ,ℝ)) (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) {M N : ℝ}
    (hM : ∀ ξ, ‖F ξ‖ ≤ M) (hN : ∀ ξ, ‖G ξ‖ ≤ N) (hMN : 0 ≤ M) :
    Integrable (fun ξ => testFourierTransform w ξ*(F ξ*G ξ)) :=
  (schwartz_testFourier_integrable w).mul_bdd (hF.mul hG).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul (hM ξ) (hN ξ) (norm_nonneg _) hMN))

theorem logOscillatoryTest_continuous_frequency (w : ℝ → ℝ) (B N β x : ℝ) :
    Continuous (fun ξ => logOscillatoryTest w B N (β*ξ) x) := by
  unfold logOscillatoryTest oscillatoryTest
  exact continuous_const.mul (continuous_additivePhase.comp
    ((continuous_const.mul continuous_id).mul continuous_const))

theorem logarithmic_histogram_integrals {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) (r : ZMod q) :
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    Integrable (fun ξ => testFourierTransform w ξ*
      (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r))) ∧
    Integrable (fun ξ => testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r))) := by
  dsimp only
  have hF (ξ x : ℝ) : ‖logOscillatoryTest w₁ B N (β*ξ) x‖ ≤ M₁ := by
    rw [logOscillatoryTest_norm]
    exact hw₁ _
  have hG (ξ x : ℝ) : ‖logOscillatoryTest w₂ B N (-β*ξ) x‖ ≤ M₂ := by
    rw [logOscillatoryTest_norm]
    exact hw₂ _
  constructor
  · refine schwartz_bounded_product_integrable
      (w := w) (M := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₁^2))
      (N := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₂^2)) _ _ ?_ ?_ ?_ ?_ ?_
    · exact manuscriptFourier_frequency_continuous m B q J g _
        (fun x => logOscillatoryTest_continuous_frequency _ _ _ _ x) _
    · exact manuscriptFourier_frequency_continuous m B q J h _
        (fun x => logOscillatoryTest_continuous_frequency _ _ _ _ x) _
    · intro ξ
      exact manuscriptFourier_norm_le hm hB J g hg _ hM₁ (fun _ _ x _ => hF ξ x) r
    · intro ξ
      exact manuscriptFourier_norm_le hm hB J h hh _ hM₂ (fun _ _ x _ => hG ξ x) (-r)
    · positivity
  · refine schwartz_bounded_product_integrable
      (w := w) (M := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₁^2))
      (N := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₂^2)) _ _ ?_ ?_ ?_ ?_ ?_
    · exact sampledProjectedFourier_frequency_continuous m B q J g _
        (fun i => logOscillatoryTest_continuous_frequency _ _ _ _ _) _
    · exact sampledProjectedFourier_frequency_continuous m B q J h _
        (fun i => logOscillatoryTest_continuous_frequency _ _ _ _ _) _
    · intro ξ
      exact sampledProjectedFourier_norm_le hm hB J g hg _ hM₁ (fun i _ => hF ξ _) r
    · intro ξ
      exact sampledProjectedFourier_norm_le hm hB J h hh _ hM₂ (fun i _ => hG ξ _) (-r)
    · positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramIntegralIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-sum identities for the integrated histogram replacement -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem integral_oppositeProductSum {q : ℕ} [NeZero q]
    (P : ZMod q → Prop) [DecidablePred P] (W : ℝ → ℂ)
    (A B : ℝ → ZMod q → ℂ)
    (hI : ∀ r, Integrable (fun ξ => W ξ*(A ξ r*B ξ (-r)))) :
    (∫ ξ : ℝ, W ξ*oppositeProductSum P (A ξ) (B ξ)) =
      ∑ r : ZMod q, if P r then ∫ ξ : ℝ, W ξ*(A ξ r*B ξ (-r)) else 0 := by
  have he : (fun ξ => W ξ*oppositeProductSum P (A ξ) (B ξ)) =
      fun ξ => ∑ r : ZMod q, if P r then W ξ*(A ξ r*B ξ (-r)) else 0 := by
    funext ξ
    simp only [oppositeProductSum,mul_sum,mul_ite,mul_zero]
  rw [he,integral_finsetSum]
  · apply sum_congr rfl
    intro r _
    by_cases hr : P r <;> simp only [hr,ite_true, if_true,ite_false, if_false,integral_zero]
  · intro r _
    by_cases hr : P r
    · simpa only [hr,ite_true, if_true] using hI r
    · simp only [hr,ite_false, if_false]
      exact integrable_zero ℝ ℂ volume

theorem manuscriptSampledIntegralError_eq {m B q : ℕ} [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (F G : ℝ → ℝ → ℂ)
    (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ))
    (hI : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*
      (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r))))
    (hJ : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)))) :
    manuscriptSampledIntegralError m B q J g h F G P w =
      (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
        (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r)) else 0)-
      (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
        (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
          sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)) else 0) := by
  have hsum (A C : ℝ → ZMod q → ℂ)
      (hh : ∀ r, Integrable (fun ξ => testFourierTransform w ξ*(A ξ r*C ξ (-r)))) :
      Integrable (fun ξ => testFourierTransform w ξ*oppositeProductSum P (A ξ) (C ξ)) := by
    have he : (fun ξ => testFourierTransform w ξ*oppositeProductSum P (A ξ) (C ξ)) =
        fun ξ => ∑ r : ZMod q, if P r then testFourierTransform w ξ*(A ξ r*C ξ (-r)) else 0 := by
      funext ξ
      simp only [oppositeProductSum,mul_sum,mul_ite,mul_zero]
    rw [he]
    apply integrable_finsetSum
    intro r _
    by_cases hr : P r
    · simpa only [hr,ite_true, if_true] using hh r
    · simp only [hr,ite_false, if_false]
      exact integrable_zero ℝ ℂ volume
  unfold manuscriptSampledIntegralError
  simp_rw [mul_sub]
  rw [integral_sub (hsum _ _ hI) (hsum _ _ hJ),
    integral_oppositeProductSum P _ _ _ hI,integral_oppositeProductSum P _ _ _ hJ]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointIntegralReplacement
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The histogram error is the difference of the original endpoint integrals -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem endpoint_integral_replacement {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (hcut : q ≤ auxiliaryCutoff B)
    {a b N : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hl₁ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₁ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (hl₂ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₂ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (β : ℝ) (P : ZMod q → Prop) [DecidablePred P] (w : 𝓢(ℝ,ℝ)) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
      (endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁
          (r.val/(q : ℝ)+β*ξ/N)*
        endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂
          (-(r.val/(q : ℝ)+β*ξ/N))) else 0)-
    (∑ r : ZMod q, if P r then ∫ ξ : ℝ, testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r)) else 0) =
      manuscriptSampledIntegralError m B q J g h F G P w := by
  dsimp only
  let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
  let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
  let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
  have hid (ξ : ℝ) (r : ZMod q) :
      endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁
          (r.val/(q : ℝ)+β*ξ/N) = manuscriptFourier m B q J g (F ξ) r := by
    have he := endpointFourierSum_histogram (m := m) (B := B) (q := q) hm hB hcut ha hab hN g w₁ hs₁ hl₁ r (β*ξ/N)
    rw [div_mul_cancel₀ _ hN.ne'] at he
    exact he
  have hid' (ξ : ℝ) (r : ZMod q) :
      endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂
          (-(r.val/(q : ℝ)+β*ξ/N)) = manuscriptFourier m B q J h (G ξ) (-r) := by
    have he := endpointFourierSum_histogram_neg (m := m) (B := B) (q := q) hm hB hcut ha hab hN h w₂ hs₂ hl₂ r (β*ξ/N)
    rw [div_mul_cancel₀ _ hN.ne',← neg_mul] at he
    exact he
  simp_rw [hid,hid']
  symm
  exact manuscriptSampledIntegralError_eq J g h F G P w
    (fun r => (logarithmic_histogram_integrals hm hB J g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ N β w r).1)
    (fun r => (logarithmic_histogram_integrals hm hB J g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ N β w r).2)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FullArcDenominators
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact normalization of the retained full-frequency model -/

namespace JointDickman
open Finset MeasureTheory

theorem fullSmallMajorArcModel_denominators {B j Q : ℕ} [NeZero j]
    (hQ : Q ≤ B^12) (X : ℝ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) :
    fullSmallMajorArcModel B j X Q F W a =
      (1/(j : ℂ))*∑ q ∈ positiveDenominators Q, a q*
        ∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*W ξ else 0 := by
  classical
  have hf : (positiveDenominators (B^12)).filter (fun q : ℕ+ => (q : ℕ) ≤ Q) = positiveDenominators Q := by
    ext q
    simp only [mem_filter,mem_positiveDenominators]
    exact ⟨And.right,fun h => ⟨h.trans hQ,h⟩⟩
  unfold fullSmallMajorArcModel
  rw [← sum_filter,hf]
  congr 1
  apply sum_congr rfl
  intro q _
  rw [mul_sum]
  apply sum_congr rfl
  intro r _
  split_ifs <;> simp only [mul_zero]

theorem fullSmallMajorArcModel_scalar_denominators {B j Q : ℕ} [NeZero j]
    (hQ : Q ≤ B^12) (X : ℝ) (F W : ℝ → ℂ) (a : ℕ+ → ℂ) (c : ℂ) :
    fullSmallMajorArcModel B j X Q F (fun ξ => c*W ξ) a =
      (c/(j : ℂ))*∑ q ∈ positiveDenominators Q, a q*
        ∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, W ξ*F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X)) else 0 := by
  rw [fullSmallMajorArcModel_denominators hQ]
  have hi (q : ℕ+) (r : ZMod (j*(q : ℕ))) :
      (∫ ξ : ℝ, F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))*(c*W ξ)) =
        c*(∫ ξ : ℝ, W ξ*F ((r.val : ℝ)/(j*(q : ℕ) : ℕ)+ξ/((j : ℝ)*X))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by ring)
  simp_rw [hi]
  simp only [div_eq_mul_inv,mul_sum,mul_ite,mul_zero]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro r _
  split_ifs <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TotientSummability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summable denominator majorant for the singular series -/

namespace JointDickman
open Filter
open scoped Topology

theorem totient_reciprocal_subpower
    (hMP : PublishedInputs.PrimeProductMertensInput) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop, 1/(q.totient : ℝ) ≤ (q : ℝ)^(-1+ε) := by
  obtain ⟨K,hK,hbound⟩ := totient_log_bound hMP
  have hlim := ((log_power_div_power_tendsto_zero 1 hε).const_mul K).comp
    tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlim
  filter_upwards [hbound,hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with q hboundq hsmall hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hφ0 : (0 : ℝ) < q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (show 0 < q by omega))
  have hlogpower : K*Real.log q ≤ (q : ℝ)^ε := by
    apply (div_le_one (Real.rpow_pos_of_pos hq0 ε)).mp
    simpa only [Function.comp_def,Real.rpow_one,mul_div_assoc] using hsmall
  have hφ : 1/(q.totient : ℝ) ≤ K*Real.log q/q := by
    apply (div_le_div_iff₀ hφ0 hq0).mpr
    simpa only [one_mul] using hboundq q (by omega)
      (Nat.le_self_pow (by norm_num : 15 ≠ 0) q)
  calc
    _ ≤ K*Real.log q/q := hφ
    _ ≤ (q : ℝ)^ε/(q : ℝ) := div_le_div_of_nonneg_right hlogpower hq0.le
    _ = (q : ℝ)^ε/(q : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hq0]; congr 1; ring

theorem summable_totient_reciprocal_sq
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    Summable (fun q : ℕ => 1/(q.totient : ℝ)^2) := by
  have hbound := totient_reciprocal_subpower hMP (by norm_num : (0 : ℝ) < 1/4)
  have hmaj : Summable (fun q : ℕ => (q : ℝ)^(-3/2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat hmaj
  filter_upwards [hbound,eventually_ge_atTop 1] with q hq hq1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 1/(q.totient : ℝ)^2)]
  calc
    _ = (1/(q.totient : ℝ))^2 := by ring
    _ ≤ ((q : ℝ)^(-1+(1/4 : ℝ)))^2 := pow_le_pow_left₀ (by positivity) hq 2
    _ = _ := by rw [← Real.rpow_mul_natCast hq0.le]; norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular series produced by the Ramanujan residue factor -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

theorem singularSeriesCoefficient_one (j : ℕ) : singularSeriesCoefficient j 1 = 1 := by
  simp [singularSeriesCoefficient]

theorem singularSeriesCoefficient_mul (j : ℕ) {a b : ℕ} (hab : a.Coprime b) :
    singularSeriesCoefficient j (a*b) =
      singularSeriesCoefficient j a*singularSeriesCoefficient j b := by
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
  simp only [singularSeriesCoefficient,Nat.coprime_mul_iff_left,Nat.totient_mul hab,hm,
    Int.cast_mul,Nat.cast_mul]
  split_ifs <;> simp_all [div_mul_div_comm,mul_pow]

theorem singularSeriesCoefficient_norm_le (j q : ℕ) :
    ‖singularSeriesCoefficient j q‖ ≤ 1/(q.totient : ℝ)^2 := by
  unfold singularSeriesCoefficient
  split_ifs
  · rw [norm_div,Real.norm_of_nonneg (sq_nonneg _),Real.norm_eq_abs]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  · simp only [norm_zero]
    positivity

theorem singularSeriesCoefficient_summable
    (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    Summable (fun q => ‖singularSeriesCoefficient j q‖) := by
  exact (summable_totient_reciprocal_sq hMP).of_nonneg_of_le (fun _ => norm_nonneg _)
    (singularSeriesCoefficient_norm_le j)

theorem singularSeriesCoefficient_prime_power_zero (j : ℕ) {p e : ℕ}
    (hp : p.Prime) (he : 2 ≤ e) : singularSeriesCoefficient j (p^e) = 0 := by
  have hm : μ (p^e) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (show e ≠ 0 by omega),
      ite_eq_right (show e ≠ 1 by omega)]
  simp [singularSeriesCoefficient,hm]

theorem singularSeries_local_factor (j : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, singularSeriesCoefficient j (p^e)) =
      if p ∣ j then 1 else 1-1/((p : ℝ)-1)^2 := by
  classical
  have hs : (∑' e : ℕ, singularSeriesCoefficient j (p^e)) =
      ∑ e ∈ ({0,1} : Finset ℕ), singularSeriesCoefficient j (p^e) := by
    apply tsum_eq_sum
    intro e he
    apply singularSeriesCoefficient_prime_power_zero j hp
    simp only [mem_insert,mem_singleton,not_or] at he
    omega
  rw [hs]
  simp only [sum_insert,mem_singleton,zero_ne_one,not_false_eq_true,sum_singleton,pow_zero,
    singularSeriesCoefficient_one,pow_one]
  rw [singularSeriesCoefficient,ArithmeticFunction.moebius_apply_prime hp,Nat.totient_prime hp]
  have hp1 : 1 ≤ p := hp.one_le
  rw [Nat.cast_sub hp1]
  simp only [Nat.cast_one,Int.cast_neg,Int.cast_one,hp.coprime_iff_not_dvd]
  by_cases hd : p ∣ j <;> simp [hd,sub_eq_add_neg,neg_div]

theorem singularSeries_hasProd (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    HasProd (fun p : Nat.Primes =>
      if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2)
      (∑' q, singularSeriesCoefficient j q) := by
  have hz : singularSeriesCoefficient j 0 = 0 := by simp [singularSeriesCoefficient]
  have h := EulerProduct.eulerProduct_hasProd (singularSeriesCoefficient_one j)
    (fun {_ _} hab => singularSeriesCoefficient_mul j hab)
    (singularSeriesCoefficient_summable hMP j) hz
  have he : (fun p : Nat.Primes => ∑' e, singularSeriesCoefficient j ((p : ℕ)^e)) =
      (fun p : Nat.Primes => if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) := by
    funext p
    exact singularSeries_local_factor j p.property
  rwa [he] at h

theorem singularSeries_local_bounds (j : ℕ) (p : Nat.Primes) :
    0 ≤ (if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) ∧
    (if (p : ℕ) ∣ j then (1 : ℝ) else 1-1/((p : ℝ)-1)^2) ≤ 1 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · have hs : 1 ≤ ((p : ℝ)-1)^2 := by nlinarith
    have hd : 1/((p : ℝ)-1)^2 ≤ 1 := (div_le_one (by positivity)).mpr hs
    constructor
    · linarith
    · exact sub_le_self _ (by positivity)

theorem singularSeries_bounds (hMP : PublishedInputs.PrimeProductMertensInput) (j : ℕ) :
    0 ≤ singularSeries j ∧ singularSeries j ≤ (j : ℝ)/j.totient := by
  have h := singularSeries_hasProd hMP j
  have hlo : 0 ≤ ∑' q, singularSeriesCoefficient j q :=
    h.nonneg (fun p => (singularSeries_local_bounds j p).1)
  have hhi : (∑' q, singularSeriesCoefficient j q) ≤ 1 := by
    apply le_of_tendsto' h
    intro s
    exact Finset.prod_le_one (fun p _ => (singularSeries_local_bounds j p).1)
      (fun p _ => (singularSeries_local_bounds j p).2)
  constructor
  · exact mul_nonneg (by positivity) hlo
  · simpa only [singularSeries,mul_one] using
      mul_le_mul_of_nonneg_left hhi (show 0 ≤ (j : ℝ)/j.totient by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_LogSampledKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampled major-arc kernel in its actual logarithmic coordinates -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem logOscillatoryTest_sample_phase (w : ℝ → ℝ) (B N β ξ x : ℝ) :
    logOscillatoryTest w B N (β*ξ) x =
      (w (Real.exp (B*x)/N) : ℂ)*additivePhase (ξ*(β*(Real.exp (B*x)/N))) := by
  unfold logOscillatoryTest oscillatoryTest
  congr 2
  ring

theorem sampledEndpointKernel_eq (m B j Q : ℕ) [NeZero j]
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) :
    sampledEndpointKernel m B j Q J g h w₁ w₂ N β w =
      ∑ q ∈ positiveDenominators Q, ((ArithmeticFunction.moebius (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
        (∑ r : ZMod (j*(q : ℕ)), if r.val.Coprime (q : ℕ) then
          ∫ ξ : ℝ, testFourierTransform w ξ*
            (sampledProjectedFourier m B (j*(q : ℕ)) J g
              (fun i => logOscillatoryTest w₁ B N (β*ξ) (channelLower (channelFineCount m B) i)) r*
            sampledProjectedFourier m B (j*(q : ℕ)) J h
              (fun i => logOscillatoryTest w₂ B N (-β*ξ) (channelLower (channelFineCount m B) i)) (-r)) else 0) := by
  have hp (ξ : ℝ) :
      (fun i : Fin (channelFineCount m B) =>
        (w₁ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ)*
          additivePhase (ξ*(β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)))) =
      fun i => logOscillatoryTest w₁ B N (β*ξ) (channelLower (channelFineCount m B) i) := by
    funext i
    exact (logOscillatoryTest_sample_phase w₁ B N β ξ _).symm
  have hn (ξ : ℝ) :
      (fun i : Fin (channelFineCount m B) =>
        (w₂ (Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N) : ℂ)*
          additivePhase (-ξ*(β*(Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/N)))) =
      fun i => logOscillatoryTest w₂ B N (-β*ξ) (channelLower (channelFineCount m B) i) := by
    funext i
    unfold logOscillatoryTest oscillatoryTest
    congr 2
    ring
  unfold sampledEndpointKernel sampledMajorKernel
  simp only [hp,hn,mul_assoc]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointFullModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact connection of the coefficient arc model to the sampled log kernel -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

theorem endpoint_full_model_replacement {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hQ : Q ≤ B^12) (hcut : j*Q ≤ auxiliaryCutoff B)
    {a b N X : ℝ} (ha : 0 < a) (hab : a ≤ b) (hN : 0 < N) (hX : 0 < X)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hl₁ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₁ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (hl₂ : ∀ k ∈ primeSplitProductSupport (auxiliaryPrimes B), w₂ (k/N) ≠ 0 →
      Real.log k/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (w : 𝓢(ℝ,ℝ)) (c : ℂ) :
    let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
    let β := N/((j : ℝ)*X)
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    fullSmallMajorArcModel B j X Q
      (fun θ => endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
        endpointFourierSum B a b N (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
      (fun ξ => c*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))-
      (c/j)*sampledEndpointKernel m B j Q J g h w₁ w₂ N β w =
      (c/j)*∑ q ∈ positiveDenominators Q, ((μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))*
        manuscriptSampledIntegralError m B (j*(q : ℕ)) J g h F G
          (fun r => r.val.Coprime (q : ℕ)) w := by
  dsimp only
  let J := histogramWindowCells (channelFineCount m B) (Real.log (a*N)/B) (Real.log (b*N)/B)
  let β := N/((j : ℝ)*X)
  let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
  let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
  rw [fullSmallMajorArcModel_scalar_denominators hQ,sampledEndpointKernel_eq,
    ← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro q hq
  rw [← mul_sub]
  congr 1
  have hd : j*(q : ℕ) ≤ auxiliaryCutoff B :=
    (Nat.mul_le_mul_left j ((mem_positiveDenominators Q q).mp hq)).trans hcut
  have he := endpoint_integral_replacement (m := m) (q := j*(q : ℕ)) hm hB hd
    ha hab hN g h hg hh w₁ w₂ hM₁ hM₂ hw₁ hw₂ hs₁ hs₂ hl₁ hl₂ β
    (fun r => r.val.Coprime (q : ℕ)) w
  have hfreq (ξ : ℝ) : β*ξ/N = ξ/((j : ℝ)*X) := by
    dsimp [β]
    field_simp
  simp only [hfreq] at he
  exact he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RetainedErrorSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual retained-denominator error weights -/

namespace JointDickman
open Finset Filter
open scoped Topology ArithmeticFunction.Moebius

theorem sum_positiveDenominators_Icc {E : Type*} [AddCommMonoid E] (Q : ℕ)
    (f : ℕ → E) :
    (∑ q ∈ positiveDenominators Q, f (q : ℕ)) = ∑ q ∈ Icc 1 Q, f q := by
  classical
  calc
    _ = ∑ q ∈ (range (Q+1)).filter (fun n => 0 < n), f q := sum_subtype_eq_sum_filter f
    _ = _ := by congr 1; ext n; simp; omega

theorem retainedErrorSum_bound (B j Q : ℕ) (E : ℕ+ → ℂ)
    {A : ℝ} (_hA : 0 ≤ A)
    (hE : ∀ q ∈ positiveDenominators Q,
      ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*A) :
    ‖retainedErrorSum B j Q E‖ ≤ ((B : ℝ)/j)*kernelDenominatorSum j Q*A := by
  have hw (q : ℕ+) : ‖(μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ)‖ ≤ 1/((q : ℕ).totient : ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ))
  have hs : (∑ q ∈ positiveDenominators Q, ‖((μ (q : ℕ) : ℂ)/(q : ℕ).totient)*E q‖) ≤
      kernelDenominatorSum j Q*A := by
    calc
      _ ≤ ∑ q ∈ positiveDenominators Q,
          (1/((q : ℕ).totient : ℝ))*(((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*A) := by
        apply sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul (hw q) (hE q hq) (norm_nonneg _) (by positivity)
      _ = kernelDenominatorSum j Q*A := by
        simp_rw [← mul_assoc]
        rw [← sum_mul,sum_positiveDenominators_Icc Q
          (fun n : ℕ => (1/(n.totient : ℝ))*((j*n : ℕ)/(Nat.totient (j*n) : ℝ)))]
        rfl
  unfold retainedErrorSum
  rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hs) (by positivity)).trans_eq (by ring)

theorem retainedErrorSum_vanishing
    (hMP : PublishedInputs.PrimeProductMertensInput) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j Q : ℕ, 0 < j → 0 < Q → j*Q ≤ B^15 →
      ∀ T C : ℝ, 0 ≤ T → 0 ≤ C → η*T ≤ j → ∀ E : ℕ+ → ℂ,
      (∀ q ∈ positiveDenominators Q,
        ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*(C/B)*
          ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) →
      T*‖retainedErrorSum B j Q E‖ ≤ C*ε B := by
  obtain ⟨ε,hε,he⟩ := histogram_residue_denominator_decay hMP hη
  refine ⟨ε,hε,?_⟩
  intro m hm
  filter_upwards [he m hm,eventually_ge_atTop 1] with B hb hB
  intro j Q hj hQ hscale T C hT hC hlag E hE
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlocal : ∀ q ∈ positiveDenominators Q,
      ‖E q‖ ≤ ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*
        ((C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) := by
    intro q hq
    exact (hE q hq).trans_eq (by ring)
  have hbound := retainedErrorSum_bound B j Q E
    (show 0 ≤ (C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) by
      unfold channelMesh; positivity) hlocal
  calc
    _ ≤ T*(((B : ℝ)/j)*kernelDenominatorSum j Q*
        ((C/B)*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))))) :=
      mul_le_mul_of_nonneg_left hbound hT
    _ = C*((T/j)*kernelDenominatorSum j Q*
        ((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ)))) := by
      field_simp
    _ ≤ C*ε B := mul_le_mul_of_nonneg_left (hb j Q T hj hQ hT hlag hscale) hC

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HistogramLossBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform small loss for the bounded major-arc frequency slope -/

namespace JointDickman

theorem histogram_frequency_loss_bound {B m : ℕ} (hB : 1 ≤ B)
    {M₁ M₂ D₁ D₂ b R β : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hb : 0 ≤ b) (hR : 0 ≤ R) (hβ : |β| ≤ R) :
    let L₁ := (D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))
    let L₂ := (D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1))
    let K := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))+2*M₁*M₂
    2*channelMesh (channelFineCount m B)*(L₁*M₂+M₁*L₂)+2*M₁*M₂*(B : ℝ)^(-(1/80 : ℝ)) ≤
      K*((B : ℝ)*channelMesh (channelFineCount m B)+(B : ℝ)^(-(1/200 : ℝ))) := by
  dsimp only
  let C := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  have hδ : 0 ≤ channelMesh (channelFineCount m B) := by unfold channelMesh; positivity
  have hL₁ : D₁+2*Real.pi*|β| * M₁ ≤ D₁+2*Real.pi*R*M₁ := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 2*Real.pi)) hM₁)
  have hL₂ : D₂+2*Real.pi*|β| * M₂ ≤ D₂+2*Real.pi*R*M₂ := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 2*Real.pi)) hM₂)
  have hlin : 2*channelMesh (channelFineCount m B)*
      ((D₁+2*Real.pi*|β| * M₁)*((B : ℝ)*(b*Real.exp 1))*M₂+
        M₁*((D₂+2*Real.pi*|β| * M₂)*((B : ℝ)*(b*Real.exp 1)))) ≤
      C*((B : ℝ)*channelMesh (channelFineCount m B)) := by
    calc
      _ ≤ 2*channelMesh (channelFineCount m B)*
          ((D₁+2*Real.pi*R*M₁)*((B : ℝ)*(b*Real.exp 1))*M₂+
            M₁*((D₂+2*Real.pi*R*M₂)*((B : ℝ)*(b*Real.exp 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL₁ (by positivity)) hM₂)
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL₂ (by positivity)) hM₁)
      _ = _ := by dsimp [C] <;> ring
  have hpow : (B : ℝ)^(-(1/80 : ℝ)) ≤ (B : ℝ)^(-(1/200 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB) (by norm_num)
  calc
    _ ≤ C*((B : ℝ)*channelMesh (channelFineCount m B))+2*M₁*M₂*(B : ℝ)^(-(1/200 : ℝ)) :=
      add_le_add hlin (mul_le_mul_of_nonneg_left hpow (by positivity))
    _ ≤ _ := by
      change _ ≤ (C+2*M₁*M₂)*_
      nlinarith [mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg B) (-(1/200 : ℝ))),
        mul_nonneg (show 0 ≤ 2*M₁*M₂ by positivity)
          (mul_nonneg (Nat.cast_nonneg B) hδ)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedGeometricError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The same vanishing error with bounded box-dependent coefficient weights -/

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology SchwartzMap

theorem weighted_geometric_retained_error_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    {D : ℝ} (hD : 0 ≤ D) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 ≤ T → η*T ≤ j → ∀ S : Finset ℤ,
      ∀ d : ℤ → ℂ, (∀ k ∈ S, ‖d k‖ ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖retainedErrorSum B j Q
        (fun q => weightedGeometricDenominatorError m B j q a b t (T/j) S d g h w₁ w₂ w)‖ ≤ ε B := by
  obtain ⟨C,hC,hgeo⟩ := geometric_sampled_integral_error_sum_jd hSD hSW hM hMP
  obtain ⟨ε,hε,hden⟩ := retainedErrorSum_vanishing hMP hη
  let R := 1/η
  let K := 2*(b*Real.exp 1)*((D₁+2*Real.pi*R*M₁)*M₂+M₁*(D₂+2*Real.pi*R*M₂))+2*M₁*M₂
  let W := ∫ ξ : ℝ, ‖testFourierTransform w ξ‖*(1+|ξ|)
  let C₀ := D*((Real.log b-Real.log a+2)*C*((1+Real.log b-Real.log a)/t+1)*K*W)
  have hb : 0 < b := ha.trans_le hab
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hK : 0 ≤ K := by dsimp [K,R] <;> positivity
  have hW : 0 ≤ W := integral_nonneg (fun ξ => by positivity)
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    have : 0 ≤ Real.log b-Real.log a+2 := by linarith
    have : 0 ≤ 1+Real.log b-Real.log a := by linarith
    positivity
  refine ⟨fun B => C₀*ε B,by simpa using hε.const_mul C₀,?_⟩
  intro m hm
  filter_upwards [hgeo m hm,hden m hm,eventually_ge_atTop 1] with B hgeoB hdenB hB
  intro j _ Q hQ hscale T hT hlag S d hd g h hg hh
  have hj : 0 < j := NeZero.pos j
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hβ : |T/(j : ℝ)| ≤ R := by
    rw [abs_of_nonneg (div_nonneg hT hj0.le)]
    apply (div_le_div_iff₀ hj0 hη).mpr
    simpa only [one_mul,mul_one,mul_comm] using hlag
  have hBpow : B ≤ B^15 := Nat.le_pow (by omega)
  apply hdenB j Q hj hQ (hscale.trans hBpow) T C₀ hT hC₀ hlag
  intro q hq
  have hjq : j*(q : ℕ) ≤ B := (Nat.mul_le_mul_left j ((mem_positiveDenominators Q q).mp hq)).trans hscale
  have he := hgeoB (j*(q : ℕ)) hjq a b t ha hab ht S g h hg hh
    w₁ w₂ w₁' w₂' M₁ M₂ D₁ D₂ (T/j) hM₁ hM₂ hD₁ hD₂
    hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ (fun r => r.val.Coprime (q : ℕ)) w
  have hloss := histogram_frequency_loss_bound (m := m) hB hM₁ hM₂ hD₁ hD₂ hb.le
    (show 0 ≤ R by dsimp [R] <;> positivity) hβ
  let P := ((j*(q : ℕ) : ℕ)/(Nat.totient (j*(q : ℕ)) : ℝ))*
    ((Real.log b-Real.log a+2)/B)*C*((1+Real.log b-Real.log a)/t+1)
  have hP : 0 ≤ P := by
    dsimp [P]
    have : 0 ≤ Real.log b-Real.log a+2 := by linarith
    have : 0 ≤ 1+Real.log b-Real.log a := by linarith
    positivity
  have hs := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloss hP) hW
  have hweighted : ‖weightedGeometricDenominatorError m B j q a b t (T/j) S d g h w₁ w₂ w‖ ≤
      D*(∑ k ∈ S, ‖manuscriptSampledIntegralError m B (j*(q : ℕ))
        (geometricHistogramWindow m B t (Real.log a) (Real.log b) k) g h
        (fun ξ => logOscillatoryTest w₁ B (Real.exp ((k : ℝ)*t)) ((T/j)*ξ))
        (fun ξ => logOscillatoryTest w₂ B (Real.exp ((k : ℝ)*t)) (-(T/j)*ξ))
        (fun r => r.val.Coprime (q : ℕ)) w‖) := by
    unfold weightedGeometricDenominatorError
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hd k hk) (norm_nonneg _)
  exact (hweighted.trans (mul_le_mul_of_nonneg_left (he.trans hs) hD)).trans_eq
    (by dsimp [P,C₀,K,W,R] <;> ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricFullModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact box-summed replacement in the full retained-arc model -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

theorem geometric_full_model_replacement {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hQ : Q ≤ B^12) (hcut : j*Q ≤ auxiliaryCutoff B)
    {a b T t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T)
    (S : Finset ℤ) (d : ℤ → ℂ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hl₁ : ∀ k ∈ S, ∀ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      w₁ (n/Real.exp ((k : ℝ)*t)) ≠ 0 → Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (hl₂ : ∀ k ∈ S, ∀ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      w₂ (n/Real.exp ((k : ℝ)*t)) ≠ 0 → Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (w : 𝓢(ℝ,ℝ)) :
    geometricFullModelDifference m B j Q a b T t S d g h w₁ w₂ w =
      retainedErrorSum B j Q (fun q => weightedGeometricDenominatorError m B j q
        a b t (T/j) S d g h w₁ w₂ w) := by
  unfold geometricFullModelDifference
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hβ (k : ℤ) : Real.exp ((k : ℝ)*t)/((j : ℝ)*(Real.exp ((k : ℝ)*t)/T)) = T/j := by
    field_simp
  have hJ (k : ℤ) : histogramWindowCells (channelFineCount m B)
      (Real.log (a*Real.exp ((k : ℝ)*t))/B) (Real.log (b*Real.exp ((k : ℝ)*t))/B) =
      geometricHistogramWindow m B t (Real.log a) (Real.log b) k := by
    simp only [geometricHistogramWindow,Real.log_mul ha.ne' (Real.exp_ne_zero _),
      Real.log_mul (ha.trans_le hab).ne' (Real.exp_ne_zero _),Real.log_exp]
    congr 2 <;> ring
  have he (k : ℤ) (hk : k ∈ S) := endpoint_full_model_replacement hm hB hQ hcut ha hab
    (Real.exp_pos ((k : ℝ)*t)) (div_pos (Real.exp_pos ((k : ℝ)*t)) hT) g h hg hh w₁ w₂ hM₁ hM₂
    hw₁ hw₂ hs₁ hs₂ (hl₁ k hk) (hl₂ k hk) w (d k)
  simp only [hβ,hJ] at he
  rw [sum_congr rfl he]
  unfold retainedErrorSum weightedGeometricDenominatorError
  simp only [div_eq_mul_inv,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro k _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BoundedBoxFullModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full retained-arc model is uniformly approximated by the sampled log kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem bounded_box_full_model_vanishing
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℂ, (∀ k ∈ S, ‖d k‖ ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖geometricFullModelDifference m B j Q a b T t S d g h w₁ w₂ w‖ ≤ ε B := by
  obtain ⟨ε,hε,he⟩ := weighted_geometric_retained_error_vanishing hSD hSW hM hMP
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hD
  refine ⟨ε,hε,?_⟩
  intro m hm
  filter_upwards [he m hm,endpoint_support_log_bounds ha hab,eventually_ge_atTop 1]
    with B heB hsupport hB
  intro j _ Q hQ hscale T hT hlag S hbox d hd g h hg hh
  have hBpos : 0 < B := by omega
  have hQbound : Q ≤ B^12 :=
    ((Nat.le_mul_of_pos_left Q (NeZero.pos j)).trans hscale).trans (Nat.le_pow (by norm_num))
  have hpow : B ≤ B^1000 := le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  have hcut : j*Q ≤ auxiliaryCutoff B := by
    change j*Q ≤ B^1000
    exact Nat.le_trans hscale hpow
  have hlocal (v : ℝ → ℝ) (hs : ∀ x, x ≤ a ∨ b < x → v x = 0)
      (k : ℤ) (hk : k ∈ S) (n : ℕ) (_hn : n ∈ primeSplitProductSupport (auxiliaryPrimes B))
      (hw : v (n/Real.exp ((k : ℝ)*t)) ≠ 0) : Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3 := by
    have hinside : a < (n : ℝ)/Real.exp ((k : ℝ)*t) ∧
        (n : ℝ)/Real.exp ((k : ℝ)*t) ≤ b := by
      constructor
      · by_contra h
        exact hw (hs _ (Or.inl (le_of_not_gt h)))
      · by_contra h
        exact hw (hs _ (Or.inr (lt_of_not_ge h)))
    apply hsupport _ (Real.exp_pos _) (by simpa only [Real.log_exp] using hbox k hk) n
      hinside.1 hinside.2
  rw [geometric_full_model_replacement hm hBpos hQbound hcut ha hab hT S _ g h hg hh
    w₁ w₂ hM₁ hM₂ hwb₁ hwb₂ hs₁ hs₂ (hlocal w₁ hs₁) (hlocal w₂ hs₂) w]
  exact heB j Q hQ hscale T hT.le hlag S d hd g h hg hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FineGridKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Schur bounds for the narrow logarithmic kernel on the fine grid -/

namespace JointDickman
open Finset

theorem fineGridKernel_row_bound {n : ℕ} (hn : 0 < n)
    (K : Fin n → Fin n → ℝ) {B C M : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmesh : B*channelMesh n ≤ 1)
    (hK : ∀ i j, |K i j| ≤ M*B)
    (hsupp : ∀ i j, K i j ≠ 0 →
      |channelLower n i-channelLower n j| ≤ C/B) (i : Fin n) :
    (∑ j, channelMesh n*|K i j|) ≤ 2*M*(C+1) := by
  classical
  let J := histogramWindowCells n (channelLower n i-C/B) (channelLower n i+C/B)
  have hr : 0 ≤ C/B := div_nonneg hC hB.le
  have hlen := histogramWindowCells_length hn (show channelLower n i-C/B ≤
    channelLower n i+C/B by linarith)
  have he : (∑ j, channelMesh n*|K i j|) = ∑ j ∈ J, channelMesh n*|K i j| := by
    apply Eq.symm
    apply sum_subset (subset_univ J)
    intro j _ hj
    have hk : K i j = 0 := by
      by_contra hk
      have hb := abs_le.mp (hsupp i j hk)
      have hw := channel_width n j
      apply hj
      simp only [J,histogramWindowCells,mem_filter,mem_univ,true_and]
      constructor <;> linarith [channelMesh_pos hn]
    simp [hk]
  rw [he]
  calc
    _ ≤ ∑ _j ∈ J, channelMesh n*(M*B) :=
      sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hK i j) (channelMesh_pos hn).le)
    _ = ((J.card : ℝ)*channelMesh n)*(M*B) := by
      rw [sum_const,nsmul_eq_mul]
      ring
    _ ≤ (2*(C/B)+2*channelMesh n)*(M*B) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hM hB.le)
      exact hlen.trans_eq (by ring)
    _ = 2*M*(C+B*channelMesh n) := by field_simp
    _ ≤ 2*M*(C+1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem fineGridKernel_schur {n : ℕ} (hn : 0 < n)
    (K : Fin n → Fin n → ℝ) {B C M : ℝ}
    (hB : 0 < B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hmesh : B*channelMesh n ≤ 1)
    (hK : ∀ i j, |K i j| ≤ M*B)
    (hsupp : ∀ i j, K i j ≠ 0 →
      |channelLower n i-channelLower n j| ≤ C/B) :
    (∀ i, (∑ j, channelMesh n*|K i j|) ≤ 2*M*(C+1)) ∧
    (∀ j, (∑ i, channelMesh n*|K i j|) ≤ 2*M*(C+1)) := by
  refine ⟨fineGridKernel_row_bound hn K hB hC hM hmesh hK hsupp,?_⟩
  apply fineGridKernel_row_bound hn (fun i j => K j i) hB hC hM hmesh (fun i j => hK j i)
  intro i j hij
  simpa only [abs_sub_comm] using hsupp j i hij

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LogMassBilinear
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse approximation for the actual logarithmic mass kernel -/

namespace JointDickman
open Finset Filter

theorem cellMassBilinear_reindex (m B : ℕ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (U V : Fin m × Fin (channelBlockCount m B) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hu : ∀ a, u (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*U a)
    (hv : ∀ a, v (channelIndexEquiv m B a) = channelMesh (channelFineCount m B)*V a) :
    cellMassBilinear m B u v K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b)) U V := by
  unfold cellMassBilinear finiteKernelBilinear finiteKernelAction
  rw [← (channelIndexEquiv m B).sum_comp]
  apply sum_congr rfl
  intro a _
  rw [← (channelIndexEquiv m B).sum_comp]
  simp only [hu,hv,mul_sum]
  apply sum_congr rfl
  intro b _
  ring

theorem logMassBilinear_reindex {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
        (groupedManuscriptChannel m B g) (groupedManuscriptChannel m B h) :=
  cellMassBilinear_reindex m B _ _ _ _ K
    (fun a => (groupedManuscriptChannel_log_mass hm hB g a).symm)
    (fun a => (groupedManuscriptChannel_log_mass hm hB h a).symm)

theorem coarseLogMassBilinear_reindex (m B : ℕ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K =
      finiteKernelBilinear (fun _ => channelMesh (channelFineCount m B))
        (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
        (coarseGroupAverage (groupedManuscriptChannel m B g))
        (coarseGroupAverage (groupedManuscriptChannel m B h)) := by
  apply cellMassBilinear_reindex
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]
  · intro a
    simp only [coarseLogMass,Equiv.symm_apply_apply]

/-- The actual logarithmic signed measures admit a fixed coarse approximation
uniformly over every kernel of height O(B) and width O(1/B). -/
theorem logMassBilinear_coarse_band
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ,
      ∀ C M : ℝ, 0 ≤ C → 0 ≤ M →
      (∀ i k, |K i k| ≤ M*B) →
      (∀ i k, K i k ≠ 0 → |channelLower (channelFineCount m B) i-
        channelLower (channelFineCount m B) k| ≤ C/B) →
      |cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K-
        cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K| ≤
        (2*M*(C+1))*ε := by
  obtain ⟨m,hm,hcoarse⟩ := groupedManuscriptChannel_bilinear_coarse hSD hSW hM hMP hε
  refine ⟨m,hm,?_⟩
  filter_upwards [hcoarse,eventually_ge_atTop 1] with B hc hB
  intro g h hg hh K C M hC hM' hK hsupp
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hrpow : (B : ℝ)^(-(1/10 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (-(1/10 : ℝ)) ≤ 0)
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans hrpow
  obtain ⟨hrow,hcol⟩ := fineGridKernel_schur (channelFineCount_pos hm hBpos) K
    hB0 hC hM' hmesh hK hsupp
  have hrow' (a : Fin m × Fin (channelBlockCount m B)) :
      (∑ b, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ 2*M*(C+1) := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun k => channelMesh (channelFineCount m B)*|K (channelIndexEquiv m B a) k|)]
    exact hrow _
  have hcol' (b : Fin m × Fin (channelBlockCount m B)) :
      (∑ a, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ 2*M*(C+1) := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun i => channelMesh (channelFineCount m B)*|K i (channelIndexEquiv m B b)|)]
    exact hcol _
  rw [logMassBilinear_reindex hm hBpos,coarseLogMassBilinear_reindex]
  exact hc g h hg hh _ (2*M*(C+1)) (by positivity) hrow' hcol'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GeometricWindowKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The summed geometric windows form a uniformly bounded narrow kernel -/

namespace JointDickman
open Finset Filter

theorem geometricWindow_pair_distance {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U : ℝ} {k : ℤ} {i j : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
      (U-L+1)/B := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hwi := channel_width (channelFineCount m B) i
  have hwj := channel_width (channelFineCount m B) j
  have hilo := (div_le_iff₀ hBr).mp hi'.2
  have hihi := (le_div_iff₀ hBr).mp hi'.1
  have hjlo := (div_le_iff₀ hBr).mp hj'.2
  have hjhi := (le_div_iff₀ hBr).mp hj'.1
  apply abs_le.mpr
  constructor
  · have hh : channelLower (channelFineCount m B) j-
        channelLower (channelFineCount m B) i ≤ (U-L+1)/B := by
      apply (le_div_iff₀ hBr).mpr
      nlinarith
    linarith
  · apply (le_div_iff₀ hBr).mpr
    nlinarith

theorem geometricWindowKernel_bounds {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U M : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hM : 0 ≤ M)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ M) :
    (∀ i j, |geometricWindowKernel m B t L U S V i j| ≤ (((1+U-L)/t+1)*M)*B) ∧
    (∀ i j, geometricWindowKernel m B t L U S V i j ≠ 0 →
      |channelLower (channelFineCount m B) i-channelLower (channelFineCount m B) j| ≤
        (U-L+1)/B) := by
  classical
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0))
  constructor
  · intro i j
    let A := S.filter (fun k => i ∈ geometricHistogramWindow m B t L U k)
    have hcard : (A.card : ℝ) ≤ (1+U-L)/t+1 :=
      (histogramWindow_overlap hBr ht hLU (channelFineCount_pos hm hBpos) S i).trans
        (by gcongr)
    have hterm (k : ℤ) (hk : k ∈ S) :
        |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| ≤
          if i ∈ geometricHistogramWindow m B t L U k then M else 0 := by
      by_cases hi : i ∈ geometricHistogramWindow m B t L U k
      · by_cases hj : j ∈ geometricHistogramWindow m B t L U k
        · simpa only [hi,hj,and_self,ite_true, if_true] using hV k hk i j
        · simpa [hi,hj] using hM
      · simp [hi]
    unfold geometricWindowKernel
    rw [abs_mul,abs_of_pos hBr]
    calc
      _ ≤ (B : ℝ)*∑ k ∈ S, |(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hBr.le
      _ ≤ (B : ℝ)*∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k then M else 0 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) hBr.le
      _ = (B : ℝ)*((A.card : ℝ)*M) := by rw [← sum_filter,sum_const,nsmul_eq_mul]
      _ ≤ (B : ℝ)*(((1+U-L)/t+1)*M) := by gcongr
      _ = _ := by ring
  · intro i j hne
    have hs : (∑ k ∈ S, if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then V k i j else 0) ≠ 0 := by
      intro hs
      exact hne (by simp [geometricWindowKernel,hs])
    obtain ⟨k,_hk,hkv⟩ := exists_ne_zero_of_sum_ne_zero hs
    have hij : i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k := by
      by_contra h
      exact hkv (ite_eq_right h)
    exact geometricWindow_pair_distance hm hB hij.1 hij.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricCoarseKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse comparison for the actual box-summed spatial kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem endpointSpatialWeight_bound (m B : ℕ) (t β : ℝ) (S : Finset ℤ)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ x, |w₁ x| ≤ M₁)
    (hw₂ : ∀ x, |w₂ x| ≤ M₂) (hw : ∀ x, |w x| ≤ M) :
    ∀ k ∈ S, ∀ i j, |endpointSpatialWeight m B t β d w₁ w₂ w k i j| ≤ D*M₁*M₂*M := by
  intro k hk i j
  unfold endpointSpatialWeight
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul (hd k hk) (hw₁ _) (abs_nonneg _) hD)
    (hw₂ _) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg hD hM₁) hM₂)

theorem geometricWindowKernel_bilinear (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (u v : Fin (channelFineCount m B) → ℝ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ) :
    cellMassBilinear m B u v (geometricWindowKernel m B t L U S V) =
      (B : ℝ)*∑ k ∈ S, ∑ i ∈ geometricHistogramWindow m B t L U k,
        ∑ j ∈ geometricHistogramWindow m B t L U k, u i*v j*V k i j := by
  classical
  unfold cellMassBilinear geometricWindowKernel
  simp_rw [mul_sum]
  have hterm (i j : Fin (channelFineCount m B)) (k : ℤ) :
      u i*v j*((B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then V k i j else 0)) =
      (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
        j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := by
    split_ifs <;> ring
  simp_rw [hterm]
  have hrestrict (k : ℤ) :
      (∑ i : Fin (channelFineCount m B), ∑ j : Fin (channelFineCount m B),
        (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0)) =
      ∑ i ∈ geometricHistogramWindow m B t L U k,
        ∑ j ∈ geometricHistogramWindow m B t L U k, (B : ℝ)*(u i*v j*V k i j) := by
    have hinner (i : Fin (channelFineCount m B)) :
        (∑ j : Fin (channelFineCount m B),
          (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
            j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0)) =
        if i ∈ geometricHistogramWindow m B t L U k then
          ∑ j ∈ geometricHistogramWindow m B t L U k, (B : ℝ)*(u i*v j*V k i j) else 0 := by
      by_cases hi : i ∈ geometricHistogramWindow m B t L U k
      · simp only [hi,true_and,ite_true, if_true,mul_ite,mul_zero]
        rw [← sum_filter]
        simp
      · simp [hi]
    simp_rw [hinner]
    rw [← sum_filter]
    simp
  calc
    _ = ∑ i : Fin (channelFineCount m B), ∑ k ∈ S,
        ∑ j : Fin (channelFineCount m B), (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ k ∈ S, ∑ i : Fin (channelFineCount m B),
        ∑ j : Fin (channelFineCount m B), (B : ℝ)*(if i ∈ geometricHistogramWindow m B t L U k ∧
          j ∈ geometricHistogramWindow m B t L U k then u i*v j*V k i j else 0) := sum_comm
    _ = _ := sum_congr rfl (fun k _ => hrestrict k)

theorem sampledLogKernel_real (m B : ℕ)
    (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (a b x y : Fin (channelFineCount m B) → ℝ) (w : 𝓢(ℝ,ℝ)) :
    sampledLogKernel m B J J g h (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) x y w =
      ((∑ i ∈ J, ∑ j ∈ J, logCellSignedMass m B g i*logCellSignedMass m B h j*
        (a i*b j*w (x i-y j)) : ℝ) : ℂ) := by
  unfold sampledLogKernel
  push_cast
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem geometricSpatialKernel_coarse
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε t L U D M₁ M₂ M : ℝ} (hε : 0 < ε) (ht : 0 < t) (hLU : L ≤ U)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M)
    (w₁ w₂ w : ℝ → ℝ) (hw₁ : ∀ x, |w₁ x| ≤ M₁)
    (hw₂ : ∀ x, |w₂ x| ≤ M₂) (hw : ∀ x, |w x| ≤ M) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℤ, ∀ β : ℝ,
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let K := geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)
      |cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K-
        cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K| ≤
        2*(((1+U-L)/t+1)*(D*M₁*M₂*M))*(U-L+2)*ε := by
  obtain ⟨m,hm,he⟩ := logMassBilinear_coarse_band hSD hSW hM hMP hε
  refine ⟨m,hm,?_⟩
  filter_upwards [he,eventually_ge_atTop 1] with B heB hB
  intro S β d hd g h hg hh
  dsimp only
  have hV := endpointSpatialWeight_bound m B t β S d w₁ w₂ w hD hM₁ hM₂ hd hw₁ hw₂ hw
  have hbound := geometricWindowKernel_bounds hm hB ht hLU
    (show 0 ≤ D*M₁*M₂*M by positivity) S _ hV
  have hwidth : 0 ≤ 1+U-L := by linarith
  have hover : 0 ≤ ((1+U-L)/t+1)*(D*M₁*M₂*M) := by positivity
  have hs := heB g h hg hh _ (U-L+1) (((1+U-L)/t+1)*(D*M₁*M₂*M))
    (by linarith) hover hbound.1 hbound.2
  exact hs.trans_eq (by congr 1; ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricKernelIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the sampled arc expression with the real spatial kernel -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem geometric_sampled_kernel_identity (m B : ℕ) (t L U β : ℝ)
    (S : Finset ℤ) (d : ℤ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    (B : ℂ)*(∑ k ∈ S, (d k : ℂ)*sampledEndpointLogKernel m B
      (geometricHistogramWindow m B t L U k) g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w) =
    (cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h)
      (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) : ℂ) := by
  rw [geometricWindowKernel_bilinear]
  push_cast
  congr 1
  apply sum_congr rfl
  intro k _
  unfold sampledEndpointLogKernel
  rw [sampledLogKernel_real]
  push_cast
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  unfold endpointSpatialWeight
  push_cast
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FullSpatialComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the full retained-arc sum to the actual spatial log kernel -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap ArithmeticFunction.Moebius

theorem geometricFullModelDifference_eq (m B j Q : ℕ) [NeZero j]
    (a b T t : ℝ) (S : Finset ℤ) (d : ℤ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    geometricFullModelDifference m B j Q a b T t S (fun k => (d k : ℂ)) g h w₁ w₂ w =
      geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*sampledEndpointKernel m B j Q
          (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w := by
  unfold geometricFullModelDifference geometricFullArcSum
  rw [sum_sub_distrib,mul_sub]
  congr 1
  simp only [mul_sum]
  apply sum_congr rfl
  intro k _
  ring

theorem geometric_full_spatial_error_split (m B j Q : ℕ) [NeZero j]
    (a b T t : ℝ) (S : Finset ℤ) (d : ℤ → ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) :
    geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
      ((singularSeries j : ℂ)/j)*
        (cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h)
          (geometricWindowKernel m B t (Real.log a) (Real.log b) S
            (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)) : ℂ) =
      geometricFullModelDifference m B j Q a b T t S (fun k => (d k : ℂ)) g h w₁ w₂ w+
      ((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
        (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
            g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w-
          (singularSeries j : ℂ)*sampledEndpointLogKernel m B
            (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
            g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w) := by
  rw [geometricFullModelDifference_eq,← geometric_sampled_kernel_identity]
  simp only [mul_sub,sum_sub_distrib,mul_sum]
  have hscalar :
      (∑ k ∈ S, (B : ℂ)/j*((d k : ℂ)*((singularSeries j : ℂ)*sampledEndpointLogKernel m B
        (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w))) =
      ∑ k ∈ S, ((singularSeries j : ℂ)/j)*((B : ℂ)*((d k : ℂ)*sampledEndpointLogKernel m B
        (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w)) := by
    apply sum_congr rfl
    intro k _
    ring
  rw [hscalar]
  ring


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BoundedBoxSpatial
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spatial comparison with bounded, varying box weights -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem bounded_box_spatial_comparison
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h)
            (geometricWindowKernel m B t (Real.log a) (Real.log b) S
              (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)) : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1) := by
  obtain ⟨ε,hε,hfull⟩ := bounded_box_full_model_vanishing hSD hSW hM hMP hD
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  obtain ⟨C,hC,hseries⟩ := geometric_singularSeries_error_jd hSD hSW hM hMP ht hlogs
    w₁ w₂ w hM₁ hM₂ hwb₁ hwb₂
  refine ⟨D*C,mul_nonneg hD hC,ε,hε,?_⟩
  intro m hm
  filter_upwards [hfull m hm,hseries m hm,eventually_ge_atTop 1]
    with B hf hs hB
  intro j _ Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  have hcut : j*Q ≤ auxiliaryCutoff B := by
    exact hscale.trans (le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0))
  have hfirst := hf j Q hQ hscale T hT hlag S hbox (fun k => (d k : ℂ))
    (fun k hk => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hdbound k hk) g h hg hh
  have hsecond := hs j Q hcut S (T/j) D hD d hdbound g h hg hh
  rw [geometric_full_spatial_error_split]
  calc
    _ ≤ T*‖geometricFullModelDifference m B j Q a b T t S (fun k => (d k : ℂ)) g h w₁ w₂ w‖+
        T*‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
          (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
              g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w-
            (singularSeries j : ℂ)*sampledEndpointLogKernel m B
              (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
              g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w)‖ := by
      exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) hT.le).trans_eq (mul_add _ _ _)
    _ ≤ ε B+T*((D*C)*(((j : ℝ)/j.totient)/j)*singularSeriesTail (Q+1)) :=
      add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hT.le)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BoundedBoxCoarse
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained-arc kernel has a fixed finite coarse approximation -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem bounded_box_coarse_comparison_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {D : ℝ} (hD : 0 ≤ D)
    {a b t η : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hη : 0 < η)
    (w₁ w₂ w₁' w₂' : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ D₁ D₂ M₀ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hM₀ : 0 ≤ M₀)
    (hw₁ : ∀ x, HasDerivAt w₁ (w₁' x) x) (hw₂ : ∀ x, HasDerivAt w₂ (w₂' x) x)
    (hwb₁ : ∀ x, |w₁ x| ≤ M₁) (hwb₂ : ∀ x, |w₂ x| ≤ M₂)
    (hwd₁ : ∀ x, |w₁' x| ≤ D₁) (hwd₂ : ∀ x, |w₂' x| ≤ D₂)
    (hwb₀ : ∀ x, |w x| ≤ M₀)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
 :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, 0 < Q → j*Q ≤ B →
      ∀ T : ℝ, 0 < T → η*T ≤ j → ∀ S : Finset ℤ,
      (∀ k ∈ S, (k : ℝ)*t ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B)) →
      ∀ d : ℤ → ℝ, (∀ k ∈ S, |d k| ≤ D) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
      T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*
          (cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K : ℂ)‖ ≤
        ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1)+δ*(T/j)*singularSeries j := by
  obtain ⟨C,hC,ε,hε,hfull⟩ := bounded_box_spatial_comparison hSD hSW hM hMP hD
    ha hab ht hη w₁ w₂ w₁' w₂' w hM₁ hM₂ hD₁ hD₂ hw₁ hw₂ hwb₁ hwb₂ hwd₁ hwd₂ hs₁ hs₂
  refine ⟨C,hC,ε,hε,?_⟩
  intro δ hδ
  let A := 2*(((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀))*(Real.log b-Real.log a+2)
  have hlogs : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hwidth : 0 ≤ 1+Real.log b-Real.log a := by linarith
  have hwidth' : 0 ≤ Real.log b-Real.log a+2 := by linarith
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have he : 0 < δ/(A+1) := div_pos hδ (by linarith)
  obtain ⟨m,hm,hcoarse⟩ := geometricSpatialKernel_coarse hSD hSW hM hMP he ht hlogs
    hD hM₁ hM₂ hM₀ w₁ w₂ w hwb₁ hwb₂ hwb₀
  refine ⟨m,hm,?_⟩
  filter_upwards [hfull m hm,hcoarse,eventually_ge_atTop 1]
    with B hf hb hB
  intro j _ Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  dsimp only
  let K := geometricWindowKernel m B t (Real.log a) (Real.log b) S
    (endpointSpatialWeight m B t (T/j) d w₁ w₂ w)
  let R := cellMassBilinear m B (logCellSignedMass m B g) (logCellSignedMass m B h) K
  let Rc := cellMassBilinear m B (coarseLogMass m B g) (coarseLogMass m B h) K
  have hclose : |R-Rc| ≤ δ := by
    have hb' : |R-Rc| ≤ A*(δ/(A+1)) := hb S (T/j) d hdbound g h hg hh
    refine hb'.trans ?_
    have he' : A/(A+1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    calc
      _ = δ*(A/(A+1)) := by ring
      _ ≤ δ*1 := mul_le_mul_of_nonneg_left he' hδ.le
      _ = δ := mul_one _
  have hSp : 0 ≤ singularSeries j := (singularSeries_bounds hMP j).1
  have hscalar : ‖((singularSeries j : ℂ)/j)*((R : ℂ)-(Rc : ℂ))‖ ≤
      (singularSeries j/(j : ℝ))*δ := by
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hSp,
      Complex.norm_natCast,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hclose (by positivity)
  have hf' := hf j Q hQ hscale T hT hlag S hbox d hdbound g h hg hh
  calc
    _ ≤ T*‖geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w-
        ((singularSeries j : ℂ)/j)*(R : ℂ)‖+
      T*‖((singularSeries j : ℂ)/j)*((R : ℂ)-(Rc : ℂ))‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub
        (geometricFullArcSum B j Q a b T t S d g h w₁ w₂ w)
        (((singularSeries j : ℂ)/j)*(R : ℂ)) (((singularSeries j : ℂ)/j)*(Rc : ℂ))
      rw [← mul_sub] at htri
      exact (mul_le_mul_of_nonneg_left htri hT.le).trans_eq (mul_add _ _ _)
    _ ≤ (ε B+C*(T/j)*((j : ℝ)/j.totient)*singularSeriesTail (Q+1))+
        T*((singularSeries j/(j : ℝ))*δ) :=
      add_le_add hf' (mul_le_mul_of_nonneg_left hscalar hT.le)
    _ = _ := by ring

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.bounded_box_coarse_comparison_jd_oai := @OAI.JointDickman.bounded_box_coarse_comparison_jd_oai
