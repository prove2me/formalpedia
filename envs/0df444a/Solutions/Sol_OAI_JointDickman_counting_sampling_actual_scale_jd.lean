-- Prove2me | solution 1 for OAI.JointDickman.counting_sampling_actual_scale_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:35:03.003209+00:00
-- url     : https://prove2.me/submissions/63329a27-d5a5-4913-8449-6f56aebe1132

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_counting_sampling_jd

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ParameterEstimates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem weightBaseExponent_pos : 0 < weightBaseExponent := by
  have h := Real.log_two_lt_d9
  unfold weightBaseExponent
  linarith

theorem weightExponent_mono : Monotone weightExponent := by
  intro a b hab
  unfold weightExponent
  have hmul := mul_le_mul_of_nonneg_right hab
    (Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num))
  linarith

theorem samplingTau_weight_margins :
    2 * weightExponent samplingTau < (32 / 100 : ℝ) ∧
      (7 / 100 : ℝ) < 1 - 6 * weightExponent samplingTau ∧
      (229 / 1000 : ℝ) < 1 - 5 * weightExponent samplingTau := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  unfold weightExponent weightBaseExponent samplingTau
  constructor
  · linarith
  constructor <;> linarith

/-- Every smaller nonnegative tolerance preserves the strict margins. -/
theorem weight_margins_of_le_samplingTau {τ : ℝ} (hτ : τ ≤ samplingTau) :
    2 * weightExponent τ < (32 / 100 : ℝ) ∧
      (7 / 100 : ℝ) < 1 - 6 * weightExponent τ ∧
      (229 / 1000 : ℝ) < 1 - 5 * weightExponent τ := by
  have hm := weightExponent_mono hτ
  obtain ⟨h₂, h₆, h₅⟩ := samplingTau_weight_margins
  constructor
  · linarith
  constructor <;> linarith

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

private theorem prime_site_probability_square_sum {α : Type*}
    (P : Finset α) (Q : Finset ℕ) :
    (∑ p : Q, (∑ _j ∈ P, 1 / (p.val : ℝ)) ^ 2) =
      (P.card : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  rw [show (∑ p : Q, (∑ _j ∈ P, 1 / (p.val : ℝ)) ^ 2) =
    ∑ p ∈ Q, (∑ _j ∈ P, 1 / (p : ℝ)) ^ 2 from
      Finset.sum_coe_sort Q (fun p => (∑ _j ∈ P, 1 / (p : ℝ)) ^ 2), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div, div_pow]

/-- For any bounded complex function of all prime hit sets, independent
Bernoulli replacement costs at most `2 L M² sum_p 1/p²`. -/
theorem categoricalPrimeProduct_test_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hcard : ∀ p ∈ Q, P.card ≤ p)
    (F : (Q → P.powerset) → ℂ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, ‖F x‖ ≤ L) :
    ‖(∑ x, (categoricalProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x : ℂ) * F x) -
      (∑ x, (bernoulliProductMass P (fun (p : Q) _ => 1 / (p.val : ℝ)) x : ℂ) * F x)‖ ≤
      2 * L * (P.card : ℝ) ^ 2 * ∑ p ∈ Q, 1 / (p : ℝ) ^ 2 := by
  classical
  have hq (p : Q) (j : α) (_hj : j ∈ P) :
      0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have hp := hQ p.val p.property
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast hp.pos
    have hp1 : (1 : ℝ) ≤ p.val := by exact_mod_cast hp.one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  have hs (p : Q) : (∑ _j ∈ P, 1 / (p.val : ℝ)) ≤ 1 := by
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast (hQ p.val p.property).pos
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact (div_le_one hp0).mpr (by exact_mod_cast hcard p.val p.property)
  have h := categoricalProduct_test_bound P (fun (p : Q) _ => 1 / (p.val : ℝ)) hq hs F hL hF
  rw [prime_site_probability_square_sum] at h
  simpa only [mul_assoc] using h

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ReciprocalTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

/-- The exact odds correction is bounded by an exponential of the
selected reciprocal mass, uniformly in the number of allowed primes. -/
theorem inverse_product_le_exp {ι : Type*} (P : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ P, 0 ≤ x i ∧ x i ≤ 1 / 2) :
    (∏ i ∈ P, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ P, x i) := by
  have hpoint (i : ι) (hi : i ∈ P) : (1 - x i)⁻¹ ≤ Real.exp (2 * x i) := by
    have hpos : 0 < 1 - x i := by linarith [(hx i hi).2]
    have herr := log_one_sub_add_error (hx i hi).1 (hx i hi).2
    have hlog : Real.log ((1 - x i)⁻¹) ≤ 2 * x i := by
      rw [Real.log_inv]
      have hmul := mul_nonneg (hx i hi).1 (show 0 ≤ 1 - 2 * x i by linarith [(hx i hi).2])
      nlinarith [(abs_le.mp herr).1]
    calc
      _ = Real.exp (Real.log ((1 - x i)⁻¹)) := (Real.exp_log (inv_pos.mpr hpos)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  calc
    _ ≤ ∏ i ∈ P, Real.exp (2 * x i) := Finset.prod_le_prod
      (fun i hi => inv_nonneg.mpr (by linarith [(hx i hi).2])) hpoint
    _ = Real.exp (∑ i ∈ P, 2 * x i) := (Real.exp_sum P (fun i => 2 * x i)).symm
    _ = _ := by rw [← mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact removal of the small prime factors

Removing a finite set of prime factors is an exact convolution identity.
The moving roughness cutoff is then controlled by Selberg–Delange estimates.
-/

namespace JointDickman

open ArithmeticFunction Finset

theorem smoothCorrection_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (smoothCorrection E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨smoothCorrection_one E z, fun {m n} hm hn _ => ?_⟩
  simp only [smoothCorrection, coe_mk, hm, hn, mul_ne_zero hm hn,
    ↓reduceIte, Nat.primeFactors_mul hm hn, union_subset_iff,
    cardFactors_mul hm hn, pow_add, ite_zero_mul_ite_zero]

theorem smoothCorrection_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    smoothCorrection E z (p ^ k) = if p ∈ E then (-z) ^ k else 0 := by
  rw [smoothCorrection, coe_mk, ite_eq_right (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow p hk, hp.primeFactors]
  simp [cardFactors_apply_prime_pow hp]

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

/-- Uniform logarithmic normalizer error, retaining both endpoint errors. -/
theorem primeNormalizer_log_error
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (Y z : ℝ), 2 ≤ N → (N : ℝ) ≤ Y →
      0 ≤ z → z ≤ 1 →
      |Real.log (primeNormalizer (largePrimeSet Y N) z) +
        z * Real.log (Real.log Y / Real.log N)| ≤
        2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
  obtain ⟨C, hC, hinterval⟩ := prime_interval_mertens_error hM
  refine ⟨C, hC, fun N Y z hN hNY hz hz1 => ?_⟩
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hP : ∀ p ∈ largePrimeSet Y (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet Y (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h₁ := prime_log_product_error (largePrimeSet Y N) hP hz hz1
    (show N ≠ 0 by omega) hcut
  have h₂ := hinterval (N : ℝ) Y hNreal hNY
  have hlog : Real.log (Real.log Y / Real.log N) =
      Real.log (Real.log Y) - Real.log (Real.log N) :=
    Real.log_div hlogY.ne' hlogN.ne'
  let S := ∑ p ∈ largePrimeSet Y (N : ℝ), 1 / (p : ℝ)
  change |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * Real.log (Real.log Y / Real.log N)| ≤ _
  calc
    _ = |(Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S) +
        z * (Real.log (Real.log Y / Real.log N) - S)| := by congr 1; ring
    _ ≤ |Real.log (primeNormalizer (largePrimeSet Y N) z) + z * S| +
        |z * (Real.log (Real.log Y / Real.log N) - S)| := abs_add_le _ _
    _ ≤ 2 * z ^ 2 / (N : ℝ) + z * (C / Real.log Y + C / Real.log N) := by
      apply add_le_add h₁
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm, hlog]
      exact mul_le_mul_of_nonneg_left h₂ hz

/-- The all-absent product has the expected logarithmic normalization.
Only Mertens' reciprocal-prime input is used. -/
theorem primeNormalizer_normalized_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (N : ℕ → ℕ) (Y : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (hY : Tendsto Y atTop atTop) (hNY : ∀ᶠ B in atTop, (N B : ℝ) ≤ Y B)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
      (Real.log (Y B) / Real.log (N B)) ^ z) atTop (𝓝 1) := by
  obtain ⟨C, _, hbound⟩ := primeNormalizer_log_error hM
  have hNreal : Tendsto (fun B => (N B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hlim : Tendsto (fun B => 2 * z ^ 2 / (N B : ℝ) +
      z * (C / Real.log (Y B) + C / Real.log (N B))) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * z ^ 2) atTop (𝓝 (2 * z ^ 2))).div_atTop hNreal
    have h₂ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hY)
    have h₃ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).div_atTop
      (Real.tendsto_log_atTop.comp hNreal)
    simpa using h₁.add ((h₂.add h₃).const_mul z)
  let E := fun B => Real.log (primeNormalizer (largePrimeSet (Y B) (N B)) z) +
    z * Real.log (Real.log (Y B) / Real.log (N B))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    simpa [E, Real.norm_eq_abs] using hbound (N B) (Y B) z hNB hNYB hz hz1
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hE
  have heq : (fun B => Real.exp (E B)) =ᶠ[atTop]
      (fun B => primeNormalizer (largePrimeSet (Y B) (N B)) z *
        (Real.log (Y B) / Real.log (N B)) ^ z) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2), hNY] with B hNB hNYB
    have hN2 : (2 : ℝ) ≤ N B := by exact_mod_cast hNB
    have hlogN : 0 < Real.log (N B) := Real.log_pos (by linarith)
    have hlogY : 0 < Real.log (Y B) := Real.log_pos (by linarith)
    have hprod : 0 < primeNormalizer (largePrimeSet (Y B) (N B)) z := by
      apply prod_pos
      intro p hp
      have hprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hfrac : z / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    dsimp [E]
    rw [Real.exp_add, Real.exp_log hprod,
      Real.rpow_def_of_pos (div_pos hlogY hlogN)]
    congr 1
    congr 1
    ring
  simpa using hexp.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeHarmonicWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact harmonic weights of squarefree prime products

The uncorrected independent-prime mass is the harmonic rough coefficient,
including the empty product. This identifies the weight used in partial summation.
-/

namespace JointDickman

open Finset ArithmeticFunction

theorem primeProduct_cardFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    cardFactors (∏ p ∈ S, p) = S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hpprime := hS p (mem_insert_self p S)
      have hrest : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
      rw [prod_insert hp, cardFactors_mul hpprime.ne_zero
        (prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)),
        cardFactors_apply_prime hpprime, ih hrest, card_insert_of_notMem hp]
      omega

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

theorem auxiliaryUpper_tendsto : Tendsto auxiliaryUpper atTop atTop :=
  Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

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

theorem auxiliary_log_ratio (B : ℕ) :
    Real.log (auxiliaryUpper B) / Real.log (auxiliaryCutoff B) =
      4 * auxiliaryRatio B := by
  simp only [auxiliaryUpper, Real.log_exp, auxiliaryCutoff, Nat.cast_pow,
    Real.log_pow, auxiliaryRatio]
  ring

/-- The paper's `Q_{z,B} ~ (4 R)^{-z}` in normalized-limit form. -/
theorem auxiliary_primeNormalizer_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => primeNormalizer (auxiliaryPrimes B) z *
      auxiliaryRatio B ^ z) atTop (𝓝 ((4 : ℝ) ^ (-z))) := by
  have h := primeNormalizer_normalized_tendsto hM auxiliaryCutoff auxiliaryUpper
    auxiliaryCutoff_tendsto auxiliaryUpper_tendsto auxiliaryCutoff_le_upper hz hz1
  simp_rw [auxiliary_log_ratio] at h
  have hdiv := h.div_const ((4 : ℝ) ^ z)
  have heq : (fun B => primeNormalizer (largePrimeSet (auxiliaryUpper B)
      (auxiliaryCutoff B)) z * (4 * auxiliaryRatio B) ^ z / (4 : ℝ) ^ z)
      =ᶠ[atTop] (fun B => primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (auxiliaryRatio_pos hB).le]
    change _ = primeNormalizer (largePrimeSet (auxiliaryUpper B) (auxiliaryCutoff B)) z * _
    have hfour : (4 : ℝ) ^ z ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) z).ne'
    field_simp
  simpa [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] using hdiv.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothCorrectionSeries
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The convergent correction series

The finite Euler factors used in removing the small primes are proved
as identities of absolutely convergent series, including at the shifted
exponent required by Rankin's bound.
-/

namespace JointDickman

open Finset

theorem smoothDirichletTerm_mul (E : Finset ℕ) (z s : ℝ) {m n : ℕ}
    (hmn : m.Coprime n) :
    smoothDirichletTerm E z s (m * n) =
      smoothDirichletTerm E z s m * smoothDirichletTerm E z s n := by
  simp only [smoothDirichletTerm, (smoothCorrection_isMultiplicative E z).map_mul_of_coprime hmn,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

theorem smoothDirichletTerm_prime_pow (E : Finset ℕ) (z s : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    smoothDirichletTerm E z s (p ^ k) =
      (if p ∈ E then -z / (p : ℝ) ^ s else 0) ^ k := by
  by_cases hk : k = 0
  · simp [hk]
  simp only [smoothDirichletTerm, smoothCorrection_prime_pow E z hp hk, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (k : ℝ) s,
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  split_ifs <;> simp [div_pow, hk]

theorem smoothDirichletTerm_ratio_lt_one (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) {p : ℕ} (hp : p.Prime) :
    ‖(if p ∈ E then -z / (p : ℝ) ^ s else 0)‖ < 1 := by
  by_cases hpE : p ∈ E
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpow : (1 : ℝ) ≤ (p : ℝ) ^ s := Real.one_le_rpow hp1 hs
    simp only [hpE, ite_eq_left, Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_pos (Real.rpow_pos_of_pos hp0 s)]
    exact (div_lt_one (Real.rpow_pos_of_pos hp0 s)).mpr (hz.trans_le hpow)
  · simp [hpE]

theorem smoothDirichletTerm_support (E : Finset ℕ) (z s : ℝ) :
    Function.support (smoothDirichletTerm E z s) ⊆ Nat.factoredNumbers E := by
  intro n hn
  rw [Function.mem_support] at hn
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp [smoothDirichletTerm] at hn
  refine ⟨hn0, ?_⟩
  by_contra h
  simp [smoothDirichletTerm, smoothCorrection, hn0, h] at hn

/-- Absolute convergence and the signed Euler-factor identity. -/
theorem smoothCorrection_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : |z| < 1) (hs : 0 ≤ s) :
    Summable (fun n => ‖smoothDirichletTerm E z s n‖) ∧
      HasSum (smoothDirichletTerm E z s)
        (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ) ^ s)⁻¹) := by
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k => ‖smoothDirichletTerm E z s (p ^ k)‖) := by
    intro p hp
    simp_rw [smoothDirichletTerm_prime_pow E z s hp]
    exact summable_norm_geometric_of_norm_lt_one
      (smoothDirichletTerm_ratio_lt_one E hz hs hp)
  obtain ⟨hnorm, hsum⟩ :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      (smoothDirichletTerm_one E z s) (smoothDirichletTerm_mul E z s) hlocal E
  have hsupport := smoothDirichletTerm_support E z s
  have habs_support : Function.support (fun n => ‖smoothDirichletTerm E z s n‖) ⊆
      Nat.factoredNumbers E := by
    intro n hn
    apply hsupport
    simpa only [Function.mem_support, norm_ne_zero_iff] using hn
  refine ⟨((hasSum_subtype_iff_of_support_subset habs_support).mp hnorm.hasSum).summable, ?_⟩
  apply (hasSum_subtype_iff_of_support_subset hsupport).mp
  convert hsum using 1
  all_goals try rfl
  apply prod_congr rfl
  intro p hp
  obtain ⟨_, hprime⟩ := mem_filter.mp hp
  simp_rw [smoothDirichletTerm_prime_pow E z s hprime]
  rw [(hasSum_geometric_of_norm_lt_one
    (smoothDirichletTerm_ratio_lt_one E hz hs hprime)).tsum_eq]
  simp [mem_of_mem_filter p hp, sub_eq_add_neg, neg_div]

/-- The zeroth correction moment is the inverse of the removed local factors. -/
theorem smoothCorrection_zeroth_moment (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    HasSum (fun n => smoothCorrection E z n / (n : ℝ))
      (∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹) := by
  have h := (smoothCorrection_hasSum E hz (by norm_num : (0 : ℝ) ≤ 1)).2
  have hf : smoothDirichletTerm E z 1 = fun n => smoothCorrection E z n / (n : ℝ) := by
    funext n
    simp [smoothDirichletTerm]
  rw [hf] at h
  simpa using h

theorem smoothDirichletTerm_abs (E : Finset ℕ) {z : ℝ} (hz : 0 ≤ z)
    (s : ℝ) (n : ℕ) :
    |smoothDirichletTerm E z s n| = smoothDirichletTerm E (-z) s n := by
  simp only [smoothDirichletTerm, abs_div, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s),
    smoothCorrection, ArithmeticFunction.coe_mk]
  split_ifs <;> simp [abs_pow, abs_neg, abs_of_nonneg hz]

/-- The absolute correction moment is a finite product of positive geometric factors. -/
theorem smoothCorrection_abs_hasSum (E : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (hs : 0 ≤ s) :
    HasSum (fun n => |smoothCorrection E z n| / (n : ℝ) ^ s)
      (∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹) := by
  have hz' : |-z| < 1 := by simpa [abs_of_nonneg hz] using hz1
  have h := (smoothCorrection_hasSum E hz' hs).2
  have hf : smoothDirichletTerm E (-z) s =
      fun n => |smoothCorrection E z n| / (n : ℝ) ^ s := by
    funext n
    rw [← smoothDirichletTerm_abs E hz]
    simp [smoothDirichletTerm, abs_div,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)]
  rw [hf] at h
  simpa [neg_div, sub_eq_add_neg] using h

/-- An exponential bound for every finite truncation of the absolute series. -/
theorem smoothCorrection_abs_sum_le_exp (E S : Finset ℕ) {z s : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (hs : 0 ≤ s) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ s) ≤
      Real.exp (2 * z * ∑ p ∈ E with p.Prime, 1 / (p : ℝ) ^ s) := by
  have hsum := smoothCorrection_abs_hasSum E hz (by linarith) hs
  calc
    _ ≤ ∏ p ∈ E with p.Prime, (1 - z / (p : ℝ) ^ s)⁻¹ := by
      rw [← hsum.tsum_eq]
      exact hsum.summable.sum_le_tsum S (fun n _ =>
        div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) s))
    _ ≤ Real.exp (2 * ∑ p ∈ E with p.Prime, z / (p : ℝ) ^ s) := by
      apply inverse_product_le_exp
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_lt.le
      have hpow := Real.one_le_rpow hp1 hs
      refine ⟨div_nonneg hz (by positivity), ?_⟩
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by
      congr 1
      simp only [div_eq_mul_inv, one_mul, ← mul_sum]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMomentBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform bounds for the moving roughness correction

The exponent shift `1 / log P` costs only a fixed power of `log P`.
This supplies the moment in Rankin's argument from Mertens' estimate,
rather than assuming a cutoff-dependent bound.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem shifted_reciprocal_le {p P : ℝ} (hp : 0 < p) (hpP : p ≤ P)
    (hlog : 0 < Real.log P) :
    1 / p ^ (1 - 1 / Real.log P) ≤ Real.exp 1 / p := by
  have hpow : p ^ (1 / Real.log P) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hp]
    apply Real.exp_le_exp.mpr
    have hle : Real.log p ≤ Real.log P := Real.log_le_log hp hpP
    simpa only [mul_one_div] using (div_le_one hlog).mpr hle
  rw [Real.rpow_sub hp, Real.rpow_one]
  simpa only [one_div_div] using div_le_div_of_nonneg_right hpow hp.le

theorem shifted_prime_sum_le (P : ℕ) (hlog : 0 < Real.log P) :
    (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) ≤
      Real.exp 1 * primeReciprocalSum P := by
  simp only [primeReciprocalSum, Nat.floor_natCast, mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpP, hprime⟩ := Nat.mem_primesLE.mp hp
  simpa only [mul_one_div] using shifted_reciprocal_le
    (by exact_mod_cast hprime.pos) (by exact_mod_cast hpP) hlog

/-- Mertens controls the shifted absolute correction moment by a fixed
power of the logarithm, uniformly over all finite truncations. -/
theorem smoothCorrection_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
        (n : ℝ) ^ (1 - 1 / Real.log P)) ≤
        A * (Real.log P) ^ (Real.exp 1) := by
  obtain ⟨M, C, hC, hbound⟩ := hM
  refine ⟨Real.exp (Real.exp 1 * (|M| + C)), Real.exp_pos _, ?_⟩
  intro P S z hP hlog hz hzhalf
  have hlogpos : 0 < Real.log P := by linarith
  have hshift : 0 ≤ 1 - 1 / Real.log P := by
    have h := (div_le_one hlogpos).mpr hlog
    linarith
  have hMertens : primeReciprocalSum P ≤ Real.log (Real.log P) + |M| + C := by
    have h := (abs_le.mp (hbound P (by exact_mod_cast hP))).2
    have hCdiv : C / Real.log P ≤ C := (div_le_iff₀ hlogpos).mpr (by nlinarith)
    have hMabs := le_abs_self M
    simp only [← primesLE_eq_filter] at h
    change primeReciprocalSum P - Real.log (Real.log P) - M ≤ C / Real.log P at h
    linarith
  have hprime : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  calc
    _ ≤ Real.exp (2 * z * ∑ p ∈ Nat.primesLE P,
        1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      simpa only [hprime] using smoothCorrection_abs_sum_le_exp
        (Nat.primesLE P) S hz hzhalf hshift
    _ ≤ Real.exp (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P)) := by
      apply Real.exp_le_exp.mpr
      have hsum : 0 ≤ ∑ p ∈ Nat.primesLE P, 1 / (p : ℝ) ^ (1 - 1 / Real.log P) :=
        sum_nonneg (fun p _ => by positivity)
      nlinarith
    _ ≤ Real.exp (Real.exp 1 * primeReciprocalSum P) :=
      Real.exp_le_exp.mpr (shifted_prime_sum_le P hlogpos)
    _ ≤ Real.exp (Real.exp 1 * (Real.log (Real.log P) + |M| + C)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hMertens (Real.exp_pos _).le)
    _ = _ := by
      rw [show Real.exp 1 * (Real.log (Real.log P) + |M| + C) =
        Real.exp 1 * (|M| + C) + Real.log (Real.log P) * Real.exp 1 by ring,
        Real.exp_add, ← Real.rpow_def_of_pos hlogpos]

theorem log_pow_le_rpow (k : ℕ) {v ε : ℝ} (hv : 1 ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤ ((k.factorial : ℝ) / ε ^ k) * v ^ ε := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have h := (div_le_iff₀ hfact).mp
    (Real.pow_div_factorial_le_exp (ε * Real.log v) (mul_nonneg hε.le (Real.log_nonneg hv)) k)
  have hexp : Real.exp (ε * Real.log v) = v ^ ε := by
    rw [Real.rpow_def_of_pos hv0, mul_comm]
  rw [mul_pow, hexp] at h
  calc
    (Real.log v) ^ k ≤ (v ^ ε * (k.factorial : ℝ)) / ε ^ k :=
      (le_div_iff₀ (pow_pos hε k)).mpr (by nlinarith [h])
    _ = _ := by ring

/-- Exponential tilting controls every logarithmic correction moment. -/
theorem smoothCorrection_log_moment_le (E S : Finset ℕ) (k : ℕ)
    (z : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k) ≤
      ((k.factorial : ℝ) / ε ^ k) *
        ∑ n ∈ S, |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε) := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / ε ^ k) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_le_rpow k hn1 hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
      field_simp

/-- The absolute constant in the roughness bound works for every fixed
moment order; only the factorial and extra logarithmic power change. -/
theorem smoothCorrection_log_moments_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (S : Finset ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      (∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| / (n : ℝ) *
        (Real.log n) ^ k) ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P S z k hP hlog hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  calc
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        ∑ n ∈ S, |smoothCorrection (Nat.primesLE P) z n| /
          (n : ℝ) ^ (1 - 1 / Real.log P) :=
      smoothCorrection_log_moment_le _ _ k z (by positivity)
    _ ≤ ((k.factorial : ℝ) / (1 / Real.log P) ^ k) *
        (A * (Real.log P) ^ (Real.exp 1)) :=
      mul_le_mul_of_nonneg_left (hbound P S z hP hlog hz hzhalf) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hlogpos, Real.rpow_natCast]
      simp only [one_div, inv_pow, div_inv_eq_mul]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CorrectionMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The coefficients' actual logarithmic moments

These are absolutely convergent series of the smooth correction.
The bounds are uniform in the moving cutoff and every fixed moment order.
-/

namespace JointDickman

open Finset

theorem correctionLogTerm_norm (E : Finset ℕ) (z : ℝ) (k n : ℕ) :
    ‖correctionLogTerm E z k n‖ =
      |smoothCorrection E z n| / (n : ℝ) * (Real.log n) ^ k := by
  rw [correctionLogTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)]

theorem correctionLogTerm_summable (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z < 1) (k : ℕ) :
    Summable (fun n => ‖correctionLogTerm E z k n‖) := by
  have hbase := (smoothCorrection_abs_hasSum E hz hz1 (by norm_num : (0 : ℝ) ≤ 1 / 2)).summable
  have hdom : Summable (fun n => ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k) *
      (|smoothCorrection E z n| / (n : ℝ) ^ (1 - (1 / 2 : ℝ)))) := by
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
      hbase.mul_left ((k.factorial : ℝ) / (1 / 2 : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hdom
  intro n
  rw [correctionLogTerm_norm]
  simpa using smoothCorrection_log_moment_le E {n} k z (by norm_num : (0 : ℝ) < 1 / 2)

theorem correctionLogMoment_zero (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    correctionLogMoment E z 0 =
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simpa [correctionLogMoment, correctionLogTerm] using
    (smoothCorrection_zeroth_moment E hz).tsum_eq

/-- The fixed-order coefficient moments are bounded with one absolute
logarithmic exponent. -/
theorem correctionLogMoment_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k| ≤
        A * (k.factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + k) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun P z k hP hlog hz hzhalf => ?_⟩
  have hsum := correctionLogTerm_summable (Nat.primesLE P) hz (by linarith) k
  have hnorm := hsum.tsum_le_of_sum_le (fun S => by
    simpa only [correctionLogTerm_norm] using hbound P S z k hP hlog hz hzhalf)
  calc
    _ = ‖∑' n, correctionLogTerm (Nat.primesLE P) z k n‖ := by
      rw [Real.norm_eq_abs, correctionLogMoment]
    _ ≤ ∑' n, ‖correctionLogTerm (Nat.primesLE P) z k n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ _ := hnorm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCoefficients
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Coefficients after removal of the small prime factors

Each coefficient is a finite combination of the published fixed-order
Selberg–Delange coefficients and the actual correction moments. The
definition has no dependence on a subsequently chosen truncation order.
-/

namespace JointDickman

open Finset

theorem roughCoefficient_zero (c : ℕ → ℝ) (E : Finset ℕ) {z : ℝ} (hz : |z| < 1) :
    roughCoefficient c E z 0 = c 0 *
      ∏ p ∈ E with p.Prime, (1 + z / (p : ℝ))⁻¹ := by
  simp [roughCoefficient, correctionLogMoment_zero E hz]

/-- Uniform coefficient bound with the absolute exponent supplied by
the correction moment estimate. -/
theorem roughCoefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (c : ℕ → ℝ)
    {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (ν : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → 1 ≤ Real.log P →
      |roughCoefficient c (Nat.primesLE P) z ν| ≤
        C * (Real.log P) ^ (Real.exp 1 + ν) := by
  obtain ⟨A, hA, hmom⟩ := correctionLogMoment_bound hM
  let C := ∑ j ∈ range (ν + 1),
    |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  refine ⟨C, hC, fun P hP hlog => ?_⟩
  unfold roughCoefficient
  calc
    _ ≤ ∑ j ∈ range (ν + 1),
        |c j * rpowShiftCoeff (z - 1 - j) (ν - j) *
          correctionLogMoment (Nat.primesLE P) z (ν - j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (ν + 1),
        (|c j * rpowShiftCoeff (z - 1 - j) (ν - j)| * A * ((ν - j).factorial : ℝ)) *
          (Real.log P) ^ (Real.exp 1 + ν) := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      have hpow : (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ)) ≤
          (Real.log P) ^ (Real.exp 1 + ν) := by
        apply Real.rpow_le_rpow_of_exponent_le hlog
        have hsub : ((ν - j : ℕ) : ℝ) ≤ ν := by exact_mod_cast Nat.sub_le ν j
        linarith
      calc
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + (ν - j : ℕ))) :=
          mul_le_mul_of_nonneg_left (hmom P z (ν - j) hP hlog hz hzhalf) (abs_nonneg _)
        _ ≤ |c j * rpowShiftCoeff (z - 1 - j) (ν - j)| *
            (A * ((ν - j).factorial : ℝ) * (Real.log P) ^ (Real.exp 1 + ν)) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeEulerProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergence of the squarefree Selberg–Delange Euler factor

Cancellation of the linear local logarithms proves absolute convergence.
This identifies the same Euler product used in the published leading
coefficient, without assuming its convergence as another input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem log_one_add_sub_error {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ 2 * x ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |-x| < 1 by rw [abs_neg, abs_of_nonneg hx]; linarith) 1
  have hbase : |Real.log (1 + x) - x| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_neg, abs_of_nonneg hx, sub_neg_eq_add, sub_eq_add_neg, add_comm] using h
  apply hbase.trans
  apply (div_le_iff₀ (show 0 < 1 - x by linarith)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)]

theorem squarefreeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    0 < squarefreeEulerFactor z p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply mul_pos
  · have h := div_nonneg hz hp0.le
    linarith
  · apply Real.rpow_pos_of_pos
    have h := (div_lt_one hp0).mpr hp1
    linarith

theorem squarefreeEulerFactor_log_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {p : ℕ} (hp : p.Prime) :
    |Real.log (squarefreeEulerFactor z p)| ≤ 4 / (p : ℝ) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsub : 0 < 1 - 1 / (p : ℝ) := by
    have h := (div_lt_one hp0).mpr hp1
    linarith
  have hadd : 0 < 1 + z / (p : ℝ) := by positivity
  have hfrac : z / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
  have h₁ := log_one_add_sub_error (div_nonneg hz hp0.le) hfrac
  have h₂ := log_one_sub_add_error (by positivity : (0 : ℝ) ≤ 1 / p) hrec
  have heq : Real.log (squarefreeEulerFactor z p) =
      (Real.log (1 + z / (p : ℝ)) - z / p) + z *
        (Real.log (1 - 1 / (p : ℝ)) + 1 / p) := by
    rw [squarefreeEulerFactor, Real.log_mul hadd.ne' (Real.rpow_pos_of_pos hsub z).ne',
      Real.log_rpow hsub]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (1 + z / (p : ℝ)) - z / p| +
        |z * (Real.log (1 - 1 / (p : ℝ)) + 1 / p)| := abs_add_le _ _
    _ ≤ 2 * (z / (p : ℝ)) ^ 2 + z * (2 * (1 / (p : ℝ)) ^ 2) := by
      rw [abs_mul, abs_of_nonneg hz]
      exact add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ hz)
    _ ≤ 4 / (p : ℝ) ^ 2 := by
      have hzsq : z ^ 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith

theorem primeEulerFactor_pos {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    0 < primeEulerFactor z n := by
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn] using squarefreeEulerFactor_pos hz hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_log_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Summable (fun n => Real.log (primeEulerFactor z n)) := by
  have hsum := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left 4
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hsum
  intro n
  rw [Real.norm_eq_abs]
  by_cases hn : n.Prime
  · simpa only [primeEulerFactor, ite_eq_left hn, mul_one_div] using squarefreeEulerFactor_log_bound hz hz1 hn
  · simp [primeEulerFactor, hn]

theorem primeEulerFactor_multipliable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Multipliable (primeEulerFactor z) :=
  Real.multipliable_of_summable_log (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)

theorem squarefreeEulerProduct_pos {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < ∏' n : ℕ, primeEulerFactor z n := by
  rw [← Real.rexp_tsum_eq_tprod (primeEulerFactor_pos hz) (primeEulerFactor_log_summable hz hz1)]
  exact Real.exp_pos _

theorem squarefreeEulerProduct_eq (z : ℝ) :
    (∏' n : ℕ, primeEulerFactor z n) =
      ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p := by
  calc
    _ = ∏' n : ℕ, ({p : ℕ | p.Prime}.mulIndicator (squarefreeEulerFactor z)) n := by
      apply tprod_congr
      intro n
      by_cases hn : n.Prime <;> simp [primeEulerFactor, Set.mulIndicator, hn]
    _ = _ := (tprod_subtype {p : ℕ | p.Prime} (squarefreeEulerFactor z)).symm

theorem squarefreeEulerProduct_partial (z : ℝ) (N : ℕ) :
    (∏ n ∈ range (N + 1), primeEulerFactor z n) =
      ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p := by
  have hset : (range (N + 1)).filter Nat.Prime = Nat.primesLE N := by
    ext p
    simp only [mem_filter, mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
  simp only [primeEulerFactor]
  rw [← prod_filter, hset]

theorem squarefreeEulerProduct_partial_tendsto {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun N => ∏ p ∈ Nat.primesLE N, squarefreeEulerFactor z p)
      atTop (𝓝 (∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p)) := by
  have h := (primeEulerFactor_multipliable hz hz1).tendsto_prod_tprod_nat.comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, squarefreeEulerProduct_partial, squarefreeEulerProduct_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughLeadingCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The leading coefficient after the roughness cutoff

Mertens' product theorem and the convergent squarefree Euler factor give
the precise constant `exp(-γ z) / Gamma(z)`.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughLeadingCoefficient_identity {z : ℝ} (hz : 0 ≤ z) (P : ℕ) :
    roughLeadingCoefficient z P * (Real.log P) ^ z =
      (squarefreeLeadingConstant z / ∏ p ∈ Nat.primesLE P, squarefreeEulerFactor z p) *
        (Real.log P * ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) ^ z := by
  let S := Nat.primesLE P
  have hlocal (p : ℕ) (hp : p ∈ S) : 0 < 1 - 1 / (p : ℝ) := by
    have hprime := (Nat.mem_primesLE.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    have hh := (div_lt_one hp0).mpr hp1
    linarith
  have hU : 0 < ∏ p ∈ S, (1 - 1 / (p : ℝ)) := prod_pos hlocal
  have hA : 0 < ∏ p ∈ S, (1 + z / (p : ℝ)) := by
    apply prod_pos
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    have hh := div_nonneg hz hp0.le
    linarith
  have hF : (∏ p ∈ S, squarefreeEulerFactor z p) =
      (∏ p ∈ S, (1 + z / (p : ℝ))) * (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z := by
    simp only [squarefreeEulerFactor, prod_mul_distrib]
    rw [Real.finsetProd_rpow S _ (fun p hp => (hlocal p hp).le)]
  change (squarefreeLeadingConstant z * ∏ p ∈ S, (1 + z / (p : ℝ))⁻¹) *
    (Real.log P) ^ z = (squarefreeLeadingConstant z / ∏ p ∈ S, squarefreeEulerFactor z p) *
      (Real.log P * ∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ z
  rw [hF, Real.mul_rpow (Real.log_natCast_nonneg P) hU.le, prod_inv_distrib]
  have hUz := (Real.rpow_pos_of_pos hU z).ne'
  field_simp [hA.ne', hUz]

/-- Only the cited Mertens product input is used in this normalization. -/
theorem roughLeadingCoefficient_tendsto
    (hM : PublishedInputs.PrimeProductMertensInput) {z : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    Tendsto (fun P => roughLeadingCoefficient z P * (Real.log P) ^ z) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) := by
  let G := ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  have hG : 0 < G := by
    dsimp only [G]
    rw [← squarefreeEulerProduct_eq]
    exact squarefreeEulerProduct_pos hz.le hz1
  have hprod : Tendsto (fun P : ℕ => Real.log P *
      ∏ p ∈ Nat.primesLE P, (1 - 1 / (p : ℝ))) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    simpa only [← primesLE_eq_filter, Function.comp_def, Nat.floor_natCast] using
      hM.comp tendsto_natCast_atTop_atTop
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => squarefreeLeadingConstant z) atTop
      (𝓝 (squarefreeLeadingConstant z))).div
        (squarefreeEulerProduct_partial_tendsto hz.le hz1) hG.ne').mul
          (hprod.rpow_const (Or.inr hz.le))
  have hconstant : squarefreeLeadingConstant z / G *
      Real.exp (-Real.eulerMascheroniConstant) ^ z =
        Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z := by
    change (G / Real.Gamma z) / G * _ = _
    rw [← Real.exp_mul]
    field_simp [hG.ne', (Real.Gamma_pos_of_pos hz).ne']
  rw [hconstant] at h
  exact h.congr' (Eventually.of_forall (fun P => (roughLeadingCoefficient_identity hz.le P).symm))

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

theorem primeNormalizer_bounds (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ primeNormalizer E z ∧ primeNormalizer E z ≤ 1 := by
  have hlocal (p : ℕ) (hp : p ∈ E) : 0 ≤ 1 - z / (p : ℝ) ∧ 1 - z / (p : ℝ) ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hE p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hE p hp).one_le
    have hdiv : z / (p : ℝ) ≤ 1 := (div_le_one hp0).mpr (hz1.trans hp1)
    constructor
    · linarith
    · linarith [div_nonneg hz hp0.le]
  exact ⟨prod_nonneg (fun p hp => (hlocal p hp).1),
    Finset.prod_le_one (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)⟩

theorem roughCoefficient_zero_eq_leading (c : ℕ → ℝ) {z : ℝ}
    (hc : c 0 = squarefreeLeadingConstant z) (hz : |z| < 1) (P : ℕ) :
    roughCoefficient c (Nat.primesLE P) z 0 = roughLeadingCoefficient z P := by
  rw [roughCoefficient_zero c _ hz, hc]
  have hp : (Nat.primesLE P).filter Nat.Prime = Nat.primesLE P :=
    filter_true_of_mem (fun p hp => (Nat.mem_primesLE.mp hp).2)
  simp only [roughLeadingCoefficient, hp]

theorem auxiliaryRatio_mul_log {B : ℕ} (hB : 1 < B) :
    auxiliaryRatio B * Real.log (auxiliaryCutoff B) = B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog : Real.log B ≠ 0 := (Real.log_pos hBreal).ne'
  simp only [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  norm_num
  field_simp

theorem scaledRoughCoefficient_zero_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hz1 : z < 1) :
    Tendsto (fun B => scaledRoughCoefficient c z 0 B) atTop
      (𝓝 ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z))) := by
  have hlead := (roughLeadingCoefficient_tendsto hMP hz hz1.le).comp auxiliaryCutoff_tendsto
  have h := (auxiliary_primeNormalizer_tendsto hM hz.le hz1.le).mul hlead
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hR : 0 ≤ auxiliaryRatio B := (auxiliaryRatio_pos hB).le
  have hlog : 0 ≤ Real.log (auxiliaryCutoff B) := Real.log_natCast_nonneg _
  have hpow : (auxiliaryRatio B) ^ z * (Real.log (auxiliaryCutoff B)) ^ z = (B : ℝ) ^ z := by
    rw [← Real.mul_rpow hR hlog, auxiliaryRatio_mul_log hB]
  unfold scaledRoughCoefficient
  rw [Nat.cast_zero, sub_zero,
    roughCoefficient_zero_eq_leading c hc (by rwa [abs_of_pos hz])]
  dsimp only [Function.comp_def]
  rw [mul_mul_mul_comm, hpow]

theorem scaledRoughCoefficient_succ_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (c : ℕ → ℝ) {z : ℝ} (hz : 0 ≤ z) (hzhalf : z ≤ 1 / 2) (j : ℕ) :
    Tendsto (fun B => scaledRoughCoefficient c z (j + 1) B) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := roughCoefficient_bound hM c hz hzhalf (j + 1)
  let a : ℝ := (j + 1 : ℕ) - z
  let r : ℝ := Real.exp 1 + (j + 1 : ℕ)
  have ha : 0 < a := by dsimp [a]; push_cast <;> linarith [Nat.cast_nonneg j (α := ℝ)]
  have hlimit := ((log_power_div_power_tendsto_zero r ha).const_mul
    (C * (1000 : ℝ) ^ r)).comp tendsto_natCast_atTop_atTop
  simp only [mul_zero] at hlimit
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlimit
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlogP : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hP, hlogP, eventually_gt_atTop 1] with B hp hlog hB
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hQ := primeNormalizer_bounds _ (auxiliaryPrimes_prime B) hz (by linarith : z ≤ 1)
  have hb := hbound (auxiliaryCutoff B) hp hlog
  rw [Real.norm_eq_abs, scaledRoughCoefficient, abs_mul, abs_mul,
    abs_of_nonneg hQ.1, abs_of_pos (Real.rpow_pos_of_pos hB0 _)]
  calc
    _ ≤ 1 * (C * (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (j + 1 : ℕ))) *
        (B : ℝ) ^ (z - (j + 1 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hQ.2 hb (abs_nonneg _) (by norm_num)) (Real.rpow_nonneg hB0.le _)
    _ = C * (1000 : ℝ) ^ r * ((Real.log B) ^ r / (B : ℝ) ^ a) := by
      have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
        simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow] <;> norm_num
      rw [one_mul, hcut, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_pos hBreal).le]
      have hexp : z - (j + 1 : ℕ) = -a := by dsimp [a] <;> ring
      rw [hexp, Real.rpow_neg hB0.le]
      dsimp [r]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform convergence of the prime-product density

Finite combinations of the actual rough coefficients converge uniformly
away from zero. This is the smooth density used for the coarse channel.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_eq (c : ℕ → ℝ) (z : ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    scaledRoughDensity c z H B s =
      B * primeNormalizer (auxiliaryPrimes B) z *
        roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (B * s) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  unfold scaledRoughDensity roughDensityPolynomial
  rw [← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  unfold scaledRoughCoefficient
  have hfirst : (B : ℝ) ^ (z - j) = B * (B : ℝ) ^ (z - 1 - j) := by
    rw [show z - (j : ℝ) = 1 + (z - 1 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  have hsecond : (B : ℝ) ^ (z - 1 - j) = B * (B : ℝ) ^ (z - 2 - j) := by
    rw [show z - 1 - (j : ℝ) = 1 + (z - 2 - j) by ring, Real.rpow_add hB0, Real.rpow_one]
  rw [Real.mul_rpow hB0.le hs.le, Real.mul_rpow hB0.le hs.le, hfirst]
  have hBn : (B : ℝ) ≠ 0 := hB0.ne'
  field_simp
  rw [hsecond]
  ring

/-- A coefficient limit gives a uniform limit for a fixed negative power. -/
theorem scalar_power_uniform {a δ c : ℝ} {u : ℕ → ℝ}
    (ha : a ≤ 0) (hδ : 0 < δ) (hu : Tendsto u atTop (𝓝 c)) :
    TendstoUniformlyOn (fun (B : ℕ) (s : ℝ) => u B * s ^ a)
      (fun s => c * s ^ a) atTop (Set.Ici δ) := by
  have hnorm : Tendsto (fun n : ℕ => |u n - c| * δ ^ a) atTop (𝓝 0) := by
    simpa using ((hu.sub_const c).abs.mul_const (δ ^ a))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall := hnorm.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hp := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    dist (c * s ^ a) (u B * s ^ a) = |u B - c| * s ^ a := by
      rw [Real.dist_eq, ← sub_mul, abs_mul, abs_sub_comm,
        abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |u B - c| * δ ^ a := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ < ε := hB

/-- Finite fixed powers preserve uniform convergence of their coefficients. -/
theorem finite_power_uniform (S : Finset ℕ) (a c : ℕ → ℝ) (u : ℕ → ℕ → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (ha : ∀ j ∈ S, a j ≤ 0)
    (hu : ∀ j ∈ S, Tendsto (fun B => u B j) atTop (𝓝 (c j))) :
    TendstoUniformlyOn (fun B s => ∑ j ∈ S, u B j * s ^ a j)
      (fun s => ∑ j ∈ S, c j * s ^ a j) atTop (Set.Ici δ) := by
  induction S using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const (Set.Ici δ)
  | @insert i S hi ih =>
      have hfirst := scalar_power_uniform (ha i (mem_insert_self i S)) hδ (hu i (mem_insert_self i S))
      have hrest := ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => hu j (mem_insert_of_mem hj))
      convert hfirst.add hrest using 1 <;> first | (with_reducible_and_instances rfl) | (ext <;> simp [sum_insert hi])

/-- The density converges uniformly on every interval bounded away from zero.
The stronger half-line statement is available because all exponents are negative. -/
theorem scaledRoughDensity_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensity c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) * s ^ (z - 1))
      atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 1 - j) b
    (fun B j => scaledRoughCoefficient c z j B) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => hcoef j)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using ((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const (z - 1 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityDerivative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Derivatives of the density used in partial summation

The finite model is differentiated directly, and its first derivative
converges uniformly away from zero along with the density itself.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem hasDerivAt_scaledRoughDensity (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (scaledRoughDensity c z H B) (scaledRoughDensityDeriv c z H B s) s := by
  have hfirst : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => scaledRoughCoefficient c z j B * t ^ (z - 1 - j))
        ((scaledRoughCoefficient c z j B * (z - 1 - j)) * s ^ (z - 2 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
    ring
  have hsecond : ∀ j ∈ range (H + 1),
      HasDerivAt (fun t => (scaledRoughCoefficient c z j B / B * (z - 1 - j)) * t ^ (z - 2 - j))
        ((scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) * s ^ (z - 3 - j)) s := by
    intro j _
    convert (Real.hasDerivAt_rpow_const (p := z - 2 - j) (Or.inl hs.ne')).const_mul
      (scaledRoughCoefficient c z j B / B * (z - 1 - j)) using 1
    all_goals try with_reducible_and_instances rfl
    rw [show z - 2 - (j : ℝ) - 1 = z - 3 - j by ring]
    ring
  exact (HasDerivAt.fun_sum hfirst).add (HasDerivAt.fun_sum hsecond)

theorem scaledRoughDensityDeriv_tendstoUniformlyOn
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    TendstoUniformlyOn (fun B s => scaledRoughDensityDeriv c z H B s)
      (fun s => ((4 : ℝ) ^ (-z) *
        (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)) *
          (z - 1) * s ^ (z - 2)) atTop (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let b : ℕ → ℝ := fun j => if j = 0 then k else 0
  have hcoef (j : ℕ) : Tendsto (fun B => scaledRoughCoefficient c z j B) atTop (𝓝 (b j)) := by
    cases j with
    | zero => exact scaledRoughCoefficient_zero_tendsto hM hMP c hc hz (by linarith)
    | succ j => simpa [b] using scaledRoughCoefficient_succ_tendsto hM c hz.le hzhalf j
  have hfirst := finite_power_uniform (range (H + 1)) (fun j => z - 2 - j)
    (fun j => b j * (z - 1 - j)) (fun B j => scaledRoughCoefficient c z j B * (z - 1 - j))
    hδ (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)])
    (fun j _ => (hcoef j).mul_const _)
  have hsecond := finite_power_uniform (range (H + 1)) (fun j => z - 3 - j) (fun _ => 0)
    (fun B j => scaledRoughCoefficient c z j B / B * (z - 1 - j) * (z - 2 - j)) hδ
    (fun j _ => by linarith [Nat.cast_nonneg j (α := ℝ)]) (fun j _ => by
      simpa using (((hcoef j).div_atTop tendsto_natCast_atTop_atTop).mul_const
        (z - 1 - j)).mul_const (z - 2 - j))
  convert hfirst.add hsecond using 1
  · rfl
  · funext s
    simp [b, k]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic coefficient weight A₀ -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_nonneg (B : ℕ) : 0 ≤ coefficientScale B := by
  unfold coefficientScale
  exact mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B))) _)

theorem coefficientWeight_nonneg (B n : ℕ) : 0 ≤ coefficientWeight B n := by
  have hs := coefficientScale_nonneg B
  unfold coefficientWeight roughSquarefreeWeight squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite divisor expansion and its mean bound -/

namespace JointDickman

open Finset

theorem primeProduct_dvd_iff (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime) (n : ℕ) :
    (∏ p ∈ D, p) ∣ n ↔ ∀ p ∈ D, p ∣ n := by
  refine ⟨fun h p hp => (dvd_prod_of_mem id hp).trans h, ?_⟩
  intro h
  by_cases hn : n = 0
  · simp [hn]
  have hsub : D ⊆ n.primeFactors := fun p hp => (hD p hp).mem_primeFactors (h p hp) hn
  exact (prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd n)

open Classical in
theorem divisor_product_expansion (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then 1 + b p else 1) =
      ∑ D ∈ P.powerset, if (∏ p ∈ D, p) ∣ n then ∏ p ∈ D, b p else 0 := by
  have heq (p : ℕ) : (if p ∣ n then 1 + b p else 1) =
      1 + (if p ∣ n then b p else 0) := by split_ifs <;> simp
  simp_rw [heq]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  rw [prod_ite_zero]
  simp only [primeProduct_dvd_iff D (fun p hp => hP p (mem_powerset.mp hD hp))]

open Classical in
theorem divisor_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b : ℕ → ℝ) (hb : ∀ p ∈ P, 0 ≤ b p) (U : ℕ) :
    (∑ n ∈ Ioc 0 U, ∏ p ∈ P, if p ∣ n then 1 + b p else 1) ≤
      (U : ℝ) * ∏ p ∈ P, (1 + b p / p) := by
  simp_rw [divisor_product_expansion P hP b]
  rw [sum_comm]
  calc
    _ = ∑ D ∈ P.powerset,
        ((U / (∏ p ∈ D, p) : ℕ) : ℝ) * ∏ p ∈ D, b p := by
      apply sum_congr rfl
      intro D _
      rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ D ∈ P.powerset, ((U : ℝ) / (∏ p ∈ D, p)) * ∏ p ∈ D, b p := by
      apply sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_right Nat.cast_div_le
      exact prod_nonneg (fun p hp => hb p (mem_powerset.mp hD hp))
    _ = (U : ℝ) * ∑ D ∈ P.powerset, ∏ p ∈ D, (b p / p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro D _
      rw [prod_div_distrib, Nat.cast_prod]
      ring
    _ = _ := by rw [← prod_one_add]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded moments of the singular factor Σ(j) -/

namespace JointDickman

open Finset

theorem singularFactor_one_le {C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    1 ≤ singularFactor C j := by
  exact Finset.one_le_prod (fun p _ => le_add_of_nonneg_right (div_nonneg hC (Nat.cast_nonneg p)))

theorem local_singular_power_bound {C : ℝ} (hC : 0 ≤ C) (r : ℕ)
    {p : ℕ} (hp : 1 ≤ p) :
    0 ≤ (1 + C / p) ^ r - 1 ∧
      (1 + C / p) ^ r - 1 ≤ ((r : ℝ) * C * (1 + C) ^ (r - 1)) / p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hx : 1 ≤ 1 + C / p := le_add_of_nonneg_right (div_nonneg hC (Nat.cast_nonneg p))
  have hupper : 1 + C / p ≤ 1 + C := by
    linarith [div_le_self hC hp1]
  have hn : 0 ≤ (1 + C / p) ^ r - 1 := by
    exact sub_nonneg.mpr (one_le_pow₀ hx)
  refine ⟨hn, ?_⟩
  have h := abs_pow_sub_pow_le (1 + C / (p : ℝ)) 1 r
  simp only [one_pow, abs_of_nonneg hn, abs_of_nonneg (by positivity : 0 ≤ 1 + C / (p : ℝ)),
    abs_one, max_eq_left hx, add_sub_cancel_left, abs_of_nonneg (by positivity : 0 ≤ C / (p : ℝ))] at h
  calc
    _ ≤ C / (p : ℝ) * r * (1 + C / p) ^ (r - 1) := h
    _ ≤ C / (p : ℝ) * r * (1 + C) ^ (r - 1) := by gcongr
    _ = _ := by ring

open Classical in
theorem singularFactor_nat_moment {C : ℝ} (hC : 0 ≤ C) (r U : ℕ) :
    (∑ j ∈ Ioc 0 U, singularFactor C j ^ r) ≤
      Real.exp ((r : ℝ) * C * (1 + C) ^ (r - 1)) * U := by
  let P := Nat.primesLE U
  let b := fun p : ℕ => (1 + C / (p : ℝ)) ^ r - 1
  let K := (r : ℝ) * C * (1 + C) ^ (r - 1)
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hb (p : ℕ) (hp : p ∈ P) : 0 ≤ b p :=
    (local_singular_power_bound hC r (hP p hp).one_le).1
  have hbBound (p : ℕ) (hp : p ∈ P) : b p / p ≤ K / (p : ℝ) ^ 2 := by
    have h := div_le_div_of_nonneg_right
      (local_singular_power_bound hC r (hP p hp).one_le).2 (Nat.cast_nonneg p)
    simpa [b, K, div_div, pow_two] using h
  have hsum : (∑ p ∈ P, b p / p) ≤ K := by
    calc
      _ ≤ ∑ p ∈ P, K / (p : ℝ) ^ 2 := sum_le_sum hbBound
      _ = K * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by simp_rw [div_eq_mul_inv]; rw [mul_sum]; simp
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left
        (by
          simpa using sum_reciprocal_square_tail P (by norm_num : (1 : ℕ) ≠ 0)
            (fun p hp => (hP p hp).one_lt)) hK
      _ = K := mul_one _
  have hprod : (∏ p ∈ P, (1 + b p / p)) ≤ Real.exp K := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (b p / p) := Finset.prod_le_prod
        (fun p hp => by have := hb p hp; positivity)
        (fun p _ => by simpa [add_comm] using Real.add_one_le_exp (b p / p))
      _ = Real.exp (∑ p ∈ P, b p / p) := (Real.exp_sum _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsum
  have heq (j : ℕ) (hj : j ∈ Ioc 0 U) : singularFactor C j ^ r =
      ∏ p ∈ P, if p ∣ j then 1 + b p else 1 := by
    have hj0 : j ≠ 0 := Nat.ne_of_gt (mem_Ioc.mp hj).1
    have hfac : j.primeFactors = P.filter (fun p => p ∣ j) := by
      ext p
      simp only [P, mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
      constructor
      · rintro ⟨hp, hd, _⟩
        exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hd).trans (mem_Ioc.mp hj).2, hp⟩, hd⟩
      · rintro ⟨⟨_, hp⟩, hd⟩
        exact ⟨hp, hd, hj0⟩
    rw [singularFactor, hfac, ← prod_pow, prod_filter]
    apply prod_congr rfl
    intro p _
    simp [b]
  calc
    _ = ∑ j ∈ Ioc 0 U, ∏ p ∈ P, if p ∣ j then 1 + b p else 1 := sum_congr rfl heq
    _ ≤ (U : ℝ) * ∏ p ∈ P, (1 + b p / p) := divisor_product_mean P hP b hb U
    _ ≤ (U : ℝ) * Real.exp K := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg U)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite periodic averages and coprime residue factorization

Integer averages of a function on `ZMod q` converge to its uniform residue
mean. The proof is the exact complete-block/remainder identity. The Chinese
remainder equivalence then gives factorization for fixed coprime moduli.
-/

namespace JointDickman

open Filter
open scoped Topology BigOperators

theorem residue_sum_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ a : ZMod q, f a) = ∑ n ∈ Finset.range q, f (n : ZMod q) := by
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  exact Fintype.sum_equiv (residueEquiv q) _ _ (fun _ => rfl)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularPrimeSets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's regular prime sets and truncated weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem RegularPrimeSet.total_lower {B L : ℕ} {τ C : ℝ} {S : Finset ℕ}
    (h : RegularPrimeSet B L τ C S) (hL : 1 ≤ L) :
    (1 / 2 - τ) * auxiliaryLogLength B ≤ (S.card : ℝ) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  simpa only [div_self hL0, primePrefix, lt_self_iff_false, ite_false, if_false] using
    (h.1 L (mem_Icc.mpr ⟨hL, le_rfl⟩)).1

theorem residueBaseWeight_le_of_count {B : ℕ} {τ : ℝ} {S : Finset ℕ}
    (hB : 1 < B) (hS : (1 / 2 - τ) * auxiliaryLogLength B ≤ (S.card : ℝ)) :
    residueBaseWeight B S ≤ auxiliaryRatio B ^ weightExponent τ := by
  have hR := auxiliaryRatio_pos hB
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have he : (1 / 2 : ℝ) ^ S.card = Real.exp (-Real.log 2 * (S.card : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), hlog]
  rw [residueBaseWeight, he, Real.rpow_def_of_pos hR, ← Real.exp_add,
    Real.rpow_def_of_pos hR]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hS (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  dsimp [auxiliaryLogLength, weightExponent, weightBaseExponent] at *
  nlinarith

theorem regularResidueWeight_nonneg (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) :
    0 ≤ regularResidueWeight B L τ C S := by
  unfold regularResidueWeight residueBaseWeight
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)
  · rfl

theorem regularCoefficientWeight_nonneg (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    0 ≤ regularCoefficientWeight B L τ C n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact coefficientWeight_nonneg _ _
  · rfl

theorem coefficientWeight_le_residueBaseWeight {B n : ℕ} (hn : n ≠ 0) :
    coefficientWeight B n ≤ Real.log (auxiliaryCutoff B) * residueBaseWeight B (coefficientPrimeSet B n) := by
  classical
  have hs0 : 0 ≤ coefficientScale B := coefficientScale_nonneg B
  have hright : 0 ≤ Real.log (auxiliaryCutoff B) * residueBaseWeight B (coefficientPrimeSet B n) := by
    exact mul_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity))
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B))
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have hsub : coefficientPrimeSet B n ⊆ n.primeFactors := by
        intro p hp
        obtain ⟨hpP, hpn⟩ := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hpP).1).2.mem_primeFactors hpn hn
      have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (card_le_card hsub)
      simpa only [coefficientWeight, roughSquarefreeWeight, ArithmeticFunction.coe_mk,
        ite_eq_left hd, squarefreeWeight, ite_eq_left hsq, hcard, residueBaseWeight,
        coefficientScale, mul_assoc] using mul_le_mul_of_nonneg_left hpow hs0
    · simpa [coefficientWeight, roughSquarefreeWeight, squarefreeWeight, hd, hsq] using hright
  · simpa [coefficientWeight, roughSquarefreeWeight, hd] using hright

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularWeightCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial caps supplied by the total-count regularity condition -/

namespace JointDickman

open Filter
open scoped Topology

theorem regular_scale_cap {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop,
      auxiliaryRatio B ^ weightExponent τ ≤ (B : ℝ) ^ weightExponent τ ∧
      Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ weightExponent τ ≤
        (B : ℝ) ^ (weightExponent τ + ε) := by
  have hh : 0 ≤ weightExponent τ := by
    have h := weightExponent_mono hτ
    have hz : weightExponent 0 = weightBaseExponent := by simp [weightExponent]
    rw [hz] at h
    exact weightBaseExponent_pos.le.trans h
  have hlim : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ) ^ ε)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop |>.const_mul 1000
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hloglarge, eventually_gt_atTop 1] with B hsmall hlog hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hR0 := (auxiliaryRatio_pos hB).le
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio, auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
  have hRB : auxiliaryRatio B ≤ B := by
    rw [hr]
    exact div_le_self hB0.le hlog
  have hpow := Real.rpow_le_rpow hR0 hRB hh
  refine ⟨hpow, ?_⟩
  have hlogsmall : Real.log (auxiliaryCutoff B) ≤ (B : ℝ) ^ ε := by
    have h := (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp
      (show (1000 * Real.log B) / (B : ℝ) ^ ε ≤ 1 by simpa only [mul_div_assoc] using hsmall)
    simpa only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  calc
    _ ≤ (B : ℝ) ^ ε * (B : ℝ) ^ weightExponent τ :=
      mul_le_mul hlogsmall hpow (Real.rpow_nonneg hR0 _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hB0]; congr 1; ring

/-- Equation (8), with an arbitrary positive exponent slack replacing o(1).
The bound is uniform in the tail tolerance C and in the selected prime set. -/
theorem regular_weights_cap {L : ℕ} (hL : 1 ≤ L) {τ ε : ℝ}
    (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ C : ℝ,
      (∀ S : Finset ℕ, regularResidueWeight B L τ C S ≤ (B : ℝ) ^ (weightExponent τ + ε)) ∧
      (∀ n : ℕ, regularCoefficientWeight B L τ C n ≤ (B : ℝ) ^ (weightExponent τ + ε)) := by
  filter_upwards [regular_scale_cap hτ hε, eventually_gt_atTop 1] with B hcap hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  intro C
  constructor
  · intro S
    unfold regularResidueWeight
    split_ifs with hreg
    · have hbase := residueBaseWeight_le_of_count hB (hreg.total_lower hL)
      have he : (B : ℝ) ^ weightExponent τ ≤ (B : ℝ) ^ (weightExponent τ + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ B)) (by linarith)
      exact hbase.trans (hcap.1.trans he)
    · positivity
  · intro n
    unfold regularCoefficientWeight
    split_ifs with hreg
    · by_cases hn : n = 0
      · subst n
        simp [coefficientWeight, roughSquarefreeWeight, squarefreeWeight]
        positivity
      · calc
          _ ≤ Real.log (auxiliaryCutoff B) * residueBaseWeight B (coefficientPrimeSet B n) :=
            coefficientWeight_le_residueBaseWeight hn
          _ ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B ^ weightExponent τ :=
            mul_le_mul_of_nonneg_left (residueBaseWeight_le_of_count hB (hreg.total_lower hL))
              (Real.log_natCast_nonneg _)
          _ ≤ _ := hcap.2
    · positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateCountScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A regular endpoint admits only polynomially many subset choices -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem RegularPrimeSet.total_upper {B L : ℕ} {τ C : ℝ} {S : Finset ℕ}
    (h : RegularPrimeSet B L τ C S) (hL : 1 ≤ L) :
    (S.card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  simpa only [div_self hL0,primePrefix,lt_self_iff_false,ite_false, if_false] using
    (h.1 L (mem_Icc.mpr ⟨hL,le_rfl⟩)).2

theorem regular_union_count {B L : ℕ} {τ C : ℝ} {S R : Finset ℕ}
    (hS : RegularPrimeSet B L τ C S) (hR : RegularPrimeSet B L τ C R) (hL : 1 ≤ L) :
    ((S ∪ R).card : ℝ) ≤ (1+2*τ)*auxiliaryLogLength B := by
  have hcard : ((S ∪ R).card : ℝ) ≤ (S.card : ℝ)+(R.card : ℝ) := by
    exact_mod_cast card_union_le S R
  have hs := hS.total_upper hL
  have hr := hR.total_upper hL
  nlinarith only [hcard,hs,hr]

theorem regular_endpoint_subset_count {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, ∀ S R : Finset ℕ,
      RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
        2^(S ∪ R).card ≤ B := by
  have hlog2 := Real.log_two_lt_d9
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc0 : 0 ≤ (1+2*τ)*Real.log 2 := mul_nonneg (by linarith) hlog20
  have hc1 : (1+2*τ)*Real.log 2 ≤ 1 := by
    have ht : τ ≤ 1/1000 := hτsmall
    have hm := mul_le_mul_of_nonneg_right ht hlog20
    nlinarith
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hR hlog hB
  intro C S R hS hSR
  change 1 ≤ Real.log (B : ℝ) at hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB.le
  have hRB : auxiliaryRatio B ≤ (B : ℝ) := by
    unfold auxiliaryRatio
    apply div_le_self hB0.le
    linarith only [hlog]
  have hcount := regular_union_count hS hSR hL
  have hp : (2 : ℝ)^(S ∪ R).card ≤ (B : ℝ) := by
    calc
      _ = Real.exp (Real.log 2*((S ∪ R).card : ℝ)) := by
        rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
      _ ≤ Real.exp (Real.log 2*((1+2*τ)*auxiliaryLogLength B)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcount hlog20)
      _ = (auxiliaryRatio B)^((1+2*τ)*Real.log 2) := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hR)]
        unfold auxiliaryLogLength
        congr 1
        ring
      _ ≤ (B : ℝ)^((1+2*τ)*Real.log 2) :=
        Real.rpow_le_rpow (by linarith only [hR]) hRB hc0
      _ ≤ (B : ℝ)^((1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hB1 hc1
      _ = _ := Real.rpow_one _
  exact_mod_cast hp

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

theorem fairRetentionBitMass_nonneg (hit retained : Bool) :
    0 ≤ fairRetentionBitMass hit retained := by
  cases hit <;> cases retained <;> norm_num [fairRetentionBitMass, bernoulliBitMass]

theorem fairRetentionBitMass_sum (hit : Bool) : ∑ retained, fairRetentionBitMass hit retained = 1 := by
  cases hit <;> norm_num [fairRetentionBitMass, bernoulliBitMass, Fintype.sum_bool]

theorem fairRetentionMass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → Bool) : 0 ≤ fairRetentionMass x y :=
  finiteProductMass_nonneg _ (fun i => fairRetentionBitMass_nonneg (x i)) y

theorem fairRetentionMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → Bool) : ∑ y, fairRetentionMass x y = 1 :=
  finiteProductMass_sum _ (fun i => fairRetentionBitMass_sum (x i))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform boundedness and Lipschitz control of the actual density

These estimates provide the profile hypotheses in the coarse channel.
Their constants are independent of the auxiliary integer B.
-/

namespace JointDickman

open Filter
open scoped Topology NNReal

theorem uniform_power_eventually_bounded {u : ℕ → ℝ → ℝ} {k a δ : ℝ}
    (hδ : 0 < δ) (ha : a ≤ 0)
    (hu : TendstoUniformlyOn u (fun s => k * s ^ a) atTop (Set.Ici δ)) :
    ∀ᶠ B : ℕ in atTop, ∀ s ∈ Set.Ici δ, |u B s| ≤ |k| * δ ^ a + 1 := by
  have h := (Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)
  filter_upwards [h] with B hB
  intro s hs
  have hs0 : 0 < s := hδ.trans_le hs
  have hdist := hB s hs
  rw [Real.dist_eq] at hdist
  have hpow := Real.rpow_le_rpow_of_nonpos hδ hs ha
  calc
    |u B s| = |(u B s - k * s ^ a) + k * s ^ a| := by congr 1; ring
    _ ≤ |u B s - k * s ^ a| + |k * s ^ a| := abs_add_le _ _
    _ = |k * s ^ a - u B s| + |k| * s ^ a := by
      rw [abs_sub_comm, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    _ ≤ |k| * δ ^ a + 1 := by nlinarith [mul_le_mul_of_nonneg_left hpow (abs_nonneg k)]

theorem scaledRoughDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) {z δ : ℝ} (hc : c 0 = squarefreeLeadingConstant z)
    (hz : 0 < z) (hzhalf : z ≤ 1 / 2) (hδ : 0 < δ) (H : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ L : ℝ≥0, ∀ᶠ B : ℕ in atTop,
      (∀ s ∈ Set.Ici δ, |scaledRoughDensity c z H B s| ≤ M) ∧
      LipschitzOnWith L (scaledRoughDensity c z H B) (Set.Ici δ) := by
  let k := (4 : ℝ) ^ (-z) * (Real.exp (-Real.eulerMascheroniConstant * z) / Real.Gamma z)
  let M := |k| * δ ^ (z - 1) + 1
  let L : ℝ≥0 := ⟨|k * (z - 1)| * δ ^ (z - 2) + 1, by positivity⟩
  have hfun := uniform_power_eventually_bounded hδ (by linarith : z - 1 ≤ 0)
    (scaledRoughDensity_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  have hder := uniform_power_eventually_bounded hδ (by linarith : z - 2 ≤ 0)
    (scaledRoughDensityDeriv_tendstoUniformlyOn hM hMP c hc hz hzhalf hδ H)
  refine ⟨M, by dsimp [M] <;> positivity, L, ?_⟩
  filter_upwards [hfun, hder] with B hf hd
  refine ⟨hf, ?_⟩
  apply (convex_Ici δ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun s hs => (hasDerivAt_scaledRoughDensity c z H B (hδ.trans_le hs)).hasDerivWithinAt)
  intro s hs
  change ‖scaledRoughDensityDeriv c z H B s‖₊ ≤ L
  exact_mod_cast hd s hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationSmoothCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth cutoff equal to one on the positive interior rectangle -/

namespace JointDickman
open Finset

theorem amplificationBump_bounds (x : ℝ) : 0 ≤ amplificationBump x ∧ amplificationBump x ≤ 1 :=
  ⟨amplificationBump.nonneg, amplificationBump.le_one⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticPeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite period of the divisor amplification -/

namespace JointDickman
open Finset

theorem auxiliaryProduct_mul_prime_dvd_period {B p : ℕ} {A : Finset ℕ}
    (hp : p ∈ auxiliaryPrimes B) (hA : A ⊆ auxiliaryPrimes B) :
    (∏ p ∈ A, p) * p ∣ auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  rw [pow_two]
  exact Nat.mul_dvd_mul (prod_dvd_prod_of_subset A (auxiliaryPrimes B) id hA)
    (dvd_prod_of_mem id hp)

theorem coefficientPrimeSet_quotient_modEq {B n m : ℕ} {A : Finset ℕ}
    (h : n ≡ m [MOD auxiliarySquarePeriod B]) (hA : A ⊆ auxiliaryPrimes B)
    (ha : (∏ p ∈ A, p) ∣ n) (hb : (∏ p ∈ A, p) ∣ m) :
    coefficientPrimeSet B (n / (∏ p ∈ A, p)) =
      coefficientPrimeSet B (m / (∏ p ∈ A, p)) := by
  ext p
  simp only [coefficientPrimeSet, mem_filter]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, (Nat.dvd_div_iff_mul_dvd hb).mpr ?_⟩
    exact (h.dvd_iff (auxiliaryProduct_mul_prime_dvd_period hp hA)).mp
      ((Nat.dvd_div_iff_mul_dvd ha).mp hn)
  · rintro ⟨hp, hm⟩
    refine ⟨hp, (Nat.dvd_div_iff_mul_dvd ha).mpr ?_⟩
    exact (h.dvd_iff (auxiliaryProduct_mul_prime_dvd_period hp hA)).mpr
      ((Nat.dvd_div_iff_mul_dvd hb).mp hm)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CRTMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete residue mean is the independent uniform product law -/

namespace JointDickman
open Finset

theorem crt_uniform_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (F : (∀ i, ZMod (m i)) → ℝ) :
    (∑ n ∈ range (∏ i, m i), F (fun i => (n : ZMod (m i)))) / (∏ i, (m i : ℝ)) =
      ∑ x, finiteProductMass (fun i (_ : ZMod (m i)) => 1 / (m i : ℝ)) x * F x := by
  classical
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (m i))⟩
  let e := ZMod.prodEquivPi m hcop
  have heval (n : ℕ) : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) := map_natCast e n
  have hr := residue_sum_eq_range (fun a : ZMod (∏ i, m i) => (F (e a) : ℂ))
  simp only [heval] at hr
  have hr' : (∑ a : ZMod (∏ i, m i), F (e a)) =
      ∑ n ∈ range (∏ i, m i), F (fun i => (n : ZMod (m i))) := by exact_mod_cast hr
  have hs : (∑ a : ZMod (∏ i, m i), F (e a)) = ∑ x, F x :=
    e.toEquiv.sum_comp F
  rw [← hr', hs, sum_div]
  apply sum_congr rfl
  intro x _
  simp only [finiteProductMass, prod_div_distrib, prod_const_one]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationMultiplier
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's multiplier scale and negligible diagonal cap -/

namespace JointDickman
open Filter
open scoped Topology

theorem amplificationMultiplier_comparable : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (B : ℝ) ^ (8/25 : ℝ) / 2 ≤ amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ (B : ℝ) ^ (8/25 : ℝ) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/25)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hp.eventually_ge_atTop 2] with B hB
  change 2 ≤ (B : ℝ) ^ (8/25 : ℝ) at hB
  have hl := Nat.lt_floor_add_one ((B : ℝ) ^ (8/25 : ℝ))
  have hpos : 0 < amplificationMultiplier B := by
    apply Nat.floor_pos.mpr
    linarith
  exact ⟨hpos,by dsimp [amplificationMultiplier] <;> linarith,
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)⟩

theorem amplificationMultiplier_valid : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
      (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := by
  have hlim := ((isLittleO_rpow_exp_pos_mul_atTop (8/25 : ℝ)
    (by norm_num : (0 : ℝ) < 1/10)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  filter_upwards [amplificationMultiplier_comparable,
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB he
  refine ⟨hB.1, hB.2.2.trans ?_⟩
  exact (div_le_one (Real.exp_pos _)).mp he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateWeightCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every individual normalized candidate weight tends uniformly to zero -/

namespace JointDickman
open Filter
open scoped Topology

theorem six_regular_weights_small {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (a b c : ℕ) (S₀ S₁ S₂ : Finset ℕ),
      (regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S₀ *
        (regularCoefficientWeight B L τ C b * regularResidueWeight B L τ C S₁) *
        (regularCoefficientWeight B L τ C c * regularResidueWeight B L τ C S₂))/(B : ℝ) ≤
          (B : ℝ)^(-(7/100 : ℝ)) := by
  let ε := (1-6*weightExponent τ-(7/100 : ℝ))/12
  have hm := (weight_margins_of_le_samplingTau hτsmall).2.1
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  have hexp : 6*(weightExponent τ+ε)-1 ≤ -(7/100 : ℝ) := by dsimp [ε] <;> linarith
  filter_upwards [regular_weights_cap hL hτ hε,eventually_gt_atTop 1] with B hcap hB
  intro C a b c S₀ S₁ S₂
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB.le
  let Q := (B : ℝ)^(weightExponent τ+ε)
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hpair (n : ℕ) (S : Finset ℕ) :
      regularCoefficientWeight B L τ C n * regularResidueWeight B L τ C S ≤ Q*Q :=
    mul_le_mul ((hcap C).2 n) ((hcap C).1 S)
      (regularResidueWeight_nonneg B L τ C S) hQ
  have hprod : regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S₀ *
      (regularCoefficientWeight B L τ C b * regularResidueWeight B L τ C S₁) *
      (regularCoefficientWeight B L τ C c * regularResidueWeight B L τ C S₂) ≤ Q^6 := by
    have h := mul_le_mul (mul_le_mul (hpair a S₀) (hpair b S₁)
      (mul_nonneg (regularCoefficientWeight_nonneg B L τ C b)
        (regularResidueWeight_nonneg B L τ C S₁)) (mul_nonneg hQ hQ)) (hpair c S₂)
      (mul_nonneg (regularCoefficientWeight_nonneg B L τ C c)
        (regularResidueWeight_nonneg B L τ C S₂)) (by positivity)
    convert h using 1 <;> first | rfl | ring
  calc
    _ ≤ Q^6/(B : ℝ) := div_le_div_of_nonneg_right hprod hBpos.le
    _ = (B : ℝ)^(6*(weightExponent τ+ε)-1) := by
      dsimp [Q]
      rw [Real.rpow_sub hBpos,Real.rpow_one,
        show 6*(weightExponent τ+ε) = (weightExponent τ+ε)*(6 : ℝ) by ring,
        Real.rpow_mul hBpos.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB1 hexp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCandidates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite candidate representations determined by endpoint types -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem mem_endpointSplits {B L : ℕ} {τ C : ℝ} {S A : Finset ℕ} :
    A ∈ endpointSplits B L τ C S ↔
      A ⊆ S ∧ RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A) := by
  classical
  simp [endpointSplits]

theorem endpointSplits_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, ∀ S : Finset ℕ,
      (endpointSplits B L τ C S).card ≤ B := by
  classical
  filter_upwards [regular_endpoint_subset_count hL hτ hτsmall] with B hB
  intro C S
  by_cases hn : (endpointSplits B L τ C S).Nonempty
  · obtain ⟨A,hA⟩ := hn
    obtain ⟨hAS,hreg,hrem⟩ := mem_endpointSplits.mp hA
    have hcount := hB C A (S \ A) hreg hrem
    have he : A ∪ (S \ A) = S := union_sdiff_of_subset hAS
    rw [he] at hcount
    exact (card_le_card (filter_subset _ _)).trans (by simpa only [card_powerset] using hcount)
  · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty]
    exact Nat.zero_le B

theorem blockCandidatePool_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ),
      (blockCandidatePool B L M τ C S).card ≤ M^2*B^2 := by
  classical
  filter_upwards [endpointSplits_card hL hτ hτsmall] with B hB
  intro C M S
  unfold blockCandidatePool
  calc
    _ ≤ ∑ ik : Fin M × Fin M,
        (((endpointSplits B L τ C (S ik.1)).product
          (endpointSplits B L τ C (S ik.2))).image (fun ab => (ik,ab))).card := card_biUnion_le
    _ ≤ ∑ _ik : Fin M × Fin M, B*B := by
      apply sum_le_sum
      intro ik _
      exact card_image_le.trans (by
        rw [Finset.product_eq_sprod,Finset.card_product]
        exact Nat.mul_le_mul (hB C (S ik.1)) (hB C (S ik.2)))
    _ = _ := by simp [pow_two,mul_assoc]

theorem blockCandidates_card {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ),
      (blockCandidates B L T H M τ C S).card ≤ M^2*B^2 := by
  classical
  filter_upwards [blockCandidatePool_card hL hτ hτsmall] with B hB
  intro C T H M S
  exact (card_le_card (filter_subset _ _)).trans (hB C M S)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRootGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniqueness of a representation at a fixed pair of endpoints -/

namespace JointDickman
open Finset

open Classical in
theorem mem_blockCandidatePool {B L M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidatePool B L M τ C S ↔
      e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
      e.2.2 ∈ endpointSplits B L τ C (S e.1.2) := by
  unfold blockCandidatePool
  constructor
  · intro h
    obtain ⟨ik,_,h⟩ := mem_biUnion.mp h
    obtain ⟨ab,hab,he⟩ := mem_image.mp h
    subst e
    simpa only [Finset.product_eq_sprod,mem_product] using hab
  · rintro ⟨hlo,hhi⟩
    apply mem_biUnion.mpr
    refine ⟨e.1,mem_univ _,mem_image.mpr ⟨e.2,?_,by cases e; rfl⟩⟩
    simpa only [Finset.product_eq_sprod,mem_product] using And.intro hlo hhi

open Classical in
theorem mem_blockCandidates {B L T H M : ℕ} {τ C : ℝ} {S : Fin M → Finset ℕ}
    {e : BlockCandidateIndex M} :
    e ∈ blockCandidates B L T H M τ C S ↔
      (e.2.1 ∈ endpointSplits B L τ C (S e.1.1) ∧
        e.2.2 ∈ endpointSplits B L τ C (S e.1.2)) ∧
      BlockCandidateAdmissible B L T H τ C e := by
  simp only [blockCandidates,mem_filter,mem_blockCandidatePool]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CutBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Real cut tests control complex label energies

This is the deterministic estimate (graph-cut-labels) in the manuscript.
It makes no independence assumption about the labels and the kernel.
-/

open scoped BigOperators ComplexConjugate

namespace JointDickman

theorem abs_cutSign (b : Bool) : |cutSign b| = 1 := by
  cases b <;> norm_num [cutSign]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-product moments for the sampling argument

All expectations here are finite sums with the actual independent site
masses. The variance identities, conditional moments, and absolute-error
estimates are proved directly; no moment or independence input is assumed.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section Expectation

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_const (w : Ω → ℝ) (hw : (∑ x, w x) = 1) (c : ℝ) :
    finiteExpectation w (fun _ => c) = c := by
  rw [finiteExpectation, ← sum_mul, hw, one_mul]

theorem finiteExpectation_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : finiteExpectation w f ≤ finiteExpectation w g := by
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x)

end Expectation

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative finite sampling transfer

The finite family consists of sampled column sequences and one sign per
sampled occurrence. Its cardinal is `(2 * N)^m`, including repeated columns.
The common bad event is paid once. Moment and tail obligations are explicit
mathematical hypotheses, not additional published inputs.
-/

open Finset
open scoped BigOperators
open JointDickman.PublishedInputs

namespace JointDickman

section ProbabilityTransfer

variable {Ω : Type*} [Fintype Ω]

theorem finiteExpectation_nonneg (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteExpectation w f :=
  sum_nonneg fun x _ => mul_nonneg (hw x) (hf x)

end ProbabilityTransfer

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernelCutMaximum_le (K : ι → ι → ℝ) (C : ℝ)
    (hC : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C) :
    kernelCutMaximum K ≤ C := by
  apply Finset.sup'_le
  intro st _
  exact hC st.1 st.2

theorem kernelCutMaximum_nonneg (K : ι → ι → ℝ) : 0 ≤ kernelCutMaximum K := by
  exact (abs_nonneg _).trans (Finset.le_sup'
    (fun st : (ι → Bool) × (ι → Bool) =>
      |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)
    (mem_univ ((fun _ => false), (fun _ => false))))

theorem kernelCutMaximum_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutMaximum K ≤ ∑ i, ∑ j, |K i j| := by
  apply kernelCutMaximum_le
  intro s t
  unfold realBilinear
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_mul, abs_cutSign]

theorem kernelCutNorm_le_absolute_mass (K : ι → ι → ℝ) :
    kernelCutNorm K ≤ kernelAbsoluteMass K :=
  div_le_div_of_nonneg_right (kernelCutMaximum_le_absolute_mass K) (Nat.cast_nonneg _)

end CutFamily

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMatrix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetric matrices assembled from unordered candidate edges -/

namespace JointDickman
open Finset

theorem realBilinear_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → κ → ℝ) (f g : κ → ℝ) :
    realBilinear (fun i k => ∑ e, K e i k) f g = ∑ e, realBilinear (K e) f g := by
  unfold realBilinear
  simp only [sum_mul]
  calc
    _ = ∑ i, ∑ e, ∑ k, K e i k*f i*g k := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

theorem candidateMatrix_bilinear {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (f g : κ → ℝ) :
    realBilinear (candidateMatrix row col v) f g =
      ∑ e, v e*(f (row e)*g (col e)+f (col e)*g (row e)) := by
  unfold candidateMatrix
  rw [realBilinear_sum]
  apply sum_congr rfl
  intro e _
  simp [realBilinear,add_mul,ite_mul,sum_add_distrib] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRootKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent auxiliary-root weights for the actual candidate list -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem independentPrimeSetMass_nonneg (B : ℕ) (R : (auxiliaryPrimes B).powerset) :
    0 ≤ independentPrimeSetMass B R := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp R.property)
  intro p hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
  exact ⟨by positivity, (div_le_one (by linarith : (0 : ℝ) < p)).mpr hp1⟩

theorem independentPrimeSetMass_sum (B : ℕ) : (∑ R, independentPrimeSetMass B R) = 1 := by
  exact (sum_coe_sort _ _).trans (bernoulliSubsetMass_sum _ _)

theorem candidateRootWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) (R : Finset ℕ) :
    0 ≤ candidateRootWeight B L τ C S χ e R := by
  unfold candidateRootWeight
  exact mul_nonneg (div_nonneg
    (mul_nonneg
      (mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))
        (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
          (regularResidueWeight_nonneg _ _ _ _ _)))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
        (regularResidueWeight_nonneg _ _ _ _ _))) (Nat.cast_nonneg B)) (hχ e)

theorem candidateRootWeight_small {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ (e : BlockCandidateIndex M) (R : Finset ℕ),
        candidateRootWeight B L τ C S χ e R ≤ (B : ℝ)^(-(7/100 : ℝ)) := by
  filter_upwards [six_regular_weights_small hL hτ hτsmall] with B hB
  intro C M S χ hχ e R
  have hn := candidateRootWeight_nonneg B L τ C S (fun _ => 1) (by simp) e R
  have he : candidateRootWeight B L τ C S χ e R =
      candidateRootWeight B L τ C S (fun _ => 1) e R * χ e := by
    simp only [candidateRootWeight,mul_one]
  rw [he]
  exact (mul_le_of_le_one_right hn (hχ e)).trans
    (by simpa only [candidateRootWeight,mul_one] using
      hB C (candidateLow e) (candidateHigh e) (candidateQuotient e)
          (S e.1.1 \ e.2.1) (S e.1.2 \ e.2.2) R)

theorem candidateMatrix_sub {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v w : ι → ℝ) (i k : κ) :
    candidateMatrix row col (fun e => v e-w e) i k =
      candidateMatrix row col v i k-candidateMatrix row col w i k := by
  unfold candidateMatrix
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  split_ifs <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RootSiteLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact categorical law of distinct residue roots at one prime -/

namespace JointDickman
open Finset

theorem rootHitSet_singleton {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (hinj : Set.InjOn root I)
    {i : ι} (hi : i ∈ I) : rootHitSet I root (root i) = {i} := by
  classical
  ext j
  simp only [rootHitSet, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hj,he⟩
    exact hinj hj hi he
  · rintro rfl
    exact ⟨hi,rfl⟩

theorem rootHitSet_test_identity {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (hinj : Set.InjOn root I)
    (F : Finset ι → ℝ) (r : ZMod p) :
    F (rootHitSet I root r) = F ∅+
      ∑ i ∈ I, if root i = r then F {i}-F ∅ else 0 := by
  classical
  by_cases h : ∃ i ∈ I, root i = r
  · obtain ⟨i,hi,rfl⟩ := h
    rw [rootHitSet_singleton I root hinj hi]
    have he (j : ι) (hj : j ∈ I) :
        (if root j = root i then F {j}-F ∅ else 0) =
          if j = i then F {j}-F ∅ else 0 := by
      have hh : root j = root i ↔ j = i := ⟨hinj hj hi, fun h => congrArg root h⟩
      simp only [hh]
    rw [sum_congr rfl he]
    simp [hi]
  · have hh (i : ι) (hi : i ∈ I) : root i ≠ r := fun he => h ⟨i,hi,he⟩
    have hzero : rootHitSet I root r = ∅ := by
      apply filter_eq_empty_iff.mpr
      exact hh
    rw [hzero]
    have hs : (∑ i ∈ I, if root i = r then F {i}-F ∅ else 0) = 0 :=
      sum_eq_zero (fun i hi => ite_eq_right (hh i hi))
    rw [hs,add_zero]

theorem categorical_mass_test {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (F : Finset ι → ℝ) :
    (∑ S ∈ I.powerset, categoricalSubsetMass I q S * F S) =
      (1-∑ i ∈ I, q i)*F ∅+∑ i ∈ I, q i*F {i} := by
  classical
  unfold categoricalSubsetMass
  simp only [add_mul, sum_add_distrib, sum_mul, ite_mul, zero_mul]
  congr 1
  · simp
  · rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    simp [mem_powerset, singleton_subset_iff, hi]

theorem root_site_uniform_mean {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) (F : Finset ι → ℝ) :
    (∑ r : ZMod p, F (rootHitSet I root r))/(p : ℝ) =
      ∑ S ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S * F S := by
  classical
  simp_rw [rootHitSet_test_identity I root hinj F]
  rw [sum_add_distrib, sum_comm, categorical_mass_test]
  have he (i : ι) : (∑ r : ZMod p, if root i = r then F {i}-F ∅ else 0) =
      F {i}-F ∅ := by simp [eq_comm]
  simp_rw [he]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_sub_distrib,
    ← mul_sum]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_BlockPrimeSites
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite-residue law at every site of a block -/

namespace JointDickman
open Finset

theorem root_site_pushMass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) :
    finitePushMass (fun (_ : ZMod p) => 1/(p : ℝ)) (rootHitType I root) =
      fun S => categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S.val := by
  classical
  funext S
  have h := root_site_uniform_mean I root hinj
    (fun R => if R = S.val then (1 : ℝ) else 0)
  have hr : (∑ R ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(p : ℝ)) R *
      (if R = S.val then (1 : ℝ) else 0)) =
      categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S.val := by
    simp only [mul_ite, mul_one, mul_zero]
    exact sum_ite_eq' I.powerset S.val _ |>.trans (ite_eq_left S.property)
  rw [hr] at h
  simpa only [finitePushMass, rootHitType, Subtype.ext_iff, sum_div,
    ite_div, zero_div] using h

theorem blockSiteRoot_injective (M p : ℕ) (hp : M < p) :
    Function.Injective (blockSiteRoot M p) := by
  intro i k hik
  have hcast : ((i.val+1 : ℕ) : ZMod p) = ((k.val+1 : ℕ) : ZMod p) :=
    neg_injective hik
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  apply Fin.ext
  omega

theorem blockPrimeHit_divisibility (M p n : ℕ) (i : Fin M) :
    i ∈ (blockPrimeHit M p (n : ZMod p)).val ↔ p ∣ n+(i.val+1) := by
  change (i ∈ rootHitSet univ (blockSiteRoot M p) (n : ZMod p)) ↔ _
  unfold rootHitSet
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, blockSiteRoot]
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    exact (eq_neg_of_add_eq_zero_left h).symm

theorem blockPrimeHit_pushMass (M p : ℕ) [NeZero p] (hp : M < p) :
    finitePushMass (fun (_ : ZMod p) => 1/(p : ℝ)) (blockPrimeHit M p) =
      fun S => categoricalSubsetMass univ (fun _ : Fin M => 1/(p : ℝ)) S.val :=
  root_site_pushMass univ (blockSiteRoot M p)
    (fun _ _ _ _ h => blockSiteRoot_injective M p hp h)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualCandidateProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The product estimate for the actual endpoint-dependent candidate list -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem block_prime_twice_sites {B M p : ℕ} (hB : 2 ≤ B) (hM : M ≤ B^2)
    (hp : p ∈ auxiliaryPrimes B) : M < p ∧ 2*M ≤ p := by
  have hcut : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
  have hpow : 2*M ≤ auxiliaryCutoff B := by
    change 2*M ≤ B^1000
    have hmul : B*B^2 = B^3 := by rw [pow_succ]; exact Nat.mul_comm _ _
    have hpower : B^3 ≤ B^1000 :=
      pow_le_pow_right₀ (show 1 ≤ B from Nat.le_trans (by decide : 1 ≤ 2) hB)
        (show (3 : ℕ) ≤ 1000 by decide)
    exact (Nat.mul_le_mul_left 2 hM).trans
      ((Nat.mul_le_mul_right (B^2) hB).trans (hmul.le.trans hpower))
  exact ⟨by omega,(hpow.trans hcut.le)⟩

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

end

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

theorem partialFairPrimeTransition_nonneg {A : Type*} [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) (a : A) :
    0 ≤ partialFairPrimeTransition Q cell x a :=
  optionCellMass_nonneg _ _ (fairRetentionMass_nonneg x) a

theorem partialFairPrimeTransition_sum_le {A : Type*} [Fintype A] [DecidableEq A]
    (Q : Finset ℕ) (cell : ℕ → Option A) (x : Q → Bool) :
    (∑ a, partialFairPrimeTransition Q cell x a) ≤ 1 := by
  have h := optionCellMass_sum_le (fairRetentionMass x) (fun y => cell (retainedPrimeProduct Q y))
    (fairRetentionMass_nonneg x)
  simpa only [partialFairPrimeTransition, fairRetentionMass_sum] using h

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

theorem channelMesh_pos {n : ℕ} (hn : 0 < n) : 0 < channelMesh n :=
  div_pos (by norm_num) (by exact_mod_cast hn)

theorem channel_width (n : ℕ) (i : Fin n) : channelUpper n i - channelLower n i = channelMesh n := by
  unfold channelUpper channelLower
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseGrid
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the manuscript grid into equal coarse cells -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem channelFineCount_eq (m B : ℕ) : channelFineCount m B = m * channelBlockCount m B := rfl

theorem channelFineCount_lower {m B : ℕ} (hm : 0 < m) :
    (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) ≤ channelFineCount m B := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left
    (Nat.le_ceil (((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m)) hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_div_cancel₀ _ hm0.ne'] using h

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

theorem averagingRamp_lipschitz {a b : ℝ} (hab : a < b) :
    LipschitzWith ⟨1 / (b - a), by positivity⟩ (averagingRamp a b) := by
  have hclip := (LipschitzWith.id.const_max a).const_min b
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc := hclip.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
  change |averagingRamp a b x - averagingRamp a b y| ≤ (1 / (b - a)) * |x - y|
  have heq : averagingRamp a b x - averagingRamp a b y =
      (min b (max a x) - min b (max a y)) / (b - a) := by unfold averagingRamp; ring
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab), one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right hc (sub_pos.mpr hab).le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughMeanNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalization of rough summatory means -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughMeanNormalization_ratio {B : ℕ} (hB : 1 < B) (z : ℝ) :
    roughMeanNormalization B z / (B : ℝ) = 1 / auxiliaryRatio B ^ z := by
  have hR := auxiliaryRatio_pos hB
  have hmul := auxiliaryRatio_mul_log hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hB)
  have hrpow : auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    simp
  unfold roughMeanNormalization
  apply (div_eq_div_iff hB0 (Real.rpow_pos_of_pos hR z).ne').mpr
  calc
    _ = Real.log (auxiliaryCutoff B) *
        (auxiliaryRatio B ^ (1 - z) * auxiliaryRatio B ^ z) := by ring
    _ = B := by rw [hrpow, mul_comm, hmul]
    _ = _ := by ring

theorem roughMeanNormalization_quotient_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun B => roughMeanNormalization B z /
      (primeNormalizer (auxiliaryPrimes B) z * B)) atTop (𝓝 ((4 : ℝ) ^ z)) := by
  have hlim := (auxiliary_primeNormalizer_tendsto hM hz hz1).inv₀
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (-z)).ne'
  have heq : (fun B => (primeNormalizer (auxiliaryPrimes B) z * auxiliaryRatio B ^ z)⁻¹) =ᶠ[atTop]
      (fun B => roughMeanNormalization B z / (primeNormalizer (auxiliaryPrimes B) z * B)) := by
    filter_upwards [eventually_gt_atTop 1] with B hB
    conv_rhs => rw [mul_comm (primeNormalizer (auxiliaryPrimes B) z)]
    rw [div_mul_eq_div_div, roughMeanNormalization_ratio hB]
    ring
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)] at hlim
  simpa only [inv_inv] using hlim.congr' heq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First and second moments of the actual coefficient A₀

These are the estimates in equation (5) of the manuscript.  The two
specializations of the published Selberg–Delange input suffice here.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_eq_roughMeanNormalization (B : ℕ) :
    coefficientScale B = roughMeanNormalization B (1 / 2) := by
  norm_num [coefficientScale, roughMeanNormalization]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform boundedness of the actual A0 density away from zero -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem auxiliary_half_normalizer_pos (B : ℕ) :
    0 < primeNormalizer (auxiliaryPrimes B) (1/2) := by
  unfold primeNormalizer
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact sub_pos.mpr ((div_lt_one (by linarith : (0 : ℝ) < p)).mpr (by norm_num <;> linarith))

theorem coefficientDensity_eq_scaled (c : ℕ → ℝ) (H B : ℕ) {s : ℝ}
    (hB : 0 < B) (hs : 0 < s) :
    coefficientDensity c H B s =
      (coefficientScale B / (primeNormalizer (auxiliaryPrimes B) (1/2)*B))*
        scaledRoughDensity c (1/2) H B s := by
  rw [scaledRoughDensity_eq c (1/2) H B hB hs]
  unfold coefficientDensity
  have hQ := (auxiliary_half_normalizer_pos B).ne'
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  field_simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCoarseFeatures
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded coarse features of the actual prime-site distribution -/

namespace JointDickman
open Finset

theorem channelBlockCount_pos {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    0 < channelBlockCount m B := by
  have h := channelFineCount_pos hm hB
  rw [channelFineCount_eq] at h
  exact Nat.pos_of_ne_zero (by intro he; simp [he] at h)

theorem channelMesh_block_normalization {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    channelMesh (channelFineCount m B)*(channelBlockCount m B : ℝ) = channelMesh m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (channelBlockCount m B : ℝ) ≠ 0 := by
    exact_mod_cast (channelBlockCount_pos hm hB).ne'
  unfold channelMesh
  rw [channelFineCount_eq,Nat.cast_mul]
  field_simp

theorem primeCoarseFeature_bounds {m B : ℕ} (hm : 0 < m)
    (d : Fin m) (x : auxiliaryPrimes B → Bool) :
    0 ≤ primeCoarseFeature m B d x ∧ primeCoarseFeature m B d x ≤ 1/channelMesh m := by
  have hp (a : Fin m × Fin (channelBlockCount m B)) :
      0 ≤ primeGroupedTransition m B x a := partialFairPrimeTransition_nonneg _ _ _ _
  have hsum : (∑ r, primeGroupedTransition m B x (d,r)) ≤ 1 := by
    have hh := single_le_sum (s := univ) (f := fun e : Fin m =>
      ∑ r, primeGroupedTransition m B x (e,r))
      (fun e _ => sum_nonneg (fun r _ => hp (e,r))) (mem_univ d)
    have htotal : (∑ e : Fin m, ∑ r, primeGroupedTransition m B x (e,r)) ≤ 1 := by
      rw [← Fintype.sum_prod_type]
      exact partialFairPrimeTransition_sum_le _ _ _
    exact hh.trans htotal
  unfold primeCoarseFeature
  exact ⟨div_nonneg (sum_nonneg (fun r _ => hp (d,r))) (channelMesh_pos hm).le,
    div_le_div_of_nonneg_right hsum (channelMesh_pos hm).le⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CoarseFeatureBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the finite-feature approximation -/

namespace JointDickman
open Finset

theorem groupedKernelCoefficient_bound {D R : Type*} [Fintype D] [Fintype R]
    (δ : ℝ) (K : D × R → D × R → ℝ) {C : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ a, (∑ b, δ*|K a b|) ≤ C) (d e : D) :
    |groupedKernelCoefficient δ K d e| ≤ δ*(Fintype.card R : ℝ)*C := by
  have hpart (r : R) : (∑ s, δ*|K (d,r) (e,s)|) ≤ C := by
    have hh := single_le_sum (s := univ) (f := fun b : D => ∑ s, δ*|K (d,r) (b,s)|)
      (fun b _ => sum_nonneg (fun s _ => mul_nonneg hδ (abs_nonneg _))) (mem_univ e)
    exact hh.trans (by simpa only [Fintype.sum_prod_type] using hrow (d,r))
  calc
    _ = δ^2*|∑ r, ∑ s, K (d,r) (e,s)| := by
      rw [groupedKernelCoefficient,abs_mul,abs_of_nonneg (sq_nonneg δ)]
    _ ≤ δ^2*(∑ r, ∑ s, |K (d,r) (e,s)|) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun r _ => abs_sum_le_sum_abs _ _))
    _ = δ*(∑ r, ∑ s, δ*|K (d,r) (e,s)|) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro r _
      apply sum_congr rfl
      intro s _
      ring
    _ ≤ δ*(∑ _r : R, C) := mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hpart r)) hδ
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul] <;> ring

theorem primeCoarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (d e : Fin m) : |primeCoarseCoefficient m B K d e| ≤ channelMesh m*C := by
  have hr (a : Fin m × Fin (channelBlockCount m B)) :
      (∑ b, channelMesh (channelFineCount m B)*
        |K (channelIndexEquiv m B a) (channelIndexEquiv m B b)|) ≤ C := by
    rw [(channelIndexEquiv m B).sum_comp
      (fun j => channelMesh (channelFineCount m B)*|K (channelIndexEquiv m B a) j|)]
    exact hrow _
  have hh := groupedKernelCoefficient_bound (channelMesh (channelFineCount m B))
    (fun a b => K (channelIndexEquiv m B a) (channelIndexEquiv m B b))
    (channelMesh_pos (channelFineCount_pos hm hB)).le hr d e
  simpa only [primeCoarseCoefficient,Fintype.card_fin,channelMesh_block_normalization hm hB] using hh

theorem primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (K : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ i, (∑ j, channelMesh (channelFineCount m B)*|K i j|) ≤ C)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B K x y| ≤ (m : ℝ)^2*C/channelMesh m := by
  have hμ := channelMesh_pos hm
  have hterm (d e : Fin m) :
      |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| ≤
        C/channelMesh m := by
    rw [abs_mul,abs_mul,
      abs_of_nonneg (primeCoarseFeature_bounds hm d x).1,
      abs_of_nonneg (primeCoarseFeature_bounds hm e y).1]
    have hh := mul_le_mul
      (mul_le_mul (primeCoarseCoefficient_bound hm hB K hrow d e)
        (primeCoarseFeature_bounds hm d x).2 (primeCoarseFeature_bounds hm d x).1
        (mul_nonneg hμ.le hC))
      (primeCoarseFeature_bounds hm e y).2 (primeCoarseFeature_bounds hm e y).1
      (by positivity : 0 ≤ channelMesh m*C*(1/channelMesh m))
    exact hh.trans_eq (by field_simp)
  unfold primeCoarseKernel
  calc
    _ ≤ ∑ d : Fin m, ∑ e : Fin m,
        |primeCoarseCoefficient m B K d e*primeCoarseFeature m B d x*primeCoarseFeature m B e y| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _d : Fin m, ∑ _e : Fin m, C/channelMesh m :=
      sum_le_sum (fun d _ => sum_le_sum (fun e _ => hterm d e))
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDensityRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Lipschitz control of the coefficient density -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientDensity_bounded_lipschitz
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    {δ : ℝ} (hδ : 0 < δ) (H : ℕ) :
    ∃ M L : ℝ, 0 ≤ M ∧ 0 ≤ L ∧ ∀ᶠ B : ℕ in atTop,
      (∀ s : ℝ, δ ≤ s → |coefficientDensity c H B s| ≤ M) ∧
      (∀ s t : ℝ, δ ≤ s → δ ≤ t →
        |coefficientDensity c H B s-coefficientDensity c H B t| ≤ L*|s-t|) := by
  obtain ⟨M,hM0,L,hbound⟩ := scaledRoughDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2) hδ H
  let J : ℝ := (4 : ℝ)^(1/2 : ℝ)+1
  have hJ : 0 ≤ J := by dsimp [J] <;> positivity
  have hquot : ∀ᶠ B : ℕ in atTop,
      |coefficientScale B/(primeNormalizer (auxiliaryPrimes B) (1/2)*B)| ≤ J := by
    have hh := (roughMeanNormalization_quotient_tendsto hM
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)).abs
    have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1/2 : ℝ)
    have he := hh.eventually (eventually_le_nhds (lt_add_one |(4 : ℝ)^(1/2 : ℝ)|))
    simpa only [← coefficientScale_eq_roughMeanNormalization,abs_of_pos hpos] using he
  refine ⟨J*M,J*(L : ℝ),mul_nonneg hJ hM0,mul_nonneg hJ L.coe_nonneg,?_⟩
  filter_upwards [hbound,hquot,eventually_gt_atTop 0] with B hboundB hquotB hB
  constructor
  · intro s hs
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),abs_mul]
    exact mul_le_mul hquotB (hboundB.1 s hs) (abs_nonneg _) hJ
  · intro s t hs ht
    rw [coefficientDensity_eq_scaled c H B hB (hδ.trans_le hs),
      coefficientDensity_eq_scaled c H B hB (hδ.trans_le ht),← mul_sub,abs_mul]
    have hh := hboundB.2.dist_le_mul s hs t ht
    rw [Real.dist_eq,Real.dist_eq] at hh
    calc
      _ ≤ J*((L : ℝ)*|s-t|) := mul_le_mul hquotB hh (abs_nonneg _) hJ
      _ = _ := by ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_GeometricCoarseKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricFeatureBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual box-summed finite-feature kernel -/

namespace JointDickman
open Finset

theorem geometric_primeCoarseKernel_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t β a b D M₁ M₂ M₀ : ℝ} (ht : 0 < t) (ha : 0 < a) (hab : a ≤ b)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k| ≤ D)
    (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (x y : auxiliaryPrimes B → Bool) :
    |primeCoarseKernel m B
      (geometricWindowKernel m B t (Real.log a) (Real.log b) S
        (endpointSpatialWeight m B t β d w₁ w₂ w)) x y| ≤
      (m : ℝ)^2*(2*((((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)))*
        (Real.log b-Real.log a+2))/channelMesh m := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogs := Real.log_le_log ha hab
  let M := ((1+Real.log b-Real.log a)/t+1)*(D*M₁*M₂*M₀)
  have hoverlap : 0 ≤ (1+Real.log b-Real.log a)/t+1 :=
    add_nonneg (div_nonneg (by linarith) ht.le) zero_le_one
  have hM : 0 ≤ M := mul_nonneg hoverlap (by positivity)
  have hwidth : 0 ≤ Real.log b-Real.log a+1 := by linarith
  have hwidth' : 0 ≤ Real.log b-Real.log a+2 := by linarith
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hlogs
    (by positivity : 0 ≤ D*M₁*M₂*M₀) S (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight_bound m B t β S d w₁ w₂ w hD hM₁ hM₂ hd hw₁ hw₂ hw)
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  have hh := primeCoarseKernel_bound hm hBpos
    (geometricWindowKernel m B t (Real.log a) (Real.log b) S
      (endpointSpatialWeight m B t β d w₁ w₂ w)) (by positivity : 0 ≤ 2*M*(Real.log b-Real.log a+2))
    (by intro i; convert hr i using 1; ring) x y
  simpa only [M,sub_add_eq_add_sub,add_assoc] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoarseCoefficientVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative variation of the actual geometric coarse coefficients -/
namespace JointDickman
open Finset Classical

theorem primeCoarseCoefficient_sub (m B : ℕ)
    (K L : Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (a b : Fin m) :
    primeCoarseCoefficient m B K a b-primeCoarseCoefficient m B L a b =
      primeCoarseCoefficient m B (fun i j => K i j-L i j) a b := by
  simp only [primeCoarseCoefficient,groupedKernelCoefficient,sum_sub_distrib,mul_sub]

theorem geometricWindowKernel_sub (m B : ℕ) (t L U : ℝ) (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (i j : Fin (channelFineCount m B)) :
    geometricWindowKernel m B t L U S V i j-geometricWindowKernel m B t L U S W i j =
      geometricWindowKernel m B t L U S (fun k i j => V k i j-W k i j) i j := by
  unfold geometricWindowKernel
  rw [← mul_sub,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem geometric_coarseCoefficient_bound {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, |V k i j| ≤ D) (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hwidth : 0 ≤ U-L+1 := by linarith
  have hoverlap : 0 ≤ (1+U-L)/t+1 := by
    apply add_nonneg _ zero_le_one
    exact div_nonneg (by linarith) ht.le
  have hM : 0 ≤ ((1+U-L)/t+1)*D := mul_nonneg hoverlap hD
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 :=
    (channelMesh_scale_bound hm hBpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : -(1/10 : ℝ) ≤ 0))
  obtain ⟨hheight,hsupp⟩ := geometricWindowKernel_bounds hm hB ht hLU hD S V hV
  have hr := (fineGridKernel_schur (channelFineCount_pos hm hBpos) _ hBr hwidth hM hmesh hheight hsupp).1
  apply primeCoarseCoefficient_bound hm hBpos _ _ a b
  intro i
  convert hr i using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem geometric_coarseCoefficient_difference {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D : ℝ} (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D)
    (S : Finset ℤ)
    (V W : ℤ → Fin (channelFineCount m B) → Fin (channelFineCount m B) → ℝ)
    (hV : ∀ k ∈ S, ∀ i j, i ∈ geometricHistogramWindow m B t L U k →
      j ∈ geometricHistogramWindow m B t L U k → |V k i j-W k i j| ≤ D)
    (a b : Fin m) :
    |primeCoarseCoefficient m B (geometricWindowKernel m B t L U S V) a b-
      primeCoarseCoefficient m B (geometricWindowKernel m B t L U S W) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*D)*(U-L+2)) := by
  let Z := fun k i j => if i ∈ geometricHistogramWindow m B t L U k ∧
    j ∈ geometricHistogramWindow m B t L U k then V k i j-W k i j else 0
  have hZ : ∀ k ∈ S, ∀ i j, |Z k i j| ≤ D := by
    intro k hk i j
    by_cases hh : i ∈ geometricHistogramWindow m B t L U k ∧ j ∈ geometricHistogramWindow m B t L U k
    · simpa [Z,hh] using hV k hk i j hh.1 hh.2
    · simpa [Z,hh] using hD
  rw [primeCoarseCoefficient_sub]
  have he : (fun i j => geometricWindowKernel m B t L U S V i j-
      geometricWindowKernel m B t L U S W i j) = geometricWindowKernel m B t L U S Z := by
    funext i j
    rw [geometricWindowKernel_sub]
    unfold geometricWindowKernel
    congr 1
    apply sum_congr rfl
    intro k _
    simp only [Z]
    split_ifs <;> rfl
  rw [he]
  exact geometric_coarseCoefficient_bound hm hB ht hLU hD S Z hZ a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplitudeParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of coarse coefficients under changing box amplitudes -/
namespace JointDickman
open Finset Classical

theorem endpointSpatialWeight_amplitude_difference (m B : ℕ) (t β : ℝ)
    (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {D M₁ M₂ M₀ : ℝ}
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (k : ℤ) (hd : |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀)
    (i j : Fin (channelFineCount m B)) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t β e w₁ w₂ w k i j| ≤ D*M₁*M₂*M₀ := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y)| ≤ _
  rw [show d k*w₁ x*w₂ y*w (β*x-β*y)-e k*w₁ x*w₂ y*w (β*x-β*y) =
    (d k-e k)*w₁ x*w₂ y*w (β*x-β*y) by ring]
  simp only [abs_mul]
  exact mul_le_mul (mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD)
    (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)) (hw _) (abs_nonneg _)
    (mul_nonneg (mul_nonneg hD hM₁) hM₂)

theorem geometric_coarseCoefficient_amplitude_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B) {t L U β D M₁ M₂ M₀ : ℝ}
    (ht : 0 < t) (hLU : L ≤ U) (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁)
    (hM₂ : 0 ≤ M₂) (hM₀ : 0 ≤ M₀)
    (S : Finset ℤ) (d e : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hd : ∀ k ∈ S, |d k-e k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁)
    (hw₂ : ∀ z, |w₂ z| ≤ M₂) (hw : ∀ z, |w z| ≤ M₀) (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β e w₁ w₂ w)) a b| ≤
      channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*M₀))*(U-L+2)) := by
  exact geometric_coarseCoefficient_difference hm hB ht hLU (by positivity) S _ _
    (fun k hk i j _ _ => endpointSpatialWeight_amplitude_difference m B t β d e w₁ w₂ w
      hD hM₁ hM₂ k (hd k hk) hw₁ hw₂ hw i j) a b

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square CRT with the first and higher digits kept separate -/

namespace JointDickman
open Finset

/-- Uniform CRT residues retain independent uniform higher digits after
all first digits are exposed. The test may depend on both entire families. -/
theorem prime_square_crt_digits (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (hP : ∀ p ∈ P, p.Prime)
    (F : (∀ p : P, ZMod p.val) → (∀ p : P, ZMod p.val) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p^2),
      F (fun p => (primeDigits p.val (n : ZMod (p.val^2))).1)
        (fun p => (primeDigits p.val (n : ZMod (p.val^2))).2)) /
      (∏ p ∈ P, (p : ℝ)^2) =
    (∑ r, ∑ t, F r t) / (∏ p ∈ P, (p : ℝ)^2) := by
  classical
  have hcop : Pairwise (fun p q : P => (p.val^2).Coprime (q.val^2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hP p.val p.property) (hP q.val q.property)).mpr
      (fun h => hpq (Subtype.ext h))).pow _ _
  let G := fun x : ∀ p : P, ZMod (p.val^2) =>
    F (fun p => (primeDigits p.val (x p)).1) (fun p => (primeDigits p.val (x p)).2)
  have h := crt_uniform_mean (fun p : P => p.val^2) hcop G
  rw [P.prod_coe_sort (fun p : ℕ => p^2)] at h
  have hd : (∏ p : P, ((p.val^2 : ℕ) : ℝ)) = ∏ p ∈ P, (p : ℝ)^2 := by
    simp only [Nat.cast_pow]
    exact prod_coe_sort P (fun p : ℕ => (p : ℝ)^2)
  rw [hd] at h
  have hw (x : ∀ p : P, ZMod (p.val^2)) :
      finiteProductMass (fun p : P => fun _ : ZMod (p.val^2) => 1/((p.val^2 : ℕ) : ℝ)) x =
        1/(∏ p ∈ P, (p : ℝ)^2) := by
    simp only [finiteProductMass,prod_div_distrib,prod_const_one,hd]
  simp_rw [hw,one_div_mul_eq_div] at h
  rw [← sum_div] at h
  have hs : (∑ x, G x) = ∑ r, ∑ t, F r t := by
    have he := (primeDigitFamilyEquiv P).sum_comp (fun x => F x.1 x.2)
    exact he.trans (Fintype.sum_prod_type _)
  exact h.trans (congrArg (fun x => x/(∏ p ∈ P, (p : ℝ)^2)) hs)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitArithmetic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic reconstruction of prime-square digit tests -/

namespace JointDickman

theorem primeDigits_first {p : ℕ} [NeZero p] (u : ℕ) :
    (primeDigits p (u : ZMod (p^2))).1 = (u : ZMod p) := by
  change (((u : ZMod (p^2)).val : ℕ) : ZMod p) = (u : ZMod p)
  rw [ZMod.val_natCast,← ZMod.natCast_mod _ p,← ZMod.natCast_mod u p]
  congr 1
  exact Nat.mod_mod_of_dvd u (dvd_pow_self _ (by omega : 2 ≠ 0))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSiteComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic comparison of all arithmetic sites of a finite block -/

namespace JointDickman
open Finset

theorem block_sites_crt_mean (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, M < p)
    (F : (P → (univ : Finset (Fin M)).powerset) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p), F (blockSiteResidues M P n))/
        (∏ p ∈ P, (p : ℝ)) =
      ∑ x, categoricalProductMass univ (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hc := crt_uniform_mean (fun p : P => p.val) hcop
    (fun x => F (fun p => blockPrimeHit M p.val (x p)))
  have hp := finiteProductMass_pushforward_test
    (fun (p : P) (_ : ZMod p.val) => 1/(p.val : ℝ))
    (fun p : P => blockPrimeHit M p.val) (fun x => (F x : ℂ))
  simp only [blockPrimeHit_pushMass M _ (hlarge _ (Subtype.property _))] at hp
  have hp' : (∑ x, categoricalProductMass univ
      (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x) =
      ∑ x, finiteProductMass (fun (p : P) (_ : ZMod p.val) => 1/(p.val : ℝ)) x *
        F (fun p => blockPrimeHit M p.val (x p)) := by
    exact_mod_cast hp
  rw [P.prod_coe_sort (fun p : ℕ => p), P.prod_coe_sort (fun p : ℕ => (p : ℝ))] at hc
  exact hc.trans hp'.symm

theorem block_sites_independent_error (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, M < p)
    (F : (P → (univ : Finset (Fin M)).powerset) → ℝ)
    {L : ℝ} (hL : 0 ≤ L) (hF : ∀ x, |F x| ≤ L) :
    |(∑ n ∈ range (∏ p ∈ P, p), F (blockSiteResidues M P n))/
        (∏ p ∈ P, (p : ℝ)) -
      ∑ x, bernoulliProductMass univ (fun p : P => fun _ : Fin M => 1/(p.val : ℝ)) x * F x| ≤
        2*L*(M : ℝ)^2*(∑ p ∈ P, 1/(p : ℝ)^2) := by
  have hcard : ∀ p ∈ P, (univ : Finset (Fin M)).card ≤ p := by
    intro p hp
    simpa using (hlarge p hp).le
  have h := categoricalPrimeProduct_test_bound (univ : Finset (Fin M)) P hP hcard
    (fun x => (F x : ℂ)) hL
    (fun x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hF x)
  rw [block_sites_crt_mean M P hP hlarge F]
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, card_univ, Fintype.card_fin] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteTranspose
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing independent prime hits as independent endpoint sets -/

namespace JointDickman
open Finset

theorem primeSiteTranspose_hit {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (x : P → I.powerset) (i : I) (p : P) :
    subsetHitEquiv P (primeSiteTranspose I P x i) p = subsetHitEquiv I (x p) i := by
  simp [primeSiteTranspose]
  rfl

theorem primeSiteTranspose_mem {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (x : P → I.powerset) (i : I) (p : P) :
    p.val ∈ (primeSiteTranspose I P x i).val ↔ i.val ∈ (x p).val := by
  have h := primeSiteTranspose_hit I P x i p
  by_cases hp : p.val ∈ (primeSiteTranspose I P x i).val <;>
    by_cases hi : i.val ∈ (x p).val <;> simp_all [subsetHitEquiv]

theorem primeSiteTranspose_mass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (P : Finset ℕ) (q : ℕ → ℝ) (x : P → I.powerset) :
    bernoulliProductMass I (fun p : P => fun _ => q p.val) x =
      finiteProductMass (fun _ : I => fun S : P.powerset => bernoulliSubsetMass P q S.val)
        (primeSiteTranspose I P x) := by
  classical
  have hl (p : P) : bernoulliSubsetMass I (fun _ : ι => q p.val) (x p).val =
      ∏ i : I, bernoulliBitMass (q p.val) (subsetHitEquiv I (x p) i) :=
    (bernoulliSubsetMass_eq_product I (fun _ : ι => q p.val) (x p)).symm
  have hr (i : I) : bernoulliSubsetMass P q (primeSiteTranspose I P x i).val =
      ∏ p : P, bernoulliBitMass (q p.val) (subsetHitEquiv I (x p) i) := by
    rw [← bernoulliSubsetMass_eq_product P q (primeSiteTranspose I P x i)]
    simp only [finiteProductMass,primeSiteTranspose_hit]
  change (∏ p : P, bernoulliSubsetMass I (fun _ : ι => q p.val) (x p).val) =
    ∏ i : I, bernoulliSubsetMass P q (primeSiteTranspose I P x i).val
  simp_rw [hl,hr]
  exact prod_comm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_MaskedResidueModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conditional law of the masked arithmetic residue model -/

namespace JointDickman
open Finset Classical

theorem primePatternsSites_mem {B M : ℕ} (H : BlockPrimePatterns B M)
    (p : auxiliaryPrimes B) (i : Fin M) :
    p.val ∈ primePatternsSites H i ↔ i ∈ (H p).val :=
  primeSiteTranspose_mem univ (auxiliaryPrimes B) H ⟨i,mem_univ _⟩ p

/-- The observed site types are exactly the auxiliary prime divisors of
all the translated integers in the block. -/
theorem primePatternsSites_arithmetic (B M u : ℕ) (i : Fin M) :
    primePatternsSites (arithmeticPrimePatterns B M u) i =
      coefficientPrimeSet B (u+(i.val+1)) := by
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · have hs := primePatternsSites_mem (arithmeticPrimePatterns B M u) ⟨p,hp⟩ i
    rw [hs]
    change i ∈ (blockPrimeHit M p (u : ZMod p)).val ↔ _
    rw [blockPrimeHit_divisibility]
    simp [coefficientPrimeSet,hp]
  · have hs : p ∉ primePatternsSites (arithmeticPrimePatterns B M u) i := by
      intro h
      exact hp (mem_powerset.mp
        (primeSiteTranspose univ (auxiliaryPrimes B) (arithmeticPrimePatterns B M u)
          ⟨i,mem_univ _⟩).property h)
    simp [hs,coefficientPrimeSet,hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSiteErrorScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block-site comparison error at the manuscript's cutoff scale -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_block_size_le_square (A : ℕ) :
    ∀ᶠ B : ℕ in atTop, A*amplificationMultiplier B ≤ B^2 := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop A,
    eventually_ge_atTop 1] with B hT hA hB
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hBreal (show (8/25 : ℝ) ≤ 1 by norm_num)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  calc
    _ ≤ B*B := Nat.mul_le_mul hA hTB
    _ = _ := by ring

theorem block_site_polynomial_error_bound {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    {C : ℝ} (hC : 0 ≤ C) :
    2*(C*(B : ℝ)^10)*(M : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) ≤
      2*C/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B)
    (show auxiliaryCutoff B ≠ 0 from pow_ne_zero _ (by omega)) (by
      intro p hp
      exact_mod_cast (mem_filter.mp hp).2)
  have hpow : (B : ℝ)^15 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff,Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 15 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 15) hpow)
  have hMreal : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  calc
    _ ≤ 2*(C*(B : ℝ)^10)*((B : ℝ)^2)^2*(1/(B : ℝ)^15) := by gcongr
    _ = _ := by field_simp

theorem block_sites_auxiliary_comparison {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    (F : (auxiliaryPrimes B → (univ : Finset (Fin M)).powerset) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ x, |F x| ≤ C*(B : ℝ)^10) :
    |(∑ n ∈ range (∏ p ∈ auxiliaryPrimes B, p), F (blockSiteResidues M (auxiliaryPrimes B) n))/
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ)) -
      ∑ x, bernoulliProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) x * F x| ≤
      2*C/(B : ℝ) := by
  have hP : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hlarge : ∀ p ∈ auxiliaryPrimes B, M < p := by
    intro p hp
    have hp' : (auxiliaryCutoff B : ℝ) < p := (mem_filter.mp hp).2
    have hcut : B^2 ≤ auxiliaryCutoff B := by
      change B^2 ≤ B^1000
      exact pow_le_pow_right₀ (Nat.le_of_lt hB) (by decide : 2 ≤ 1000)
    have hpi : auxiliaryCutoff B < p := by exact_mod_cast hp'
    exact (hM.trans hcut).trans_lt hpi
  exact (block_sites_independent_error M (auxiliaryPrimes B) hP hlarge F
    (by positivity) hF).trans (block_site_polynomial_error_bound hB hM hC)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeDigitAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the adaptive coefficient exceptions over prime digits -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem uniformZModMass_sum (p : ℕ) [NeZero p] :
    (∑ _ : ZMod p, (1 : ℝ)/p) = 1 := by
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  field_simp

theorem primeDigitMass_sum (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val] :
    (∑ r, primeDigitMass B r) = 1 :=
  finiteProductMass_sum _ (fun p => uniformZModMass_sum p.val)

theorem residuePrimePatterns_arithmetic (B M u : ℕ) :
    residuePrimePatterns (M := M) (arithmeticFirstDigits B u) = arithmeticPrimePatterns B M u := by
  funext p
  let : NeZero p.val := ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  simp only [residuePrimePatterns,arithmeticFirstDigits,primeDigits_first,arithmeticPrimePatterns]

theorem prime_square_crt_average (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (F : (∀ p : auxiliaryPrimes B, ZMod p.val) →
      (∀ p : auxiliaryPrimes B, ZMod p.val) → ℝ) :
    (∑ u ∈ range (∏ p ∈ auxiliaryPrimes B, p^2),
      F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u)) /
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2) =
      finiteExpectation (primeDigitMass B)
        (fun r => finiteExpectation (primeDigitMass B) (F r)) := by
  trans (∑ r, ∑ t, F r t)/(∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2)
  · exact prime_square_crt_digits (auxiliaryPrimes B) (auxiliaryPrimes_prime B) F
  · have hw (r : ∀ p : auxiliaryPrimes B, ZMod p.val) :
        primeDigitMass B r = 1/(∏ p ∈ auxiliaryPrimes B, (p : ℝ)) := by
      simp only [primeDigitMass,finiteProductMass,prod_div_distrib,prod_const_one]
      rw [(auxiliaryPrimes B).prod_coe_sort]
    have hsq : (∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2) =
        (∏ p ∈ auxiliaryPrimes B, (p : ℝ))^2 := prod_pow _ _ _
    simp only [finiteExpectation,hw,hsq]
    simp_rw [mul_sum,one_div_mul_eq_div,div_div]
    rw [sum_div]
    apply sum_congr rfl
    intro r _
    rw [sum_div]
    congr 1
    funext t
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockPatternTranspose
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transposing all block-prime patterns to their endpoint types -/

namespace JointDickman
open Finset Classical PublishedInputs

theorem blockPatternEquiv_val {B M : ℕ} (H : BlockPrimePatterns B M) (i : Fin M) :
    (blockPatternEquiv B M H i).val = primePatternsSites H i := rfl

theorem blockPatternEquiv_mass {B M : ℕ} (H : BlockPrimePatterns B M) :
    bernoulliProductMass univ
      (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H =
    siteProductMass (fun _ : Fin M => independentPrimeSetMass B) (blockPatternEquiv B M H) := by
  rw [primeSiteTranspose_mass univ (auxiliaryPrimes B) (fun p : ℕ => 1/(p : ℝ)) H]
  change (∏ i : (univ : Finset (Fin M)),
    independentPrimeSetMass B (blockPatternEquiv B M H i.val)) =
      ∏ i : Fin M, independentPrimeSetMass B (blockPatternEquiv B M H i)
  exact (univ : Finset (Fin M)).prod_coe_sort
    (fun i => independentPrimeSetMass B (blockPatternEquiv B M H i))

theorem blockPatternEquiv_sum {B M : ℕ}
    (F : (Fin M → (auxiliaryPrimes B).powerset) → ℝ) :
    (∑ H : BlockPrimePatterns B M, bernoulliProductMass univ
      (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) H *
        F (blockPatternEquiv B M H)) =
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B)) F := by
  simp only [blockPatternEquiv_mass]
  exact (blockPatternEquiv B M).sum_comp
    (fun S => siteProductMass (fun _ : Fin M => independentPrimeSetMass B) S * F S)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticPatternMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-digit pattern averages over the full prime-square period -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem residuePrimePatterns_mean {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (F : BlockPrimePatterns B M → ℝ) :
    finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r)) =
      ∑ S : BlockPrimePatterns B M, categoricalProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S * F S := by
  have ht := finiteProductMass_pushforward_test
    (fun (p : auxiliaryPrimes B) (_ : ZMod p.val) => 1/(p.val : ℝ))
    (fun p : auxiliaryPrimes B => blockPrimeHit M p.val) (fun S => (F S : ℂ))
  simp only [blockPrimeHit_pushMass M _ (hsize _ (Subtype.property _))] at ht
  exact_mod_cast ht.symm

theorem arithmeticSquareMean_patterns {B M : ℕ}
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (F : BlockPrimePatterns B M → ℝ) :
    arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u)) =
      ∑ S : BlockPrimePatterns B M, categoricalProductMass univ
        (fun p : auxiliaryPrimes B => fun _ : Fin M => 1/(p.val : ℝ)) S * F S := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  have hh := prime_square_crt_average B (fun r _ => F (residuePrimePatterns r))
  change arithmeticSquareMean B (fun u => F (residuePrimePatterns (arithmeticFirstDigits B u))) = _ at hh
  simp only [residuePrimePatterns_arithmetic,finiteExpectation_const _ (primeDigitMass_sum B)] at hh
  exact hh.trans (residuePrimePatterns_mean hsize F)

theorem arithmeticSquareMean_pattern_comparison {B M : ℕ}
    (hB : 1 < B) (hM : M ≤ B^2) (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (F : BlockPrimePatterns B M → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ S, |F S| ≤ C*(B : ℝ)^10) :
    |arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u))-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => F ((blockPatternEquiv B M).symm S))| ≤ 2*C/(B : ℝ) := by
  have hc := block_sites_auxiliary_comparison hB hM F hC hF
  rw [block_sites_crt_mean M (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hsize] at hc
  rw [← arithmeticSquareMean_patterns hsize F] at hc
  have ht := blockPatternEquiv_sum (fun S => F ((blockPatternEquiv B M).symm S))
  simp only [Equiv.symm_apply_apply] at ht
  rwa [ht] at hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRootMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded scalar root mean in the latent kernel -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem regularResidueWeight_le_base (B L : ℕ) (τ C : ℝ) (S : Finset ℕ) :
    regularResidueWeight B L τ C S ≤ residueBaseWeight B S := by
  unfold regularResidueWeight
  split_ifs
  · exact le_rfl
  · unfold residueBaseWeight
    exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)

theorem independent_root_base_mean (B : ℕ) :
    finiteExpectation (independentPrimeSetMass B) (fun R => residueBaseWeight B R.val) =
      auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B) (1/2) := by
  have he := bernoulliSubsetMass_tilt (auxiliaryPrimes B)
    (fun p => 1/(p : ℝ)) (fun _ => (1/2 : ℝ))
  simp only [prod_const] at he
  have hlocal (p : ℕ) : 1-1/(p : ℝ)+1/(p : ℝ)*(1/2) = 1-(1/2)/(p : ℝ) := by ring
  simp_rw [hlocal] at he
  unfold finiteExpectation independentPrimeSetMass
  change (∑ x : (auxiliaryPrimes B).powerset,
    (fun R : Finset ℕ => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R *
      residueBaseWeight B R) x.val) = _
  calc
    _ = ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*residueBaseWeight B R :=
      Finset.sum_coe_sort _ _
    _ = auxiliaryRatio B^(1/2 : ℝ)*
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*(1/2 : ℝ)^R.card := by
      rw [mul_sum]
      apply sum_congr rfl
      intro R _
      unfold residueBaseWeight
      ring
    _ = _ := by rw [he]; rfl

theorem independentRootMean_nonneg (B L : ℕ) (τ C : ℝ) :
    0 ≤ independentRootMean B L τ C :=
  finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => regularResidueWeight_nonneg B L τ C R.val)

/-- Only reciprocal-prime Mertens is used to bound the root mean, uniformly
in all truncation parameters. -/
theorem independentRootMean_bounded (hM : PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L : ℕ) (τ C : ℝ),
      independentRootMean B L τ C ≤ K := by
  let K : ℝ := (4 : ℝ)^(-(1/2 : ℝ))+1
  refine ⟨K,by dsimp [K] <;> positivity,?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1/2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ)^(-(1/2 : ℝ)) < K by
    dsimp [K] <;> linarith))] with B hB
  intro L τ C
  calc
    _ ≤ finiteExpectation (independentPrimeSetMass B) (fun R => residueBaseWeight B R.val) :=
      finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
        (fun R => regularResidueWeight_le_base B L τ C R.val)
    _ = auxiliaryRatio B^(1/2 : ℝ)*primeNormalizer (auxiliaryPrimes B) (1/2) :=
      independent_root_base_mean B
    _ ≤ K := by simpa only [mul_comm] using hB.le

/-- Averaging the sixth factor produces precisely the scalar k_B in
manuscript equation (20). -/
theorem candidateMeanWeight_eq {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      (regularCoefficientWeight B L τ C (candidateLow e)*
        regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
        (regularCoefficientWeight B L τ C (candidateHigh e)*
          regularResidueWeight B L τ C (S e.1.2 \ e.2.2))*
        regularCoefficientWeight B L τ C (candidateQuotient e))/(B : ℝ)*χ e*
          independentRootMean B L τ C := by
  unfold candidateMeanWeight independentRootMean finiteExpectation candidateRootWeight
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidatePairSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The latent kernel as a local sum over its two endpoint splits -/

namespace JointDickman
open Finset

open Classical in
theorem candidate_pair_sum {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (w : BlockCandidateIndex M → ℝ) (i k : Fin M) :
    (∑ e ∈ blockCandidates B L T H M τ C S,
      if e.1 = (i,k) then w e else 0) =
      ∑ A ∈ endpointSplits B L τ C (S i),
        ∑ D ∈ endpointSplits B L τ C (S k),
          if BlockCandidateAdmissible B L T H τ C ((i,k),(A,D))
          then w ((i,k),(A,D)) else 0 := by
  rw [← sum_filter]
  let J := ((endpointSplits B L τ C (S i)).product
    (endpointSplits B L τ C (S k))).filter
      (fun ab => BlockCandidateAdmissible B L T H τ C ((i,k),ab))
  have heq : (∑ e ∈ (blockCandidates B L T H M τ C S).filter (fun e => e.1 = (i,k)), w e) =
      ∑ ab ∈ J, w ((i,k),ab) := by
    apply sum_bij (fun e _ => e.2)
    · intro e he
      obtain ⟨he,hpair⟩ := mem_filter.mp he
      obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
      apply mem_filter.mpr
      constructor
      · simp only [Finset.product_eq_sprod,mem_product]
        simpa only [hpair] using hs
      · have heq : e = ((i,k),e.2) := Prod.ext hpair rfl
        exact heq ▸ ha
    · intro e he f hf hef
      have hepair := (mem_filter.mp he).2
      have hfpair := (mem_filter.mp hf).2
      exact Prod.ext (hepair.trans hfpair.symm) hef
    · intro ab hab
      obtain ⟨hs,ha⟩ := mem_filter.mp hab
      refine ⟨((i,k),ab),?_,rfl⟩
      apply mem_filter.mpr
      refine ⟨mem_blockCandidates.mpr ⟨?_,ha⟩,rfl⟩
      simpa only [Finset.product_eq_sprod,mem_product] using hs
    · intro e he
      exact congrArg w (Prod.ext (mem_filter.mp he).2 rfl)
  rw [heq]
  dsimp [J]
  rw [sum_filter,sum_product]

open Classical in
/-- For i<k only the forward orientation contributes. -/
theorem latentCandidateKernel_pair {M : ℕ} (B L T H : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      ∑ A ∈ endpointSplits B L τ C (S i),
        ∑ D ∈ endpointSplits B L τ C (S k),
          if BlockCandidateAdmissible B L T H τ C ((i,k),(A,D))
          then candidateMeanWeight B L τ C S χ ((i,k),(A,D)) else 0 := by
  classical
  rw [← candidate_pair_sum B L T H τ C S (candidateMeanWeight B L τ C S χ) i k]
  unfold latentCandidateKernel candidateMatrix
  change (∑ e : blockCandidates B L T H M τ C S,
    (fun e : BlockCandidateIndex M =>
      (if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0)) e.val) = _
  trans ∑ e ∈ blockCandidates B L T H M τ C S,
    ((if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0))
  · exact sum_coe_sort (blockCandidates B L T H M τ C S)
      (fun (e : BlockCandidateIndex M) =>
        (if i = e.1.1 then if k = e.1.2 then candidateMeanWeight B L τ C S χ e else 0 else 0)+
        (if i = e.1.2 then if k = e.1.1 then candidateMeanWeight B L τ C S χ e else 0 else 0))
  · apply sum_congr rfl
    intro e he
    have heord := (mem_blockCandidates.mp he).2.1
    have hback : ¬(i = e.1.2 ∧ k = e.1.1) := by
      rintro ⟨hi,hk⟩
      rw [← hi,← hk] at heord
      exact (not_lt_of_ge hik.le) heord
    have hpair : e.1 = (i,k) ↔ i = e.1.1 ∧ k = e.1.2 := by
      simp only [Prod.ext_iff]
      exact and_congr eq_comm eq_comm
    by_cases hi : i = e.1.1 <;> by_cases hk : k = e.1.2 <;>
      by_cases hi' : i = e.1.2 <;> by_cases hk' : k = e.1.1 <;>
      simp_all only [ite_true, if_true,ite_false, if_false,add_zero,not_true_eq_false,and_self,
        and_false,false_and,not_false_eq_true]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ForwardLagSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the distinct forward lags of one block position -/

namespace JointDickman
open Finset

open Classical in
theorem forward_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0) ≤
      Real.exp 24*(T : ℝ) := by
  let I : Finset (Fin M) := univ.filter (fun k => i < k ∧ k.val-i.val < T)
  have hinj : Set.InjOn (fun k : Fin M => k.val-i.val) I := by
    intro k hk l hl he
    have hk' : i.val < k.val := (mem_filter.mp hk).2.1
    have hl' : i.val < l.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => k.val-i.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : i.val < k.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, singularFactor 24 (k.val-i.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => k.val-i.val), singularFactor 24 j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, singularFactor 24 j := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    _ ≤ _ := by
      simpa only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,mul_one] using
        singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 T

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateKernelMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic polynomial bounds for both candidate kernels -/

namespace JointDickman
open Finset Filter
open PublishedInputs
open scoped Topology

theorem candidateMatrix_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (hv : ∀ e, 0 ≤ v e) (i k : κ) :
    0 ≤ candidateMatrix row col v i k := by
  apply sum_nonneg
  intro e _
  apply add_nonneg <;> split_ifs <;> first | exact hv e | exact le_rfl

theorem candidateMatrix_total {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) :
    (∑ i, ∑ k, candidateMatrix row col v i k) = 2*∑ e, v e := by
  have h := candidateMatrix_bilinear row col v (fun _ => 1) (fun _ => 1)
  simp only [realBilinear,mul_one,one_add_one_eq_two] at h
  rw [← sum_mul] at h
  exact h.trans (mul_comm _ _)

theorem candidateMatrix_absolute_mass_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (hv : ∀ e, 0 ≤ v e ∧ v e ≤ 1) :
    (∑ i, ∑ k, |candidateMatrix row col v i k|) ≤ 2*(Fintype.card ι : ℝ) := by
  simp_rw [abs_of_nonneg (candidateMatrix_nonneg row col v (fun e => (hv e).1) _ _)]
  rw [candidateMatrix_total]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (sum_le_sum (fun e _ => (hv e).2)).trans_eq (by simp)

theorem candidateMeanWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) :
    0 ≤ candidateMeanWeight B L τ C S χ e := by
  exact finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => candidateRootWeight_nonneg B L τ C S χ hχ e R.val)

theorem candidateWeight_and_mean_le_one {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      (∀ e R, candidateRootWeight B L τ C S χ e R ≤ 1) ∧
      (∀ e, candidateMeanWeight B L τ C S χ e ≤ 1) := by
  filter_upwards [candidateRootWeight_small hL hτ hτsmall,eventually_ge_atTop 1] with B hB hB1
  intro C M S χ hχ
  have hw (e : BlockCandidateIndex M) (R : Finset ℕ) :
      candidateRootWeight B L τ C S χ e R ≤ 1 :=
    (hB C M S χ (fun e => (hχ e).2) e R).trans
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hB1) (by norm_num))
  refine ⟨hw,?_⟩
  intro e
  exact (finiteExpectation_mono _ (independentPrimeSetMass_nonneg B)
    (fun R => hw e R.val)).trans_eq (by
      simp only [finiteExpectation,mul_one,independentPrimeSetMass_sum])

theorem candidate_kernels_polynomial_mass {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      (∑ i, ∑ k, |latentCandidateKernel B L T H M τ C S χ i k|) ≤
        2*(M : ℝ)^2*(B : ℝ)^2 ∧
      ∀ R, (∑ i, ∑ k, |independentCandidateKernel B L T H M τ C S χ R i k|) ≤
        2*(M : ℝ)^2*(B : ℝ)^2 := by
  filter_upwards [blockCandidates_card hL hτ hτsmall,
    candidateWeight_and_mean_le_one hL hτ hτsmall] with B hcard hweight
  intro C T H M S χ hχ
  have hcount : (Fintype.card (blockCandidates B L T H M τ C S) : ℝ) ≤ (M : ℝ)^2*(B : ℝ)^2 := by
    simpa only [Fintype.card_coe,Nat.cast_mul,Nat.cast_pow] using
      (show ((blockCandidates B L T H M τ C S).card : ℝ) ≤ (M^2*B^2 : ℕ) by
        exact_mod_cast hcard C T H M S)
  have hb := hweight C M S χ hχ
  constructor
  · exact (candidateMatrix_absolute_mass_le
      (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
      (fun e : blockCandidates B L T H M τ C S => e.val.1.2)
      (fun e : blockCandidates B L T H M τ C S => candidateMeanWeight B L τ C S χ e.val)
      (fun e =>
      ⟨candidateMeanWeight_nonneg B L τ C S χ (fun e => (hχ e).1) e.val,hb.2 e.val⟩)).trans
      (by nlinarith only [hcount])
  · intro R
    exact (candidateMatrix_absolute_mass_le
      (fun e : blockCandidates B L T H M τ C S => e.val.1.1)
      (fun e : blockCandidates B L T H M τ C S => e.val.1.2)
      (fun e : blockCandidates B L T H M τ C S => candidateRootWeight B L τ C S χ e.val (R e).val)
      (fun e =>
      ⟨candidateRootWeight_nonneg B L τ C S χ (fun e => (hχ e).1) e.val (R e).val,
        hb.1 e.val (R e).val⟩)).trans (by nlinarith only [hcount])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateRootErrorCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound on the actual candidate fluctuation test -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem kernelCutNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℝ) :
    0 ≤ kernelCutNorm K := div_nonneg (kernelCutMaximum_nonneg K) (Nat.cast_nonneg _)

theorem kernel_difference_absolute_mass {ι : Type*} [Fintype ι] (K L : ι → ι → ℝ) :
    (∑ i, ∑ j, |K i j-L i j|) ≤ (∑ i, ∑ j, |K i j|)+(∑ i, ∑ j, |L i j|) := by
  simp only [← sum_add_distrib]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => abs_sub (K i j) (L i j)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateArithmeticPeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square periodicity of the actual candidate quotient data -/

namespace JointDickman
open Finset Classical

theorem coefficientPrimeSet_modEq {B n m : ℕ}
    (h : n ≡ m [MOD auxiliarySquarePeriod B]) :
    coefficientPrimeSet B n = coefficientPrimeSet B m := by
  simpa only [prod_empty,Nat.div_one] using
    coefficientPrimeSet_quotient_modEq (A := ∅) h (empty_subset _) (one_dvd n) (one_dvd m)

theorem blockPrimeSites_modEq {B M u v : ℕ}
    (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    (fun i : Fin M => coefficientPrimeSet B (u+(i.val+1))) =
      (fun i : Fin M => coefficientPrimeSet B (v+(i.val+1))) := by
  funext i
  exact coefficientPrimeSet_modEq (h.add_right _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smooth separated factors for compact polynomial approximation -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem schwartz_value_derivative_bounds (w : 𝓢(ℝ,ℝ)) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧ (∀ x, |w x| ≤ M) ∧
      (∀ x, |deriv w x| ≤ D) ∧ Continuous (deriv w) := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 w,
    SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℝ w),
    apply_nonneg _ _,apply_nonneg _ _,?_,?_,?_⟩
  · intro x
    simpa only [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ w x
  · intro x
    simpa only [Real.norm_eq_abs,SchwartzMap.derivCLM_apply] using
      SchwartzMap.norm_le_seminorm ℝ (SchwartzMap.derivCLM ℝ ℝ w) x
  · exact (SchwartzMap.derivCLM ℝ ℝ w).continuous

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GeometricDyadicPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic recombination of the original amplification weight -/

namespace JointDickman
open Finset

theorem exp_nat_log_two (k : ℕ) : Real.exp ((k : ℝ)*Real.log 2) = (2 : ℝ)^k := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_DyadicScaleWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete dyadic indices in the manuscript's scale window -/

namespace JointDickman
open Finset

theorem dyadic_scale_window {B : ℕ} (hB : 30 ≤ B) {T : ℝ} (hT : 1 ≤ T)
    (hlogT : Real.log T ≤ (B : ℝ)/10) :
    dyadicBoxLower B T ≤ dyadicBoxUpper B T ∧
    (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      (k : ℝ)*Real.log 2 ∈ Set.Icc ((9/10 : ℝ)*B) ((5/2 : ℝ)*B) ∧
      Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) ∈
        Set.Icc ((9/10 : ℝ)*B) ((11/5 : ℝ)*B)) ∧
    (∀ c : ℝ, 0 < c → (B : ℝ) ≤ Real.log c → Real.log c ≤ 2*B →
      2 ≤ (c*T)/(2 : ℝ)^(dyadicBoxLower B T) ∧
      (c*T)/(2 : ℝ)^(dyadicBoxUpper B T) ≤ 1) := by
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 < 1 := by
    simpa only [show (2 : ℝ)-1 = 1 by norm_num] using Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  let v := ((B : ℝ)+Real.log T)/Real.log 2
  let w := (2*(B : ℝ)+Real.log T)/Real.log 2
  have hv : (1 : ℝ) ≤ v := by
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  have hw : 0 ≤ w := by dsimp [w] <;> positivity
  have hvw : v ≤ w := by dsimp [v,w]; gcongr; linarith
  have hf1 : 1 ≤ ⌊v⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ v)).mpr (by simpa only [Nat.cast_one] using hv)
  have hL : dyadicBoxLower B T+1 = ⌊v⌋₊ := Nat.sub_add_cancel hf1
  have hU : dyadicBoxUpper B T = ⌈w⌉₊+1 := rfl
  have hfloor := Nat.floor_le (show 0 ≤ v by linarith)
  have hfloor' := Nat.lt_floor_add_one v
  have hceil := Nat.le_ceil w
  have hceil' := Nat.ceil_lt_add_one hw
  have hfv : (⌊v⌋₊ : ℝ)*Real.log 2 ≤ (B : ℝ)+Real.log T := by
    have hm := mul_le_mul_of_nonneg_right hfloor hl2.le
    simpa only [v,div_mul_cancel₀ _ hl2.ne'] using hm
  have hfv' : (B : ℝ)+Real.log T-Real.log 2 < (⌊v⌋₊ : ℝ)*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hfloor' hl2
    dsimp only [v] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    nlinarith
  have hcw : 2*(B : ℝ)+Real.log T ≤ (dyadicBoxUpper B T : ℝ)*Real.log 2 := by
    have hm := mul_le_mul_of_nonneg_right hceil hl2.le
    dsimp only [w] at hm
    rw [div_mul_cancel₀ _ hl2.ne'] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hcw' : (dyadicBoxUpper B T : ℝ)*Real.log 2 < 2*(B : ℝ)+Real.log T+2*Real.log 2 := by
    have hm := mul_lt_mul_of_pos_right hceil' hl2
    dsimp only [w] at hm
    rw [add_mul,div_mul_cancel₀ _ hl2.ne',one_mul] at hm
    rw [hU,Nat.cast_add,Nat.cast_one]
    nlinarith
  have hLU : dyadicBoxLower B T ≤ dyadicBoxUpper B T := by
    have hh := (Nat.floor_mono hvw).trans (Nat.floor_le_ceil w)
    dsimp only [dyadicBoxLower,dyadicBoxUpper]
    exact (Nat.sub_le _ _).trans (hh.trans (Nat.le_succ _))
  refine ⟨hLU,?_,?_⟩
  · intro k hk
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hk
    obtain ⟨hnL,hnU⟩ := mem_Ico.mp hn
    have hlo : ⌊v⌋₊ ≤ n+1 := by rw [← hL]; omega
    have hhi : n+1 ≤ dyadicBoxUpper B T := by omega
    have hlo' : (⌊v⌋₊ : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast hlo
    have hhi' : ((n+1 : ℕ) : ℝ) ≤ dyadicBoxUpper B T := by exact_mod_cast hhi
    have hlo'' := mul_le_mul_of_nonneg_right hlo' hl2.le
    have hhi'' := mul_le_mul_of_nonneg_right hhi' hl2.le
    have hlog : Real.log (Real.exp (((n+1 : ℕ) : ℝ)*Real.log 2)/T) =
        ((n+1 : ℕ) : ℝ)*Real.log 2-Real.log T := by
      rw [Real.log_div (Real.exp_pos _).ne' hTpos.ne',Real.log_exp]
    simp only [Int.cast_natCast]
    rw [hlog]
    constructor <;> constructor <;> nlinarith
  · intro c hc hclo hchi
    have hct := mul_pos hc hTpos
    have hlogct : Real.log (c*T) = Real.log c+Real.log T := Real.log_mul hc.ne' hTpos.ne'
    constructor
    · apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      have hh : (2 : ℝ)^(dyadicBoxLower B T+1) ≤ c*T := by
        rw [← exp_nat_log_two,← Real.exp_log hct]
        apply Real.exp_le_exp.mpr
        rw [hlogct,hL]
        exact hfv.trans (by linarith)
      simpa only [pow_succ,mul_comm] using hh
    · apply (div_le_one (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
      rw [← exp_nat_log_two,← Real.exp_log hct]
      apply Real.exp_le_exp.mpr
      rw [hlogct]
      exact (show Real.log c+Real.log T ≤ 2*(B : ℝ)+Real.log T by linarith).trans hcw

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSiteKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The latent graph as a kernel of its two endpoint types -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C S χ k i := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_congr rfl
  intro e _
  dsimp only
  split_ifs <;> simp_all

theorem latentCandidateKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    latentCandidateKernel B L T H M τ C S χ i i = 0 := by
  unfold latentCandidateKernel candidateMatrix
  apply sum_eq_zero
  intro e _
  have hord := (mem_blockCandidates.mp e.property).2.1
  dsimp only
  by_cases hi : i = e.val.1.1 <;> by_cases hk : i = e.val.1.2
  · have hh : e.val.1.1 = e.val.1.2 := hi.symm.trans hk
    rw [hh] at hord
    exact False.elim (lt_irrefl _ hord)
  all_goals simp [hi,hk,ne_of_lt hord,Ne.symm (ne_of_lt hord)]

theorem latentCandidateKernel_nonneg (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (i k : Fin M) :
    0 ≤ latentCandidateKernel B L T H M τ C S χ i k := by
  unfold latentCandidateKernel
  apply candidateMatrix_nonneg
  intro e
  exact candidateMeanWeight_nonneg B L τ C S χ hχ e.val

/-- Other endpoint types have no effect on this entry, even though the
full candidate list depends on the entire configuration. -/
theorem latentCandidateKernel_local {B L T H M : ℕ} {τ C : ℝ}
    (S R : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hi : S i = R i) (hk : S k = R k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      latentCandidateKernel B L T H M τ C R χ i k := by
  have hf (i k : Fin M) (hik : i < k) (hi : S i = R i) (hk : S k = R k) :
      latentCandidateKernel B L T H M τ C S χ i k =
        latentCandidateKernel B L T H M τ C R χ i k := by
    rw [latentCandidateKernel_pair B L T H τ C S χ i k hik,
      latentCandidateKernel_pair B L T H τ C R χ i k hik]
    simp_rw [candidateMeanWeight_eq]
    rw [hi,hk]
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik hi hk
  · rw [latentCandidateKernel_diag,latentCandidateKernel_diag]
  · rw [latentCandidateKernel_symm B L T H M τ C S χ,
      latentCandidateKernel_symm B L T H M τ C R χ]
    exact hf k i hki hk hi

theorem candidateSiteKernel_realizes (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (S : Fin M → Finset ℕ) (i k : Fin M) :
    candidateSiteKernel B L T H M τ C χ i k (S i) (S k) =
      latentCandidateKernel B L T H M τ C S χ i k := by
  apply latentCandidateKernel_local
  · by_cases h : i = k <;> simp [h]
  · simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPolynomialBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the compact smooth finite-feature kernels -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedPolynomialTermKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialTermKernel P d m B j c H T t S s r x y| ≤ C := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,_,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,_,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,_,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C := (m : ℝ)^2*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(R*M₀*M₁*M₂)))*
    (Real.log (17/4)-Real.log (1/4)+2))/channelMesh m
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hw : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hw' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  refine ⟨C,by dsimp [C] <;> positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s hs r hr x y
  have hcoeff : ∀ k ∈ S, |(r k*(P.coeff d*(s k)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R := by
    intro k hk
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog k hk]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr k hk) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) zero_le_one).trans_eq (one_mul _)
  exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
    hR hM₀ hM₁ hM₂ S _ _ _ _ hcoeff hw₀ hw₁ hw₂ x y

theorem weightedPolynomialPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (H : (Fin 4 →₀ ℕ) → ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialPrimeKernel P m B j c H T t S s r x y| ≤ C := by
  choose C hC hbound using fun d => weightedPolynomialTermKernel_bounded hM hMP P d (hm d) (c d) (hc d) (H d) ht
  refine ⟨∑ d ∈ P.support, C d,sum_nonneg (fun d _ => hC d),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hb
  intro j T S hlog s hs r hr x y
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d hd => hb d hd j T S hlog s hs r hr x y))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingRamp
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A continuous approximation of the actual counting-scale cutoff -/

namespace JointDickman
open Finset

theorem countingRamp_bounds {δ : ℝ} (hδ : 0 < δ) (s x : ℝ) :
    0 ≤ countingRamp δ s x ∧ countingRamp δ s x ≤ 1 :=
  averagingRamp_bounds (by linarith) x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RampedCandidate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual candidate cutoff and its ramped arithmetic counterpart -/
namespace JointDickman
open Finset

open Classical in
theorem rampedCandidateCutoff_bounds {M : ℕ} {δ : ℝ} (hδ : 0 < δ) (B T : ℕ)
    (σ : ℝ) (e : BlockCandidateIndex M) :
    0 ≤ rampedCandidateCutoff B T δ σ e ∧ rampedCandidateCutoff B T δ σ e ≤ 1 := by
  have hb : 0 ≤ candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ∧
      candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T) e ≤ 1 := by
    unfold candidateCutoff amplificationOuterWeight amplificationInnerWeight
    have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    constructor
    · exact mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    · exact (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 zero_le_one) h3.2 h3.1
        (by norm_num)).trans_eq (by norm_num)
  have hr := countingRamp_bounds hδ σ ((candidateLow e : ℝ)/(T*candidateQuotient e))
  exact ⟨mul_nonneg hb.1 hr.1,
    (mul_le_mul hb.2 hr.2 hr.1 zero_le_one).trans_eq (one_mul _)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCutoffError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact error when the finite counting cutoff is replaced by its ramp -/
namespace JointDickman
open Finset

theorem smoothCandidateCutoff_nonneg {M : ℕ} (B T : ℕ) (e : BlockCandidateIndex M) :
    0 ≤ smoothCandidateCutoff B T e := by
  change 0 ≤ amplificationBump _*amplificationBump _*amplificationBump _
  exact mul_nonneg (mul_nonneg amplificationBump.nonneg amplificationBump.nonneg) amplificationBump.nonneg

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CutNormTriangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Triangle inequalities for the finite cut norm -/

namespace JointDickman
open Finset Classical

theorem kernelCutMaximum_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (s t : ι → Bool) :
    |realBilinear K (fun i => cutSign (s i)) (fun i => cutSign (t i))| ≤ kernelCutMaximum K :=
  le_sup' (fun st : (ι → Bool) × (ι → Bool) =>
    |realBilinear K (fun i => cutSign (st.1 i)) (fun i => cutSign (st.2 i))|) (mem_univ (s,t))

theorem kernelCutNorm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : ι → ι → ℝ) :
    kernelCutNorm (fun i k => K i k+L i k) ≤ kernelCutNorm K+kernelCutNorm L := by
  unfold kernelCutNorm
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply kernelCutMaximum_le
  intro s t
  have he : realBilinear (fun i k => K i k+L i k) (fun i => cutSign (s i)) (fun i => cutSign (t i)) =
      realBilinear K (fun i => cutSign (s i)) (fun i => cutSign (t i))+
        realBilinear L (fun i => cutSign (s i)) (fun i => cutSign (t i)) := by
    simp [realBilinear,add_mul,sum_add_distrib]
  rw [he]
  exact (abs_add_le _ _).trans
    (add_le_add (kernelCutMaximum_bilinear K s t) (kernelCutMaximum_bilinear L s t))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateCutoffNorm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A cut-norm error from the weights of the candidate representations -/
namespace JointDickman
open Finset

theorem candidateMatrix_abs_le {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (i k : κ) :
    |candidateMatrix row col v i k| ≤ candidateMatrix row col (fun e => |v e|) i k := by
  unfold candidateMatrix
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e _
  split_ifs <;> simp_all
  exact abs_add_le _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSiteMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform means in either orientation of the latent site kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem backward_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) ≤
      Real.exp 24*(T : ℝ) := by
  let I : Finset (Fin M) := univ.filter (fun k => k < i ∧ i.val-k.val < T)
  have hinj : Set.InjOn (fun k : Fin M => i.val-k.val) I := by
    intro k hk l hl he
    have hk' : k.val < i.val := (mem_filter.mp hk).2.1
    have hl' : l.val < i.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    dsimp only at he
    omega
  have hsub : I.image (fun k => i.val-k.val) ⊆ Ioc 0 T := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
    have hk := (mem_filter.mp hk).2
    have hik : k.val < i.val := hk.1
    exact mem_Ioc.mpr ⟨by omega,by omega⟩
  calc
    _ = ∑ k ∈ I, singularFactor 24 (i.val-k.val) := (sum_filter _ _).symm
    _ = ∑ j ∈ I.image (fun k => i.val-k.val), singularFactor 24 j := (sum_image hinj).symm
    _ ≤ ∑ j ∈ Ioc 0 T, singularFactor 24 j := sum_le_sum_of_subset_of_nonneg hsub
      (fun j _ _ => zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    _ ≤ _ := by
      simpa only [pow_one,Nat.cast_one,Nat.sub_self,pow_zero,one_mul,mul_one] using
        singularFactor_nat_moment (by norm_num : (0 : ℝ) ≤ 24) 1 T

theorem distance_lag_singular_sum {M : ℕ} (i : Fin M) (T : ℕ) :
    (∑ k : Fin M, if i ≠ k ∧ Nat.dist i.val k.val < T then
      singularFactor 24 (Nat.dist i.val k.val) else 0) ≤ 2*Real.exp 24*(T : ℝ) := by
  have he (k : Fin M) :
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) =
      (if i < k ∧ k.val-i.val < T then singularFactor 24 (k.val-i.val) else 0) +
      (if k < i ∧ i.val-k.val < T then singularFactor 24 (i.val-k.val) else 0) := by
    rcases lt_trichotomy i k with h | rfl | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le,Nat.dist_eq_sub_of_le h.le]
    · simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,Nat.dist_eq_sub_of_le_right h.le]
  simp_rw [he]
  rw [sum_add_distrib]
  have hf := forward_lag_singular_sum i T
  have hb := backward_lag_singular_sum i T
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateExpectedDegree
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform conditional degrees of the actual latent graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentPrimeSiteKernel_realizes (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ)
    (S : Fin M → (auxiliaryPrimes B).powerset) (i k : Fin M) :
    realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) S i k =
      latentCandidateKernel B L T H M τ C (fun i => (S i).val) χ i k :=
  candidateSiteKernel_realizes B L T H M τ C χ (fun i => (S i).val) i k

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lipschitz dependence of the spatial model on its lag parameter -/
namespace JointDickman
open Finset Classical

theorem histogramLocation_le {m B : ℕ} (hB : 0 < B)
    {t L U : ℝ} {k : ℤ} {i : Fin (channelFineCount m B)}
    (hi : i ∈ geometricHistogramWindow m B t L U k) :
    Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t) ≤ Real.exp U := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := (le_div_iff₀ hBr).mp (mem_filter.mp hi).2.1
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem endpointSpatialWeight_parameter_difference {m B : ℕ} (hB : 0 < B)
    {t L U D M₁ M₂ β γ : ℝ} (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ) {K : NNReal} (hw : LipschitzWith K w)
    (k : ℤ) (hd : |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (i j : Fin (channelFineCount m B))
    (hi : i ∈ geometricHistogramWindow m B t L U k)
    (hj : j ∈ geometricHistogramWindow m B t L U k) :
    |endpointSpatialWeight m B t β d w₁ w₂ w k i j-
      endpointSpatialWeight m B t γ d w₁ w₂ w k i j| ≤
      D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| := by
  let x := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) i)/Real.exp ((k : ℝ)*t)
  let y := Real.exp ((B : ℝ)*channelLower (channelFineCount m B) j)/Real.exp ((k : ℝ)*t)
  have hx0 : 0 < x := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hy0 : 0 < y := div_pos (Real.exp_pos _) (Real.exp_pos _)
  have hx : x ≤ Real.exp U := histogramLocation_le hB hi
  have hy : y ≤ Real.exp U := histogramLocation_le hB hj
  have hxy : |x-y| ≤ Real.exp U := abs_le.mpr ⟨by linarith,by linarith⟩
  have hl := hw.dist_le_mul (β*x-β*y) (γ*x-γ*y)
  rw [Real.dist_eq,Real.dist_eq,show β*x-β*y-(γ*x-γ*y) = (β-γ)*(x-y) by ring,abs_mul] at hl
  have hl' : |w (β*x-β*y)-w (γ*x-γ*y)| ≤ (K : ℝ)*|β-γ| *Real.exp U :=
    by
      have hh := hl.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxy (abs_nonneg _)) K.coe_nonneg)
      simpa only [mul_assoc] using hh
  have hc : |d k*w₁ x*w₂ y| ≤ D*M₁*M₂ := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul hd (hw₁ x) (abs_nonneg _) hD) (hw₂ y) (abs_nonneg _) (mul_nonneg hD hM₁)
  change |d k*w₁ x*w₂ y*w (β*x-β*y)-d k*w₁ x*w₂ y*w (γ*x-γ*y)| ≤ _
  rw [← mul_sub,abs_mul]
  have hh := mul_le_mul hc hl' (abs_nonneg _) (by positivity : 0 ≤ D*M₁*M₂)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring


theorem geometric_coarseCoefficient_parameter_difference {m B : ℕ}
    (hm : 0 < m) (hB : 1 ≤ B)
    {t L U D M₁ M₂ β γ : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (hD : 0 ≤ D) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (S : Finset ℤ) (d : ℤ → ℝ) (w₁ w₂ w : ℝ → ℝ)
    {K : NNReal} (hw : LipschitzWith K w)
    (hd : ∀ k ∈ S, |d k| ≤ D) (hw₁ : ∀ z, |w₁ z| ≤ M₁) (hw₂ : ∀ z, |w₂ z| ≤ M₂)
    (a b : Fin m) :
    |primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t β d w₁ w₂ w)) a b-
      primeCoarseCoefficient m B
        (geometricWindowKernel m B t L U S (endpointSpatialWeight m B t γ d w₁ w₂ w)) a b| ≤
      (channelMesh m*(2*(((1+U-L)/t+1)*(D*M₁*M₂*(K : ℝ)*Real.exp U))*(U-L+2)))*|β-γ| := by
  have hh := geometric_coarseCoefficient_difference hm hB ht hLU
    (show 0 ≤ D*M₁*M₂*(K : ℝ)*Real.exp U*|β-γ| by positivity) S
    (endpointSpatialWeight m B t β d w₁ w₂ w)
    (endpointSpatialWeight m B t γ d w₁ w₂ w)
    (fun k hk i j hi hj => endpointSpatialWeight_parameter_difference (by omega)
      hD hM₁ hM₂ d w₁ w₂ w hw k (hd k hk) hw₁ hw₂ i j hi hj) a b
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingShift
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving a counting threshold from an endpoint to its block origin -/
namespace JointDickman

 theorem countingRamp_translate (δ s x : ℝ) :
    countingRamp δ s x = averagingRamp 0 δ (x-s) := by
  have he : min (s+δ) (max s x)-s = min δ (max 0 (x-s)) := by
    rw [← min_sub_sub_right,← max_sub_sub_right]
    simp
  unfold countingRamp averagingRamp
  rw [he]
  simp

theorem countingRamp_threshold_lipschitz {δ : ℝ} (hδ : 0 < δ) (s t x : ℝ) :
    |countingRamp δ s x-countingRamp δ t x| ≤ |s-t|/δ := by
  rw [countingRamp_translate,countingRamp_translate]
  have he := (averagingRamp_lipschitz (a := 0) hδ).dist_le_mul (x-s) (x-t)
  simp only [Real.dist_eq] at he
  change |averagingRamp 0 δ (x-s)-averagingRamp 0 δ (x-t)| ≤
    (1/(δ-0))*|(x-s)-(x-t)| at he
  simp only [sub_zero] at he
  have hs : (x-s)-(x-t) = -(s-t) := by ring
  simpa only [hs,abs_neg,one_div_mul_eq_div] using he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteRampWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite-cutoff error in each retained candidate weight -/
namespace JointDickman
open Finset

 theorem candidateMeanWeight_cutoff_factor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      candidateMeanWeight B L τ C S (fun _ => 1) e*χ e := by
  rw [candidateMeanWeight_eq,candidateMeanWeight_eq]
  ring

theorem candidateMeanWeight_cutoff_error {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ ψ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    |candidateMeanWeight B L τ C S χ e-candidateMeanWeight B L τ C S ψ e| =
      candidateMeanWeight B L τ C S (fun _ => 1) e*|χ e-ψ e| := by
  rw [candidateMeanWeight_cutoff_factor B L τ C S χ e,
    candidateMeanWeight_cutoff_factor B L τ C S ψ e,← mul_sub,abs_mul,
    abs_of_nonneg (candidateMeanWeight_nonneg B L τ C S (fun _ => 1) (fun _ => zero_le_one) e)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized reciprocal lag is uniformly Lipschitz away from zero -/
namespace JointDickman

theorem reciprocal_lag_difference {T η x y : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hx : η*T ≤ x) (hy : η*T ≤ y) :
    |T/x-T/y| ≤ |x-y|/(η^2*T) := by
  have hx0 : 0 < x := (mul_pos hη hT).trans_le hx
  have hy0 : 0 < y := (mul_pos hη hT).trans_le hy
  have hxy : η^2*T^2 ≤ x*y := by
    have hh := mul_le_mul hx hy (mul_pos hη hT).le hx0.le
    nlinarith
  have he : T/x-T/y = T*(y-x)/(x*y) := by field_simp
  rw [he,abs_div,abs_mul,abs_of_pos hT,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  have hb := div_le_div_of_nonneg_left (mul_nonneg hT.le (abs_nonneg (x-y)))
    (by positivity : 0 < η^2*T^2) hxy
  refine hb.trans_eq ?_
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PolynomialTermLagVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lag variation of the polynomial model's finite coefficients -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem weightedPolynomialTermKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) (x y : auxiliaryPrimes B → Bool) :
    weightedPolynomialTermKernel P d m B j c H T t S s r x y =
      ∑ a, ∑ b, weightedTermCoefficient P d m B j c H T t S s r a b*
        primeCoarseFeature m B a x*primeCoarseFeature m B b y := rfl

theorem weightedTermCoefficient_lag_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T : ℝ),
      0 < T → η*T ≤ j → η*T ≤ k → ∀ S : Finset ℤ,
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ u ∈ S, |s u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s r a b-
        weightedTermCoefficient P d m B k c H T t S s r a b| ≤
        C*|(j : ℝ)-k|/T := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,_,hD₂,_,hd₂,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let K : NNReal := ⟨D₂,hD₂⟩
  have hLip : LipschitzWith K (tensorPowerFactor (d 2)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (tensorPowerFactor (d 2)).differentiable
    intro x
    change ‖deriv (tensorPowerFactor (d 2)) x‖₊ ≤ K
    exact_mod_cast hd₂ x
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C₀ := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*(K : ℝ)*Real.exp (Real.log (17/4))))*(Real.log (17/4)-Real.log (1/4)+2))
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hR : 0 ≤ R := by positivity
  have hC₀ : 0 ≤ C₀ := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C₀]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C₀/η^2,by positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j k T hT hj hk S hlog s hs r hr a b
  have hcoeff : ∀ u ∈ S, |(r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hs u hu) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr u hu) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
      zero_le_one).trans_eq (one_mul _)
  have he := geometric_coarseCoefficient_parameter_difference hm hB ht hlogs hR hM₀ hM₁
    S (fun u => (r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B))
    (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))
    (β := T/j) (γ := T/k) hLip hcoeff hw₀ hw₁ a b
  change |weightedTermCoefficient P d m B j c H T t S s r a b-
    weightedTermCoefficient P d m B k c H T t S s r a b| ≤ C₀*|T/j-T/k| at he
  have hb := he.trans (mul_le_mul_of_nonneg_left (reciprocal_lag_difference hT hη hj hk) hC₀)
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PolynomialTermAmplitudeVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform variation of the polynomial model in its cutoff parameter -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem weightedTermCoefficient_parameter_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s₁ s₂ : ℤ → ℝ, (∀ u ∈ S, |s₁ u| ≤ 3) → (∀ u ∈ S, |s₂ u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ δ : ℝ, 0 ≤ δ →
      (∀ u ∈ S, |s₁ u-s₂ u| ≤ δ) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
        weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ C*δ := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(d 3 : ℝ)*(3 : ℝ)^(d 3-1)*D
  let C := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*M₂))*(Real.log (17/4)-Real.log (1/4)+2))
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hC : 0 ≤ C := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C,hC,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s₁ s₂ hs₁ hs₂ r hr δ hδ hdist a b
  have hcoeff : ∀ u ∈ S,
      |(r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R*δ := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    have hp : |(s₁ u)^(d 3)-(s₂ u)^(d 3)| ≤ δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1) := by
      refine (abs_pow_sub_pow_le (s₁ u) (s₂ u) (d 3)).trans ?_
      gcongr
      · exact hdist u hu
      · exact max_le (hs₁ u hu) (hs₂ u hu)
    rw [show (r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) =
        r u*P.coeff d*((s₁ u)^(d 3)-(s₂ u)^(d 3))*
          coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) by ring]
    simp only [abs_mul]
    have hh := mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_right (hr u hu) (abs_nonneg (P.coeff d))) hp
        (abs_nonneg _) (by positivity : 0 ≤ 1*|P.coeff d|)) hden'
      (abs_nonneg _) (by positivity : 0 ≤ (1*|P.coeff d|)*(δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1)))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [R]
    ring
  have hh := geometric_coarseCoefficient_amplitude_difference (β := T/j) hm hB ht hlogs
    (mul_nonneg hR hδ) hM₀ hM₁ hM₂ S _ _ _ _ _ hcoeff hw₀ hw₁ hw₂ a b
  change |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
    weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [C]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCandidateModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite prime-feature model for each ramped candidate entry -/
namespace JointDickman
open Finset

theorem countingCandidateModel_bound (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L j : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (H : (Fin 4 →₀ ℕ) → ℕ) (T σ K : ℝ)
    (hseries : 0 ≤ singularSeries j)
    (hK : ∀ x y, |countingPrimeKernel P m B j c H T σ x y| ≤ K)
    (S R : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c H T σ S R| ≤
      (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*K := by
  unfold countingCandidateModel subsetPrimeModel
  rw [abs_mul,abs_of_nonneg (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))]
  exact mul_le_mul_of_nonneg_left (hK _ _) (mul_nonneg (independentRootMean_nonneg ..)
    (div_nonneg hseries (Nat.cast_nonneg _)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SingularSeriesMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary lag moments of the singular series -/

namespace JointDickman
open Finset

theorem totient_ratio_le_singularFactor {j : ℕ} (hj : 0 < j) :
    (j : ℝ)/j.totient ≤ singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hp (p : ℕ) (h : p ∈ j.primeFactors) : (2 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).two_le
  have hfactor (p : ℕ) (h : p ∈ j.primeFactors) : 0 < 1-1/(p : ℝ) := by
    have hpp := hp p h
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have hprod : (0 : ℝ) < ∏ p ∈ j.primeFactors, (1-1/(p : ℝ)) := prod_pos hfactor
  have he : (j : ℝ)/j.totient = ∏ p ∈ j.primeFactors, (1-1/(p : ℝ))⁻¹ := by
    rw [totient_eq_prime_product_real,prod_inv_distrib]
    field_simp
  rw [he]
  apply Finset.prod_le_prod
  · intro p h
    exact inv_nonneg.mpr (hfactor p h).le
  · intro p h
    have hpp := hp p h
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < p-1 := by linarith
    have heq : (1-1/(p : ℝ))⁻¹ = p/(p-1) := by field_simp
    rw [heq]
    apply (div_le_iff₀ hp1).mpr
    have hh : (1+24/(p : ℝ))*(p-1)-(p : ℝ) = (23*p-24)/p := by field_simp <;> ring
    have hnonneg : 0 ≤ (23*(p : ℝ)-24)/p := div_nonneg (by linarith) (by linarith)
    linarith

theorem singularSeries_le_singularFactor
    (hMP : PublishedInputs.PrimeProductMertensInput) {j : ℕ} (hj : 0 < j) :
    singularSeries j ≤ singularFactor 24 j :=
  (singularSeries_bounds hMP j).2.trans (totient_ratio_le_singularFactor hj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSiteModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The symmetric finite-feature block model and its lag envelope -/
namespace JointDickman
open Finset Classical

theorem countingSiteModel_diag (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i i a b = 0 := by
  simp only [countingSiteModel,lt_self_iff_false,ite_false, if_false]

theorem countingSiteModel_symm (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    countingSiteModel P m B L T H M τ C c D σ i k a b =
      countingSiteModel P m B L T H M τ C c D σ k i b a := by
  rcases lt_trichotomy i k with h | rfl | h
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]
  · rw [countingSiteModel_diag,countingSiteModel_diag]
  · simp only [countingSiteModel,h,not_lt_of_ge h.le,ite_true, if_true,ite_false, if_false]

theorem countingCandidateModel_lag_bound
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L j : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {T η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hlag : η*T ≤ j)
    (hbound : ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (a b : Finset ℕ) :
    |countingCandidateModel P m B L j τ C c D T σ a b| ≤
      (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 j := by
  have hjr : (0 : ℝ) < j := (mul_pos hη hT).trans_le hlag
  have hj : 0 < j := by exact_mod_cast hjr
  have hsf : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  have he : singularSeries j/(j : ℝ) ≤ singularFactor 24 j/(η*T) :=
    (div_le_div_of_nonneg_right (singularSeries_le_singularFactor hMP hj) hjr.le).trans
      (div_le_div_of_nonneg_left hsf (mul_pos hη hT) hlag)
  calc
    _ ≤ (independentRootMean B L τ C*(singularSeries j/(j : ℝ)))*C₀ :=
      countingCandidateModel_bound P m B L j τ C c D T σ C₀ (singularSeries_bounds hMP j).1 hbound a b
    _ ≤ (independentRootMean B L τ C*(singularFactor 24 j/(η*T)))*C₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (independentRootMean_nonneg ..)) hC₀
    _ = _ := by ring

theorem countingSiteModel_lag_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hf (i k : Fin M) (hik : i < k) (a b : (auxiliaryPrimes B).powerset) :
      |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      if i ≠ k ∧ Nat.dist i.val k.val < T then
        (independentRootMean B L τ C*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) else 0 := by
    rw [countingSiteModel,ite_eq_left hik,Nat.dist_eq_sub_of_le hik.le]
    by_cases ha : H < k.val-i.val ∧ k.val-i.val < T
    · rw [ite_eq_left ha,ite_eq_left ⟨ne_of_lt hik,ha.2⟩]
      apply countingCandidateModel_lag_bound hMP P m B L _ τ C c D hTr hη hC₀ _ (hbound _ ha.1 ha.2)
      exact hH.trans (by exact_mod_cast ha.1.le)
    · rw [ite_eq_right ha,abs_zero]
      split_ifs
      · exact mul_nonneg (div_nonneg (mul_nonneg (independentRootMean_nonneg ..) hC₀)
          (mul_pos hη hTr).le) (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
      · exact le_rfl
  rcases lt_trichotomy i k with h | rfl | h
  · exact hf i k h a b
  · simp only [countingSiteModel_diag,ne_eq,not_true_eq_false,false_and,ite_false, if_false,abs_zero,le_refl]
  · rw [countingSiteModel_symm, Nat.dist_comm i.val k.val]
    have hh := hf k i h b a
    simpa only [ne_comm] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LagEnvelopeMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Row moments of the deterministic singular-factor envelope -/
namespace JointDickman
open Finset Classical PublishedInputs

theorem lagEnvelope_row_sum {M T : ℕ} (hT : 0 < T) {D : ℝ} (hD : 0 ≤ D) (i : Fin M) :
    (∑ k, lagEnvelope T D i k) ≤ 2*D*Real.exp 24 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have he (k : Fin M) : lagEnvelope T D i k = D/(T : ℝ)*
      (if i ≠ k ∧ Nat.dist i.val k.val < T then singularFactor 24 (Nat.dist i.val k.val) else 0) := by
    unfold lagEnvelope
    split_ifs <;> simp only [mul_zero]
  simp_rw [he]
  rw [← mul_sum]
  exact (mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) (div_nonneg hD hTr.le)).trans_eq
    (by field_simp)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingModelEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lag envelope at the actual amplification scale -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingSiteModel_uniform_envelope
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {η C₀ R σ : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hC₀ : 0 ≤ C₀)
    (hroot : independentRootMean B L τ C ≤ R) (hH : η*T ≤ H)
    (hbound : ∀ j : ℕ, H < j → j < T →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ C₀)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteModel P m B L T H M τ C c D σ i k a b| ≤
      lagEnvelope T (R*C₀/η) i k := by
  apply (countingSiteModel_lag_envelope hMP P m B L T H M τ C c D
    hT hη hC₀ hH hbound i k a b).trans
  unfold lagEnvelope
  split_ifs
  · have hden : 0 ≤ η*(T : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
    have hs : 0 ≤ singularFactor 24 (Nat.dist i.val k.val) :=
      zero_le_one.trans (singularFactor_one_le (by norm_num) _)
    calc
      _ ≤ (R*C₀/(η*T))*singularFactor 24 (Nat.dist i.val k.val) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hC₀) hden) hs
      _ = _ := by ring
  · exact le_rfl

theorem amplification_sampling_scale : ∀ᶠ B : ℕ in atTop,
    0 < amplificationMultiplier B ∧
    (amplificationMultiplier B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) ∧
    amplificationMultiplier B ≤ auxiliaryCutoff B ∧
    (amplificationMultiplier B : ℝ) ≤ (B : ℝ)^2 ∧
    Real.log (amplificationMultiplier B) ≤ (B : ℝ)/10 ∧
    (B : ℝ)^(32/100 : ℝ)/2 ≤ amplificationMultiplier B := by
  filter_upwards [amplificationMultiplier_valid,amplificationMultiplier_comparable,
    amplification_block_size_le_square 1,eventually_ge_atTop 1] with B hv hc hs hB
  have hs' : amplificationMultiplier B ≤ B^2 := by simpa using hs
  have hcut : B^2 ≤ auxiliaryCutoff B :=
    pow_le_pow_right₀ hB (by norm_num : 2 ≤ 1000)
  refine ⟨hv.1,hv.2,hs'.trans hcut,by exact_mod_cast hs',?_,?_⟩
  · have hlog := Real.log_le_log (by exact_mod_cast hv.1) hv.2
    rw [Real.log_exp] at hlog
    convert hlog using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert hc.2.1 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingApplicationScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The scales used to apply the counting model -/
namespace JointDickman
open Filter
open scoped Topology

theorem countingMajorDenominator_valid : ∀ᶠ B : ℕ in atTop,
    0 < countingMajorDenominator B ∧ (B : ℝ)^(2/5 : ℝ) ≤ countingMajorDenominator B ∧
      amplificationMultiplier B*countingMajorDenominator B ≤ B := by
  have hp₀ := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/25)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hp : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ)^(7/25 : ℝ) := hp₀
  filter_upwards [amplificationMultiplier_comparable,hp,eventually_ge_atTop 1] with B hT hp hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith
  have hq := Nat.le_ceil ((B : ℝ)^(2/5 : ℝ))
  have hqpos : 0 < countingMajorDenominator B := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos hBp _
  refine ⟨hqpos,hq,?_⟩
  have hqhi : (countingMajorDenominator B : ℝ) ≤ 2*(B : ℝ)^(2/5 : ℝ) := by
    have hf := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg B) (2/5 : ℝ))
    have hone := Real.one_le_rpow hBr (by norm_num : (0 : ℝ) ≤ 2/5)
    dsimp [countingMajorDenominator]
    linarith
  have hmul : (B : ℝ)^(8/25 : ℝ)*(B : ℝ)^(2/5 : ℝ) = (B : ℝ)^(18/25 : ℝ) := by
    rw [← Real.rpow_add hBp]
    norm_num
  have hpow : (B : ℝ)^(18/25 : ℝ)*(B : ℝ)^(7/25 : ℝ) = B := by
    rw [← Real.rpow_add hBp]
    norm_num
  have hh : (amplificationMultiplier B : ℝ)*countingMajorDenominator B ≤ B := calc
    _ ≤ (B : ℝ)^(8/25 : ℝ)*(2*(B : ℝ)^(2/5 : ℝ)) :=
      mul_le_mul hT.2.2 hqhi (Nat.cast_nonneg _) (by positivity)
    _ = 2*(B : ℝ)^(18/25 : ℝ) := by rw [← hmul]; ring
    _ ≤ (B : ℝ)^(18/25 : ℝ)*(B : ℝ)^(7/25 : ℝ) := by
      calc
        _ = (B : ℝ)^(18/25 : ℝ)*2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (Nat.cast_nonneg B) (18/25 : ℝ))
    _ = B := hpow
  exact_mod_cast hh

theorem counting_block_scale {A : ℕ} (hA : 0 < A) : ∀ᶠ B : ℕ in atTop,
    (1/(2*(A : ℝ)))*amplificationMultiplier B ≤ ((amplificationMultiplier B/A : ℕ) : ℝ) ∧
      amplificationMultiplier B ≤ A*amplificationMultiplier B ∧
      ((A : ℝ)/2)*(B : ℝ)^(0.32 : ℝ) ≤ A*amplificationMultiplier B ∧
      (A*amplificationMultiplier B : ℕ) ≤ (A : ℝ)*(B : ℝ)^(0.32 : ℝ) ∧
      A*amplificationMultiplier B ≤ B^2 := by
  have ht : Tendsto amplificationMultiplier atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8/25)).comp
      tendsto_natCast_atTop_atTop)
  filter_upwards [amplificationMultiplier_comparable,ht.eventually_ge_atTop (2*A),
    amplification_block_size_le_square A] with B hT hlarge hsquare
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hlarge' : 2*(A : ℝ) ≤ amplificationMultiplier B := by exact_mod_cast hlarge
  have hdiv : (amplificationMultiplier B : ℝ)/(2*(A : ℝ)) ≤ (amplificationMultiplier B/A : ℕ) := by
    have hfloor : (amplificationMultiplier B : ℝ) < ((amplificationMultiplier B/A : ℕ) : ℝ)*A+A := by
      have hh := Nat.lt_mul_div_succ (amplificationMultiplier B) hA
      have hh' : (amplificationMultiplier B : ℝ) < (A : ℝ)*((amplificationMultiplier B/A : ℕ)+1) := by exact_mod_cast hh
      nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2*(A : ℝ))).mpr
    nlinarith
  refine ⟨?_,?_,?_,?_,hsquare⟩
  · simpa only [one_div_mul_eq_div] using hdiv
  · nlinarith
  · have hh := mul_le_mul_of_nonneg_left hT.2.1 hAr.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    · norm_num <;> ring
  · have hh := mul_le_mul_of_nonneg_left hT.2.2 hAr.le
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingArithmeticMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transfer of the counting-model error to actual integer sites -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem arithmeticSiteCutMean_comparison {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ x, kernelCutNorm (realizedSiteKernel K x) ≤ C*(B : ℝ)^10) :
    |arithmeticSiteCutMean K -
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel K x))| ≤ 2*C/(B : ℝ) := by
  have hh := arithmeticSquareMean_pattern_comparison hB hM
    (fun p hp => (block_prime_twice_sites (by omega) hM hp).1)
    (fun S => kernelCutNorm (realizedSiteKernel K (blockPatternEquiv B M S))) hC
    (fun S => by rw [abs_of_nonneg (kernelCutNorm_nonneg _)]; exact hcap _)
  simpa only [arithmeticSiteCutMean,Equiv.apply_symm_apply] using hh

theorem latent_model_cut_cap {B L T H M : ℕ} {τ C D : ℝ}
    (hB : 1 ≤ B) (hT : 0 < T) (hM : 0 < M) (hM2 : M ≤ B^2) (hD : 0 ≤ D)
    (χ : BlockCandidateIndex M → ℝ)
    (hcap : ∀ S, (∑ i, ∑ k, |latentCandidateKernel B L T H M τ C S χ i k|) ≤
      2*(M : ℝ)^2*(B : ℝ)^2)
    (J : Fin M → Fin M → (auxiliaryPrimes B).powerset →
      (auxiliaryPrimes B).powerset → ℝ)
    (hJ : ∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k)
    (x : Fin M → (auxiliaryPrimes B).powerset) :
    kernelCutNorm (realizedSiteKernel
      (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b) x) ≤
      (2+2*D*Real.exp 24)*(B : ℝ)^10 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hM2r : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM2
  have hlat : (∑ i, ∑ k,
      |realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) x i k|) ≤
      2*(M : ℝ)^2*(B : ℝ)^2 := by
    simpa only [latentPrimeSiteKernel_realizes] using hcap (fun i => (x i).val)
  have hj : (∑ i, ∑ k, |realizedSiteKernel J x i k|) ≤
      (M : ℝ)*(2*D*Real.exp 24) := by
    calc
      _ ≤ ∑ i : Fin M, ∑ k : Fin M, lagEnvelope T D i k :=
        sum_le_sum (fun i _ => sum_le_sum (fun k _ => hJ i k (x i) (x k)))
      _ ≤ ∑ _i : Fin M, (2*D*Real.exp 24) :=
        sum_le_sum (fun i _ => lagEnvelope_row_sum hT hD i)
      _ = _ := by simp
  have hs := (kernel_difference_absolute_mass
    (realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C χ) x)
    (realizedSiteKernel J x)).trans (add_le_add hlat hj)
  calc
    _ ≤ (2*(M : ℝ)^2*(B : ℝ)^2+(M : ℝ)*(2*D*Real.exp 24))/(M : ℝ) := by
      apply (kernelCutNorm_le_absolute_mass _).trans
      simpa only [kernelAbsoluteMass,Fintype.card_fin,realizedSiteKernel] using
        div_le_div_of_nonneg_right hs hMr.le
    _ = 2*(M : ℝ)*(B : ℝ)^2+2*D*Real.exp 24 := by field_simp
    _ ≤ 2*((B : ℝ)^2)*(B : ℝ)^2+2*D*Real.exp 24 := by gcongr
    _ = 2*(B : ℝ)^4+2*D*Real.exp 24 := by ring
    _ ≤ 2*(B : ℝ)^10+(2*D*Real.exp 24)*(B : ℝ)^10 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hBr (by norm_num : 4 ≤ 10)) (by norm_num)
      · exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hBr)
    _ = _ := by ring

theorem latent_model_arithmetic_comparison {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < T → 0 < M → M ≤ B^2 →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ J : Fin M → Fin M → (auxiliaryPrimes B).powerset →
        (auxiliaryPrimes B).powerset → ℝ,
      (∀ i k a b, |J i k a b| ≤ lagEnvelope T D i k) →
      |arithmeticSiteCutMean
        (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b)-
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => kernelCutNorm (realizedSiteKernel
            (fun i k a b => latentPrimeSiteKernel B L T H M τ C χ i k a b-J i k a b) x))| ≤
        2*(2+2*D*Real.exp 24)/(B : ℝ) := by
  filter_upwards [candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2]
    with B hcap hB
  intro C T H M hT hM hM2 χ hχ J hJ
  apply arithmeticSiteCutMean_comparison (by omega) hM2 _ (by positivity)
  exact latent_model_cut_cap (by omega) hT hM hM2 hD χ
    (fun S => (hcap C T H M S χ hχ).1) J hJ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingCoefficientRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coefficients of the actual counting model and their regularity -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingPrimeKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B j : ℕ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (H : (Fin 4 →₀ ℕ) → ℕ) (T σ : ℝ) (x y : auxiliaryPrimes B → Bool) :
    countingPrimeKernel P m B j c H T σ x y =
      ∑ d ∈ P.support, ∑ a, ∑ b, countingTermCoefficient P d (m d) B j (c d) (H d) T σ a b*
        primeCoarseFeature (m d) B a x*primeCoarseFeature (m d) B b y := by
  unfold countingPrimeKernel weightedPolynomialPrimeKernel
  apply sum_congr rfl
  intro d _
  rw [weightedPolynomialTermKernel_coefficients]
  rfl

theorem countingTermCoefficient_regular
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T σ σ' : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → η*T ≤ k →
      |σ| ≤ 3 → |σ'| ≤ 3 → ∀ a b : Fin m,
      |countingTermCoefficient P d m B j c H T σ a b-
        countingTermCoefficient P d m B k c H T σ' a b| ≤ C*(|(j : ℝ)-k|/T+|σ-σ'|) := by
  obtain ⟨C₁,hC₁,hLag⟩ := weightedTermCoefficient_lag_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hη
  obtain ⟨C₂,hC₂,hAmp⟩ := weightedTermCoefficient_parameter_variation hM hMP P d hm c hc H
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C₁+C₂,add_nonneg hC₁ hC₂,?_⟩
  filter_upwards [hLag,hAmp,eventually_ge_atTop 30] with B hLag hAmp hB
  intro j k T σ σ' hT hlog hj hk hσ hσ' a b
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  let r := fun u : ℤ => amplificationBump (Real.log (Real.exp ((u : ℝ)*Real.log 2)/T)/B)
  have hS : ∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*Real.log 2)/T) := by
    intro u hu
    exact (((dyadic_scale_window hB hT hlog).2.1 u hu).2).1
  have hr : ∀ u ∈ S, |r u| ≤ 1 := by
    intro u _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  have hl := hLag j k T (lt_of_lt_of_le zero_lt_one hT) hj hk S hS (fun _ => σ)
    (fun _ _ => hσ) r hr a b
  have ha := hAmp k T S hS (fun _ => σ) (fun _ => σ') (fun _ _ => hσ) (fun _ _ => hσ')
    r hr |σ-σ'| (abs_nonneg _) (fun _ _ => le_rfl) a b
  change |countingTermCoefficient P d m B j c H T σ a b-
    countingTermCoefficient P d m B k c H T σ a b| ≤ _ at hl
  change |countingTermCoefficient P d m B k c H T σ a b-
    countingTermCoefficient P d m B k c H T σ' a b| ≤ _ at ha
  have ht := (abs_sub_le (countingTermCoefficient P d m B j c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ a b)
    (countingTermCoefficient P d m B k c H T σ' a b)).trans (add_le_add hl ha)
  apply ht.trans
  rw [mul_div_assoc]
  have hnn : 0 ≤ |(j : ℝ)-k|/T := div_nonneg (abs_nonneg _) (by linarith)
  nlinarith [mul_nonneg hC₁ (abs_nonneg (σ-σ')),mul_nonneg hC₂ hnn]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingParameterVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform parameter variation of the finite counting kernel -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingPrimeKernel_parameter_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ σ' : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → η*T ≤ j → |σ| ≤ 3 → |σ'| ≤ 3 →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y-
        countingPrimeKernel P m B j c D T σ' x y| ≤ K*|σ-σ'| := by
  choose C hC hbound using fun d =>
    countingTermCoefficient_regular hM hMP P d (hm d) (c d) (hc d) (D d) hη
  let K := ∑ d ∈ P.support, (m d : ℝ)^2*C d/(channelMesh (m d))^2
  refine ⟨K,by dsimp [K]; exact sum_nonneg (fun d _ => div_nonneg (mul_nonneg (sq_nonneg _) (hC d)) (sq_nonneg _)),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hB
  intro j T σ σ' hT hlog hj hσ hσ' x y
  simp only [countingPrimeKernel_coefficients,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ P.support, (m d : ℝ)^2*C d/(channelMesh (m d))^2*|σ-σ'| := by
      apply sum_le_sum
      intro d hd
      apply (abs_sum_le_sum_abs _ _).trans
      calc
        _ ≤ ∑ a : Fin (m d), ∑ b : Fin (m d), C d*|σ-σ'|/(channelMesh (m d))^2 := by
          apply sum_le_sum
          intro a _
          apply (abs_sum_le_sum_abs _ _).trans
          apply sum_le_sum
          intro b _
          have hmesh := channelMesh_pos (hm d)
          have hCd := hC d
          have hh := hB d hd j j T σ σ' hT hlog hj hj hσ hσ' a b
          simp only [sub_self,abs_zero,zero_div,zero_add] at hh
          rw [← sub_mul,← sub_mul,abs_mul,abs_mul]
          have hx := primeCoarseFeature_bounds (hm d) a x
          have hy := primeCoarseFeature_bounds (hm d) b y
          rw [abs_of_nonneg hx.1,abs_of_nonneg hy.1]
          have hprod := mul_le_mul
            (mul_le_mul hh hx.2 hx.1 (mul_nonneg (hC d) (abs_nonneg _)))
            hy.2 hy.1 (by positivity : 0 ≤ C d*|σ-σ'| *(1/channelMesh (m d)))
          exact hprod.trans_eq (by ring)
        _ = _ := by simp <;> ring
    _ = K*|σ-σ'| := by rw [sum_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CutNormParameter
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of the finite cut norm under parameter changes -/
namespace JointDickman
open Finset Classical

theorem kernelCutNorm_difference_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K J : ι → ι → ℝ) :
    |kernelCutNorm K-kernelCutNorm J| ≤ kernelAbsoluteMass (fun i k => K i k-J i k) := by
  have h₁ : kernelCutNorm K ≤ kernelCutNorm (fun i k => K i k-J i k)+kernelCutNorm J := by
    convert kernelCutNorm_add (fun i k => K i k-J i k) J using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext i k
    ring
  have h₂ : kernelCutNorm J ≤ kernelCutNorm (fun i k => J i k-K i k)+kernelCutNorm K := by
    convert kernelCutNorm_add (fun i k => J i k-K i k) K using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext i k
    ring
  have hb₁ := kernelCutNorm_le_absolute_mass (fun i k => K i k-J i k)
  have hb₂ := kernelCutNorm_le_absolute_mass (fun i k => J i k-K i k)
  have he : kernelAbsoluteMass (fun i k => J i k-K i k) =
      kernelAbsoluteMass (fun i k => K i k-J i k) := by
    simp only [kernelAbsoluteMass,abs_sub_comm]
  rw [he] at hb₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem kernelAbsoluteMass_entry_bound {M : ℕ} (hM : 0 < M)
    (K : Fin M → Fin M → ℝ) {C : ℝ} (hentry : ∀ i k, |K i k| ≤ C) :
    kernelAbsoluteMass K ≤ (M : ℝ)*C := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold kernelAbsoluteMass
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  exact (sum_le_sum (fun i _ => sum_le_sum (fun k _ => hentry i k))).trans_eq (by simp <;> ring)

theorem kernel_error_parameter_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K K' J J' : ι → ι → ℝ) {A B : ℝ}
    (hK : kernelAbsoluteMass (fun i k => K i k-K' i k) ≤ A)
    (hJ : kernelAbsoluteMass (fun i k => J i k-J' i k) ≤ B) :
    |kernelCutNorm (fun i k => K i k-J i k)-kernelCutNorm (fun i k => K' i k-J' i k)| ≤ A+B := by
  apply (kernelCutNorm_difference_bound _ _).trans
  apply le_trans _ (add_le_add hK hJ)
  unfold kernelAbsoluteMass
  rw [← add_div,← sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro i _
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  convert abs_sub (K i k-K' i k) (J i k-J' i k) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingEntryVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parameter continuity of the actual counting-model entries -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem countingSiteWithSeries_entry_variation (F : ℕ → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ)
    (B L T H M : ℕ) (τ C : ℝ) (c : (Fin 4 →₀ ℕ) → ℕ → ℝ)
    (D : (Fin 4 →₀ ℕ) → ℕ) {σ σ' K : ℝ} (hK : 0 ≤ K)
    (hkernel : ∀ j : ℕ, H < j → j < T → ∀ x y,
      |countingPrimeKernel P m B j c D T σ x y-countingPrimeKernel P m B j c D T σ' x y| ≤ K*|σ-σ'|)
    (i k : Fin M) (a b : (auxiliaryPrimes B).powerset) :
    |countingSiteWithSeries F P m B L T H M τ C c D σ i k a b-
      countingSiteWithSeries F P m B L T H M τ C c D σ' i k a b| ≤
      (∑ j ∈ range (T+1), |independentRootMean B L τ C*(F j/(j : ℝ))| *K)*|σ-σ'| := by
  let V := ∑ j ∈ range (T+1), |independentRootMean B L τ C*(F j/(j : ℝ))| *K
  have hV : 0 ≤ V := sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hK)
  have hj (j : ℕ) (hH : H < j) (hT : j < T) (a b : Finset ℕ) :
      |countingCandidateWithSeries F P m B L j τ C c D T σ a b-
        countingCandidateWithSeries F P m B L j τ C c D T σ' a b| ≤ V*|σ-σ'| := by
    unfold countingCandidateWithSeries subsetPrimeModel
    rw [← mul_sub,abs_mul]
    apply (mul_le_mul_of_nonneg_left (hkernel j hH hT _ _) (abs_nonneg _)).trans
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact single_le_sum (s := range (T+1))
      (f := fun l => |independentRootMean B L τ C*(F l/(l : ℝ))| *K)
      (fun l _ => mul_nonneg (abs_nonneg _) hK) (mem_range.mpr (by omega))
  change _ ≤ V*|σ-σ'|
  unfold countingSiteWithSeries
  split_ifs with hik hh hki hh
  · exact hj _ hh.1 hh.2 _ _
  · simp only [sub_self,abs_zero] <;> positivity
  · exact hj _ hh.1 hh.2 _ _
  · simp only [sub_self,abs_zero] <;> positivity
  · simp only [sub_self,abs_zero] <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_OriginRampShift
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The within-block shift of the counting ramp disappears in the long average -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_absoluteMass {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e) :
    kernelAbsoluteMass (latentCandidateKernel B L T H M τ C S χ) =
      (2*∑ e : blockCandidates B L T H M τ C S,
        candidateMeanWeight B L τ C S χ e.val)/(M : ℝ) := by
  unfold kernelAbsoluteMass
  simp only [abs_of_nonneg (latentCandidateKernel_nonneg B L T H M τ C S χ hχ _ _),
    Fintype.card_fin]
  exact congrArg (fun x : ℝ => x/(M : ℝ)) (candidateMatrix_total _ _ _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RampedKernelVariation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute-mass variation of the actual ramped candidate kernel -/
namespace JointDickman
open Finset Classical

theorem candidateMatrix_absoluteMass_sub {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v w : ι → ℝ) :
    kernelAbsoluteMass (fun i k => candidateMatrix row col v i k-candidateMatrix row col w i k) ≤
      (2*∑ e, |v e-w e|)/(Fintype.card κ : ℝ) := by
  unfold kernelAbsoluteMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp_rw [← candidateMatrix_sub]
  exact (sum_le_sum (fun i _ => sum_le_sum (fun k _ =>
    candidateMatrix_abs_le row col _ i k))).trans_eq (candidateMatrix_total row col _)

theorem rampedKernel_absolute_variation {B L T H M : ℕ} {τ C δ σ σ' : ℝ}
    (hδ : 0 < δ) (S : Fin M → Finset ℕ) :
    kernelAbsoluteMass (fun i k =>
      latentCandidateKernel B L T H M τ C S (rampedCandidateCutoff B T δ σ) i k-
      latentCandidateKernel B L T H M τ C S (rampedCandidateCutoff B T δ σ') i k) ≤
    (|σ-σ'|/δ)*kernelAbsoluteMass
      (latentCandidateKernel B L T H M τ C S (smoothCandidateCutoff B T)) := by
  let r := |σ-σ'|/δ
  have hw (e : BlockCandidateIndex M) :
      |candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e-
        candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e| ≤
      r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e := by
    rw [candidateMeanWeight_cutoff_error]
    have hf : |rampedCandidateCutoff B T δ σ e-rampedCandidateCutoff B T δ σ' e| ≤
        smoothCandidateCutoff B T e*r := by
      change |smoothCandidateCutoff B T e*countingRamp δ σ _-
        smoothCandidateCutoff B T e*countingRamp δ σ' _| ≤ _
      rw [← mul_sub,abs_mul,abs_of_nonneg (smoothCandidateCutoff_nonneg B T e)]
      exact mul_le_mul_of_nonneg_left (countingRamp_threshold_lipschitz hδ _ _ _)
        (smoothCandidateCutoff_nonneg B T e)
    exact (mul_le_mul_of_nonneg_left hf
      (candidateMeanWeight_nonneg B L τ C S (fun _ => 1) (fun _ => zero_le_one) e)).trans_eq (by
        rw [candidateMeanWeight_cutoff_factor B L τ C S (smoothCandidateCutoff B T) e]
        ring)
  calc
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        |candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e.val-
          candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e.val|)/(M : ℝ) := by
      unfold latentCandidateKernel
      simpa only [Fintype.card_fin] using candidateMatrix_absoluteMass_sub
        (fun e : blockCandidates B L T H M τ C S => e.val.1.1) (fun e => e.val.1.2)
        (fun e => candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ) e.val)
        (fun e => candidateMeanWeight B L τ C S (rampedCandidateCutoff B T δ σ') e.val)
    _ ≤ (2*∑ e : blockCandidates B L T H M τ C S,
        r*candidateMeanWeight B L τ C S (smoothCandidateCutoff B T) e.val)/(M : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun e _ => hw e.val)) (by norm_num)
    _ = _ := by
      rw [latentCandidateKernel_absoluteMass S _ (smoothCandidateCutoff_nonneg B T),← mul_sum]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingErrorParameter
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity of the actual sampling error in the counting parameter -/
namespace JointDickman
open Finset Classical

theorem countingError_parameter_bound (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ)
    {A K : ℝ} (_hA : 0 ≤ A) (hK : 0 ≤ K) (hw : 0 < w) (hM : 0 < M)
    (hcap : ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ A)
    (hkernel : ∀ (j : ℕ) (s t : ℝ), H < j → j < T → |s| ≤ 3 → |t| ≤ 3 → ∀ x y,
      |countingPrimeKernel P m B j c D T s x y-countingPrimeKernel P m B j c D T t x y| ≤ K*|s-t|) :
    ∀ (s t : ℝ), |s| ≤ 3 → |t| ≤ 3 → ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      |kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D s) x)-
        kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D t) x)| ≤
      (A/w+(M : ℝ)*(∑ j ∈ range (T+1), |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K))*|s-t| := by
  intro s t hs ht x
  let V := ∑ j ∈ range (T+1), |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K
  let R := fun a => latentCandidateKernel B L T H M τ C (fun i => (x i).val)
    (rampedCandidateCutoff B T w a)
  let J := fun a => realizedSiteKernel (countingSiteModel P m B L T H M τ C c D a) x
  have he (a : ℝ) : realizedSiteKernel (countingSiteError P m B L T H M τ C w c D a) x =
      fun i k => R a i k-J a i k := by
    funext i k
    change realizedSiteKernel (latentPrimeSiteKernel B L T H M τ C (rampedCandidateCutoff B T w a)) x i k-
      J a i k = _
    rw [latentPrimeSiteKernel_realizes]
  rw [he,he]
  have hR : kernelAbsoluteMass (fun i k => R s i k-R t i k) ≤ (A/w)*|s-t| := by
    apply (rampedKernel_absolute_variation hw (fun i => (x i).val)).trans
    exact (mul_le_mul_of_nonneg_left (hcap x) (by positivity)).trans_eq (by ring)
  have hJ : kernelAbsoluteMass (fun i k => J s i k-J t i k) ≤ (M : ℝ)*V*|s-t| := by
    apply (kernelAbsoluteMass_entry_bound hM _ (fun i k => ?_)).trans_eq (mul_assoc _ _ _).symm
    exact countingSiteWithSeries_entry_variation singularSeries P m B L T H M τ C c D hK
      (fun j hj hjT => hkernel j s t hj hjT hs ht) i k (x i) (x k)
  exact (kernel_error_parameter_bound (R s) (R t) (J s) (J t) hR hJ).trans_eq (by ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingKernelBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the actual counting prime kernel -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → |σ| ≤ 3 →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K := by
  obtain ⟨K,hK,hbound⟩ := weightedPolynomialPrimeKernel_bounded hM hMP P m hm c hc D
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 30] with B hb hB
  intro j T σ hT hlog hσ x y
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  have hS : ∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) := by
    intro k hk
    exact (((dyadic_scale_window hB hT hlog).2.1 k hk).2).1
  let r := fun k : ℤ => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
  have hr : ∀ k ∈ S, |r k| ≤ 1 := by
    intro k _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  exact hb j T S hS (fun _ => σ) (fun _ _ => hσ) r hr x y

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingOriginParameter
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving block origin is a bounded, slowly varying parameter -/
namespace JointDickman
open Finset Classical

theorem countingOriginParameter_bound (T N u : ℕ) :
    |countingOriginParameter T N u| ≤ 3 := by
  rw [abs_of_nonneg (le_min (by norm_num) (by positivity))]
  exact min_le_left _ _

theorem countingOriginParameter_step {T : ℕ} (hT : 0 < T) (N q b r : ℕ) (hr : r < q) :
    |countingOriginParameter T N (b*q+r)-countingOriginParameter T N (b*q)| ≤
      (q : ℝ)/((T : ℝ)*(N+1)) := by
  have hd : (0 : ℝ) < (T : ℝ)*(N+1) := by positivity
  have hh := abs_min_sub_min_le_max (3 : ℝ) (((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1)))
    3 (((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1)))
  have habs : (0 : ℝ) ≤ |((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1))-((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1))| := abs_nonneg _
  simp only [sub_self,abs_zero,max_eq_right habs] at hh
  apply hh.trans
  have he : ((b*q+r : ℕ) : ℝ)/((T : ℝ)*(N+1))-((b*q : ℕ) : ℝ)/((T : ℝ)*(N+1)) =
      (r : ℝ)/((T : ℝ)*(N+1)) := by push_cast <;> ring
  rw [he,abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hr.le) hd.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SlowPeriodicMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic average with a slowly varying counting parameter -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem sum_range_blocks_real (f : ℕ → ℝ) (q k : ℕ) :
    (∑ u ∈ range (k*q), f u) = ∑ b ∈ range k, ∑ r ∈ range q, f (b*q+r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,sum_range_add,ih,sum_range_succ]

theorem slow_periodic_sum_bound {q : ℕ} (hq : 0 < q) (f : ℕ → ℝ → ℝ)
    {A L δ : ℝ} (hL : 0 ≤ L) (_hδ : 0 ≤ δ)
    (hpos : ∀ u s, |s| ≤ 3 → 0 ≤ f u s)
    (hper : ∀ b r s, f (b*q+r) s = f r s)
    (hmean : ∀ s, |s| ≤ 3 → (∑ r ∈ range q, f r s) ≤ (q : ℝ)*A)
    (hlip : ∀ u s t, |s| ≤ 3 → |t| ≤ 3 → |f u s-f u t| ≤ L*|s-t|)
    (K : ℕ) (σ : ℕ → ℝ) (hσ : ∀ u, |σ u| ≤ 3)
    (hstep : ∀ b r, r < q → |σ (b*q+r)-σ (b*q)| ≤ δ) :
    (∑ u ∈ range K, f u (σ u)) ≤ ((K/q+1)*q : ℕ)*(A+L*δ) := by
  have hsub : range K ⊆ range ((K/q+1)*q) := by
    apply range_mono
    have hm := Nat.mod_lt K hq
    have he : K/q*q+K%q = K := by simpa only [Nat.mul_comm] using Nat.div_add_mod K q
    simp only [Nat.add_mul,one_mul]
    omega
  calc
    _ ≤ ∑ u ∈ range ((K/q+1)*q), f u (σ u) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hpos u (σ u) (hσ u))
    _ = ∑ b ∈ range (K/q+1), ∑ r ∈ range q, f (b*q+r) (σ (b*q+r)) :=
      sum_range_blocks_real _ _ _
    _ ≤ ∑ b ∈ range (K/q+1), (q : ℝ)*(A+L*δ) := by
      apply sum_le_sum
      intro b _
      calc
        _ ≤ ∑ r ∈ range q, (f r (σ (b*q))+L*δ) := by
          apply sum_le_sum
          intro r hr
          have hh := (le_abs_self (f (b*q+r) (σ (b*q+r))-f (b*q+r) (σ (b*q)))).trans
            ((hlip _ _ _ (hσ _) (hσ _)).trans
              (mul_le_mul_of_nonneg_left (hstep b r (mem_range.mp hr)) hL))
          simp only [hper] at hh ⊢
          linarith
        _ = (∑ r ∈ range q, f r (σ (b*q)))+(q : ℝ)*(L*δ) := by simp [sum_add_distrib]
        _ ≤ (q : ℝ)*A+(q : ℝ)*(L*δ) := add_le_add (hmean _ (hσ _)) le_rfl
        _ = _ := by ring
    _ = _ := by simp <;> ring

theorem slow_periodic_mean_bound {q T : ℕ} (hq : 0 < q) (hT : 0 < T)
    (f : ℕ → ℝ → ℝ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hpos : ∀ u s, |s| ≤ 3 → 0 ≤ f u s)
    (hper : ∀ b r s, f (b*q+r) s = f r s)
    (hmean : ∀ s, |s| ≤ 3 → (∑ r ∈ range q, f r s) ≤ (q : ℝ)*A)
    (hlip : ∀ u s t, |s| ≤ 3 → |t| ≤ 3 → |f u s-f u t| ≤ L*|s-t|)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
      (∀ b r, r < q → |σ (b*q+r)-σ (b*q)| ≤ (q : ℝ)/((T : ℝ)*(N+1))) →
      (∑ u ∈ range (J*N), f u (σ u))/(N : ℝ) < (J : ℝ)*A+ε := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hrec := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (q : ℝ)
  have hrec' : Tendsto (fun N : ℕ => (q : ℝ)/((T : ℝ)*(N+1))) atTop (𝓝 0) := by
    have hh := (tendsto_add_atTop_nat 1).comp tendsto_id
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ((q : ℝ)/T)).comp hh
    simpa only [Function.comp_def,id_eq,Nat.cast_add,Nat.cast_one,div_div] using ht
  have hlim : Tendsto (fun N : ℕ => ((J : ℝ)+(q : ℝ)/N)*
      (A+L*((q : ℝ)/((T : ℝ)*(N+1))))) atTop (𝓝 ((J : ℝ)*A)) := by
    simpa only [add_zero,mul_zero] using
      (tendsto_const_nhds.add hrec).mul (tendsto_const_nhds.add (hrec'.const_mul L))
  filter_upwards [hlim.eventually (eventually_lt_nhds (lt_add_of_pos_right ((J : ℝ)*A) hε)),
    eventually_gt_atTop 0] with N hN hNpos
  intro σ hσ hstep
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply (div_le_div_of_nonneg_right (slow_periodic_sum_bound hq f hL (by positivity)
    hpos hper hmean hlip (J*N) σ hσ hstep) hNr.le).trans_lt
  have hcard : (((J*N/q+1)*q : ℕ) : ℝ) ≤ (J : ℝ)*N+q := by
    exact_mod_cast (show (J*N/q+1)*q ≤ J*N+q by
      nlinarith [Nat.div_mul_le_self (J*N) q])
  calc
    _ ≤ (((J : ℝ)*N+q)*(A+L*((q : ℝ)/((T : ℝ)*(N+1)))))/(N : ℝ) := by
      gcongr
    _ = ((J : ℝ)+(q : ℝ)/N)*(A+L*((q : ℝ)/((T : ℝ)*(N+1)))) := by field_simp
    _ < _ := hN

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSlowMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # From the periodic sampling error to the moving counting scale -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem arithmeticSiteCutMean_period_bound {B M : ℕ}
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset → (auxiliaryPrimes B).powerset → ℝ)
    {E : ℝ} (hE : arithmeticSiteCutMean K ≤ E) :
    (∑ u ∈ range (auxiliarySquarePeriod B), kernelCutNorm
      (realizedSiteKernel K (blockPatternEquiv B M (arithmeticPrimePatterns B M u)))) ≤
        (auxiliarySquarePeriod B : ℝ)*E := by
  have hq : auxiliarySquarePeriod B = ∏ p ∈ auxiliaryPrimes B, p^2 := by
    simp only [auxiliarySquarePeriod,prod_pow]
  have hqr : (auxiliarySquarePeriod B : ℝ) = ∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2 := by
    rw [hq]
    simp only [Nat.cast_prod,Nat.cast_pow]
  have hqp : (0 : ℝ) < auxiliarySquarePeriod B := by exact_mod_cast auxiliarySquarePeriod_pos B
  unfold arithmeticSiteCutMean arithmeticSquareMean at hE
  rw [← hq,← hqr] at hE
  exact (div_le_iff₀ hqp).mp hE |>.trans_eq (mul_comm _ _)

theorem blockPatternEquiv_arithmetic_modEq {B M u v : ℕ}
    (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    blockPatternEquiv B M (arithmeticPrimePatterns B M u) =
      blockPatternEquiv B M (arithmeticPrimePatterns B M v) := by
  funext i
  apply Subtype.ext
  simpa only [blockPatternEquiv_val,primePatternsSites_arithmetic] using
    congrFun (blockPrimeSites_modEq (M := M) h) i

theorem counting_slow_mean (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ)
    {A K E : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hw : 0 < w) (hT : 0 < T) (hM : 0 < M)
    (hcap : ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ A)
    (hkernel : ∀ (j : ℕ) (s t : ℝ), H < j → j < T → |s| ≤ 3 → |t| ≤ 3 → ∀ x y,
      |countingPrimeKernel P m B j c D T s x y-countingPrimeKernel P m B j c D T t x y| ≤ K*|s-t|)
    (hmean : ∀ σ : ℝ, |σ| ≤ 3 → arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ) ≤ E)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
      (∀ b r, r < auxiliarySquarePeriod B →
        |σ (b*auxiliarySquarePeriod B+r)-σ (b*auxiliarySquarePeriod B)| ≤
          (auxiliarySquarePeriod B : ℝ)/((T : ℝ)*(N+1))) →
      (∑ u ∈ range (J*N), countingArithmeticCutError P m B L T H M τ C w c D (σ u) u)/(N : ℝ) <
        (J : ℝ)*E+ε := by
  let V := A/w+(M : ℝ)*(∑ j ∈ range (T+1),
    |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K)
  have hV : 0 ≤ V := add_nonneg (div_nonneg hA hw.le) (mul_nonneg (Nat.cast_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hK)))
  apply slow_periodic_mean_bound (auxiliarySquarePeriod_pos B) hT
    (fun u s => countingArithmeticCutError P m B L T H M τ C w c D s u) hE hV
    (fun _ _ _ => kernelCutNorm_nonneg _) _ _ _ J hε
  · intro b r s
    unfold countingArithmeticCutError
    rw [blockPatternEquiv_arithmetic_modEq (show b*auxiliarySquarePeriod B+r ≡ r [MOD auxiliarySquarePeriod B] by
      unfold Nat.ModEq
      simp)]
  · intro s hs
    exact arithmeticSiteCutMean_period_bound _ (hmean s hs)
  · intro u s t hs ht
    exact countingError_parameter_bound P m B L T H M τ C w c D hA hK hw hM hcap hkernel
      s t hs ht _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSamplingMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published sampling inputs control the actual moving arithmetic error -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_slow_mean
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (H M U V Q : ℕ),
        Cmin ≤ C →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → amplificationMultiplier B*Q ≤ B →
        η*amplificationMultiplier B ≤ H → amplificationMultiplier B ≤ M →
        c₁*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U₁*(B : ℝ)^(0.32 : ℝ) →
        M ≤ B^2 →
        FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
        ∀ (J : ℕ) (δ : ℝ), 0 < δ → ∀ᶠ N : ℕ in atTop,
        ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
        (∀ b r, r < auxiliarySquarePeriod B →
          |σ (b*auxiliarySquarePeriod B+r)-σ (b*auxiliarySquarePeriod B)| ≤
            (auxiliarySquarePeriod B : ℝ)/((amplificationMultiplier B : ℝ)*(N+1))) →
        (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
          H M τ C w c D (σ u) u)/(N : ℝ) < (J : ℝ)*(ε+Kerror/(B : ℝ))+δ := by
  obtain ⟨τ,hτ,hτcap,hτsmall,hsample⟩ := counting_sampling_jd hFord hSD hSW hM hMP hL hη hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w c₁ U₁ ε hw hc₁ hU₁ hε
  obtain ⟨P,c,hc,D,m,hm,Cmin,hCmin,hmodel⟩ := hsample w c₁ U₁ ε hw hc₁ hU₁ hε
  obtain ⟨V,hV,hbound⟩ := countingPrimeKernel_bounded hM hMP P m hm c (fun d => (hc d).1) D
  obtain ⟨K,hK,hvariation⟩ := countingPrimeKernel_parameter_variation hM hMP P m hm c
    (fun d => (hc d).1) D hη
  obtain ⟨R,hR,hroot⟩ := independentRootMean_bounded hM
  let E := R*V/η
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  let Kerror := 2*(2+2*E*Real.exp 24)
  refine ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,by dsimp [Kerror] <;> positivity,?_⟩
  filter_upwards [hmodel,hbound,hvariation,hroot,amplification_sampling_scale,
    latent_model_arithmetic_comparison (by omega : 1 ≤ L) hτ.le hτsmall hE,
    candidate_kernels_polynomial_mass (by omega : 1 ≤ L) hτ.le hτsmall]
    with B hmodel hbound hvariation hroot hscale hcompare hmass
  intro C H M U V₀ Q hC hU hV₀ hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hM2 hMC J δ hδ
  let T := amplificationMultiplier B
  have hT : 0 < T := hscale.1
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : Real.log (T : ℝ) ≤ (B : ℝ)/10 := hscale.2.2.2.2.1
  have hMp : 0 < M := hT.trans_le hTM
  have hmean (σ : ℝ) (hσ : |σ| ≤ 3) : arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ) ≤ ε+Kerror/(B : ℝ) := by
    have he := hmodel C H M U V₀ Q hC hU hV₀ hdyU hdyV hQ hcut hTQ hH hTM hMlo hMhi hMC σ hσ
    have hc' := hcompare C T H M hT hMp hM2 (rampedCandidateCutoff B T w σ)
      (rampedCandidateCutoff_bounds hw B T σ) (countingSiteModel P m B L T H M τ C c D σ)
      (countingSiteModel_uniform_envelope hMP P m B L T H M τ C c D hT hη hV
        (hroot L τ C) hH (fun j _ _ => hbound j T σ hT1 hlog hσ))
    have hdiff := le_abs_self (arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ)-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel
          (countingSiteError P m B L T H M τ C w c D σ) x)))
    change |arithmeticSiteCutMean (countingSiteError P m B L T H M τ C w c D σ)-
      finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun x => kernelCutNorm (realizedSiteKernel
          (countingSiteError P m B L T H M τ C w c D σ) x))| ≤ Kerror/(B : ℝ) at hc'
    linarith
  have hmass' (x : Fin M → (auxiliaryPrimes B).powerset) :
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ 2*(M : ℝ)*(B : ℝ)^2 := by
    have hχ : ∀ e : BlockCandidateIndex M, 0 ≤ smoothCandidateCutoff B T e ∧ smoothCandidateCutoff B T e ≤ 1 := by
      intro e
      refine ⟨smoothCandidateCutoff_nonneg B T e,?_⟩
      unfold smoothCandidateCutoff candidateCutoff amplificationOuterWeight amplificationInnerWeight
      exact (mul_le_mul (mul_le_mul (amplificationBump_bounds _).2 (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num)) (amplificationBump_bounds _).2
        (amplificationBump_bounds _).1 (by norm_num)).trans_eq (by norm_num)
    have hh := (hmass C T H M (fun i => (x i).val) (smoothCandidateCutoff B T) hχ).1
    unfold kernelAbsoluteMass
    simp only [Fintype.card_fin]
    apply (div_le_div_of_nonneg_right hh (Nat.cast_nonneg M)).trans_eq
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hMp.ne'
    field_simp
  exact counting_slow_mean P m B L T H M τ C w c D (by positivity) hK
    (by positivity : 0 ≤ ε+Kerror/(B : ℝ)) hw hT hMp hmass'
    (fun j s t hj hjT hs ht => hvariation j T s t hT1 hlog
      (hH.trans (by exact_mod_cast hj.le)) hs ht) hmean J hδ

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CountingSamplingScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampling at the manuscript's actual block and cutoff scales -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_actual_scale_jd_oai
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {L A : ℕ} {cap : ℝ} (hL : 10000 ≤ L) (hA : 0 < A) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w ε : ℝ, 0 < w → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin Kerror : ℝ, 0 ≤ Cmin ∧ 0 ≤ Kerror ∧
      ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, Cmin ≤ C →
      ∀ J : ℕ, ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
        (∑ u ∈ range (J*N), countingArithmeticCutError P m B L (amplificationMultiplier B)
          (amplificationMultiplier B/A) (A*amplificationMultiplier B) τ C w c D
          (countingOriginParameter (amplificationMultiplier B) N u) u)/(N : ℝ) <
          (J : ℝ)*(ε+Kerror/(B : ℝ))+δ := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨τ,hτ,hτcap,hτsmall,hsample⟩ := counting_sampling_slow_mean hFord hSD hSW hM hMP
    hL (by positivity : 0 < 1/(2*(A : ℝ))) hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro w ε hw hε
  obtain ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,hKerror,hs⟩ :=
    hsample w ((A : ℝ)/2) A ε hw (by positivity) (Nat.cast_nonneg _) hε
  refine ⟨P,c,hc,D,m,hm,Cmin,Kerror,hCmin,hKerror,?_⟩
  filter_upwards [hs,countingMajorDenominator_valid,counting_block_scale hA,
    amplificationMultiplier_comparable] with B hb hQ hscale hT
  intro C hC J δ hδ
  let S := dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
    (dyadicBoxUpper B (amplificationMultiplier B))
  let f := fun k : ℤ => ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊
  let g := fun k : ℤ => ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊
  let U := max (∏ p ∈ auxiliaryPrimes B,p) (S.sup f)
  let V := max ⌊Real.exp (2*(B : ℝ))⌋₊ (S.sup g)
  have hh := hb C (amplificationMultiplier B/A) (A*amplificationMultiplier B) U V
    (countingMajorDenominator B) hC (le_max_left _ _) (le_max_left _ _)
    (fun k hk => (le_sup (f := f) hk).trans (le_max_right _ _))
    (fun k hk => (le_sup (f := g) hk).trans (le_max_right _ _))
    hQ.1 hQ.2.1 hQ.2.2 hscale.1 hscale.2.1 (by simpa only [Nat.cast_mul] using hscale.2.2.1) hscale.2.2.2.1 hscale.2.2.2.2
    (hMC B _) J δ hδ
  filter_upwards [hh] with N hN
  exact hN (countingOriginParameter (amplificationMultiplier B) N)
    (countingOriginParameter_bound _ _)
    (countingOriginParameter_step hT.1 N _)

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.counting_sampling_actual_scale_jd_oai := @OAI.JointDickman.counting_sampling_actual_scale_jd_oai
