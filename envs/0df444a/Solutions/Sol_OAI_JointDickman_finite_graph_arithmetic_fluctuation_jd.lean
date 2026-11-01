-- Prove2me | solution 1 for OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:38:07.761787+00:00
-- url     : https://prove2.me/submissions/f2a85d7b-6181-4c72-bd60-184cd25816a8

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_masked_arithmetic_fluctuation_bound_jd

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

/-- Every smaller real power is negligible compared with a larger one. -/
theorem power_div_power_tendsto_zero {a b : ℝ} (hab : a < b) :
    Tendsto (fun B : ℝ => B ^ a / B ^ b) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  rw [← Real.rpow_sub hB]
  congr 1
  ring

/-- In particular, each fixed polynomial degree below the cutoff exponent
is negligible compared with `P₀ = B^1000`. -/
theorem polynomial_div_primeCutoff_tendsto_zero {k : ℕ} (hk : k < 1000) :
    Tendsto (fun B : ℝ => B ^ k / B ^ (1000 : ℕ)) atTop (𝓝 0) := by
  have h : (k : ℝ) < (1000 : ℝ) := by exact_mod_cast hk
  have hlim := power_div_power_tendsto_zero h
  change Tendsto (fun B : ℝ => B ^ (k : ℝ) / B ^ ((1000 : ℕ) : ℝ))
    atTop (𝓝 0) at hlim
  simpa only [Real.rpow_natCast] using hlim

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

theorem primeProduct_squarefree (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
  · exact fun p hp => (hS p hp).squarefree

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicAverages
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- Complete blocks have exactly the same sum, with an unaltered final
prefix. This equality also holds when the modulus is zero. -/
theorem periodic_sum_blocks {q : ℕ} (f : ZMod q → ℂ) (k r : ℕ) :
    (∑ n ∈ Finset.range (k * q + r), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range r, f (n : ZMod q) := by
  have hshift (k n : ℕ) : f ((k * q + n : ℕ) : ZMod q) = f (n : ZMod q) := by
    simp
  have hblocks : ∀ k : ℕ, (∑ n ∈ Finset.range (k * q), f (n : ZMod q)) =
      (k : ℂ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add,
        Nat.cast_one]
      ring
  rw [Finset.sum_range_add, hblocks]
  simp only [hshift]

theorem periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, f (n : ZMod q)) =
      (N / q : ℕ) * (∑ n ∈ Finset.range q, f (n : ZMod q)) +
        ∑ n ∈ Finset.range (N % q), f (n : ZMod q) := by
  have hsplit : N / q * q + N % q = N := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod N q
  simpa only [hsplit] using periodic_sum_blocks f (N / q) (N % q)

private theorem prefix_centered_bound {q r : ℕ} (hq : 0 < q) (hr : r ≤ q)
    (F : ℕ → ℂ) {M : ℝ} (hF : ∀ i < q, ‖F i‖ ≤ M) :
    ‖(∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i‖ ≤ q * M := by
  classical
  have hprefix : (∑ i ∈ Finset.range r, F i) =
      ∑ i ∈ Finset.range q, if i < r then F i else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  have hid : (∑ i ∈ Finset.range r, F i) -
      ((r : ℂ) / q) * ∑ i ∈ Finset.range q, F i =
      ∑ i ∈ Finset.range q, ((if i < r then (1 : ℂ) else 0) - (r : ℂ) / q) * F i := by
    rw [hprefix, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  rw [hid]
  refine (norm_sum_le _ _).trans ?_
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hquot0 : 0 ≤ (r : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hqR.le
  have hquot1 : (r : ℝ) / q ≤ 1 := (div_le_one hqR).mpr (by exact_mod_cast hr)
  calc
    _ ≤ ∑ i ∈ Finset.range q, M := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoef : ‖(if i < r then (1 : ℂ) else 0) - (r : ℂ) / q‖ ≤ 1 := by
        have hcast : (r : ℂ) / q = (((r : ℝ) / q : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        split_ifs
        · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        · simp only [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hquot0]
          exact hquot1
      rw [norm_mul]
      exact (mul_le_mul hcoef (hF i (Finset.mem_range.mp hi)) (norm_nonneg _) (by norm_num)).trans
        (by simp)
    _ = q * M := by simp

/-- The remainder error is at most one period times the uniform norm,
divided by the averaging length. -/
theorem periodicAverage_error {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    {N : ℕ} (hN : 0 < N) :
    ‖periodicAverage f N - residueMean f‖ ≤ (q : ℝ) * ‖f‖ / N := by
  have hq : 0 < q := NeZero.pos q
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hid : periodicAverage f N - residueMean f =
      ((∑ i ∈ Finset.range (N % q), f (i : ZMod q)) -
        ((N % q : ℕ) : ℂ) / q * ∑ i ∈ Finset.range q, f (i : ZMod q)) / N := by
    unfold periodicAverage residueMean
    rw [residue_sum_eq_range, periodic_sum_div_mod]
    have hdecomp : (N : ℂ) = ((N / q : ℕ) : ℂ) * q + (N % q : ℕ) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm :
        N = N / q * q + N % q)
    field_simp
    linear_combination -(∑ i ∈ Finset.range q, f (i : ZMod q)) * hdecomp
  rw [hid, norm_div]
  have hprefix := prefix_centered_bound hq (Nat.mod_lt N hq).le
    (fun i => f (i : ZMod q)) (fun i _ => norm_le_pi_norm f _)
  have hnormN : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hnormN]
  exact div_le_div_of_nonneg_right hprefix (Nat.cast_nonneg _)

theorem periodicAverage_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    Tendsto (periodicAverage f) atTop (𝓝 (residueMean f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun N : ℕ => (q : ℝ) * ‖f‖ / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((eventually_gt_atTop 0).mono (fun N hN => periodicAverage_error f hN)) hlim

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

/-- On nonzero integers the dividing-prime set is exactly the intersection
with the integer's finite prime-factor set. -/
theorem coefficientPrimeSet_eq_inter {B n : ℕ} (hn : n ≠ 0) :
    coefficientPrimeSet B n = n.primeFactors ∩ auxiliaryPrimes B := by
  classical
  ext p
  simp only [coefficientPrimeSet, mem_filter, mem_inter]
  constructor
  · rintro ⟨hp, hpn⟩
    exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.mem_primeFactors hpn hn, hp⟩
  · rintro ⟨hp, hP⟩
    exact ⟨hP, (Nat.mem_primeFactors.mp hp).2.1⟩

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithGraph
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact arithmetic reindexing in the divisor graph

The change of variables turns two divisor representations into an additive
edge. The underlying integer identities hold in both directions without
asymptotic hypotheses.
-/

namespace JointDickman

/-- Reconstruct the second quotient and the additive edge from the first
quotient. All variables are integers, allowing both signs of the lag. -/
theorem divisor_edge_forward {a b c j m z : ℤ}
    (hcoeff : a - b = j * c) (hquot : c * z = a * m + 1) :
    c * (z - j * m) = b * m + 1 ∧
      b * z + j = a * (z - j * m) := by
  constructor
  · linear_combination hquot + m * hcoeff
  · linear_combination -z * hcoeff - j * hquot

/-- The congruence at the new endpoint reconstructs the old divisor
representation. Coprimality with the lag is precisely the cancellation
needed in the reverse direction. -/
theorem divisor_edge_iff {a b c j z : ℤ}
    (hcoeff : a - b = j * c) (hcop : IsCoprime a j) :
    (∃ m : ℤ, c * z = a * m + 1) ↔ a ∣ b * z + j := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨z - j * m, (divisor_edge_forward hcoeff hm).2⟩
  · rintro ⟨k, hk⟩
    have hdiv : a ∣ j * (c * z - 1) := by
      refine ⟨z - k, ?_⟩
      linear_combination -z * hcoeff - hk
    obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdiv
    exact ⟨m, by linarith⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SelectedPrimeOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform odds corrections on bounded prime products -/

namespace JointDickman

open Finset

theorem selectedPrime_card_log_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log (∏ p ∈ S, p : ℕ) := by
  rw [Nat.cast_prod, Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)]
  calc
    _ = ∑ _p ∈ S, Real.log 2 := by simp
    _ ≤ _ := sum_le_sum (fun p hp => Real.log_le_log (by norm_num)
      (by exact_mod_cast (hS p hp).two_le))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDyadicBoxes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic boxes covering the amplification coefficients -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem nat_two_pow_exp (k : ℕ) :
    ((2^k : ℕ) : ℝ) = Real.exp ((k : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_cast

theorem coefficientDyadicCover_contains {B T a c : ℕ} (hB : 0 < B)
    (hcl : Real.exp (B : ℝ) ≤ c) (hcu : (c : ℝ) ≤ Real.exp (2 * B))
    (ha : T * c ≤ a) (ha' : a < 2 * T * c) :
    (a, c) ∈ coefficientDyadicCover B T := by
  have hc0 : 0 < c := by exact_mod_cast (Real.exp_pos (B : ℝ)).trans_le hcl
  have hcne : c ≠ 0 := Nat.ne_of_gt hc0
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlo : B ≤ Nat.log 2 c := by
    apply (Nat.le_log_iff_pow_le (by norm_num) hcne).mpr
    have hpow : ((2^B : ℕ) : ℝ) ≤ c := by
      rw [nat_two_pow_exp]
      apply le_trans (Real.exp_le_exp.mpr _) hcl
      nlinarith only [Real.log_two_lt_d9]
    exact_mod_cast hpow
  have hhi : Nat.log 2 c < 4 * B := by
    apply (Nat.log_lt_iff_lt_pow (by norm_num) hcne).mpr
    have hpow : (c : ℝ) < ((2^(4 * B) : ℕ) : ℝ) := by
      rw [nat_two_pow_exp]
      apply lt_of_le_of_lt hcu
      apply Real.exp_lt_exp.mpr
      push_cast
      nlinarith only [Real.log_two_gt_d9, hB0]
    exact_mod_cast hpow
  have hcp := Nat.pow_log_le_self 2 hcne
  have hcp' := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) c
  rw [pow_succ, mul_comm _ 2] at hcp'
  apply mem_biUnion.mpr
  refine ⟨Nat.log 2 c, mem_Ico.mpr ⟨hlo, hhi⟩, ?_⟩
  apply mem_product.mpr
  constructor
  · apply mem_Ico.mpr
    constructor
    · exact (Nat.mul_le_mul_left T hcp).trans ha
    · have hh := Nat.mul_le_mul_left (2 * T) hcp'.le
      nlinarith only [ha', hh]
  · exact mem_Ico.mpr ⟨hcp, hcp'⟩

theorem mem_amplificationCoefficientPairs {B T a c : ℕ} (hB : 0 < B) :
    (a, c) ∈ amplificationCoefficientPairs B T ↔
      Real.exp (B : ℝ) ≤ c ∧ (c : ℝ) ≤ Real.exp (2 * B) ∧
        T * c ≤ a ∧ a < 2 * T * c := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨coefficientDyadicCover_contains hB h.1 h.2.1 h.2.2.1 h.2.2.2, h⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticSplitWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic coefficient weights on actual squarefree site divisors -/

namespace JointDickman
open Finset

theorem coefficientPrimeSet_primeProduct {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : coefficientPrimeSet B (∏ p ∈ A, p) = A := by
  have hp : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hn : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  rw [coefficientPrimeSet_eq_inter hn, Nat.primeFactors_prod hp, inter_eq_left.mpr hA]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SquarefreeQuotientSite
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing a squarefree coefficient from a site without square hits -/

namespace JointDickman
open Finset

theorem primeProduct_dvd_site_iff {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (∏ p ∈ A, p) ∣ n ↔ A ⊆ coefficientPrimeSet B n := by
  rw [primeProduct_dvd_iff A (fun p hp => auxiliaryPrimes_prime B p (hA hp))]
  constructor
  · intro h p hp
    exact mem_filter.mpr ⟨hA hp, h p hp⟩
  · intro h p hp
    exact (mem_filter.mp (h hp)).2

/-- The quotient prime set is the complementary subset when none of the
selected site primes has a square dividing the original integer. -/
theorem coefficientPrimeSet_quotient {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n)
    (hno : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n) :
    coefficientPrimeSet B (n / (∏ p ∈ A, p)) = coefficientPrimeSet B n \ A := by
  have he : (∏ p ∈ A, p) * (n / (∏ p ∈ A, p)) = n := Nat.mul_div_cancel' ha
  have hpos : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hA hp)).ne_zero)
  have hf : (∏ p ∈ A, p).primeFactors = A :=
    Nat.primeFactors_prod (fun p hp => auxiliaryPrimes_prime B p (hA hp))
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hpq⟩ := mem_filter.mp hp
    have hpn : p ∣ n := by rw [← he]; exact dvd_mul_of_dvd_right hpq _
    refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨hpP, hpn⟩, ?_⟩
    intro hpA
    have hpa : p ∣ ∏ p ∈ A, p := dvd_prod_of_mem id hpA
    have hsq : p^2 ∣ n := by
      rw [pow_two, ← he]
      exact Nat.mul_dvd_mul hpa hpq
    exact hno p hpP hsq
  · intro hp
    obtain ⟨hpn, hpA⟩ := mem_sdiff.mp hp
    obtain ⟨hpP, hpn⟩ := mem_filter.mp hpn
    have hprime := auxiliaryPrimes_prime B p hpP
    have hpa : ¬ p ∣ ∏ p ∈ A, p := by
      intro h
      have hm := hprime.mem_primeFactors h hpos
      rw [hf] at hm
      exact hpA hm
    refine mem_filter.mpr ⟨hpP, ?_⟩
    rw [← he] at hpn
    exact (hprime.dvd_mul.mp hpn).resolve_left hpa

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationSmoothCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem amplificationBump_zero {x : ℝ} (hx : x ≤ 1 ∨ 2 ≤ x) : amplificationBump x = 0 := by
  apply amplificationBump.zero_of_le_dist
  change (1/4 : ℝ) ≤ dist x (11/8 : ℝ)
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem amplificationBump_support {x : ℝ} (hx : amplificationBump x ≠ 0) : 1 < x ∧ x < 2 := by
  constructor
  · by_contra h
    exact hx (amplificationBump_zero (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hx (amplificationBump_zero (Or.inr (le_of_not_gt h)))

open Classical in
theorem amplificationSmoothWeight_support {B T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (a c : ℕ) (h : (a,c) ∉ amplificationCoefficientPairs B T) :
    amplificationSmoothWeight B T a c = 0 := by
  by_contra hn
  have hs := mul_ne_zero_iff.mp hn
  obtain ⟨hcl,hcu⟩ := amplificationBump_support hs.1
  obtain ⟨hal,hau⟩ := amplificationBump_support hs.2
  have hc : 0 < c := by
    by_contra hc
    have hz : c = 0 := by omega
    subst c
    norm_num at hcl
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 := mul_pos hT0 hc0
  apply h
  apply (mem_amplificationCoefficientPairs hB).mpr
  have hcl' : (B : ℝ) < Real.log c := by
    have hh := (lt_div_iff₀ hB0).mp hcl
    simpa only [one_mul] using hh
  have hcu' := (div_lt_iff₀ hB0).mp hcu
  have hal' := (lt_div_iff₀ hTC0).mp hal
  have hau' := (div_lt_iff₀ hTC0).mp hau
  refine ⟨?_,?_,?_,?_⟩
  · exact (Real.exp_le_exp.mpr hcl'.le).trans_eq (Real.exp_log hc0)
  · exact (Real.exp_log hc0).symm.trans_le (Real.exp_le_exp.mpr hcu'.le)
  · exact_mod_cast (by simpa only [one_mul] using hal'.le : (T : ℝ)*c ≤ a)
  · have hh : (a : ℝ) < (2*T*c : ℕ) := by push_cast; nlinarith only [hau']
    exact_mod_cast hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_RealPeriodicMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real moments of a fixed finite-period function -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem real_periodic_moment_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (f n)^k) / (N : ℝ))
      atTop (nhds ((∑ a : ZMod q, (f a)^k) / (q : ℝ))) := by
  have h := periodicAverage_tendsto (fun a => (((f a)^k : ℝ) : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, periodicAverage, residueMean,
    Complex.div_natCast_re, Complex.re_sum, Complex.ofReal_re] using hr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_QuotientSiteUnion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor and quotient together cover the full prime site -/

namespace JointDickman
open Finset

theorem coefficientPrimeSet_union_quotient {B n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n) :
    A ∪ coefficientPrimeSet B (n / (∏ p ∈ A, p)) = coefficientPrimeSet B n := by
  have he : (∏ p ∈ A, p) * (n / (∏ p ∈ A, p)) = n := Nat.mul_div_cancel' ha
  ext p
  constructor
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · exact (primeProduct_dvd_site_iff hA).mp ha hp
    · obtain ⟨hpP, hpq⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpP, by rw [← he]; exact dvd_mul_of_dvd_right hpq _⟩
  · intro hp
    obtain ⟨hpP, hpn⟩ := mem_filter.mp hp
    have hprime := auxiliaryPrimes_prime B p hpP
    rw [← he] at hpn
    rcases hprime.dvd_mul.mp hpn with hpa | hpq
    · have hm : p ∈ coefficientPrimeSet B (∏ p ∈ A, p) := mem_filter.mpr ⟨hpP, hpa⟩
      rw [coefficientPrimeSet_primeProduct hA] at hm
      exact mem_union_left _ hm
    · exact mem_union_right _ (mem_filter.mpr ⟨hpP, hpq⟩)

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueQuotientMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform residue means descend to every divisor of the period -/

namespace JointDickman
open Finset

/-- A whole number of periods has exactly the uniform residue mean. -/
theorem periodic_mean_at_multiple {d q : ℕ} [NeZero d] (hq : 0 < q)
    (hd : d ∣ q) (F : ZMod d → ℝ) :
    (∑ n ∈ range q, F n) / (q : ℝ) = (∑ a : ZMod d, F a) / (d : ℝ) := by
  obtain ⟨k, hk⟩ := hd
  have he : q = k*d := hk.trans (Nat.mul_comm _ _)
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hk0 : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := by intro h; simp [h] at he; omega
    exact_mod_cast this
  have hs := periodic_sum_blocks (fun a => (F a : ℂ)) k 0
  simp only [add_zero, sum_range_zero, add_zero] at hs
  have hs' : (∑ n ∈ range (k*d), F n) = (k : ℝ) * ∑ n ∈ range d, F n := by
    exact_mod_cast hs
  have hf := residue_sum_eq_range (fun a => (F a : ℂ))
  have hf' : (∑ a : ZMod d, F a) = ∑ n ∈ range d, F n := by exact_mod_cast hf
  rw [he, hs', hf', Nat.cast_mul]
  field_simp

/-- Taking a representative and reducing modulo a divisor preserves the
uniform law, with all fibers having equal size. -/
theorem residue_quotient_mean {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (F : ZMod d → ℝ) :
    (∑ a : ZMod q, F (a.val : ZMod d)) / (q : ℝ) =
      (∑ a : ZMod d, F a) / (d : ℝ) := by
  have hs := residue_sum_eq_range (fun a : ZMod q => (F (a.val : ZMod d) : ℂ))
  have hs' : (∑ a : ZMod q, F (a.val : ZMod d)) = ∑ n ∈ range q, F n := by
    have hn (n : ℕ) (hn : n ∈ range q) : (n : ZMod q).val = n :=
      ZMod.val_natCast_of_lt (mem_range.mp hn)
    have hr : (∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)) =
        ∑ n ∈ range q, F n := sum_congr rfl (fun n hn' => by rw [hn n hn'])
    exact (by exact_mod_cast hs : (∑ a : ZMod q, F (a.val : ZMod d)) =
      ∑ n ∈ range q, F ((n : ZMod q).val : ZMod d)).trans hr
  rw [hs']
  exact periodic_mean_at_multiple (NeZero.pos q) hd F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticSquareHits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact rare-square error for the arithmetic amplification -/

namespace JointDickman
open Finset

theorem auxiliarySquare_dvd_period {B p : ℕ} (hp : p ∈ auxiliaryPrimes B) :
    p^2 ∣ auxiliarySquarePeriod B := by
  unfold auxiliarySquarePeriod
  exact pow_dvd_pow_of_dvd (dvd_prod_of_mem id hp) 2

open Classical in
theorem residue_square_divisor_mean {B p : ℕ} (hp : p ∈ auxiliaryPrimes B) (k : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B),
      if p^2 ∣ a.val+k then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) =
        1 / (p : ℝ)^2 := by
  let : NeZero (p^2) := ⟨pow_ne_zero _ (auxiliaryPrimes_prime B p hp).ne_zero⟩
  have h := residue_quotient_mean (auxiliarySquare_dvd_period hp)
    (fun r : ZMod (p^2) => if r = -(k : ZMod (p^2)) then (1 : ℝ) else 0)
  have he (n : ℕ) :
      (if (n : ZMod (p^2)) = -(k : ZMod (p^2)) then (1 : ℝ) else 0) =
        if p^2 ∣ n+k then 1 else 0 := by
    congr 1
    rw [← ZMod.natCast_eq_zero_iff]
    simp only [Nat.cast_add, add_eq_zero_iff_eq_neg]
  simp only [he, sum_ite_eq', mem_univ, ite_true, if_true, Nat.cast_pow] at h
  exact h

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorGraphSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic support of the unequal-coefficient graph edges -/

namespace JointDickman
open Finset

theorem coprime_of_divisor_linear_succ {a c m : ℕ} (h : c ∣ a*m+1) :
    a.Coprime c ∧ m.Coprime c := by
  have ha : a.Coprime (a*m+1) :=
    (Nat.coprime_mul_left_add_right a 1 m).mpr (Nat.coprime_one_right a)
  have hm : m.Coprime (a*m+1) :=
    (Nat.coprime_mul_right_add_right m 1 a).mpr (Nat.coprime_one_right m)
  exact ⟨ha.coprime_dvd_right h, hm.coprime_dvd_right h⟩

/-- A prime-product coefficient is coprime to every nonzero small lag. -/
theorem auxiliaryProduct_coprime_small {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) {d : ℕ} (hd : 0 < d)
    (hdsmall : d ≤ auxiliaryCutoff B) : (∏ p ∈ A, p).Coprime d := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpd
  have hpos : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr
    (fun q hq => (auxiliaryPrimes_prime B q (hA hq)).ne_zero)
  have hpA := hp.mem_primeFactors hpa hpos
  rw [Nat.primeFactors_prod (fun q hq => auxiliaryPrimes_prime B q (hA hq))] at hpA
  have hpP := hA hpA
  have hpgt : auxiliaryCutoff B < p := by
    exact_mod_cast (mem_filter.mp hpP).2
  exact (not_lt_of_ge ((Nat.le_of_dvd hd hpd).trans hdsmall)) hpgt

/-- Once the coefficient is coprime to the lag and to c, the edge's two
coefficients are coprime. This is the cancellation used by the inverse map. -/
theorem divisor_edge_coprime {a b c : ℕ} {j : ℤ}
    (hac : a.Coprime c) (haj : a.Coprime j.natAbs)
    (he : (a : ℤ)-b = j*c) : a.Coprime b := by
  apply Nat.coprime_of_dvd'
  intro p hp hpa hpb
  have hpjc : (p : ℤ) ∣ j*c := by
    rw [← he]
    exact dvd_sub (by exact_mod_cast hpa) (by exact_mod_cast hpb)
  have hpjc' : p ∣ j.natAbs*c := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Int.natCast_dvd.mp hpjc
  have hpj : p ∣ j.natAbs := (hac.coprime_dvd_left hpa).dvd_mul_right.mp hpjc'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes haj hpa hpj)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorEdgeEndpoints
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual integer endpoints of a divisor-graph edge -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Forward reindexing at the actual natural quotients, for either sign
of the lag. The shifted endpoint is positive automatically. -/
theorem natural_divisor_edge_endpoints {a b c m : ℕ} {j : ℤ}
    (hc : 0 < c) (ha : c ∣ a*m+1) (hb : c ∣ b*m+1)
    (he : (a : ℤ)-b = j*c) :
    ((b*((a*m+1)/c) : ℕ) : ℤ)+j = ((a*((b*m+1)/c) : ℕ) : ℤ) := by
  have hqa : (c : ℤ)*((a*m+1)/c : ℕ) = (a : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' ha
  have hqb : (c : ℤ)*((b*m+1)/c : ℕ) = (b : ℤ)*m+1 := by
    exact_mod_cast Nat.mul_div_cancel' hb
  change (b : ℤ)*(((a*m+1)/c : ℕ) : ℤ)+j =
    (a : ℤ)*(((b*m+1)/c : ℕ) : ℤ)
  apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by exact_mod_cast (ne_of_gt hc))
  linear_combination (b : ℤ)*hqa - (a : ℤ)*hqb - he

/-- The inverse congruence reconstructs a nonnegative multiplier. It uses
only coprimality with the lag and positivity of the endpoint. -/
theorem natural_divisor_edge_inverse {a b c n : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (hn : 0 < n) (hb : b ∣ n)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (hdiv : (a : ℤ) ∣ (n : ℤ)+j) :
    ∃! m : ℕ, c*(n/b) = a*m+1 := by
  have hb0 : 0 < b := Nat.pos_of_dvd_of_pos hb hn
  have hnb : b*(n/b) = n := Nat.mul_div_cancel' hb
  have hcop' : IsCoprime (a : ℤ) j := by
    have h := hcop.isCoprime
    exact h.of_isCoprime_of_dvd_right Int.dvd_natAbs_self
  have hd' : (a : ℤ) ∣ (b : ℤ)*((n/b : ℕ) : ℤ)+j := by
    have hid : (b : ℤ)*((n/b : ℕ) : ℤ) = n := by exact_mod_cast hnb
    rwa [hid]
  obtain ⟨m,hm⟩ := (divisor_edge_iff he hcop').mpr hd'
  have hnq : 0 < n/b := Nat.div_pos (Nat.le_of_dvd hn hb) hb0
  have hmul : 0 ≤ (a : ℤ)*m := by
    have hcz : (1 : ℤ) ≤ (c : ℤ)*((n/b : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos hc hnq
    linarith
  have hm0 : 0 ≤ m := nonneg_of_mul_nonneg_right hmul (by exact_mod_cast ha)
  refine ⟨m.toNat,?_,?_⟩
  · have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
      simpa only [Int.toNat_of_nonneg hm0] using hm
    exact_mod_cast heq
  · intro m' hm'
    apply Nat.eq_of_mul_eq_mul_left ha
    have hmnat : c*(n/b) = a*m.toNat+1 := by
      have heq : (c : ℤ)*((n/b : ℕ) : ℤ) = (a : ℤ)*(m.toNat : ℤ)+1 := by
        simpa only [Int.toNat_of_nonneg hm0] using hm
      exact_mod_cast heq
    omega

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorEdgeReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite transport from multiplier sums to additive graph endpoints -/

namespace JointDickman
open Finset

theorem divisorEdgeInverse_eq {a b c n m : ℕ} (ha : 0 < a)
    (h : c*(n/b) = a*m+1) : divisorEdgeInverse a b c n = m := by
  unfold divisorEdgeInverse
  rw [h,Nat.add_sub_cancel,Nat.mul_div_cancel_left m ha]

/-- Membership in the multiplier sum gives an endpoint with exactly the
inverse multiplier; the finite endpoints include every original summand. -/
theorem divisorEdge_forward_mem {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) {m : ℕ} (hm : m ∈ divisorEdgeOld a b c N) :
    b*((a*m+1)/c) ∈ divisorEdgeNew a b c N j ∧
      divisorEdgeInverse a b c (b*((a*m+1)/c)) = m := by
  classical
  obtain ⟨_,ham,hbm,hca,hcb⟩ := mem_filter.mp hm
  let z := (a*m+1)/c
  have hcz : c*z = a*m+1 := Nat.mul_div_cancel' hca
  have hz : 0 < z := by nlinarith
  have hdiv : b ∣ b*z := dvd_mul_right b z
  have hnb : (b*z)/b = z := Nat.mul_div_cancel_left z hb
  have hinv : divisorEdgeInverse a b c (b*z) = m :=
    divisorEdgeInverse_eq ha (by rw [hnb]; exact hcz)
  refine ⟨?_,hinv⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨Nat.mul_pos hb hz,?_⟩,hdiv,?_,?_,?_⟩
  · have hzN : z ≤ N := (Nat.div_le_self _ _).trans (by omega)
    exact Nat.mul_le_mul_left b hzN
  · have hends := natural_divisor_edge_endpoints hc hca hcb he
    rw [hends]
    exact_mod_cast (dvd_mul_right a ((b*m+1)/c))
  · change a*divisorEdgeInverse a b c (b*z) < N
    rwa [hinv]
  · change b*divisorEdgeInverse a b c (b*z) < N
    rwa [hinv]

/-- Every allowed endpoint reconstructs one old multiplier. -/
theorem divisorEdge_inverse_mem {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    divisorEdgeInverse a b c n ∈ divisorEdgeOld a b c N ∧
      b*((a*divisorEdgeInverse a b c n+1)/c) = n := by
  classical
  obtain ⟨hnrange,hbn,hd,ham,hbm⟩ := mem_filter.mp hn
  have hn0 : 0 < n := (mem_Icc.mp hnrange).1
  obtain ⟨m,hm,_⟩ := natural_divisor_edge_inverse ha hc hn0 hbn he hcop hd
  have hinv : divisorEdgeInverse a b c n = m := divisorEdgeInverse_eq ha hm
  have hca : c ∣ a*m+1 := by rw [← hm]; exact dvd_mul_right c (n/b)
  have hcb : c ∣ b*m+1 := by
    have hdiff : (c : ℤ) ∣ (a : ℤ)-b := ⟨j,by simpa only [mul_comm] using he⟩
    have hx : (c : ℤ) ∣ (a : ℤ)*m+1 := by exact_mod_cast hca
    have hy := dvd_sub hx (dvd_mul_of_dvd_left hdiff (m : ℤ))
    have hz : (a : ℤ)*m+1-((a : ℤ)-b)*m = (b : ℤ)*m+1 := by ring
    rw [hz] at hy
    exact_mod_cast hy
  have hmN : m < N := by
    rw [hinv] at ham
    exact (Nat.le_mul_of_pos_left m ha).trans_lt ham
  rw [hinv]
  refine ⟨mem_filter.mpr ⟨mem_range.mpr hmN,?_,?_,?_,?_⟩,?_⟩
  · simpa only [hinv] using ham
  · simpa only [hinv] using hbm
  · simpa only [hinv] using hca
  · simpa only [hinv] using hcb
  · rw [← hm,Nat.mul_div_cancel_left _ hc]
    exact Nat.mul_div_cancel' hbn

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphPair
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic graph weight obtained from the actual quadratic form -/

namespace JointDickman
open Finset

theorem divisorEdge_new_quotients {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) :
    (a*divisorEdgeInverse a b c n+1)/c = n/b ∧
      (b*divisorEdgeInverse a b c n+1)/c = ((n : ℤ)+j).toNat/a := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  constructor
  · calc
      _ = (b*((a*divisorEdgeInverse a b c n+1)/c))/b :=
        (Nat.mul_div_cancel_left _ hb).symm
      _ = n/b := congrArg (fun t => t/b) hback
  · have hend : (n : ℤ)+j = ((a*((b*divisorEdgeInverse a b c n+1)/c) : ℕ) : ℤ) := by
      have h := natural_divisor_edge_endpoints hc hca hcb he
      rwa [hback] at h
    rw [hend,Int.toNat_natCast,Nat.mul_div_cancel_left _ ha]

theorem firstFormPairWeight_graph {B L : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {D A E : Finset ℕ} {N : ℕ} {j : ℤ}
    (ha : 0 < ∏ p ∈ A, p) (hb : 0 < ∏ p ∈ E, p) (hc : 0 < ∏ p ∈ D, p)
    (he : ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ))
    (hcop : (∏ p ∈ A, p).Coprime j.natAbs) {n : ℕ}
    (hn : n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N j) :
    firstFormPairWeight B L τ C u v D A E
        (divisorEdgeInverse (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) n) =
      arithmeticGraphPairWeight B L τ C u v
        (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) j n := by
  obtain ⟨hqa,hqb⟩ := divisorEdge_new_quotients ha hb hc he hcop hn
  unfold firstFormPairWeight arithmeticGraphPairWeight firstFormWeight
  rw [hqa,hqb]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positivity and support of the actual arithmetic graph kernel -/

namespace JointDickman
open Finset

theorem arithmeticGraphPairWeight_nonneg (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (hu : ∀ c, 0 ≤ u c)
    (hv : ∀ a c, 0 ≤ v a c) (a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ arithmeticGraphPairWeight B L τ C u v a b c j n := by
  have hA (d l : ℕ) : 0 ≤ regularCoefficientWeight B L τ C d *
      arithmeticResidueWeight B L τ C l * v d c :=
    mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C d)
      (regularResidueWeight_nonneg B L τ C _)) (hv d c)
  have hC : 0 ≤ u c * regularCoefficientWeight B L τ C c *
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n) :=
    mul_nonneg (mul_nonneg (hu c) (regularCoefficientWeight_nonneg B L τ C c))
      (regularResidueWeight_nonneg B L τ C _)
  exact mul_nonneg (mul_nonneg hC (hA a (n/b))) (hA b (((n : ℤ)+j).toNat/a))

theorem rawArithmeticGraphKernel_nonneg (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (j : ℤ) (n : ℕ) : 0 ≤ rawArithmeticGraphKernel B L τ C T N j n := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs
  · exact arithmeticGraphPairWeight_nonneg B L τ C (amplificationOuterWeight B)
      (amplificationInnerWeight T) (fun _ => (amplificationBump_bounds _).1)
      (fun _ _ => (amplificationBump_bounds _).1) _ _ _ _ _
  · rfl

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalCandidateRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational roots of candidate representations -/

namespace JointDickman

/-- A reduced coefficient with denominator greater than one can never
vanish after translation by an integer multiple of that denominator. -/
theorem translated_candidate_coefficient_ne_zero {b c : ℕ}
    (hbc : b.Coprime c) (hc : 1 < c) (t : ℤ) : (b : ℤ)+t*c ≠ 0 := by
  intro he
  have hg : Int.gcd ((b : ℤ)+t*c) (c : ℤ) = 1 := by
    rw [Int.gcd_add_mul_right_left]
    simpa only [Int.gcd,Int.natAbs_natCast] using hbc
  rw [he,Int.zero_gcd,Int.natAbs_natCast] at hg
  omega

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LargeDivisorReciprocals
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional large primes attached to nonzero coefficient differences -/

namespace JointDickman
open Finset

theorem prime_divisor_card_log {b : ℕ} (hb : b ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ b.primeFactors) :
    (S.card : ℝ)*Real.log 2 ≤ Real.log b := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
  have hd : (∏ p ∈ S, p) ∣ b :=
    (prod_dvd_prod_of_subset _ _ id hS).trans (Nat.prod_primeFactors_dvd b)
  have hle : (∏ p ∈ S, p : ℕ) ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hd
  have hp0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
  exact (selectedPrime_card_log_bound S hprime).trans
    (Real.log_le_log hp0 (by exact_mod_cast hle))

/-- Only logarithmic size, nonvanishing, and the prime cutoff are needed.
This applies both to forced third-site roots and to cross-root collisions. -/
theorem large_prime_divisor_reciprocals {b : ℤ} (hb : b ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ b.natAbs.primeFactors)
    {P H : ℝ} (hP : 0 < P) (hcut : ∀ p ∈ S, P ≤ (p : ℝ))
    (hsize : (b.natAbs : ℝ) ≤ Real.exp H) :
    ∑ p ∈ S, 1/(p : ℝ) ≤ H/(Real.log 2*P) := by
  have hb0 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  have hlog := prime_divisor_card_log hb0 S hS
  have hbpos : (0 : ℝ) < b.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hb0
  have hcard : (S.card : ℝ)*Real.log 2 ≤ H :=
    hlog.trans (by simpa only [Real.log_exp] using Real.log_le_log hbpos hsize)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ _p ∈ S, 1/P := sum_le_sum (fun p hp => one_div_le_one_div_of_le hP (hcut p hp))
    _ = (S.card : ℝ)/P := by simp [div_eq_mul_inv]
    _ ≤ (H/Real.log 2)/P := div_le_div_of_nonneg_right ((le_div_iff₀ hlog2).mpr hcard) hP.le
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateExceptionalPrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large-prime obstructions attached to actual candidate roots -/

namespace JointDickman
open Finset

theorem candidate_quotient_exp_bounds {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    Real.exp (B : ℝ) ≤ candidateQuotient e ∧
      (candidateQuotient e : ℝ) ≤ Real.exp (2*B) := by
  have hc : (0 : ℝ) < candidateQuotient e := by exact_mod_cast he.2.2.2.1
  have hlo := he.2.2.2.2.2.2.2.2.2.2.1
  have hhi := he.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨(Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hc),
    (Real.exp_log hc).symm.trans_le (Real.exp_le_exp.mpr hhi)⟩

/-- An affine coefficient of a candidate has logarithmic size O(B), with
an explicit exponent sufficient for every exceptional-prime estimate. -/
theorem affine_candidate_size {B T M b c : ℕ} {t : ℤ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hc : (c : ℝ) ≤ Real.exp (2*B)) (hb : b ≤ 2*T*c) (ht : t.natAbs ≤ M) :
    (((b : ℤ)+t*c).natAbs : ℝ) ≤ Real.exp (5*B) := by
  have habs : ((b : ℤ)+t*c).natAbs ≤ b+t.natAbs*c := by
    simpa only [Int.natAbs_natCast,Int.natAbs_mul] using Int.natAbs_add_le (b : ℤ) (t*c)
  have ht' : (t.natAbs : ℝ) ≤ M := by exact_mod_cast ht
  have hb' : (b : ℝ) ≤ 2*T*c := by exact_mod_cast hb
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hbig : (3 : ℝ) ≤ Real.exp (2*B) := by
    have h := Real.add_one_le_exp (2*(B : ℝ))
    linarith
  calc
    (((b : ℤ)+t*c).natAbs : ℝ) ≤ (b : ℝ)+(t.natAbs : ℝ)*c := by exact_mod_cast habs
    _ ≤ (2*(T : ℝ)+M)*c := by nlinarith
    _ ≤ (3*Real.exp B)*Real.exp (2*B) :=
      mul_le_mul (by linarith) hc (Nat.cast_nonneg c) (by positivity)
    _ = 3*Real.exp (3*B) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp (2*B)*Real.exp (3*B) := mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem candidateSiteValue_size {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    ((candidateSiteValue e s).natAbs : ℝ) ≤ Real.exp (5*B) := by
  have ht : ((s.val : ℤ)-e.1.1.val).natAbs ≤ M := by
    have hh : |(s.val : ℤ)-e.1.1.val| ≤ (M : ℤ) := by
      apply abs_le.mpr
      have hs := s.isLt
      have hi := e.1.1.isLt
      constructor <;> omega
    rw [← Int.natCast_natAbs] at hh
    exact_mod_cast hh
  exact affine_candidate_size hB hT hM (candidate_quotient_exp_bounds he).2
    he.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ht

theorem candidateSiteValue_ne_zero {B L T H M : ℕ} {τ C : ℝ} (hB : 2 ≤ B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    candidateSiteValue e s ≠ 0 := by
  have hc : 1 < candidateQuotient e := by
    have h := (candidate_quotient_exp_bounds he).1
    have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
    have hx := Real.add_one_le_exp (B : ℝ)
    have : (1 : ℝ) < candidateQuotient e := by linarith
    exact_mod_cast this
  exact translated_candidate_coefficient_ne_zero he.2.2.2.2.2.2.1 hc _

/-- Forced hits at another endpoint involve only primes dividing this
nonzero affine coefficient. -/
theorem candidateSiteValue_prime_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M)
    (P : ℝ) (hP : 0 < P) (Q : Finset ℕ)
    (hQ : Q ⊆ (candidateSiteValue e s).natAbs.primeFactors)
    (hcut : ∀ p ∈ Q, P ≤ (p : ℝ)) :
    (∑ p ∈ Q, 1/(p : ℝ)) ≤ (5*(B : ℝ))/(Real.log 2*P) :=
  large_prime_divisor_reciprocals (candidateSiteValue_ne_zero hB he s) Q hQ hP hcut
    (candidateSiteValue_size hB hT hM he s)


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RequiredPrimeSubset
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability that an independent site contains prescribed primes -/

namespace JointDickman
open Finset

open Classical in
theorem bernoulliSubsetMass_required {α : Type*} [DecidableEq α]
    (P A : Finset α) (q : α → ℝ) (hA : A ⊆ P) :
    (∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S else 0) =
      ∏ p ∈ A, q p := by
  have hm {S : Finset α} (hS : S ⊆ P) (hAS : A ⊆ S) :
      bernoulliSubsetMass P q S =
        (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q (S \ A) := by
    have he : (P \ A) \ (S \ A) = P \ S := by
      ext p
      simp only [mem_sdiff]
      constructor
      · rintro ⟨⟨hp, ha⟩, hs⟩
        exact ⟨hp, fun h => hs ⟨h,ha⟩⟩
      · rintro ⟨hp, hs⟩
        exact ⟨⟨hp, fun h => hs (hAS h)⟩, fun h => hs h.1⟩
    unfold bernoulliSubsetMass
    rw [he, ← prod_sdiff hAS]
    ring
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S), bernoulliSubsetMass P q S := by
      rw [sum_filter]
    _ = ∑ T ∈ (P \ A).powerset, (∏ p ∈ A, q p)*bernoulliSubsetMass (P \ A) q T := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        apply mem_powerset.mpr
        intro p hp
        exact mem_sdiff.mpr ⟨(mem_powerset.mp (mem_filter.mp hS).1)
          (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
      · intro S hS T hT he
        have hAS := (mem_filter.mp hS).2
        have hAT := (mem_filter.mp hT).2
        have hs := sdiff_union_of_subset hAS
        have ht := sdiff_union_of_subset hAT
        rw [he] at hs
        exact hs.symm.trans ht
      · intro T hT
        have ht := mem_powerset.mp hT
        refine ⟨A ∪ T, mem_filter.mpr ⟨mem_powerset.mpr (union_subset hA (ht.trans sdiff_subset)),
          subset_union_left⟩, ?_⟩
        ext p
        have hp : p ∈ T → p ∉ A := fun h => (mem_sdiff.mp (ht h)).2
        simp only [mem_sdiff, mem_union]
        tauto
      · intro S hS
        exact hm (mem_powerset.mp (mem_filter.mp hS).1) (mem_filter.mp hS).2
    _ = _ := by rw [← mul_sum,bernoulliSubsetMass_sum,mul_one]

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingConcentration
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concentration after restriction to a common good event

The extension used in the manuscript's sampling argument is constructed
explicitly from a finite good set. The only concentration hypothesis below
is the uniform-constant finite-product specialization of McDiarmid's
published bounded-differences inequality.
-/

open Finset
open scoped BigOperators

namespace JointDickman

section FiniteProbability

variable {Ω : Type*} [Fintype Ω]

theorem finiteProbability_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {E F : Ω → Prop} (hEF : ∀ x, E x → F x) :
    finiteProbability w E ≤ finiteProbability w F := by
  classical
  apply sum_le_sum
  intro x _
  by_cases hE : E x
  · simp [hE, hEF x hE]
  · by_cases hF : F x <;> simp [hE, hF, hw x]

theorem finiteProbability_union_le {J : Type*} [Fintype J]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (E : J → Ω → Prop) :
    finiteProbability w (fun x => ∃ j, E j x) ≤ ∑ j, finiteProbability w (E j) := by
  classical
  unfold finiteProbability
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ j, E j x
  · obtain ⟨j, hj⟩ := h
    simp only [show (∃ j, E j x) from ⟨j, hj⟩, ite_true, if_true]
    have ht : (if E j x then w x else 0) ≤ ∑ k, if E k x then w x else 0 :=
      single_le_sum (f := fun k => if E k x then w x else 0)
        (fun k _ => by by_cases hk : E k x <;> simp [hk, hw x]) (mem_univ j)
    simpa [hj] using ht
  · simp only [h, ite_false, if_false]
    exact sum_nonneg (fun j _ => by by_cases hj : E j x <;> simp [hj, hw x])

end FiniteProbability

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SamplingMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem finiteExpectation_const_mul (w f : Ω → ℝ) (c : ℝ) :
    finiteExpectation w (fun x => c * f x) = c * finiteExpectation w f := by
  simp only [finiteExpectation, mul_sum]
  apply sum_congr rfl
  intro x _
  ring

theorem finiteExpectation_const (w : Ω → ℝ) (hw : (∑ x, w x) = 1) (c : ℝ) :
    finiteExpectation w (fun _ => c) = c := by
  rw [finiteExpectation, ← sum_mul, hw, one_mul]

theorem finiteExpectation_mono (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    {f g : Ω → ℝ} (hfg : ∀ x, f x ≤ g x) : finiteExpectation w f ≤ finiteExpectation w g := by
  exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hw x)

end Expectation

section IndependentSites

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

omit [DecidableEq ι] [Fintype A] in
theorem siteProductMass_nonneg (p : ι → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → A) :
    0 ≤ siteProductMass p x := prod_nonneg fun i _ => hp i (x i)

/-- The finite sum-product identity supplies independence, with no probabilistic input. -/
theorem siteProduct_expectation_prod (p f : ι → A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation, siteProductMass, ← prod_mul_distrib]
  simpa using (prod_univ_sum (fun _ : ι => (univ : Finset A))
    (fun i a => p i a * f i a)).symm

theorem siteProductMass_sum (p : ι → A → ℝ) (hpone : ∀ i, ∑ a, p i a = 1) :
    (∑ x, siteProductMass p x) = 1 := by
  have h := siteProduct_expectation_prod p (fun _ _ => 1)
  simpa [finiteExpectation, hpone] using h

theorem siteProduct_expectation_coordinate (p : ι → A → ℝ)
    (hpone : ∀ i, ∑ a, p i a = 1) (i : ι) (f : A → ℝ) :
    finiteExpectation (siteProductMass p) (fun x => f (x i)) = finiteExpectation (p i) f := by
  classical
  let g : ι → A → ℝ := fun j a => if j = i then f a else 1
  have hl (x : ι → A) : (∏ j, g j (x j)) = f (x i) := by simp [g]
  have hr : (∏ j, finiteExpectation (p j) (g j)) = finiteExpectation (p i) f := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji
      simp [g, hji, finiteExpectation, hpone]
    · simp
  simpa only [hl, hr] using siteProduct_expectation_prod p g

end IndependentSites

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentForcedHits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forced hits at an independently sampled third endpoint -/

namespace JointDickman
open Finset

open Classical in
theorem independent_subset_intersects_bound {α : Type*} [DecidableEq α]
    (P Q : Finset α) (q : α → ℝ) (hQ : Q ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if ∃ p ∈ Q, p ∈ S then bernoulliSubsetMass P q S else 0) ≤
      ∑ p ∈ Q, q p := by
  have hpoint (S : Finset α) (hS : S ∈ P.powerset) :
      (if ∃ p ∈ Q, p ∈ S then bernoulliSubsetMass P q S else 0) ≤
        ∑ p ∈ Q, if p ∈ S then bernoulliSubsetMass P q S else 0 := by
    have hm := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    by_cases hh : ∃ p ∈ Q, p ∈ S
    · obtain ⟨p,hpQ,hpS⟩ := hh
      rw [ite_eq_left ⟨p,hpQ,hpS⟩]
      calc
        _ = (if p ∈ S then bernoulliSubsetMass P q S else 0) := by rw [ite_eq_left hpS]
        _ ≤ _ := single_le_sum (f := fun r => if r ∈ S then bernoulliSubsetMass P q S else 0)
          (fun r _ => by split_ifs <;> first | exact hm | exact le_rfl) hpQ
    · rw [ite_eq_right hh]
      exact sum_nonneg (fun p _ => by split_ifs; exact hm; rfl)
  calc
    _ ≤ ∑ S ∈ P.powerset, ∑ p ∈ Q, if p ∈ S then bernoulliSubsetMass P q S else 0 :=
      sum_le_sum hpoint
    _ = ∑ p ∈ Q, ∑ S ∈ P.powerset, if p ∈ S then bernoulliSubsetMass P q S else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      simpa only [singleton_subset_iff,prod_singleton] using
        bernoulliSubsetMass_required P {p} q (singleton_subset_iff.mpr (hQ hp))

/-- Once a candidate's endpoints have been exposed, an independent third
site meets one of its forced primes with probability O(B/P0). -/
theorem candidate_forced_hit_bound {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) (s : Fin M) :
    finiteExpectation (independentPrimeSetMass B) (fun R =>
      if ∃ p ∈ candidateForcedPrimes B e s, p ∈ R.val then 1 else 0) ≤
        (5*(B : ℝ))/(Real.log 2*auxiliaryCutoff B) := by
  classical
  have hsub : candidateForcedPrimes B e s ⊆ auxiliaryPrimes B := filter_subset _ _
  have hq (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      0 ≤ 1/(p : ℝ) ∧ 1/(p : ℝ) ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
    exact ⟨by positivity,(div_le_one (by linarith)).mpr hp1⟩
  have hhit := independent_subset_intersects_bound (auxiliaryPrimes B)
    (candidateForcedPrimes B e s) (fun p => 1/(p : ℝ)) hsub hq
  have heq : finiteExpectation (independentPrimeSetMass B) (fun R =>
      if ∃ p ∈ candidateForcedPrimes B e s, p ∈ R.val then 1 else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset,
        if ∃ p ∈ candidateForcedPrimes B e s, p ∈ S then
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0 := by
    unfold finiteExpectation independentPrimeSetMass
    simp_rw [mul_ite,mul_one,mul_zero]
    exact sum_coe_sort (auxiliaryPrimes B).powerset
      (fun S : Finset ℕ => if ∃ p ∈ candidateForcedPrimes B e s, p ∈ S then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S else 0)
  rw [heq]
  apply hhit.trans
  apply candidateSiteValue_prime_mass hB hT hM he s (auxiliaryCutoff B)
    (by exact_mod_cast hP) (candidateForcedPrimes B e s)
  · intro p hp
    have hh := mem_filter.mp hp
    exact (auxiliaryPrimes_prime B p hh.1).mem_primeFactors hh.2
      (Int.natAbs_ne_zero.mpr (candidateSiteValue_ne_zero hB he s))
  · intro p hp
    exact (mem_filter.mp (hsub hp)).2.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateThirdSiteProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditional probability of a repeated candidate root -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem finiteProbability_eq_indicator_mean {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (E : Ω → Prop) :
    finiteProbability w E = finiteExpectation w (fun x => if E x then 1 else 0) := by
  simp only [finiteProbability,finiteExpectation,mul_ite,mul_one,mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SitePartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact disintegration of independent site laws over a chosen set -/

namespace JointDickman
open Finset PublishedInputs

section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

omit [Fintype ι] [Fintype Ω] in
theorem mergeSitePartition_restrict (I : Finset ι) (S : ι → Ω) :
    mergeSitePartition I (fun i => S i.val) (fun i => S i.val) = S := by
  funext i
  unfold mergeSitePartition
  split_ifs <;> rfl

omit [Fintype Ω] in
theorem siteProductMass_merge (p : ι → Ω → ℝ) (I : Finset ι)
    (a : I → Ω) (b : {i : ι // i ∉ I} → Ω) :
    siteProductMass p (mergeSitePartition I a b) =
      siteProductMass (fun i : I => p i.val) a*
        siteProductMass (fun i : {i : ι // i ∉ I} => p i.val) b := by
  unfold siteProductMass
  have hh := Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ I)
    (fun i => p i (mergeSitePartition I a b i))
  apply hh.symm.trans
  apply congrArg₂ (fun a b : ℝ => a*b)
  · apply Finset.prod_congr (by ext; simp)
    intro i _
    simp only [mergeSitePartition,dite_eq_left i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [mergeSitePartition,dite_eq_right i.property]

/-- The exposed endpoint block is integrated outside the independent law
of all remaining sites. No probability of the exposed event is divided out. -/
theorem siteProduct_partition (p : ι → Ω → ℝ) (I : Finset ι) (F : (ι → Ω) → ℝ) :
    finiteExpectation (siteProductMass p) F =
      finiteExpectation (siteProductMass (fun i : I => p i.val)) (fun a =>
        finiteExpectation (siteProductMass (fun i : {i : ι // i ∉ I} => p i.val))
          (fun b => F (mergeSitePartition I a b))) := by
  classical
  unfold finiteExpectation
  calc
    _ = ∑ ab : (I → Ω) × ({i : ι // i ∉ I} → Ω),
        siteProductMass p (mergeSitePartition I ab.1 ab.2)*F (mergeSitePartition I ab.1 ab.2) := by
      refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun _ => Ω)) _ _ ?_
      intro S
      change siteProductMass p S*F S =
        siteProductMass p (mergeSitePartition I (fun i => S i.val) (fun i => S i.val))*
          F (mergeSitePartition I (fun i => S i.val) (fun i => S i.val))
      rw [mergeSitePartition_restrict]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [siteProductMass_merge,mul_sum,mul_assoc]

end
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteEventUnion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A union over a finite list of events -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem finiteProbability_exists_mem {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (I : Finset ι) (E : ι → Ω → Prop) :
    finiteProbability w (fun x => ∃ i ∈ I, E i x) ≤ ∑ i ∈ I, finiteProbability w (E i) := by
  have he : (fun x => ∃ i ∈ I, E i x) = (fun x => ∃ i : I, E i.val x) := by
    funext x
    apply propext
    constructor
    · rintro ⟨i,hi,hE⟩
      exact ⟨⟨i,hi⟩,hE⟩
    · rintro ⟨i,hE⟩
      exact ⟨i.val,i.property,hE⟩
  rw [he]
  exact (finiteProbability_union_le w hw (fun i : I => E i.val)).trans_eq
    (sum_coe_sort I (fun i => finiteProbability w (E i)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SitePartitionProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a bound conditional on exposed sites -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem siteProduct_probability_of_conditional_bound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (p : ι → Ω → ℝ) (hp : ∀ i x, 0 ≤ p i x)
    (hpone : ∀ i, ∑ x, p i x = 1) (I : Finset ι)
    (E : (ι → Ω) → Prop) {K : ℝ}
    (hK : ∀ a : I → Ω,
      finiteProbability (siteProductMass (fun i : {i : ι // i ∉ I} => p i.val))
        (fun b => E (mergeSitePartition I a b)) ≤ K) :
    finiteProbability (siteProductMass p) E ≤ K := by
  rw [finiteProbability_eq_indicator_mean, siteProduct_partition p I]
  calc
    _ ≤ finiteExpectation (siteProductMass (fun i : I => p i.val)) (fun _ => K) := by
      apply finiteExpectation_mono _
        (siteProductMass_nonneg (fun i : I => p i.val) (fun i => hp i.val))
      intro a
      simpa only [← finiteProbability_eq_indicator_mean] using hK a
    _ = K := finiteExpectation_const _
      (siteProductMass_sum (fun i : I => p i.val) (fun i => hpone i.val)) K

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionedRootComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent-root error at an unoccupied prime -/

namespace JointDickman
open Finset

theorem unoccupied_reciprocal_estimates (p M : ℕ) (hp : M < p) (hhalf : 2*M ≤ p) :
    1/((p-M : ℕ) : ℝ) ≤ 2/(p : ℝ) ∧
      |1/((p-M : ℕ) : ℝ)-1/(p : ℝ)| ≤ 2*(M : ℝ)/(p : ℝ)^2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le M).trans_lt hp
  have hd0 : (0 : ℝ) < (p-M : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hp
  have hd : ((p-M : ℕ) : ℝ) = (p : ℝ)-M := Nat.cast_sub hp.le
  have hmreal : 2*(M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hhalf
  have hden : (p : ℝ)/2 ≤ ((p-M : ℕ) : ℝ) := by rw [hd]; linarith only [hmreal]
  have hq : 1/((p-M : ℕ) : ℝ) ≤ 2/(p : ℝ) := by
    calc
      _ ≤ 1/((p : ℝ)/2) := one_div_le_one_div_of_le (by positivity) hden
      _ = _ := by ring
  refine ⟨hq,?_⟩
  have hdiff : 0 ≤ 1/((p-M : ℕ) : ℝ)-1/(p : ℝ) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le hd0
    rw [hd]
    exact sub_le_self _ (Nat.cast_nonneg M)
  have he : 1/((p-M : ℕ) : ℝ)-1/(p : ℝ) =
      (1/((p-M : ℕ) : ℝ))*((M : ℝ)/p) := by
    field_simp
    rw [hd]
    ring
  rw [abs_of_nonneg hdiff,he]
  calc
    _ ≤ (2/(p : ℝ))*((M : ℝ)/p) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FinitePointMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing a finite hit law with the empty outcome -/

namespace JointDickman
open Finset PublishedInputs

theorem finitePushMass_sum {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) : (∑ a, finitePushMass w f a) = ∑ x, w x := by
  classical
  unfold finitePushMass
  rw [sum_comm]
  simp

theorem finitePushMass_test_real {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) (F : A → ℝ) :
    (∑ a, finitePushMass w f a*F a) = ∑ x, w x*F (f x) := by
  classical
  unfold finitePushMass
  simp_rw [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteHitMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite subset laws controlled by their hit probabilities -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem finitePushMass_probability {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (f : Ω → A) (E : A → Prop) :
    finiteProbability (finitePushMass w f) E = finiteProbability w (fun x => E (f x)) := by
  simp only [finiteProbability_eq_indicator_mean,finiteExpectation]
  exact finitePushMass_test_real w f (fun a => if E a then 1 else 0)

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RestrictedRootMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual root-hit law on a restricted residue set -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem restrictedRootMass_hit_le {α : Type*} [DecidableEq α]
    (I : Finset α) {p : ℕ} (root : α → ZMod p) (U : Finset (ZMod p))
    {i : α} (hi : i ∈ I) :
    finiteProbability (restrictedRootMass I root U) (fun S => i ∈ S.val) ≤ 1/(U.card : ℝ) := by
  unfold restrictedRootMass
  rw [finitePushMass_probability]
  unfold finiteProbability
  have he (r : U) : i ∈ (rootHitType I root r.val).val ↔ root i = r.val := by
    simp only [rootHitType,rootHitSet,mem_filter,hi,true_and]
  simp only [he]
  have hh : (∑ r : U, if root i = r.val then 1/(U.card : ℝ) else 0) =
      ∑ r ∈ U, if root i = r then 1/(U.card : ℝ) else 0 :=
    sum_coe_sort U (fun r => if root i = r then 1/(U.card : ℝ) else 0)
  rw [hh]
  by_cases hr : root i ∈ U
  · simp [eq_comm,hr]
  · simp [eq_comm,hr]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateModularRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Modular collisions force the explicit integer obstructions -/

namespace JointDickman

theorem candidateModRoot_site_collision {M p : ℕ} [Fact p.Prime]
    (e : BlockCandidateIndex M) (s : Fin M) (he : ¬ p ∣ candidateQuotient e)
    (hroot : candidateModRoot p e = blockSiteRoot M p s) :
    p ∣ (candidateSiteValue e s).natAbs := by
  have he0 : (candidateQuotient e : ZMod p) ≠ 0 :=
    fun h => he ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hh := (div_eq_iff he0).mp hroot
  have hv : candidateSiteValue e s =
      candidateRootNumerator e + (s.val+1)*candidateQuotient e := by
    unfold candidateSiteValue candidateRootNumerator
    ring
  apply Int.natCast_dvd.mp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [hv,Int.cast_add,Int.cast_mul]
  rw [hh]
  simp only [blockSiteRoot,Int.cast_add,Int.cast_one,Int.cast_natCast,
    Nat.cast_add,Nat.cast_one,neg_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteWeightedUnion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonnegative weights on finite unions -/

namespace JointDickman
open Finset

theorem sum_union_le_nonneg {α : Type*} [DecidableEq α] (S T : Finset α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x)+(∑ x ∈ T, f x) := by
  have h := sum_union_inter (s₁ := S) (s₂ := T) (f := f)
  have hi : 0 ≤ ∑ x ∈ S ∩ T, f x := sum_nonneg (fun x _ => hf x)
  linarith only [h,hi]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateDefectPrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite set of primes defective for candidate root comparison -/

namespace JointDickman
open Finset

theorem auxiliaryDivisors_mass {B : ℕ} {z : ℤ} (hz : z ≠ 0) {K : ℝ}
    (hsize : (z.natAbs : ℝ) ≤ Real.exp K) (hP : 0 < auxiliaryCutoff B) :
    (∑ p ∈ auxiliaryDivisors B z, 1/(p : ℝ)) ≤ K/(Real.log 2*auxiliaryCutoff B) := by
  apply large_prime_divisor_reciprocals hz _ _ (by exact_mod_cast hP) _ hsize
  · intro p hp
    obtain ⟨hp,hdiv⟩ := mem_filter.mp hp
    exact (auxiliaryPrimes_prime B p hp).mem_primeFactors hdiv (Int.natAbs_ne_zero.mpr hz)
  · intro p hp
    exact (mem_filter.mp (mem_filter.mp hp).1).2.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OutsideCandidateMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional candidate-root distribution at an unoccupied prime -/

namespace JointDickman
open Finset

theorem blockForbidden_card {M p : ℕ} (hp : M < p) :
    (univ.image (blockSiteRoot M p)).card = M := by
  classical
  rw [card_image_of_injective _ (blockSiteRoot_injective M p hp),card_univ,Fintype.card_fin]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticCandidateRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic quotient and its candidate root -/

namespace JointDickman
open Finset

/-- Outside coefficient primes the remaining arithmetic argument has the
ordinary linear root used by the candidate model. -/
theorem affine_quotient_prime_root {a b c m n p : ℕ} [Fact p.Prime]
    (he : a*b*m+b = c*n) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hc : ¬ p ∣ c) :
    p ∣ m ↔ (n : ZMod p) = (b : ZMod p)/(c : ZMod p) := by
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hc0 : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hz : (a : ZMod p)*b*m+b = (c : ZMod p)*n := by
    simpa only [Nat.cast_add,Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) he
  rw [← ZMod.natCast_eq_zero_iff, eq_div_iff hc0]
  constructor
  · intro hm
    simpa only [hm,mul_zero,zero_add,mul_comm] using hz.symm
  · intro hn
    have hm : (a : ZMod p)*b*m = 0 := by linear_combination hz + hn
    exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero ha0 hb0)

/-- A prime of the third coefficient cannot divide the remaining argument. -/
theorem affine_quotient_no_third_coefficient {a b c m n p : ℕ} [Fact p.Prime]
    (he : a*b*m+b = c*n) (hb : ¬ p ∣ b) (hc : p ∣ c) : ¬ p ∣ m := by
  intro hm
  have hleft : p ∣ a*b*m+b := by
    rw [he]
    exact dvd_mul_of_dvd_left hc n
  have habm : p ∣ a*b*m := dvd_mul_of_dvd_right hm (a*b)
  exact hb ((Nat.dvd_add_iff_right habm).mpr hleft)

/-- For a coefficient with exactly one factor of `p`, testing the quotient
for `p` is a test of the original numerator modulo `p²`. -/
theorem prime_square_product_iff {p d m : ℕ} (hp : p.Prime)
    (hd : p ∣ d) (hdd : ¬ p^2 ∣ d) : p^2 ∣ d*m ↔ p ∣ m := by
  obtain ⟨k,rfl⟩ := hd
  have hk : ¬ p ∣ k := by
    intro h
    apply hdd
    simpa only [pow_two] using Nat.mul_dvd_mul_left p h
  rw [pow_two,mul_assoc,Nat.mul_dvd_mul_iff_left hp.pos]
  exact ⟨fun h => (hp.dvd_mul.mp h).resolve_left hk, fun h => dvd_mul_of_dvd_right h k⟩

/-- With the manuscript's site indexing, the linear root is precisely
`candidateModRoot`, not a new independently specified residue. -/
theorem candidate_affine_quotient_root {M p u m : ℕ} [Fact p.Prime]
    (e : BlockCandidateIndex M)
    (he : candidateHigh e*candidateLow e*m+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e) :
    p ∣ m ↔ (u : ZMod p) = candidateModRoot p e := by
  rw [affine_quotient_prime_root he ha hb hc]
  have hc0 : (candidateQuotient e : ZMod p) ≠ 0 :=
    fun h => hc ((ZMod.natCast_eq_zero_iff _ _).mp h)
  unfold candidateModRoot candidateRootNumerator
  simp only [Nat.cast_add,Nat.cast_one,Int.cast_sub,Int.cast_natCast,Int.cast_mul,
    Int.cast_add,Int.cast_one]
  rw [eq_div_iff hc0,eq_div_iff hc0]
  constructor <;> intro h <;> linear_combination h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HigherPrimeDigits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The next digit at a coefficient prime remains uniform -/

namespace JointDickman
open Finset Classical

/-- Cancellation of one known prime factor leaves the next-digit test. -/
theorem prime_square_affine_digit {p : ℕ} (hp : p ≠ 0) {z c t : ℤ}
    (hz : (p : ℤ) ∣ z) :
    (p : ℤ)^2 ∣ z+(p : ℤ)*c*t ↔ (p : ℤ) ∣ z/p+c*t := by
  obtain ⟨k,rfl⟩ := hz
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  rw [Int.mul_ediv_cancel_left _ hp0, pow_two]
  have he : (p : ℤ)*k+(p : ℤ)*c*t = (p : ℤ)*(k+c*t) := by ring
  rw [he,Int.mul_dvd_mul_iff_left hp0]

/-- The actual second-digit divisibility condition is one residue class;
no conditioning on absence of squares is used. -/
theorem prime_square_digit_root {p : ℕ} [Fact p.Prime] {z c : ℤ}
    (hz : (p : ℤ) ∣ z) (hc : ¬ (p : ℤ) ∣ c) (t : ZMod p) :
    ((p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)) ↔ t = higherDigitRoot p z c := by
  rw [prime_square_affine_digit (Fact.out : p.Prime).ne_zero hz]
  have hc0 : (c : ZMod p) ≠ 0 :=
    fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, higherDigitRoot, eq_div_iff hc0]
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val]
  constructor <;> intro h <;> linear_combination h

/-- Given any first digit compatible with the coefficient, the probability
of the quotient prime test over its unconditioned next digit is exactly 1/p. -/
theorem prime_square_digit_probability {p : ℕ} [Fact p.Prime] {z c : ℤ}
    (hz : (p : ℤ) ∣ z) (hc : ¬ (p : ℤ) ∣ c) :
    (∑ t : ZMod p, if (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)
      then (1 : ℝ) else 0)/(p : ℝ) = 1/(p : ℝ) := by
  simp_rw [prime_square_digit_root hz hc]
  simp

/-- An incompatible first digit gives probability zero; the uniform bound
therefore holds without a first-digit compatibility hypothesis. -/
theorem prime_square_digit_probability_le {p : ℕ} [Fact p.Prime] (z c : ℤ)
    (hc : ¬ (p : ℤ) ∣ c) :
    (∑ t : ZMod p, if (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ)
      then (1 : ℝ) else 0)/(p : ℝ) ≤ 1/(p : ℝ) := by
  by_cases hz : (p : ℤ) ∣ z
  · exact (prime_square_digit_probability hz hc).le
  · have hn (t : ZMod p) : ¬ (p : ℤ)^2 ∣ z+(p : ℤ)*c*(t.val : ℤ) := by
      intro h
      have hpz : (p : ℤ) ∣ z+(p : ℤ)*c*(t.val : ℤ) :=
        (dvd_pow_self _ (by omega : 2 ≠ 0)).trans h
      have hpt : (p : ℤ) ∣ (p : ℤ)*c*(t.val : ℤ) := by
        exact ⟨c*(t.val : ℤ),by ring⟩
      exact hz (by simpa using dvd_sub hpz hpt)
    simp only [hn,ite_false, if_false,sum_const_zero,zero_div]
    positivity

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem prime_square_affine_digits {p : ℕ} [NeZero p] (u : ℕ) (c b i : ℤ) :
    (p : ℤ)^2 ∣ c*((u : ℤ)+i)-b ↔
    (p : ℤ)^2 ∣ c*((primeDigits p (u : ZMod (p^2))).1.val+
      (p : ℤ)*(primeDigits p (u : ZMod (p^2))).2.val+i)-b := by
  have he := join_primeDigits (u : ZMod (p^2))
  change (((primeDigits p (u : ZMod (p^2))).1.val+
    p*(primeDigits p (u : ZMod (p^2))).2.val : ℕ) : ZMod (p^2)) = (u : ZMod (p^2)) at he
  have hv : ((c*((u : ℤ)+i)-b : ℤ) : ZMod (p^2)) =
      ((c*((primeDigits p (u : ZMod (p^2))).1.val+
        (p : ℤ)*(primeDigits p (u : ZMod (p^2))).2.val+i)-b : ℤ) : ZMod (p^2)) := by
    simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,Int.cast_natCast]
    have he' := he
    push_cast at he'
    conv_lhs => rw [← he']
  have hi (z : ℤ) : (z : ZMod (p^2)) = 0 ↔ (p : ℤ)^2 ∣ z := by
    have heq : ((p^2 : ℕ) : ℤ) = (p : ℤ)^2 := by simp
    rw [← heq]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd z (p^2)
  rw [← hi,← hi,hv]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DependentProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate means for the prime-dependent higher-digit spaces -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem finiteProduct_expectation_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p f : ∀ i, Ω i → ℝ) :
    finiteExpectation (finiteProductMass p) (fun x => ∏ i, f i (x i)) =
      ∏ i, finiteExpectation (p i) (f i) := by
  simp only [finiteExpectation,finiteProductMass,← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => p i x*f i x)).symm

theorem finiteProduct_expectation_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (p : ∀ i, Ω i → ℝ) (hp : ∀ i, ∑ x, p i x = 1)
    (i : ι) (f : Ω i → ℝ) :
    finiteExpectation (finiteProductMass p) (fun x => f (x i)) =
      finiteExpectation (p i) f := by
  let g : ∀ j, Ω j → ℝ := fun j x => if h : j = i then f (h ▸ x) else 1
  have hl (x : ∀ j, Ω j) : (∏ j, g j (x j)) = f (x i) := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji; simp [g,hji]
    · simp
  have hr : (∏ j, finiteExpectation (p j) (g j)) = finiteExpectation (p i) f := by
    rw [prod_eq_single i]
    · simp [g]
    · intro j _ hji; simp [g,hji,finiteExpectation,hp]
    · simp
  simpa only [hl,hr] using finiteProduct_expectation_prod p g

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedEvent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Occupied third-site primes that force an auxiliary root hit -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem forcedWitness_merge_iff {B M : ℕ} (e : BlockCandidateIndex M)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset)
    (b : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} → (auxiliaryPrimes B).powerset) :
    CandidateForcedWitness B e (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val) ↔
      ∃ s : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))},
        ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val := by
  constructor
  · rintro ⟨s,hi,hk,p,hp,hS⟩
    have hs : s ∉ ({e.1.1,e.1.2} : Finset (Fin M)) := by
      simp only [mem_insert,mem_singleton]; tauto
    refine ⟨⟨s,hs⟩,p,hp,?_⟩
    simpa only [mergeSitePartition,dite_eq_right hs] using hS
  · rintro ⟨s,p,hp,hS⟩
    have hs : s.val ≠ e.1.1 ∧ s.val ≠ e.1.2 := by
      simpa only [mem_insert,mem_singleton,not_or] using s.property
    refine ⟨s.val,hs.1,hs.2,p,hp,?_⟩
    simpa only [mergeSitePartition,dite_eq_right s.property] using hS

open Classical in
theorem forcedWitness_remaining_probability {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e)
    (a : ({e.1.1,e.1.2} : Finset (Fin M)) → (auxiliaryPrimes B).powerset) :
    finiteProbability
      (siteProductMass (fun _ : {s : Fin M // s ∉ ({e.1.1,e.1.2} : Finset (Fin M))} =>
        independentPrimeSetMass B))
      (fun b => CandidateForcedWitness B e
        (fun i => (mergeSitePartition {e.1.1,e.1.2} a b i).val)) ≤
      (M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) := by
  classical
  let I : Finset (Fin M) := {e.1.1,e.1.2}
  let w := siteProductMass (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
  let D := 5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hs (s : {s : Fin M // s ∉ I}) : finiteProbability w
      (fun b => ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) ≤ D := by
    have hm := siteProduct_expectation_coordinate
      (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
      (fun _ => independentPrimeSetMass_sum B) s
      (fun R => if ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ R.val then 1 else 0)
    have hh := hm.le.trans (candidate_forced_hit_bound hB hT hM hP he s.val)
    rw [finiteProbability_eq_indicator_mean]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (finiteExpectation w)
    funext b
    split_ifs <;> rfl
  have hevent : (fun b => CandidateForcedWitness B e
      (fun i => (mergeSitePartition I a b i).val)) =
      (fun b => ∃ s : {s : Fin M // s ∉ I},
        ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) := by
    funext b
    exact propext (forcedWitness_merge_iff e a b)
  rw [hevent]
  calc
    _ ≤ ∑ s : {s : Fin M // s ∉ I}, finiteProbability w
        (fun b => ∃ p ∈ candidateForcedPrimes B e s.val, p ∈ (b s).val) :=
      finiteProbability_union_le w
        (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) _
    _ ≤ ∑ _s : {s : Fin M // s ∉ I}, D := sum_le_sum (fun s _ => hs s)
    _ = (Fintype.card {s : Fin M // s ∉ I} : ℝ)*D := by simp
    _ ≤ (M : ℝ)*D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show Fintype.card {s : Fin M // s ∉ I} ≤ M from by
        simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun s : Fin M => s ∉ I))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteConditionalProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite disintegration for coordinate observations -/

namespace JointDickman
open Finset Classical

theorem uniform_image_conditional {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (x : Ω) :
    uniformImageMass f y * uniformConditionalMass f y x =
      if f x = y then 1/(Fintype.card Ω : ℝ) else 0 := by
  by_cases h : f x = y
  · have hc : (uniformFiber f y).card ≠ 0 := by
      apply card_ne_zero.mpr
      exact ⟨x,by simp [uniformFiber,h]⟩
    simp only [uniformImageMass,uniformConditionalMass,h,ite_true, if_true]
    have hc' : ((uniformFiber f y).card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp
  · simp [uniformConditionalMass,h]

/-- Observation kernels can be multiplied before disintegrating, even when
the final test depends on the whole observed family. -/
theorem finiteProduct_disintegration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)]
    (f : ∀ i, Ω i → α i) (w : ∀ i, Ω i → ℝ)
    (a : ∀ i, α i → ℝ) (k : ∀ i, α i → Ω i → ℝ)
    (hk : ∀ i y x, a i y*k i y x = if f i x = y then w i x else 0)
    (F : (∀ i, α i) → (∀ i, Ω i) → ℝ) :
    (∑ x, finiteProductMass w x * F (fun i => f i (x i)) x) =
      ∑ y, finiteProductMass a y *
        ∑ x, finiteProductMass (fun i => k i (y i)) x * F y x := by
  have hprod (x : ∀ i, Ω i) (y : ∀ i, α i) :
      finiteProductMass a y * finiteProductMass (fun i => k i (y i)) x =
        if (fun i => f i (x i)) = y then finiteProductMass w x else 0 := by
    simp only [finiteProductMass,← prod_mul_distrib,hk]
    by_cases he : (fun i => f i (x i)) = y
    · have he' (i : ι) : f i (x i) = y i := congrFun he i
      simp [he']
    · rw [ite_eq_right he]
      obtain ⟨i,hi⟩ : ∃ i, f i (x i) ≠ y i := by
        by_contra h
        push Not at h
        exact he (funext h)
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  symm
  simp only [mul_sum,← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [hprod,ite_mul,zero_mul]
  simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformResidueFibers
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform conditional residues, including null observation fibers -/

namespace JointDickman
open Finset Classical

theorem uniformImageMass_eq_push {Ω α : Type*} [Fintype Ω] [Fintype α]
    (f : Ω → α) (y : α) :
    uniformImageMass f y = finitePushMass (fun _ : Ω => 1/(Fintype.card Ω : ℝ)) f y := by
  unfold uniformImageMass finitePushMass uniformFiber
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  ring

theorem uniformConditionalMass_sum {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (hy : 0 < (uniformFiber f y).card) :
    (∑ x, uniformConditionalMass f y x) = 1 := by
  unfold uniformConditionalMass
  rw [← sum_filter]
  change (∑ _x ∈ uniformFiber f y, 1/((uniformFiber f y).card : ℝ)) = 1
  simp only [sum_const,nsmul_eq_mul]
  have h : ((uniformFiber f y).card : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp

theorem totalUniformConditionalMass_nonneg {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) : 0 ≤ totalUniformConditionalMass f y x := by
  unfold totalUniformConditionalMass uniformConditionalMass
  split_ifs <;> positivity

theorem totalUniformConditionalMass_sum {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) : (∑ x, totalUniformConditionalMass f y x) = 1 := by
  by_cases h : (uniformFiber f y).card = 0
  · simp [totalUniformConditionalMass,h]
  · simp only [totalUniformConditionalMass,h,ite_false, if_false]
    exact uniformConditionalMass_sum f y (Nat.pos_of_ne_zero h)

theorem total_uniform_image_conditional {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) :
    uniformImageMass f y * totalUniformConditionalMass f y x =
      if f x = y then 1/(Fintype.card Ω : ℝ) else 0 := by
  by_cases h : (uniformFiber f y).card = 0
  · have hn : f x ≠ y := by
      intro hx
      have hm : x ∈ uniformFiber f y := by simp [uniformFiber,hx]
      have hc := card_pos.mpr ⟨x,hm⟩
      omega
    simp [uniformImageMass,totalUniformConditionalMass,h,hn]
  · simp only [totalUniformConditionalMass,h,ite_false, if_false]
    exact uniform_image_conditional f y x

theorem total_uniform_product_disintegration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)] [∀ i, Inhabited (Ω i)]
    (f : ∀ i, Ω i → α i) (F : (∀ i, α i) → (∀ i, Ω i) → ℝ) :
    (∑ x, finiteProductMass (fun i (_ : Ω i) => 1/(Fintype.card (Ω i) : ℝ)) x *
      F (fun i => f i (x i)) x) =
    ∑ y, finiteProductMass (fun i => uniformImageMass (f i)) y *
      ∑ x, finiteProductMass (fun i => totalUniformConditionalMass (f i) (y i)) x * F y x :=
  finiteProduct_disintegration f _ _ _ (fun i y x => total_uniform_image_conditional (f i) y x) F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConditionedPrimeResidues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying conditional residue fibers with the candidate root model -/

namespace JointDickman
open Finset Classical

theorem blockPrimeHit_empty_iff (M p : ℕ) (r : ZMod p) :
    blockPrimeHit M p r = emptyBlockPrimeHit M ↔
      r ∉ univ.image (blockSiteRoot M p) := by
  constructor
  · intro h hr
    obtain ⟨i,_,hi⟩ := mem_image.mp hr
    have hm : i ∈ (blockPrimeHit M p r).val := by
      change i ∈ rootHitSet univ (blockSiteRoot M p) r
      simp [rootHitSet,hi]
    rw [h] at hm
    simp only [emptyBlockPrimeHit,Finset.notMem_empty] at hm
  · intro hr
    apply Subtype.ext
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hi' : blockSiteRoot M p i = r := (mem_filter.mp hi).2
    exact hr (mem_image.mpr ⟨i,mem_univ _,hi'⟩)

theorem blockPrimeFiber_empty (M p : ℕ) [NeZero p] :
    uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M) =
      univ \ univ.image (blockSiteRoot M p) := by
  ext r
  simp only [uniformFiber,mem_filter,mem_univ,true_and,mem_sdiff,
    blockPrimeHit_empty_iff]

theorem emptyBlockPrimeFiber_pos {M p : ℕ} [NeZero p] (hp : M < p) :
    0 < (uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M)).card := by
  rw [blockPrimeFiber_empty,card_sdiff_of_subset (subset_univ _),card_univ,
    ZMod.card,blockForbidden_card hp]
  omega

/-- At the empty site pattern, the conditional root law is exactly the
uniform residue law outside the forbidden classes. -/
theorem emptySite_candidate_push {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : M < p) (R : I.powerset) :
    finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) (emptyBlockPrimeHit M))
      (rootHitType I (candidateModRoot p)) R = outsideCandidatePrimeMass I p R := by
  have hpos := emptyBlockPrimeFiber_pos hp
  have hn : (uniformFiber (blockPrimeHit M p) (emptyBlockPrimeHit M)).card ≠ 0 := hpos.ne'
  have hn' : (univ \ univ.image (blockSiteRoot M p)).card ≠ 0 := by
    rwa [blockPrimeFiber_empty] at hn
  have he (r : ZMod p) :
      totalUniformConditionalMass (blockPrimeHit M p) (emptyBlockPrimeHit M) r =
      if r ∈ univ \ univ.image (blockSiteRoot M p) then
        1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0 := by
    simp only [totalUniformConditionalMass,blockPrimeFiber_empty,hn',ite_false, if_false,uniformConditionalMass,
      blockPrimeHit_empty_iff,blockPrimeFiber_empty,mem_sdiff,mem_univ,true_and]
  unfold outsideCandidatePrimeMass restrictedRootMass finitePushMass
  simp only [he]
  rw [sum_coe_sort (univ \ univ.image (blockSiteRoot M p))
    (fun r => if rootHitType I (candidateModRoot p) r = R then
      1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0)]
  have hU : univ.filter (fun r : ZMod p => r ∈ univ \ univ.image (blockSiteRoot M p)) =
      univ \ univ.image (blockSiteRoot M p) := by ext r; simp
  have hs := sum_filter (s := univ)
    (p := fun r : ZMod p => r ∈ univ \ univ.image (blockSiteRoot M p))
    (f := fun r => if rootHitType I (candidateModRoot p) r = R then
      1/((univ \ univ.image (blockSiteRoot M p)).card : ℝ) else 0)
  rw [hU] at hs
  rw [hs]
  apply sum_congr rfl
  intro r _
  by_cases hr : r ∈ univ.image (blockSiteRoot M p) <;>
    by_cases hh : rootHitType I (candidateModRoot p) r = R <;> simp [hr,hh]

/-- Occupied classes have zero masked tests; empty classes retain their
actual conditional residue law. Both branches are exact identities. -/
theorem maskedCandidatePrimeHit_push {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (hp : M < p)
    (H : (univ : Finset (Fin M)).powerset) (R : I.powerset) :
    finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) H)
      (maskedCandidatePrimeHit I p H) R =
    if H = emptyBlockPrimeHit M then outsideCandidatePrimeMass I p R else
      (if R.val = ∅ then 1 else 0) := by
  by_cases hH : H = emptyBlockPrimeHit M
  · subst H
    have hf : maskedCandidatePrimeHit I p (emptyBlockPrimeHit M) =
        rootHitType I (candidateModRoot p) := by funext r; simp [maskedCandidatePrimeHit]
    rw [hf,ite_eq_left rfl]
    exact emptySite_candidate_push I hp R
  · simp only [maskedCandidatePrimeHit,hH,ite_false, if_false,finitePushMass]
    have he : (⟨∅,by simp⟩ : I.powerset) = R ↔ R.val = ∅ := by
      constructor
      · intro h; exact (congrArg Subtype.val h).symm
      · intro h; exact Subtype.ext h.symm
    simp only [he]
    by_cases hR : R.val = ∅
    · simp only [hR,ite_true, if_true]
      exact totalUniformConditionalMass_sum _ _
    · simp [hR]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticRootMask
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching arithmetic quotient tests with the masked residue tests -/

namespace JointDickman
open Finset Classical

theorem candidateSiteValue_low {M : ℕ} (e : BlockCandidateIndex M) :
    candidateSiteValue e e.1.1 = (candidateLow e : ℤ) := by
  simp [candidateSiteValue]

theorem candidateSiteValue_high {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    candidateSiteValue e e.1.2 = (candidateHigh e : ℤ) := by
  have hi : e.1.1.val ≤ e.1.2.val := (show e.1.1.val < e.1.2.val from he.1).le
  have hlag : (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val := by
    unfold candidateLag
    exact Int.ofNat_sub hi
  have hco : (candidateHigh e : ℤ) = candidateLow e+
      (candidateLag e : ℤ)*candidateQuotient e := by
    exact_mod_cast he.2.2.2.2.1
  rw [hlag] at hco
  exact hco.symm

/-- Away from coefficient primes, an occupied residue root would be one
of the already controlled forced hits at a third site. -/
theorem candidate_occupied_root_impossible {B L T H M p u : ℕ} {τ C : ℝ}
    [Fact p.Prime] {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) (hp : p ∈ auxiliaryPrimes B)
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e)
    (hno : ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hocc : blockPrimeHit M p (u : ZMod p) ≠ emptyBlockPrimeHit M) :
    (u : ZMod p) ≠ candidateModRoot p e := by
  intro hroot
  have hnonempty : (blockPrimeHit M p (u : ZMod p)).val.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro h
    exact hocc (Subtype.ext h)
  obtain ⟨s,hs⟩ := hnonempty
  have hsite : blockSiteRoot M p s = (u : ZMod p) := (mem_filter.mp hs).2
  have hd := candidateModRoot_site_collision e s hc (hroot.symm.trans hsite.symm)
  by_cases hslo : s = e.1.1
  · subst s
    rw [candidateSiteValue_low,Int.natAbs_natCast] at hd
    exact hb hd
  by_cases hshi : s = e.1.2
  · subst s
    rw [candidateSiteValue_high he,Int.natAbs_natCast] at hd
    exact ha hd
  apply hno
  refine ⟨s,hslo,hshi,p,mem_filter.mpr ⟨hp,hd⟩,?_⟩
  exact mem_filter.mpr ⟨hp,(blockPrimeHit_divisibility M p u s).mp hs⟩

/-- Thus every nonexceptional auxiliary prime has the same test in the
actual quotient and the masked conditional model. -/
theorem arithmetic_quotient_masked_hit {B L T H M p u m : ℕ} {τ C : ℝ}
    [Fact p.Prime] (I : Finset (BlockCandidateIndex M))
    {e : BlockCandidateIndex M} (heI : e ∈ I)
    (he : BlockCandidateAdmissible B L T H τ C e) (hp : p ∈ auxiliaryPrimes B)
    (heq : candidateHigh e*candidateLow e*m+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e)
    (hno : ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    p ∣ m ↔ e ∈ (maskedCandidatePrimeHit I p
      (blockPrimeHit M p (u : ZMod p)) (u : ZMod p)).val := by
  have hr := candidate_affine_quotient_root e heq ha hb hc
  by_cases hocc : blockPrimeHit M p (u : ZMod p) = emptyBlockPrimeHit M
  · simp only [maskedCandidatePrimeHit,hocc,ite_true, if_true,rootHitType,rootHitSet,
      mem_filter,heI,true_and]
    exact hr.trans eq_comm
  · have hn := candidate_occupied_root_impossible he hp ha hb hc hno hocc
    have hm : ¬ p ∣ m := fun h => hn (hr.mp h)
    simp [maskedCandidatePrimeHit,hocc,hm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CandidateCoefficientPrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocal mass of the exceptional coefficient primes -/

namespace JointDickman
open Finset Classical

theorem mem_candidateCoefficientPrimes {B M p : ℕ} (e : BlockCandidateIndex M) :
    p ∈ candidateCoefficientPrimes B e ↔ p ∈ auxiliaryPrimes B ∧
      (p ∣ candidateLow e ∨ p ∣ candidateHigh e ∨ p ∣ candidateQuotient e) := by
  simp only [candidateCoefficientPrimes,auxiliaryDivisors,mem_union,mem_filter,
    Int.natAbs_natCast]
  tauto

theorem candidateCoefficientPrimes_mass {B L T H M : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) :
    (∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ)) ≤
      12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hl : (∑ p ∈ auxiliaryDivisors B (candidateLow e : ℤ), 1/(p : ℝ)) ≤
      5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    have hh := auxiliaryDivisors_mass (candidateSiteValue_ne_zero hB he e.1.1)
      (candidateSiteValue_size hB hT hM he e.1.1) hP
    simpa only [candidateSiteValue_low] using hh
  have hh : (∑ p ∈ auxiliaryDivisors B (candidateHigh e : ℤ), 1/(p : ℝ)) ≤
      5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    have hh := auxiliaryDivisors_mass (candidateSiteValue_ne_zero hB he e.1.2)
      (candidateSiteValue_size hB hT hM he e.1.2) hP
    simpa only [candidateSiteValue_high he] using hh
  have hc : (∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ)) ≤
      2*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
    apply auxiliaryDivisors_mass (by exact_mod_cast he.2.2.2.1.ne') _ hP
    simpa only [Int.natAbs_natCast] using (candidate_quotient_exp_bounds he).2
  unfold candidateCoefficientPrimes
  calc
    _ ≤ ((∑ p ∈ auxiliaryDivisors B (candidateLow e : ℤ), 1/(p : ℝ))+
        ∑ p ∈ auxiliaryDivisors B (candidateHigh e : ℤ), 1/(p : ℝ))+
        ∑ p ∈ auxiliaryDivisors B (candidateQuotient e : ℤ), 1/(p : ℝ) :=
      (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ)) (fun _ => by positivity)).trans
        (add_le_add (sum_union_le_nonneg _ _ (fun p : ℕ => 1/(p : ℝ))
          (fun _ => by positivity)) le_rfl)
    _ ≤ 5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)+
        5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)+
        2*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := add_le_add (add_le_add hl hh) hc
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDigitEvents
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exceptional coefficient tests after the endpoint digits are exposed -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem primeDigitMass_nonneg (B : ℕ) [∀ p : auxiliaryPrimes B, NeZero p.val]
    (t : ∀ p : auxiliaryPrimes B, ZMod p.val) : 0 ≤ primeDigitMass B t :=
  finiteProductMass_nonneg _ (fun _ _ => by positivity) t

theorem prime_digit_test_bound {B : ℕ} [∀ p : auxiliaryPrimes B, NeZero p.val]
    (p : auxiliaryPrimes B) (z c : ℤ) (hc : ¬ (p.val : ℤ) ∣ c) :
    finiteProbability (primeDigitMass B) (fun t =>
      (p.val : ℤ)^2 ∣ z+(p.val : ℤ)*c*((t p).val : ℤ)) ≤ 1/(p.val : ℝ) := by
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  have hone (q : auxiliaryPrimes B) :
      (∑ _t : ZMod q.val, 1/(q.val : ℝ)) = 1 := by
    simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]
    have hq : (q.val : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q.val)
    field_simp
  let f := fun t : ZMod p.val =>
    if (p.val : ℤ)^2 ∣ z+(p.val : ℤ)*c*(t.val : ℤ) then (1 : ℝ) else 0
  have hb : finiteExpectation (fun _ : ZMod p.val => 1/(p.val : ℝ)) f ≤ 1/(p.val : ℝ) := by
    have h := prime_square_digit_probability_le z c hc
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    simp only [finiteExpectation,f,mul_ite,mul_one,mul_zero,sum_div,ite_div,zero_div]
  have hh := (finiteProduct_expectation_coordinate _ hone p f).trans_le hb
  rw [finiteProbability_eq_indicator_mean]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (finiteExpectation (primeDigitMass B))
  funext t
  dsimp only [f]
  split_ifs <;> rfl

theorem coefficient_digit_single_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) {p : ℕ} (hp : p ∈ auxiliaryPrimes B) :
    finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) ≤ 1/(p : ℝ) := by
  by_cases hd : p ∣ candidateLow e*candidateHigh e
  · have hcop := he.2.2.2.2.2.2.1.mul_left he.2.2.2.2.2.2.2.1
    have hc : ¬ p ∣ candidateQuotient e :=
      (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mp (hcop.coprime_dvd_left hd)
    have hc' : ¬ (p : ℤ) ∣ (candidateQuotient e : ℤ) := by exact_mod_cast hc
    have hh := prime_digit_test_bound (B := B) ⟨p,hp⟩
      ((candidateQuotient e : ℤ)*((r ⟨p,hp⟩).val+(e.1.1.val+1))-candidateLow e)
      (candidateQuotient e) hc'
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (finiteProbability (primeDigitMass B))
    funext t
    apply propext
    simp only [coefficientDigitTest,dite_eq_left hp,hd,true_and]
    ring_nf
  · have hz : finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) = 0 := by
      simp [coefficientDigitTest,hp,hd,finiteProbability]
    rw [hz]
    positivity

/-- Uniform in every exposed first-digit family and its resulting candidate
list. No independence between that list and its endpoint types is assumed. -/
theorem coefficient_digit_event_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (I : Finset (BlockCandidateIndex M))
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (r : ∀ p : auxiliaryPrimes B, ZMod p.val) :
    finiteProbability (primeDigitMass B) (CoefficientDigitEvent B I r) ≤
      12*(I.card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hw := primeDigitMass_nonneg B
  calc
    _ ≤ ∑ e ∈ I, finiteProbability (primeDigitMass B)
        (fun t => ∃ p ∈ candidateCoefficientPrimes B e, coefficientDigitTest B e r t p) :=
      finiteProbability_exists_mem _ hw I _
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e,
        finiteProbability (primeDigitMass B) (fun t => coefficientDigitTest B e r t p) :=
      sum_le_sum (fun e _ => finiteProbability_exists_mem _ hw _ _)
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ) := by
      apply sum_le_sum
      intro e hei
      apply sum_le_sum
      intro p hp
      exact coefficient_digit_single_bound (he e hei) r ((mem_candidateCoefficientPrimes e).mp hp).1
    _ ≤ ∑ _e ∈ I, 12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) :=
      sum_le_sum (fun e hei => candidateCoefficientPrimes_mass hB hT hM hP (he e hei))
    _ = _ := by simp only [sum_const,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticCoefficientHits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every arithmetic coefficient-prime hit is a controlled digit event -/

namespace JointDickman
open Finset Classical

theorem arithmetic_coefficient_hit_implies_digit {B L T H M u : ℕ} {τ C : ℝ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hhit : ArithmeticCoefficientHit B I m) :
    CoefficientDigitEvent B I (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
  obtain ⟨e,hei,p,hpc,hpm⟩ := hhit
  obtain ⟨hp,hl|hh|hc⟩ := (mem_candidateCoefficientPrimes e).mp hpc
  all_goals
    let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p hp⟩
    have hpcop := he e hei
  case inr.inr =>
    have hpn : ¬ p ∣ candidateLow e :=
      (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mp
        (hpcop.2.2.2.2.2.2.1.symm.coprime_dvd_left hc)
    exact False.elim (affine_quotient_no_third_coefficient (heq e hei) hpn hc hpm)
  all_goals
    have hab : p ∣ candidateLow e*candidateHigh e := by
      first | exact dvd_mul_of_dvd_left hl _ | exact dvd_mul_of_dvd_right hh _
    refine ⟨e,hei,p,hpc,?_⟩
    simp only [coefficientDigitTest,dite_eq_left hp]
    refine ⟨hab,?_⟩
    have hd : (p : ℤ)^2 ∣ (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1))-candidateLow e := by
      have hm : p^2 ∣ candidateHigh e*candidateLow e*m e := by
        simpa only [pow_two,mul_comm (candidateLow e) (candidateHigh e)] using Nat.mul_dvd_mul hab hpm
      have hm' : (p : ℤ)^2 ∣ (candidateHigh e : ℤ)*candidateLow e*m e := by exact_mod_cast hm
      have heq' : (candidateHigh e : ℤ)*candidateLow e*m e+candidateLow e =
          (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1)) := by exact_mod_cast heq e hei
      have hz : (candidateQuotient e : ℤ)*((u : ℤ)+(e.1.1.val+1))-candidateLow e =
          (candidateHigh e : ℤ)*candidateLow e*m e := by linear_combination -heq'
      rwa [hz]
    exact (prime_square_affine_digits u (candidateQuotient e) (candidateLow e) (e.1.1.val+1)).mp hd

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TrimmedCandidateRoots
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic identification after removing coefficient tests -/

namespace JointDickman
open Finset Classical

/-- The finite exclusions used here are explicit arithmetic events. Outside
them, the original quotient prime sets equal the trimmed residue model. -/
theorem arithmetic_candidate_hit_eq_trimmed {B L T H M p u : ℕ} {τ C : ℝ}
    [Fact p.Prime] (I : Finset (BlockCandidateIndex M))
    (m : BlockCandidateIndex M → ℕ) (hp : p ∈ auxiliaryPrimes B)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hforce : ∀ e ∈ I, ¬ CandidateForcedWitness B e
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hcoeff : ∀ e ∈ I, p ∈ candidateCoefficientPrimes B e → ¬ p ∣ m e) :
    arithmeticCandidateHit I p m = trimmedCandidatePrimeHit B I p
      (blockPrimeHit M p (u : ZMod p)) (u : ZMod p) := by
  apply Subtype.ext
  ext e
  by_cases hei : e ∈ I
  · by_cases hc : p ∈ candidateCoefficientPrimes B e
    · have hn := hcoeff e hei hc
      simp [arithmeticCandidateHit,trimmedCandidatePrimeHit,hei,hc,hn]
    · have hn : ¬ p ∣ candidateLow e ∧ ¬ p ∣ candidateHigh e ∧ ¬ p ∣ candidateQuotient e := by
        have hh : ¬ (p ∣ candidateLow e ∨ p ∣ candidateHigh e ∨ p ∣ candidateQuotient e) :=
          fun h => hc ((mem_candidateCoefficientPrimes e).mpr ⟨hp,h⟩)
        tauto
      have hr := arithmetic_quotient_masked_hit I hei (he e hei) hp (heq e hei)
        hn.2.1 hn.1 hn.2.2 (hforce e hei)
      simpa only [arithmeticCandidateHit,trimmedCandidatePrimeHit,mem_filter,hei,true_and,
        hc,not_false_eq_true,and_true] using hr
  · have hm : e ∉ (maskedCandidatePrimeHit I p (blockPrimeHit M p (u : ZMod p))
        (u : ZMod p)).val := fun h => hei (mem_powerset.mp
          (maskedCandidatePrimeHit I p (blockPrimeHit M p (u : ZMod p)) (u : ZMod p)).property h)
    simp [arithmeticCandidateHit,trimmedCandidatePrimeHit,hei,hm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_MaskedCoefficientErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restoring coefficient-prime tests in the masked comparison model -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem maskedPrimeHit_probability {M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (H : (univ : Finset (Fin M)).powerset)
    (hp : M < p) (hhalf : 2*M ≤ p) {e : BlockCandidateIndex M} (he : e ∈ I) :
    finiteProbability (totalUniformConditionalMass (blockPrimeHit M p) H)
      (fun r => e ∈ (maskedCandidatePrimeHit I p H r).val) ≤ 2/(p : ℝ) := by
  rw [← finitePushMass_probability _ (maskedCandidatePrimeHit I p H)
    (fun R : I.powerset => e ∈ R.val)]
  have hm : finitePushMass (totalUniformConditionalMass (blockPrimeHit M p) H)
      (maskedCandidatePrimeHit I p H) =
      (fun R => if H = emptyBlockPrimeHit M then outsideCandidatePrimeMass I p R
        else (if R.val = ∅ then 1 else 0)) := by
    funext R
    exact maskedCandidatePrimeHit_push I hp H R
  rw [hm]
  by_cases hH : H = emptyBlockPrimeHit M
  · simp only [hH,ite_true, if_true]
    have hh := restrictedRootMass_hit_le I (candidateModRoot p)
      (univ \ univ.image (blockSiteRoot M p)) he
    have hc : (univ \ univ.image (blockSiteRoot M p)).card = p-M := by
      rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card,blockForbidden_card hp]
    rw [hc] at hh
    exact hh.trans (unoccupied_reciprocal_estimates p M hp hhalf).1
  · simp only [hH,ite_false, if_false,finiteProbability]
    have hz : (∑ R : I.powerset, if e ∈ R.val then (if R.val = ∅ then (1 : ℝ) else 0) else 0) = 0 := by
      apply sum_eq_zero
      intro R _
      by_cases hr : R.val = ∅ <;> simp [hr]
    rw [hz]
    positivity

theorem masked_coefficient_single_bound {B M p : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (I : Finset (BlockCandidateIndex M)) (H : BlockPrimePatterns B M)
    {e : BlockCandidateIndex M} (he : e ∈ I) (hp : p ∈ auxiliaryPrimes B)
    (hsize : M < p) (hhalf : 2*M ≤ p) :
    finiteProbability (conditionalResidueMass H) (maskedCoefficientTest I H e p) ≤ 2/(p : ℝ) := by
  let q : auxiliaryPrimes B := ⟨p,hp⟩
  let : Fact p.Prime := ⟨auxiliaryPrimes_prime B p hp⟩
  let a := fun q : auxiliaryPrimes B => totalUniformConditionalMass (blockPrimeHit M q.val) (H q)
  let f := fun r : ZMod p => if e ∈ (maskedCandidatePrimeHit I p (H q) r).val then (1 : ℝ) else 0
  have ha : ∀ q : auxiliaryPrimes B, ∑ r, a q r = 1 := fun q => totalUniformConditionalMass_sum _ _
  have hb : finiteExpectation (a q) f ≤ 2/(p : ℝ) := by
    have h := maskedPrimeHit_probability I (H q) hsize hhalf he
    rw [finiteProbability_eq_indicator_mean] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg (finiteExpectation (a q))
    funext r
    by_cases hr : e ∈ (maskedCandidatePrimeHit I p (H q) r).val <;> simp [f,hr]
  have hc := (finiteProduct_expectation_coordinate a ha q f).trans_le hb
  rw [finiteProbability_eq_indicator_mean]
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (finiteExpectation (conditionalResidueMass H))
  funext r
  have ht : maskedCoefficientTest I H e p r ↔
      e ∈ (maskedCandidatePrimeHit I p (H q) (r q)).val := by
    simp [maskedCoefficientTest,hp,q]
  by_cases hr : e ∈ (maskedCandidatePrimeHit I p (H q) (r q)).val <;> simp [f,ht,hr]

theorem masked_coefficient_event_bound {B L T H M : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (I : Finset (BlockCandidateIndex M))
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p) (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (S : BlockPrimePatterns B M) :
    finiteProbability (conditionalResidueMass S) (MaskedCoefficientEvent I S) ≤
      24*(I.card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hw : ∀ r, 0 ≤ conditionalResidueMass S r :=
    finiteProductMass_nonneg _ (fun _ => totalUniformConditionalMass_nonneg _ _)
  calc
    _ ≤ ∑ e ∈ I, finiteProbability (conditionalResidueMass S)
        (fun r => ∃ p ∈ candidateCoefficientPrimes B e, maskedCoefficientTest I S e p r) :=
      finiteProbability_exists_mem _ hw I _
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e,
        finiteProbability (conditionalResidueMass S) (maskedCoefficientTest I S e p) :=
      sum_le_sum (fun e _ => finiteProbability_exists_mem _ hw _ _)
    _ ≤ ∑ e ∈ I, ∑ p ∈ candidateCoefficientPrimes B e, 2/(p : ℝ) := by
      apply sum_le_sum
      intro e hei
      apply sum_le_sum
      intro p hp
      have hpa := ((mem_candidateCoefficientPrimes e).mp hp).1
      exact masked_coefficient_single_bound I S hei hpa (hsize p hpa) (hhalf p hpa)
    _ = ∑ e ∈ I, 2*(∑ p ∈ candidateCoefficientPrimes B e, 1/(p : ℝ)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro e _
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ _e ∈ I, 2*(12*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :=
      sum_le_sum (fun e hei => mul_le_mul_of_nonneg_left
        (candidateCoefficientPrimes_mass hB hT hM hP (he e hei)) (by norm_num))
    _ = _ := by simp only [sum_const,nsmul_eq_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticRootIdentification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic root families agree outside the explicit exceptional events -/

namespace JointDickman
open Finset Classical

theorem trimmedCandidatePrimeHit_eq {B M p : ℕ} [Fact p.Prime]
    (I : Finset (BlockCandidateIndex M)) (H : (univ : Finset (Fin M)).powerset)
    (r : ZMod p)
    (hno : ∀ e ∈ I, p ∈ candidateCoefficientPrimes B e →
      e ∉ (maskedCandidatePrimeHit I p H r).val) :
    trimmedCandidatePrimeHit B I p H r = maskedCandidatePrimeHit I p H r := by
  apply Subtype.ext
  apply filter_eq_self.mpr
  intro e he
  have hei : e ∈ I := mem_powerset.mp (maskedCandidatePrimeHit I p H r).property he
  exact fun hc => hno e hei hc he

/-- All three exclusions have their own proved probability bounds. The
quotient family here is the actual family satisfying the affine equations. -/
theorem arithmetic_roots_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ)
    (he : ∀ e ∈ I, BlockCandidateAdmissible B L T H τ C e)
    (heq : ∀ e ∈ I, candidateHigh e*candidateLow e*m e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (hforce : ∀ e ∈ I, ¬ CandidateForcedWitness B e
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hactual : ¬ ArithmeticCoefficientHit B I m)
    (hmasked : ¬ MaskedCoefficientEvent I (arithmeticPrimePatterns B M u)
      (fun p => (u : ZMod p.val))) :
    arithmeticCandidatePrimeFamily B I m =
      maskedPrimeRootFamily I (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val)) := by
  funext p
  let : Fact p.val.Prime := ⟨auxiliaryPrimes_prime B p.val p.property⟩
  have hc : ∀ e ∈ I, p.val ∈ candidateCoefficientPrimes B e → ¬ p.val ∣ m e := by
    intro e hei hcoef hdiv
    exact hactual ⟨e,hei,p.val,hcoef,hdiv⟩
  have hm : ∀ e ∈ I, p.val ∈ candidateCoefficientPrimes B e →
      e ∉ (maskedCandidatePrimeHit I p.val (blockPrimeHit M p.val (u : ZMod p.val))
        (u : ZMod p.val)).val := by
    intro e hei hcoef hdiv
    apply hmasked
    refine ⟨e,hei,p.val,hcoef,?_⟩
    simpa only [maskedCoefficientTest,dite_eq_left p.property,arithmeticPrimePatterns] using hdiv
  exact (arithmetic_candidate_hit_eq_trimmed I m p.property he heq hforce hc).trans
    (trimmedCandidatePrimeHit_eq I _ _ hm)

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSquareHits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing all site squares in a block, after taking digit averages -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem residue_block_squareHit_bound (B M : ℕ) :
    (∑ u : ZMod (auxiliarySquarePeriod B),
      if BlockSquareHit B M u.val then (1 : ℝ) else 0)/
        (auxiliarySquarePeriod B : ℝ) ≤
      (M : ℝ)*∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2 := by
  let w := fun _ : ZMod (auxiliarySquarePeriod B) => 1/(auxiliarySquarePeriod B : ℝ)
  have hw : ∀ u, 0 ≤ w u := by intro u; dsimp [w] <;> positivity
  have hunif (E : ZMod (auxiliarySquarePeriod B) → Prop) :
      finiteProbability w E = (∑ u, if E u then (1 : ℝ) else 0)/(auxiliarySquarePeriod B : ℝ) := by
    simp only [finiteProbability,w,ite_div,one_div,zero_div,sum_div]
  have hp (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      finiteProbability w (fun u => p^2 ∣ u.val+(i.val+1)) = 1/(p : ℝ)^2 := by
    rw [hunif]
    convert residue_square_divisor_mean hp (i.val+1) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply sum_congr rfl
    intro u _
    by_cases h : p^2 ∣ u.val+(i.val+1) <;> simp [h]
  rw [← hunif]
  change finiteProbability w (fun u => ∃ i : Fin M, ∃ p ∈ auxiliaryPrimes B,
    p^2 ∣ u.val+(i.val+1)) ≤ _
  calc
    _ ≤ ∑ i : Fin M, finiteProbability w
        (fun u => ∃ p ∈ auxiliaryPrimes B, p^2 ∣ u.val+(i.val+1)) :=
      finiteProbability_union_le w hw _
    _ ≤ ∑ i : Fin M, ∑ p ∈ auxiliaryPrimes B,
        finiteProbability w (fun u => p^2 ∣ u.val+(i.val+1)) :=
      sum_le_sum (fun i _ => finiteProbability_exists_mem w hw _ _)
    _ = _ := by simp_rw [sum_congr rfl (fun p h => hp _ p h)] <;> simp

/-- Polynomially bounded graph tests pay a vanishing total cost when all
site squares are removed. -/
theorem block_squareHit_polynomial_bound {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2) :
    (B : ℝ)^10 * ((∑ u : ZMod (auxiliarySquarePeriod B),
      if BlockSquareHit B M u.val then (1 : ℝ) else 0)/(auxiliarySquarePeriod B : ℝ)) ≤
        1/(B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B)
    (show auxiliaryCutoff B ≠ 0 from pow_ne_zero _ (by omega)) (by
      intro p hp
      exact_mod_cast (mem_filter.mp hp).2)
  have hpow : (B : ℝ)^13 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff,Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 13 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 13) hpow)
  have hMr : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  calc
    _ ≤ (B : ℝ)^10*((M : ℝ)*∑ p ∈ auxiliaryPrimes B, 1/(p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (residue_block_squareHit_bound B M) (by positivity)
    _ ≤ (B : ℝ)^10*((B : ℝ)^2*(1/(B : ℝ)^13)) := by gcongr
    _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticCandidateWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six arithmetic graph factors are the candidate root weight -/

namespace JointDickman
open Finset Classical

/-- Removing the selected squarefree factors leaves exactly the two
endpoint complements occurring in the candidate kernel. -/
theorem arithmetic_graph_candidate_weight {B L T H M u : ℕ} {τ C : ℝ}
    (w : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hsq : ¬ BlockSquareHit B M u) :
    arithmeticGraphPairWeight B L τ C w v
      (candidateHigh e) (candidateLow e) (candidateQuotient e) (candidateLag e)
      (u+(e.1.1.val+1))/(B : ℝ) =
    candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (candidateCutoff w v) e
      (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
        (candidateQuotient e) (u+(e.1.1.val+1)))) := by
  obtain ⟨hs,hadm⟩ := mem_blockCandidates.mp he
  obtain ⟨hlo,_,_⟩ := mem_endpointSplits.mp hs.1
  obtain ⟨hhi,_,_⟩ := mem_endpointSplits.mp hs.2
  have hlowP : e.2.1 ⊆ auxiliaryPrimes B := hlo.trans (filter_subset _ _)
  have hhighP : e.2.2 ⊆ auxiliaryPrimes B := hhi.trans (filter_subset _ _)
  have hlowD : candidateLow e ∣ u+(e.1.1.val+1) :=
    (primeProduct_dvd_site_iff hlowP).mpr hlo
  have hhighD : candidateHigh e ∣ u+(e.1.2.val+1) :=
    (primeProduct_dvd_site_iff hhighP).mpr hhi
  have hno (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : ¬ p^2 ∣ u+(i.val+1) :=
    fun hd => hsq ⟨i,p,hp,hd⟩
  have hqlow := coefficientPrimeSet_quotient hlowP hlowD (hno e.1.1)
  have hqhigh := coefficientPrimeSet_quotient hhighP hhighD (hno e.1.2)
  change coefficientPrimeSet B ((u+(e.1.1.val+1))/candidateLow e) = _ at hqlow
  change coefficientPrimeSet B ((u+(e.1.2.val+1))/candidateHigh e) = _ at hqhigh
  have hshift : (((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ)).toNat =
      u+(e.1.2.val+1) := by
    have hi : e.1.1.val ≤ e.1.2.val := (show e.1.1.val < e.1.2.val from hadm.1).le
    have hl : (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val := Int.ofNat_sub hi
    rw [hl]
    omega
  unfold arithmeticGraphPairWeight arithmeticResidueWeight candidateRootWeight candidateCutoff
  rw [hshift]
  change (_ * (_ * regularResidueWeight B L τ C
      (coefficientPrimeSet B ((u+(e.1.1.val+1))/candidateLow e)) * _) *
    (_ * regularResidueWeight B L τ C
      (coefficientPrimeSet B ((u+(e.1.2.val+1))/candidateHigh e)) * _))/(B : ℝ) = _
  rw [hqlow,hqhigh]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph coefficient triples have no multiplicity at a fixed lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTriple_subsets {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    i.1 ⊆ auxiliaryPrimes B ∧ i.2.1 ⊆ auxiliaryPrimes B ∧ i.2.2 ⊆ auxiliaryPrimes B := by
  classical
  have h := mem_product.mp (mem_filter.mp hi).1
  exact ⟨mem_powerset.mp h.1, mem_powerset.mp (mem_product.mp h.2).1,
    mem_powerset.mp (mem_product.mp h.2).2⟩

theorem graphTriple_positive_relation {B T j : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ supportedGraphTriples B T (j : ℤ)) :
    (∏ p ∈ i.2.1, p) = (∏ p ∈ i.2.2, p)+j*(∏ p ∈ i.1, p) := by
  classical
  have h := (mem_filter.mp (mem_filter.mp hi).1).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at h
  rw [(mem_filter.mp hi).2.1] at h
  have h' : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) =
      (∏ p ∈ i.2.2, p : ℕ)+(j : ℤ)*(∏ p ∈ i.1, p : ℕ) := by linarith
  exact_mod_cast h'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphTripleSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Only supported coprime coefficient triples contribute to a lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTripleWeight_nonzero_supported {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) {i : GraphCoefficientTriple} {j : ℤ}
    (hi : i ∈ arithmeticGraphTriples B T) (hlag : graphTripleLag i = j)
    {n : ℕ} (hw : graphTripleWeight B L τ C T i n ≠ 0) :
    i ∈ supportedGraphTriples B T j := by
  classical
  let a := ∏ p ∈ i.2.1, p
  let b := ∏ p ∈ i.2.2, p
  let c := ∏ p ∈ i.1, p
  have hzero (hu : amplificationOuterWeight B c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change (amplificationOuterWeight B c * _ * _) * _ * _ = 0
    rw [hu, zero_mul, zero_mul, zero_mul, zero_mul]
  have hza (hu : amplificationInnerWeight T a c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T a c) * _ = 0
    rw [hu, mul_zero, mul_zero, zero_mul]
  have hzb (hu : amplificationInnerWeight T b c = 0) : False := by
    apply hw
    simp only [graphTripleWeight, arithmeticGraphPairWeight]
    change _ * (_ * _ * amplificationInnerWeight T b c) = 0
    rw [hu, mul_zero, mul_zero]
  have hpa : (a,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT a c hn
    exact (mul_ne_zero hzero hza) hs
  have hpb : (b,c) ∈ amplificationCoefficientPairs B T := by
    by_contra hn
    have hs := amplificationSmoothWeight_support hB hT b c hn
    exact (mul_ne_zero hzero hzb) hs
  exact mem_filter.mpr ⟨hi,hlag,hpa,hpb⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateGraphEncoding
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding endpoint candidates as the original graph's coefficient triples -/

namespace JointDickman
open Finset Classical

theorem candidateLag_pos {B L T H M : ℕ} {τ C : ℝ} {e : BlockCandidateIndex M}
    (he : BlockCandidateAdmissible B L T H τ C e) : 0 < candidateLag e := by
  unfold candidateLag
  exact Nat.sub_pos_of_lt he.1

theorem candidateGraphTriple_lag {B L T H M : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M} (he : BlockCandidateAdmissible B L T H τ C e) :
    graphTripleLag (candidateGraphTriple B e) = (candidateLag e : ℤ) := by
  have hq := he.2.2.2.2.2.2.2.2.1
  have hq0 : (candidateQuotient e : ℤ) ≠ 0 := by exact_mod_cast he.2.2.2.1.ne'
  have heq : (candidateHigh e : ℤ)-candidateLow e =
      (candidateLag e : ℤ)*candidateQuotient e := by
    have h : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e := by
      exact_mod_cast he.2.2.2.2.1
    linarith
  change ((candidateHigh e : ℤ)-candidateLow e)/
    ((∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p : ℕ) : ℤ) = _
  rw [← hq,heq,Int.mul_ediv_cancel _ hq0]

theorem candidateGraphTriple_mem {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C S) :
    candidateGraphTriple B e ∈ arithmeticGraphTriples B T := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1.trans (hS e.1.1)
  have hhi := (mem_endpointSplits.mp hs.2).1.trans (hS e.1.2)
  have hj := candidateLag_pos ha
  have hq := ha.2.2.2.2.2.2.2.2.1
  have hab : e.2.2 ≠ e.2.1 := by
    intro hab
    have hsame : candidateHigh e = candidateLow e := by
      change (∏ p ∈ e.2.2, p) = ∏ p ∈ e.2.1, p
      rw [hab]
    have hrel := ha.2.2.2.2.1
    have hc := ha.2.2.2.1
    nlinarith
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_powerset.mpr (filter_subset _ _),
    mem_product.mpr ⟨mem_powerset.mpr hhi,mem_powerset.mpr hlo⟩⟩,?_⟩
  unfold GraphCoefficientAdmissible
  change e.2.2 ≠ e.2.1 ∧ graphTripleLag (candidateGraphTriple B e) ≠ 0 ∧
    (graphTripleLag (candidateGraphTriple B e)).natAbs < T ∧
    (candidateHigh e : ℤ)-candidateLow e = graphTripleLag (candidateGraphTriple B e)*
      ((∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p : ℕ) : ℤ) ∧
    (candidateHigh e).Coprime (graphTripleLag (candidateGraphTriple B e)).natAbs
  rw [candidateGraphTriple_lag ha,Int.natAbs_natCast,← hq]
  refine ⟨hab,by exact_mod_cast hj.ne',ha.2.2.1,?_,?_⟩
  · have hh : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e := by
      exact_mod_cast ha.2.2.2.2.1
    linarith
  · exact auxiliaryProduct_coprime_small hhi hj (ha.2.2.1.le.trans hT)

theorem candidateGraphTriple_weight {B L T H M u : ℕ} {τ C : ℝ}
    {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hsq : ¬ BlockSquareHit B M u) :
    graphTripleWeight B L τ C T (candidateGraphTriple B e) (u+(e.1.1.val+1))/(B : ℝ) =
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
        (candidateCutoff (amplificationOuterWeight B) (amplificationInnerWeight T)) e
        (coefficientPrimeSet B (divisorEdgeInverse (candidateHigh e) (candidateLow e)
          (candidateQuotient e) (u+(e.1.1.val+1)))) := by
  have ha := (mem_blockCandidates.mp he).2
  have hq := ha.2.2.2.2.2.2.2.2.1
  unfold graphTripleWeight
  rw [candidateGraphTriple_lag ha]
  change arithmeticGraphPairWeight B L τ C _ _ _ _
    (∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p) _ _ / _ = _
  rw [← hq]
  exact arithmetic_graph_candidate_weight _ _ he hsq

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphCandidateDecoding
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering endpoint candidates from nonzero arithmetic graph terms -/

namespace JointDickman
open Finset Classical

theorem graphBlockCandidate_quotient {B T M : ℕ} {i k : Fin M}
    {g : GraphCoefficientTriple} (hik : i < k)
    (hg : g ∈ supportedGraphTriples B T ((k.val-i.val : ℕ) : ℤ)) :
    candidateQuotient (graphBlockCandidate i k g) = ∏ p ∈ g.1, p := by
  have hj : 0 < k.val-i.val := Nat.sub_pos_of_lt hik
  have he := graphTriple_positive_relation hg
  change ((∏ p ∈ g.2.1, p)-(∏ p ∈ g.2.2, p))/(k.val-i.val) = _
  rw [he,Nat.add_sub_cancel_left,Nat.mul_div_cancel_left _ hj]

theorem graphBlockCandidate_roundtrip {B T M : ℕ} {i k : Fin M}
    {g : GraphCoefficientTriple} (hik : i < k)
    (hg : g ∈ supportedGraphTriples B T ((k.val-i.val : ℕ) : ℤ)) :
    candidateGraphTriple B (graphBlockCandidate i k g) = g := by
  have hs := graphTriple_subsets (mem_filter.mp hg).1
  unfold candidateGraphTriple
  rw [graphBlockCandidate_quotient hik hg,coefficientPrimeSet_primeProduct hs.1]
  rfl

theorem candidateGraphTriple_roundtrip {B M : ℕ} {i k : Fin M}
    {e : BlockCandidateIndex M} (he : e.1 = (i,k)) :
    graphBlockCandidate i k (candidateGraphTriple B e) = e := by
  exact Prod.ext he.symm rfl

theorem graphTripleWeight_nonzero_regular {B L T n : ℕ} {τ C : ℝ}
    {g : GraphCoefficientTriple} (hg : g ∈ arithmeticGraphTriples B T)
    (hw : graphTripleWeight B L τ C T g n ≠ 0) :
    RegularPrimeSet B L τ C g.1 ∧
    RegularPrimeSet B L τ C g.2.1 ∧
    RegularPrimeSet B L τ C g.2.2 ∧
    RegularPrimeSet B L τ C (coefficientPrimeSet B (n/(∏ p ∈ g.2.2, p))) ∧
    RegularPrimeSet B L τ C
      (coefficientPrimeSet B (((n : ℤ)+graphTripleLag g).toNat/(∏ p ∈ g.2.1, p))) := by
  have hs := graphTriple_subsets hg
  have hc (d : ℕ) (h : regularCoefficientWeight B L τ C d ≠ 0) :
      RegularPrimeSet B L τ C (coefficientPrimeSet B d) := by
    by_contra hn
    exact h (by simp [regularCoefficientWeight,hn])
  have hr (d : ℕ) (h : arithmeticResidueWeight B L τ C d ≠ 0) :
      RegularPrimeSet B L τ C (coefficientPrimeSet B d) := by
    by_contra hn
    exact h (by simp [arithmeticResidueWeight,regularResidueWeight,hn])
  change (_ * _ * _) * (_ * _ * _) * (_ * _ * _) ≠ 0 at hw
  obtain ⟨hca,heb⟩ := mul_ne_zero_iff.mp hw
  obtain ⟨hcc,hea⟩ := mul_ne_zero_iff.mp hca
  obtain ⟨huc,_⟩ := mul_ne_zero_iff.mp hcc
  obtain ⟨_,hregc⟩ := mul_ne_zero_iff.mp huc
  obtain ⟨hara,_⟩ := mul_ne_zero_iff.mp hea
  obtain ⟨hrega,hra⟩ := mul_ne_zero_iff.mp hara
  obtain ⟨hbrb,_⟩ := mul_ne_zero_iff.mp heb
  obtain ⟨hregb,hrb⟩ := mul_ne_zero_iff.mp hbrb
  refine ⟨?_,?_,?_,hr _ hra,hr _ hrb⟩
  · simpa only [coefficientPrimeSet_primeProduct hs.1] using hc _ hregc
  · simpa only [coefficientPrimeSet_primeProduct hs.2.1] using hc _ hrega
  · simpa only [coefficientPrimeSet_primeProduct hs.2.2] using hc _ hregb

theorem graphBlockCandidate_mem {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) {i k : Fin M} (hik : i < k)
    (hH : H < k.val-i.val) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0)
    (hsq : ¬ BlockSquareHit B M u) :
    graphBlockCandidate i k g ∈ blockCandidates B L T H M τ C
      (fun l => coefficientPrimeSet B (u+(l.val+1))) := by
  have hs := graphTriple_subsets hg
  have hsup := graphTripleWeight_nonzero_supported hB hT τ C hg hlag hw
  have hq := graphBlockCandidate_quotient hik hsup
  have hreg := graphTripleWeight_nonzero_regular hg hw
  have hj : 0 < k.val-i.val := Nat.sub_pos_of_lt hik
  have hshift : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g).toNat = u+(k.val+1) := by
    rw [hlag,Int.ofNat_sub hik.le]
    omega
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hadiv : (∏ p ∈ g.2.1, p) ∣ u+(k.val+1) := by
    have h := (mem_filter.mp hn).2.2.1
    have he : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g) = (u+(k.val+1) : ℕ) := by
      rw [hlag,Int.ofNat_sub hik.le]
      push_cast
      ring
    rw [he] at h
    exact_mod_cast h
  have hno (l : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : ¬ p^2 ∣ u+(l.val+1) :=
    fun hd => hsq ⟨l,p,hp,hd⟩
  have hcompb := coefficientPrimeSet_quotient hs.2.2 hbdiv (hno i)
  have hcompa := coefficientPrimeSet_quotient hs.2.1 hadiv (hno k)
  have hrega : RegularPrimeSet B L τ C (coefficientPrimeSet B (u+(k.val+1)) \ g.2.1) := by
    rw [hshift,hcompa] at hreg
    exact hreg.2.2.2.2
  have hregb : RegularPrimeSet B L τ C (coefficientPrimeSet B (u+(i.val+1)) \ g.2.2) := by
    rw [hcompb] at hreg
    exact hreg.2.2.2.1
  apply mem_blockCandidates.mpr
  refine ⟨⟨mem_endpointSplits.mpr ⟨(primeProduct_dvd_site_iff hs.2.2).mp hbdiv,
    hreg.2.2.1,hregb⟩,mem_endpointSplits.mpr
    ⟨(primeProduct_dvd_site_iff hs.2.1).mp hadiv,hreg.2.1,hrega⟩⟩,?_⟩
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have he : ((∏ p ∈ g.2.1, p : ℕ) : ℤ)-(∏ p ∈ g.2.2, p) =
      graphTripleLag g*(∏ p ∈ g.1, p) := hadm.2.2.2.1
  have hm := (divisorEdge_inverse_mem ha hc he hadm.2.2.2.2 hn).1
  have hca := (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.1).1
  have hcb := (coprime_of_divisor_linear_succ (mem_filter.mp hm).2.2.2.2).1
  have hab := divisor_edge_coprime hca hadm.2.2.2.2 he
  have hwa := (mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hsup).2.2.1
  have hwb := (mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hsup).2.2.2
  unfold BlockCandidateAdmissible
  change i < k ∧ H < k.val-i.val ∧ k.val-i.val < T ∧
    0 < candidateQuotient (graphBlockCandidate i k g) ∧ _
  rw [hq]
  refine ⟨hik,hH,?_,hc,graphTriple_positive_relation hsup,hab.symm,hcb,hca,?_,?_,?_,?_,
    hwb.2.2.1,hwb.2.2.2.le,hwa.2.2.1,hwa.2.2.2.le⟩
  · have hjlt : (graphTripleLag g).natAbs < T := hadm.2.2.1
    simpa only [hlag,Int.natAbs_natCast] using hjlt
  · rw [coefficientPrimeSet_primeProduct hs.1]
  · simpa only [coefficientPrimeSet_primeProduct hs.1] using hreg.1
  · exact (Real.le_log_iff_exp_le (by positivity)).mpr hwa.1
  · exact (Real.log_le_iff_le_exp (by positivity)).mpr hwa.2.1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticCandidateSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reindexing of the arithmetic graph by its endpoint candidates -/

namespace JointDickman
open Finset Classical

theorem rawArithmeticGraphKernel_candidate_sum {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    {i k : Fin M} (hik : i < k) (hH : H < k.val-i.val)
    (hsq : ¬ BlockSquareHit B M u) :
    rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ)
        (u+(i.val+1))/(B : ℝ) =
      ∑ e ∈ blockCandidates B L T H M τ C
          (fun l => coefficientPrimeSet B (u+(l.val+1))),
        if e.1 = (i,k) ∧ u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e)
        then arithmeticCandidateWeight B L T τ C u e else 0 := by
  unfold rawArithmeticGraphKernel
  rw [sum_div]
  let f (g : GraphCoefficientTriple) : ℝ :=
    (if graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
        u+(i.val+1) ∈ graphTripleEdges N g
      then graphTripleWeight B L τ C T g (u+(i.val+1)) else 0)/(B : ℝ)
  have hsupport (g : GraphCoefficientTriple) (hf : f g ≠ 0) :
      graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
      u+(i.val+1) ∈ graphTripleEdges N g ∧
      graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0 := by
    dsimp [f] at hf
    by_cases h : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
        u+(i.val+1) ∈ graphTripleEdges N g
    · refine ⟨h.1,h.2,?_⟩
      intro hz
      simp [h,hz] at hf
    · simp [h] at hf
  apply sum_bij_ne_zero (fun g _ _ => graphBlockCandidate i k g)
  · intro g hg hf
    obtain ⟨hlag,hn,hw⟩ := hsupport g hf
    exact graphBlockCandidate_mem hB hT hik hH hg hlag hn hw hsq
  · intro g hg hf g' hg' hf' heq
    have hs := hsupport g hf
    have hs' := hsupport g' hf'
    have hr := graphBlockCandidate_roundtrip hik
      (graphTripleWeight_nonzero_supported hB hT τ C hg hs.1 hs.2.2)
    have hr' := graphBlockCandidate_roundtrip hik
      (graphTripleWeight_nonzero_supported hB hT τ C hg' hs'.1 hs'.2.2)
    exact hr.symm.trans ((congrArg (candidateGraphTriple B) heq).trans hr')
  · intro e he hwe
    have hp : e.1 = (i,k) ∧
        u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e) := by
      by_contra h
      simp only [ite_eq_right h,ne_eq,not_true_eq_false] at hwe
    have hg := candidateGraphTriple_mem _ (fun l => filter_subset _ _) hTP he
    have ha := (mem_blockCandidates.mp he).2
    have hj : candidateLag e = k.val-i.val := by
      change e.1.2.val-e.1.1.val = _
      rw [hp.1]
    have hlag : graphTripleLag (candidateGraphTriple B e) = ((k.val-i.val : ℕ) : ℤ) :=
      (candidateGraphTriple_lag ha).trans (congrArg (fun j : ℕ => (j : ℤ)) hj)
    refine ⟨candidateGraphTriple B e,hg,?_,candidateGraphTriple_roundtrip hp.1⟩
    have heweight := candidateGraphTriple_weight he hsq
    have hilow : e.1.1 = i := congrArg Prod.fst hp.1
    change _ = arithmeticCandidateWeight B L T τ C u e at heweight
    rw [hilow] at heweight
    dsimp [f]
    rw [ite_eq_left ⟨hlag,hp.2⟩,heweight]
    simpa only [ite_eq_left hp] using hwe
  · intro g hg hf
    obtain ⟨hlag,hn,hw⟩ := hsupport g hf
    have hs := graphTripleWeight_nonzero_supported hB hT τ C hg hlag hw
    have he := graphBlockCandidate_mem hB hT hik hH hg hlag hn hw hsq
    have hr := graphBlockCandidate_roundtrip hik hs
    have hwgt := candidateGraphTriple_weight he hsq
    change _ = arithmeticCandidateWeight B L T τ C u (graphBlockCandidate i k g) at hwgt
    rw [hr] at hwgt
    rw [ite_eq_left ⟨hlag,hn⟩,ite_eq_left (show
      (graphBlockCandidate i k g).1 = (i,k) ∧
        u+(i.val+1) ∈ graphTripleEdges N (candidateGraphTriple B (graphBlockCandidate i k g))
      from ⟨rfl,hr.symm ▸ hn⟩)]
    exact hwgt

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticCandidateKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original candidate weights and the masked residue kernel -/

namespace JointDickman
open Finset Classical

/-- Both endpoint divisibilities reconstruct the affine quotient, without
any counting-scale cutoff or squarefree-site assumption. -/
theorem candidateArithmeticQuotient_equation {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    candidateHigh e*candidateLow e*candidateArithmeticQuotient u e+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1
  have hhi := (mem_endpointSplits.mp hs.2).1
  have hloP := hlo.trans (show coefficientPrimeSet B (u+(e.1.1.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hhiP := hhi.trans (show coefficientPrimeSet B (u+(e.1.2.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hloD : candidateLow e ∣ u+(e.1.1.val+1) := (primeProduct_dvd_site_iff hloP).mpr hlo
  have hhiD : candidateHigh e ∣ u+(e.1.2.val+1) := (primeProduct_dvd_site_iff hhiP).mpr hhi
  have hapos : 0 < candidateHigh e :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hhiP hp)).pos)
  have hj := candidateLag_pos ha
  have heq : (candidateHigh e : ℤ)-candidateLow e = (candidateLag e : ℤ)*candidateQuotient e := by
    have h : (candidateHigh e : ℤ) = candidateLow e+(candidateLag e : ℤ)*candidateQuotient e :=
      by exact_mod_cast ha.2.2.2.2.1
    linarith
  have hcop : (candidateHigh e).Coprime (Int.natAbs (candidateLag e : ℤ)) := by
    rw [Int.natAbs_natCast]
    exact auxiliaryProduct_coprime_small hhiP hj (ha.2.2.1.le.trans hT)
  have hshift : ((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ) =
      (u+(e.1.2.val+1) : ℕ) := by
    rw [show (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val from Int.ofNat_sub ha.1.le]
    push_cast
    ring
  obtain ⟨m,hm,_⟩ := natural_divisor_edge_inverse hapos ha.2.2.2.1
    (by omega : 0 < u+(e.1.1.val+1)) hloD heq hcop
    (by rw [hshift]; exact_mod_cast hhiD)
  have hinv : candidateArithmeticQuotient u e = m := divisorEdgeInverse_eq hapos hm
  rw [hinv]
  calc
    _ = candidateLow e*(candidateHigh e*m+1) := by ring
    _ = candidateLow e*(candidateQuotient e*((u+(e.1.1.val+1))/candidateLow e)) := by rw [hm]
    _ = candidateQuotient e*(candidateLow e*((u+(e.1.1.val+1))/candidateLow e)) := by ring
    _ = _ := by rw [Nat.mul_div_cancel' hloD]

theorem arithmeticCandidatePrimeFamily_transpose {M B : ℕ}
    (I : Finset (BlockCandidateIndex M)) (m : BlockCandidateIndex M → ℕ) (e : I) :
    (primeSiteTranspose I (auxiliaryPrimes B) (arithmeticCandidatePrimeFamily B I m) e).val =
      coefficientPrimeSet B (m e.val) := by
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · rw [primeSiteTranspose_mem I (auxiliaryPrimes B)
      (arithmeticCandidatePrimeFamily B I m) e ⟨p,hp⟩]
    simp [arithmeticCandidatePrimeFamily,arithmeticCandidateHit,coefficientPrimeSet,hp,e.property]
  · have hleft : p ∉ (primeSiteTranspose I (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B I m) e).val :=
      fun h => hp (mem_powerset.mp
        (primeSiteTranspose I (auxiliaryPrimes B) (arithmeticCandidatePrimeFamily B I m) e).property h)
    simp [coefficientPrimeSet,hp,hleft]

/-- Pointwise identification of the arithmetic kernel with the masked
model outside the three explicitly bounded exceptional events. -/
theorem actualCandidateKernel_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hforce : ∀ e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))),
      ¬ CandidateForcedWitness B e (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (hactual : ¬ ArithmeticCoefficientHit B
      (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
      (candidateArithmeticQuotient u))
    (hmasked : ¬ MaskedCoefficientEvent
      (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
      (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val))) :
    actualCandidateKernel B L T H M τ C χ u =
      independentCandidateKernel B L T H M τ C
        (fun i => coefficientPrimeSet B (u+(i.val+1))) χ
        (primeSiteTranspose _ (auxiliaryPrimes B)
          (maskedPrimeRootFamily _ (arithmeticPrimePatterns B M u) (fun p => (u : ZMod p.val)))) := by
  have heq := arithmetic_roots_eq_masked
    (blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (candidateArithmeticQuotient u) (fun _ he => (mem_blockCandidates.mp he).2)
    (fun _ he => candidateArithmeticQuotient_equation hT he) hforce hactual hmasked
  unfold actualCandidateKernel
  dsimp only
  rw [heq]

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
/-- The exposed observations may determine the entire candidate family. -/
theorem primeDigit_conditional_bound {B M : ℕ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (F : BlockPrimePatterns B M → (∀ p : auxiliaryPrimes B, ZMod p.val) → ℝ)
    {K : ℝ} (hF : ∀ H, finiteExpectation (conditionalResidueMass H) (F H) ≤ K) :
    finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r) r) ≤ K := by
  let a := fun p : auxiliaryPrimes B => uniformImageMass (blockPrimeHit M p.val)
  have ha (p : auxiliaryPrimes B) : (∑ H, a p H) = 1 := by
    simp only [a,uniformImageMass_eq_push,finitePushMass_sum]
    simpa only [ZMod.card] using uniformZModMass_sum p.val
  have han : ∀ H, 0 ≤ finiteProductMass a H := by
    apply finiteProductMass_nonneg
    intro p H
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd := total_uniform_product_disintegration
    (fun p : auxiliaryPrimes B => blockPrimeHit M p.val) F
  simp only [ZMod.card] at hd
  change finiteExpectation (primeDigitMass B) (fun r => F (residuePrimePatterns r) r) =
    finiteExpectation (finiteProductMass a)
      (fun H => finiteExpectation (conditionalResidueMass H) (F H)) at hd
  rw [hd]
  exact (finiteExpectation_mono _ han hF).trans_eq
    (finiteExpectation_const _ (finiteProductMass_sum a ha) K)

theorem adaptive_masked_coefficient_probability {B L T H M N : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (I : BlockPrimePatterns B M → Finset (BlockCandidateIndex M))
    (he : ∀ S e, e ∈ I S → BlockCandidateAdmissible B L T H τ C e)
    (hcard : ∀ S, (I S).card ≤ N) :
    finiteProbability (primeDigitMass B) (fun r =>
      MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r) ≤
      24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  rw [finiteProbability_eq_indicator_mean]
  apply primeDigit_conditional_bound (fun S r => if MaskedCoefficientEvent (I S) S r then 1 else 0)
  intro S
  have h := masked_coefficient_event_bound hB hT hM hP (I S) (he S) hsize hhalf S
  rw [finiteProbability_eq_indicator_mean] at h
  exact h.trans (by gcongr; exact_mod_cast hcard S)

theorem adaptive_coefficient_digit_probability {B L T H M N : ℕ} {τ C : ℝ}
    [∀ p : auxiliaryPrimes B, NeZero p.val]
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (I : (∀ p : auxiliaryPrimes B, ZMod p.val) → Finset (BlockCandidateIndex M))
    (he : ∀ r e, e ∈ I r → BlockCandidateAdmissible B L T H τ C e)
    (hcard : ∀ r, (I r).card ≤ N) :
    finiteExpectation (primeDigitMass B) (fun r =>
      finiteProbability (primeDigitMass B) (CoefficientDigitEvent B (I r) r)) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  have hpoint r := (coefficient_digit_event_bound hB hT hM hP (I r) (he r) r).trans
    (show 12*((I r).card : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) by
        gcongr; exact_mod_cast hcard r)
  exact (finiteExpectation_mono _ (primeDigitMass_nonneg B) hpoint).trans_eq
    (finiteExpectation_const _ (primeDigitMass_sum B) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticCoefficientProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient exceptions for the actual arithmetic candidate family -/

namespace JointDickman
open Finset PublishedInputs Classical

theorem residueCandidates_arithmetic (B L T H M u : ℕ) (τ C : ℝ) :
    residueCandidates B L T H M τ C (arithmeticFirstDigits B u) =
      blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) := by
  unfold residueCandidates
  rw [residuePrimePatterns_arithmetic]
  have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
      (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
    funext (primePatternsSites_arithmetic B M u)
  rw [hs]

theorem actual_coefficient_exception_bound {B L T H M N : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B) (hTP : T ≤ auxiliaryCutoff B)
    (hcard : ∀ S : Fin M → Finset ℕ, (blockCandidates B L T H M τ C S).card ≤ N) :
    arithmeticSquareMean B (fun u => if ActualCoefficientException B L T H M τ C u then 1 else 0) ≤
      12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  let I := residueCandidates B L T H M τ C
  let F := fun r t => if CoefficientDigitEvent B (I r) r t then (1 : ℝ) else 0
  have hpoint (u : ℕ) :
      (if ActualCoefficientException B L T H M τ C u then (1 : ℝ) else 0) ≤
        F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
    by_cases hu : ActualCoefficientException B L T H M τ C u
    · have hd := arithmetic_coefficient_hit_implies_digit _ (candidateArithmeticQuotient u)
        (fun _ he => (mem_blockCandidates.mp he).2)
        (fun _ he => candidateArithmeticQuotient_equation hTP he) hu
      have he : CoefficientDigitEvent B (I (arithmeticFirstDigits B u))
          (arithmeticFirstDigits B u) (arithmeticSecondDigits B u) := by
        simpa only [I,residueCandidates_arithmetic] using hd
      simp only [F,hu,he,ite_true, if_true,le_refl]
    · simp only [hu,ite_false, if_false,F]
      split_ifs <;> norm_num
  calc
    _ ≤ arithmeticSquareMean B (fun u => F (arithmeticFirstDigits B u) (arithmeticSecondDigits B u)) := by
      apply div_le_div_of_nonneg_right (sum_le_sum (fun u _ => hpoint u))
      positivity
    _ = finiteExpectation (primeDigitMass B) (fun r => finiteProbability (primeDigitMass B)
        (CoefficientDigitEvent B (I r) r)) := by
      rw [arithmeticSquareMean,prime_square_crt_average]
      apply congrArg (finiteExpectation (primeDigitMass B))
      funext r
      exact (finiteProbability_eq_indicator_mean _ _).symm
    _ ≤ _ := adaptive_coefficient_digit_probability hB hT hM hP I
      (fun _ _ he => (mem_blockCandidates.mp he).2) (fun r => hcard _)

theorem masked_coefficient_exception_bound {B L T H M N : ℕ} {τ C : ℝ}
    (hB : 2 ≤ B) (hT : (T : ℝ) ≤ Real.exp B) (hM : (M : ℝ) ≤ Real.exp B)
    (hP : 0 < auxiliaryCutoff B)
    (hsize : ∀ p ∈ auxiliaryPrimes B, M < p)
    (hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p)
    (hcard : ∀ S : Fin M → Finset ℕ, (blockCandidates B L T H M τ C S).card ≤ N) :
    arithmeticSquareMean B (fun u => if MaskedCoefficientException B L T H M τ C u then 1 else 0) ≤
      24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B) := by
  let : ∀ p : auxiliaryPrimes B, NeZero p.val :=
    fun p => ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
  let I := fun S : BlockPrimePatterns B M => blockCandidates B L T H M τ C (primePatternsSites S)
  let F := fun r : ∀ p : auxiliaryPrimes B, ZMod p.val =>
    if MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r then (1 : ℝ) else 0
  have hF (u : ℕ) :
      (if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0) =
        F (arithmeticFirstDigits B u) := by
    have hd : arithmeticFirstDigits B u = (fun p : auxiliaryPrimes B => (u : ZMod p.val)) :=
      funext (fun (p : auxiliaryPrimes B) => primeDigits_first u)
    have hs := residueCandidates_arithmetic B L T H M u τ C
    change (if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0) =
      if MaskedCoefficientEvent (residueCandidates B L T H M τ C (arithmeticFirstDigits B u))
        (residuePrimePatterns (arithmeticFirstDigits B u)) (arithmeticFirstDigits B u) then 1 else 0
    rw [hs,residuePrimePatterns_arithmetic,hd]
    rfl
  calc
    _ = arithmeticSquareMean B (fun u => F (arithmeticFirstDigits B u)) :=
      congrArg (arithmeticSquareMean B) (funext hF)
    _ = finiteExpectation (primeDigitMass B) F := by
      rw [arithmeticSquareMean,prime_square_crt_average B (fun r _ => F r)]
      simp only [finiteExpectation_const _ (primeDigitMass_sum B)]
    _ = finiteProbability (primeDigitMass B) (fun r =>
        MaskedCoefficientEvent (I (residuePrimePatterns r)) (residuePrimePatterns r) r) :=
      (finiteProbability_eq_indicator_mean _ _).symm
    _ ≤ _ := adaptive_masked_coefficient_probability hB hT hM hP hsize hhalf I
      (fun _ _ he => (mem_blockCandidates.mp he).2) (fun _ => hcard _)

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

theorem arithmeticSquareMean_add (B : ℕ) (f g : ℕ → ℝ) :
    arithmeticSquareMean B (fun u => f u+g u) = arithmeticSquareMean B f+arithmeticSquareMean B g := by
  simp only [arithmeticSquareMean,sum_add_distrib,add_div]

theorem arithmeticSquareMean_const_mul (B : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    arithmeticSquareMean B (fun u => c*f u) = c*arithmeticSquareMean B f := by
  simp only [arithmeticSquareMean,← mul_sum,mul_div_assoc]

theorem arithmeticSquareMean_mono (B : ℕ) {f g : ℕ → ℝ} (h : ∀ u, f u ≤ g u) :
    arithmeticSquareMean B f ≤ arithmeticSquareMean B g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun u _ => h u)) (by positivity)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedConditional
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional forced-hit bound over an exposed endpoint pair -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

theorem pairForcedEvent_conditional_bound {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), (T : ℝ) ≤ Real.exp B →
      (M : ℝ) ≤ Real.exp B → ∀ (i k : Fin M),
      ∀ a : ({i,k} : Finset (Fin M)) → (auxiliaryPrimes B).powerset,
      finiteProbability (siteProductMass
        (fun _ : {s : Fin M // s ∉ ({i,k} : Finset (Fin M))} => independentPrimeSetMass B))
        (fun b => PairForcedEvent B L T H M τ C i k
          (fun s => (mergeSitePartition {i,k} a b s).val)) ≤
        (B : ℝ)^2*(M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) := by
  classical
  filter_upwards [endpointSplits_card hL hτ hτsmall,eventually_ge_atTop 2] with B hcard hB
  intro C T H M hT hM i k a
  have hP : 0 < auxiliaryCutoff B := pow_pos (by omega) 1000
  let I : Finset (Fin M) := {i,k}
  let S₁ := (a ⟨i,by simp⟩).val
  let S₂ := (a ⟨k,by simp⟩).val
  let J := pairSplitChoices B L τ C S₁ S₂
  let w := siteProductMass (fun _ : {s : Fin M // s ∉ I} => independentPrimeSetMass B)
  let Z := (M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B))
  have hZ : 0 ≤ Z := by dsimp [Z] <;> positivity
  have hJ : (J.card : ℝ) ≤ (B : ℝ)^2 := by
    have hn : J.card ≤ B*B := by
      dsimp [J,pairSplitChoices]
      rw [card_product]
      exact Nat.mul_le_mul (hcard C S₁) (hcard C S₂)
    simpa only [pow_two] using (show (J.card : ℝ) ≤ (B : ℝ)*B by exact_mod_cast hn)
  have hmerge₁ (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) :
      (mergeSitePartition I a b i).val = S₁ := by simp [mergeSitePartition,I,S₁]
  have hmerge₂ (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) :
      (mergeSitePartition I a b k).val = S₂ := by simp [mergeSitePartition,I,S₂]
  let E := fun (ab : Finset ℕ × Finset ℕ) (b : {s : Fin M // s ∉ I} → (auxiliaryPrimes B).powerset) =>
    BlockCandidateAdmissible B L T H τ C ((i,k),ab) ∧
      CandidateForcedWitness B ((i,k),ab) (fun s => (mergeSitePartition I a b s).val)
  have hprob (ab : Finset ℕ × Finset ℕ) : finiteProbability w (E ab) ≤ Z := by
    by_cases he : BlockCandidateAdmissible B L T H τ C ((i,k),ab)
    · simpa only [E,he,true_and] using forcedWitness_remaining_probability hB hT hM hP he a
    · simpa only [E,he,false_and,finiteProbability,ite_false, if_false,sum_const_zero] using hZ
  have hevent : (fun b => PairForcedEvent B L T H M τ C i k
      (fun s => (mergeSitePartition I a b s).val)) = (fun b => ∃ ab ∈ J, E ab b) := by
    funext b
    simp only [PairForcedEvent,hmerge₁,hmerge₂,J,E]
  rw [hevent]
  calc
    _ ≤ ∑ ab ∈ J, finiteProbability w (E ab) := finiteProbability_exists_mem w
      (siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)) J E
    _ ≤ ∑ _ab ∈ J, Z := sum_le_sum (fun ab _ => hprob ab)
    _ = (J.card : ℝ)*Z := by simp
    _ ≤ (B : ℝ)^2*Z := mul_le_mul_of_nonneg_right hJ hZ
    _ = _ := by dsimp [Z] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForcedProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forced occupied-prime hits in the actual random candidate list -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

open Classical in
theorem forcedCandidateHit_pair_event {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (h : ForcedCandidateHit B L T H M τ C S) :
    ∃ ik : Fin M × Fin M, PairForcedEvent B L T H M τ C ik.1 ik.2 S := by
  obtain ⟨e,he,hw⟩ := h
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  refine ⟨e.1,e.2,?_,ha,hw⟩
  simpa only [pairSplitChoices,Finset.product_eq_sprod,mem_product] using hs

open Classical in
theorem pairForcedEvent_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → ∀ (i k : Fin M),
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => PairForcedEvent B L T H M τ C i k (fun s => (S s).val)) ≤
        (B : ℝ)^2*(M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) := by
  filter_upwards [pairForcedEvent_conditional_bound hL hτ hτsmall] with B hB
  intro C T H M hT hM i k
  apply siteProduct_probability_of_conditional_bound _
    (fun _ => independentPrimeSetMass_nonneg B)
    (fun _ => independentPrimeSetMass_sum B) {i,k}
  exact hB C T H M hT hM i k

open Classical in
/-- Exposing endpoints first makes the union bound valid for the actual
candidate family, although that family depends on the random sites. -/
theorem forcedCandidateHit_probability {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B →
      finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ForcedCandidateHit B L T H M τ C (fun s => (S s).val)) ≤
        5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B) := by
  filter_upwards [pairForcedEvent_probability hL hτ hτsmall] with B hB
  intro C T H M hT hM
  let w := siteProductMass (fun _ : Fin M => independentPrimeSetMass B)
  have hw : ∀ S, 0 ≤ w S := siteProductMass_nonneg _ (fun _ => independentPrimeSetMass_nonneg B)
  calc
    _ ≤ finiteProbability w (fun S => ∃ ik : Fin M × Fin M,
        PairForcedEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) := by
      apply finiteProbability_mono w hw
      intro S hS
      exact forcedCandidateHit_pair_event hS
    _ ≤ ∑ ik : Fin M × Fin M, finiteProbability w
        (fun S => PairForcedEvent B L T H M τ C ik.1 ik.2 (fun s => (S s).val)) :=
      finiteProbability_union_le w hw _
    _ ≤ ∑ _ik : Fin M × Fin M, (B : ℝ)^2*(M : ℝ)*(5*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :=
      sum_le_sum (fun ik _ => hB C T H M hT hM ik.1 ik.2)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticForcedCost
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted cost of forced third-site hits in the arithmetic block -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem blockPatternEquiv_symm_sites {B M : ℕ}
    (S : Fin M → (auxiliaryPrimes B).powerset) :
    primePatternsSites ((blockPatternEquiv B M).symm S) = (fun i => (S i).val) := by
  have h := (blockPatternEquiv B M).apply_symm_apply S
  funext i
  exact congrArg Subtype.val (congrFun h i)

theorem arithmetic_forced_cost {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      (T : ℝ) ≤ Real.exp B → (M : ℝ) ≤ Real.exp B → M ≤ B^2 →
      arithmeticSquareMean B (fun u => (B : ℝ)^10 *
        (if ForcedCandidateHit B L T H M τ C
          (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)) ≤
      (B : ℝ)^10 * (5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ) := by
  filter_upwards [forcedCandidateHit_probability hL hτ hτsmall,eventually_ge_atTop 2]
    with B hprob hB
  intro C T H M hT hMexp hM
  let F := fun S : BlockPrimePatterns B M => (B : ℝ)^10 *
    (if ForcedCandidateHit B L T H M τ C (primePatternsSites S) then (1 : ℝ) else 0)
  have hcap S : |F S| ≤ 1*(B : ℝ)^10 := by
    dsimp only [F]
    split_ifs <;> simp [abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℝ) B) 10)]
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).1
  have hc := arithmeticSquareMean_pattern_comparison (by omega : 1 < B) hM hsize F
    (C := 1) (by norm_num) hcap
  have hleft : arithmeticSquareMean B (fun u => F (arithmeticPrimePatterns B M u)) =
      arithmeticSquareMean B (fun u => (B : ℝ)^10 *
        (if ForcedCandidateHit B L T H M τ C
          (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)) := by
    apply congrArg (arithmeticSquareMean B)
    funext u
    have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
        (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
      funext (primePatternsSites_arithmetic B M u)
    dsimp only [F]
    rw [hs]
  have hright : finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
      (fun S => F ((blockPatternEquiv B M).symm S)) =
      (B : ℝ)^10 * finiteProbability (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
        (fun S => ForcedCandidateHit B L T H M τ C (fun i => (S i).val)) := by
    simp only [F,blockPatternEquiv_symm_sites,finiteProbability_eq_indicator_mean,
      finiteExpectation_const_mul]
  rw [hleft,hright] at hc
  have hp := mul_le_mul_of_nonneg_left (hprob C T H M hT hMexp)
    (pow_nonneg (Nat.cast_nonneg (α := ℝ) B) 10)
  have hu := (le_abs_self _).trans hc
  simp only [mul_one] at hu
  linarith only [hp,hu]

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem candidate_root_error_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < M → M ≤ B^2 →
      ∀ (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) → ∀ R,
      |kernelCutNorm (fun i k => independentCandidateKernel B L T H M τ C S χ R i k-
        latentCandidateKernel B L T H M τ C S χ i k)| ≤ (B : ℝ)^10 := by
  filter_upwards [candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2]
    with B hmass hB
  intro C T H M hM0 hM S χ hχ R
  obtain ⟨hlat,hind⟩ := hmass C T H M S χ hχ
  let K := fun i k => independentCandidateKernel B L T H M τ C S χ R i k-
    latentCandidateKernel B L T H M τ C S χ i k
  have habs : (∑ i, ∑ k, |K i k|) ≤ 4*(M : ℝ)^2*(B : ℝ)^2 :=
    (kernel_difference_absolute_mass _ _).trans (by linarith [hind R,hlat])
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
  have hm2 : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hb2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hb1 : (1 : ℝ) ≤ B := by linarith
  have hb4 : (4 : ℝ) ≤ (B : ℝ)^4 := by
    have hsq : (4 : ℝ) ≤ (B : ℝ)^2 := by nlinarith
    exact hsq.trans (pow_le_pow_right₀ hb1 (by norm_num : 2 ≤ 4))
  rw [abs_of_nonneg (kernelCutNorm_nonneg _)]
  calc
    kernelCutNorm K ≤ kernelAbsoluteMass K := kernelCutNorm_le_absolute_mass K
    _ ≤ (4*(M : ℝ)^2*(B : ℝ)^2)/(M : ℝ) := by
      simpa only [kernelAbsoluteMass,Fintype.card_fin] using
        div_le_div_of_nonneg_right habs (Nat.cast_nonneg M)
    _ ≤ 4*(M : ℝ)^2*(B : ℝ)^2 := div_le_self (by positivity) hm1
    _ ≤ 4*((B : ℝ)^2)^2*(B : ℝ)^2 := by gcongr
    _ = 4*(B : ℝ)^6 := by ring
    _ ≤ (B : ℝ)^4*(B : ℝ)^6 := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = (B : ℝ)^10 := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionedRootErrorLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditioned root-model error survives the polynomial weight bound -/

namespace JointDickman
open Filter
open scoped Topology

theorem conditionedRootError_weighted_tendsto :
    Tendsto (fun B : ℕ => (B : ℝ)^10*conditionedRootError B) atTop (𝓝 0) := by
  have hp := (polynomial_div_primeCutoff_tendsto_zero (k := 29) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have he := ((isLittleO_pow_exp_pos_mul_atTop 18 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop
  have he' : Tendsto (fun B : ℕ => (B : ℝ)^18/Real.exp B) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_mul] using he
  have hp' : Tendsto (fun B : ℕ => (B : ℝ)^29/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using hp
  have hh := (hp'.const_mul 214).add (he'.const_mul 2)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [] with B
  unfold conditionedRootError
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualArithmeticFluctuation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the root-identification exceptions from the arithmetic kernel -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem actualCandidateCutError_eq_masked {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hf : ¬ ForcedCandidateHit B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))))
    (ha : ¬ ActualCoefficientException B L T H M τ C u)
    (hm : ¬ MaskedCoefficientException B L T H M τ C u) :
    actualCandidateCutError B L T H M τ C χ u =
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u) := by
  have hk := actualCandidateKernel_eq_masked hT χ
    (fun e he hw => hf ⟨e,he,hw⟩) ha hm
  unfold actualCandidateCutError
  rw [hk]
  unfold maskedDigitCutError patternRootCutError
  rw [residuePrimePatterns_arithmetic]
  have hs : primePatternsSites (arithmeticPrimePatterns B M u) =
      (fun i => coefficientPrimeSet B (u+(i.val+1))) :=
    funext (primePatternsSites_arithmetic B M u)
  rw [hs]
  have hd : arithmeticFirstDigits B u = (fun p : auxiliaryPrimes B => (u : ZMod p.val)) := by
    funext p
    let : NeZero p.val := ⟨(auxiliaryPrimes_prime B p.val p.property).ne_zero⟩
    exact primeDigits_first u
  rw [hd]

theorem actualCandidateCutError_pointwise {B L T H M u : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ)
    (hcap : actualCandidateCutError B L T H M τ C χ u ≤ (B : ℝ)^10) :
    actualCandidateCutError B L T H M τ C χ u ≤
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u)+
        (B : ℝ)^10 *
          ((if ForcedCandidateHit B L T H M τ C
            (fun i => coefficientPrimeSet B (u+(i.val+1))) then 1 else 0)+
           (if ActualCoefficientException B L T H M τ C u then 1 else 0)+
           (if MaskedCoefficientException B L T H M τ C u then 1 else 0)) := by
  have hg : 0 ≤ maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u) :=
    kernelCutNorm_nonneg _
  have hQ : 0 ≤ (B : ℝ)^10 := pow_nonneg (Nat.cast_nonneg B) _
  by_cases hf : ForcedCandidateHit B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))
  · simp only [hf,ite_true, if_true]
    split_ifs <;> nlinarith
  · by_cases ha : ActualCoefficientException B L T H M τ C u
    · simp only [hf,ha,ite_false, if_false,ite_true, if_true]
      split_ifs <;> nlinarith
    · by_cases hm : MaskedCoefficientException B L T H M τ C u
      · simp only [hf,ha,hm,ite_false, if_false,ite_true, if_true]
        nlinarith
      · rw [actualCandidateCutError_eq_masked hT χ hf ha hm]
        simp only [hf,ha,hm,ite_false, if_false,mul_zero,add_zero,le_refl]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientErrorScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient-prime exclusions survive the graph's polynomial weight cap -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficient_error_polynomial {B N : ℕ} (hB : 2 ≤ B) (hN : N ≤ B^6)
    {a b : ℝ}
    (ha : a ≤ 12*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B))
    (hb : b ≤ 24*(N : ℝ)*(B : ℝ)/(Real.log 2*auxiliaryCutoff B)) :
    (B : ℝ)^10*(a+b) ≤ coefficientRootError B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (show 0 < auxiliaryCutoff B from pow_pos (by omega) 1000)
  have hNr : (N : ℝ) ≤ (B : ℝ)^6 := by exact_mod_cast hN
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by have h := Real.log_two_gt_d9; linarith
  have hr : 1/(Real.log 2*auxiliaryCutoff B) ≤ 2/(auxiliaryCutoff B : ℝ) := by
    have hm : (auxiliaryCutoff B : ℝ)/2 ≤ Real.log 2*auxiliaryCutoff B := by nlinarith
    exact (one_div_le_one_div_of_le (by positivity) hm).trans_eq (by ring)
  calc
    _ ≤ (B : ℝ)^10*(12*(N : ℝ)*B/(Real.log 2*auxiliaryCutoff B)+
        24*(N : ℝ)*B/(Real.log 2*auxiliaryCutoff B)) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
    _ = 36*(B : ℝ)^10*(N : ℝ)*B*(1/(Real.log 2*auxiliaryCutoff B)) := by ring
    _ ≤ 36*(B : ℝ)^10*((B : ℝ)^6)*B*(2/(auxiliaryCutoff B : ℝ)) := by gcongr
    _ = coefficientRootError B := by unfold coefficientRootError; ring

theorem coefficientRootError_tendsto :
    Tendsto coefficientRootError atTop (𝓝 0) := by
  have h := (polynomial_div_primeCutoff_tendsto_zero (k := 17) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun B : ℕ => (B : ℝ)^17/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using h
  have ht := hh.const_mul 72
  simp only [mul_zero] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext B
  unfold coefficientRootError
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualArithmeticMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing arithmetic candidate fluctuations after all root exceptions -/

namespace JointDickman
open Finset Filter PublishedInputs Classical
open scoped Topology

theorem actual_arithmetic_fluctuation_bound
    (hFord : FordUpperSieveInput) (hMertens : PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
      0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤
        K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+
        coefficientRootError B+
        (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+4/(B : ℝ) := by
  obtain ⟨K,hK,hmask⟩ := masked_arithmetic_fluctuation_bound_jd hFord hMertens hL hτ hτsmall
  refine ⟨K,hK,?_⟩
  filter_upwards [hmask,arithmetic_forced_cost hL hτ hτsmall,
    candidate_root_error_cap hL hτ hτsmall,blockCandidates_card hL hτ hτsmall,
    eventually_ge_atTop 2] with B hmask hforced hcap hcount hB
  intro C T H M hT hTs hTP hM0 hM hMexp χ hχ
  have hTe : (T : ℝ) ≤ Real.exp B := hTs.trans (Real.exp_le_exp.mpr (by
    have hBr := Nat.cast_nonneg (α := ℝ) B
    nlinarith))
  have hP : 0 < auxiliaryCutoff B := pow_pos (by omega) _
  have hsize : ∀ p ∈ auxiliaryPrimes B, M < p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).1
  have hhalf : ∀ p ∈ auxiliaryPrimes B, 2*M ≤ p :=
    fun _ hp => (block_prime_twice_sites hB hM hp).2
  have hN : M^2*B^2 ≤ B^6 := by
    calc
      _ ≤ (B^2)^2*B^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
      _ = _ := by ring
  let fa := fun u => if ActualCoefficientException B L T H M τ C u then (1 : ℝ) else 0
  let fm := fun u => if MaskedCoefficientException B L T H M τ C u then (1 : ℝ) else 0
  let ff := fun u => if ForcedCandidateHit B L T H M τ C
    (fun i => coefficientPrimeSet B (u+(i.val+1))) then (1 : ℝ) else 0
  have ha := actual_coefficient_exception_bound hB hTe hMexp hP hTP
    (fun S => hcount C T H M S)
  have hm := masked_coefficient_exception_bound hB hTe hMexp hP hsize hhalf
    (fun S => hcount C T H M S)
  have hcoeff : (B : ℝ)^10*(arithmeticSquareMean B fa+arithmeticSquareMean B fm) ≤
      coefficientRootError B := coefficient_error_polynomial hB hN ha hm
  have hpoint u : actualCandidateCutError B L T H M τ C χ u ≤
      maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u)+
        (B : ℝ)^10*(ff u+fa u+fm u) := by
    apply actualCandidateCutError_pointwise hTP χ
    have hc : |actualCandidateCutError B L T H M τ C χ u| ≤ (B : ℝ)^10 :=
      hcap C T H M hM0 hM (fun i => coefficientPrimeSet B (u+(i.val+1))) χ hχ
        (primeSiteTranspose _ (auxiliaryPrimes B)
          (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u)))
    exact (le_abs_self _).trans hc
  have he := arithmeticSquareMean_mono B hpoint
  rw [arithmeticSquareMean_add,arithmeticSquareMean_const_mul,
    arithmeticSquareMean_add,arithmeticSquareMean_add] at he
  have hfo := hforced C T H M hTe hMexp hM
  rw [arithmeticSquareMean_const_mul] at hfo
  have hma := hmask C T H M hT hTs hM0 hM hMexp χ hχ
  change (B : ℝ)^10*arithmeticSquareMean B ff ≤
    (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ) at hfo
  calc
    _ ≤ arithmeticSquareMean B (fun u => maskedDigitCutError B L T H M τ C χ (arithmeticFirstDigits B u))+
        (B : ℝ)^10*arithmeticSquareMean B ff+
        (B : ℝ)^10*(arithmeticSquareMean B fa+arithmeticSquareMean B fm) := he.trans_eq (by ring)
    _ ≤ (K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+2/(B : ℝ))+
        ((B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B))+2/(B : ℝ))+
        coefficientRootError B := add_le_add (add_le_add hma hfo) hcoeff
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActualArithmeticLimit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform decay of the arithmetic candidate root fluctuations -/

namespace JointDickman
open Filter
open scoped Topology

theorem arithmeticFluctuationError_tendsto (K : ℝ) :
    Tendsto (arithmeticFluctuationError K) atTop (𝓝 0) := by
  have hr := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7/200)).comp
    tendsto_natCast_atTop_atTop
  have hp := (polynomial_div_primeCutoff_tendsto_zero (k := 19) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hp' : Tendsto (fun B : ℕ => (B : ℝ)^19/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using hp
  have hi : Tendsto (fun B : ℕ => 4/(B : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht := ((((hr.const_mul K).add conditionedRootError_weighted_tendsto).add
    coefficientRootError_tendsto).add (hp'.const_mul 10)).add hi
  simp only [mul_zero,add_zero] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext B
  unfold arithmeticFluctuationError
  simp only [Function.comp_def]
  ring

theorem forced_cost_polynomial {B M : ℕ} (hB : 2 ≤ B) (hM : M ≤ B^2) :
    (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B)) ≤
      10*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (show 0 < auxiliaryCutoff B from pow_pos (by omega) _)
  have hMr : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by have h := Real.log_two_gt_d9; linarith
  have hinv : 1/(Real.log 2*auxiliaryCutoff B) ≤ 2/(auxiliaryCutoff B : ℝ) := by
    have hh : (auxiliaryCutoff B : ℝ)/2 ≤ Real.log 2*auxiliaryCutoff B := by nlinarith
    exact (one_div_le_one_div_of_le (by positivity) hh).trans_eq (by ring)
  calc
    _ = 5*(B : ℝ)^10*(M : ℝ)^3*(B : ℝ)^3*(1/(Real.log 2*auxiliaryCutoff B)) := by ring
    _ ≤ 5*(B : ℝ)^10*((B : ℝ)^2)^3*(B : ℝ)^3*(2/(auxiliaryCutoff B : ℝ)) := by gcongr
    _ = _ := by ring

theorem actual_arithmetic_fluctuation_decay
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
          arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤ E B := by
  obtain ⟨K,_,hbound⟩ := actual_arithmetic_fluctuation_bound hFord hMertens hL hτ hτsmall
  refine ⟨arithmeticFluctuationError K,arithmeticFluctuationError_tendsto K,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with B hbound hB
  intro C T H M hT hTs hTP hM0 hM hMexp χ hχ
  exact (hbound C T H M hT hTs hTP hM0 hM hMexp χ hχ).trans
    (by unfold arithmeticFluctuationError; linarith only [forced_cost_polynomial hB hM])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphPointCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A pointwise graph bound valid even on site-square exceptions -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem graphTripleWeight_le_one {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T n : ℕ) (g : GraphCoefficientTriple),
      graphTripleWeight B L τ C T g n/(B : ℝ) ≤ 1 := by
  filter_upwards [six_regular_weights_small hL hτ hτsmall,eventually_ge_atTop 1] with B hB hB1
  intro C T n g
  let a := ∏ p ∈ g.2.1, p
  let b := ∏ p ∈ g.2.2, p
  let c := ∏ p ∈ g.1, p
  let j := graphTripleLag g
  let W := fun d m => regularCoefficientWeight B L τ C d*arithmeticResidueWeight B L τ C m
  have hW d m : 0 ≤ W d m := mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
    (regularResidueWeight_nonneg _ _ _ _ _)
  have hc : amplificationOuterWeight B c*W c (divisorEdgeInverse a b c n) ≤
      W c (divisorEdgeInverse a b c n) :=
    mul_le_of_le_one_left (hW _ _) (amplificationBump_bounds _).2
  have ha : W a (n/b)*amplificationInnerWeight T a c ≤ W a (n/b) :=
    mul_le_of_le_one_right (hW _ _) (amplificationBump_bounds _).2
  have hb : W b (((n : ℤ)+j).toNat/a)*amplificationInnerWeight T b c ≤ W b (((n : ℤ)+j).toNat/a) :=
    mul_le_of_le_one_right (hW _ _) (amplificationBump_bounds _).2
  have hp : graphTripleWeight B L τ C T g n ≤
      W c (divisorEdgeInverse a b c n)*W a (n/b)*W b (((n : ℤ)+j).toNat/a) := by
    change (amplificationOuterWeight B c*regularCoefficientWeight B L τ C c*
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n))*
      (W a (n/b)*amplificationInnerWeight T a c)*
      (W b (((n : ℤ)+j).toNat/a)*amplificationInnerWeight T b c) ≤ _
    rw [mul_assoc (amplificationOuterWeight B c)]
    exact mul_le_mul (mul_le_mul hc ha (mul_nonneg (hW _ _) (amplificationBump_bounds _).1)
      (hW _ _)) hb (mul_nonneg (hW _ _) (amplificationBump_bounds _).1)
        (mul_nonneg (hW _ _) (hW _ _))
  calc
    _ ≤ (W c (divisorEdgeInverse a b c n)*W a (n/b)*W b (((n : ℤ)+j).toNat/a))/(B : ℝ) :=
      div_le_div_of_nonneg_right hp (Nat.cast_nonneg B)
    _ ≤ (B : ℝ)^(-(7/100 : ℝ)) := hB C c a b _ _ _
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hB1) (by norm_num)

theorem graph_endpoint_prime_subsets {B T M N u : ℕ} {i k : Fin M}
    (hik : i < k) {g : GraphCoefficientTriple} (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g) :
    g.2.2 ⊆ coefficientPrimeSet B (u+(i.val+1)) ∧
      g.2.1 ⊆ coefficientPrimeSet B (u+(k.val+1)) := by
  have hs := graphTriple_subsets hg
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hadiv : (∏ p ∈ g.2.1, p) ∣ u+(k.val+1) := by
    have h := (mem_filter.mp hn).2.2.1
    have he : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g) = (u+(k.val+1) : ℕ) := by
      rw [hlag,Int.ofNat_sub hik.le]
      push_cast
      ring
    rw [he] at h
    exact_mod_cast h
  exact ⟨(primeProduct_dvd_site_iff hs.2.2).mp hbdiv,
    (primeProduct_dvd_site_iff hs.2.1).mp hadiv⟩

theorem graph_regular_endpoint_count {B L T M N u : ℕ} {τ C : ℝ}
    (hcount : ∀ S R : Finset ℕ, RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
      2^(S ∪ R).card ≤ B)
    {i k : Fin M} (hik : i < k) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T)
    (hlag : graphTripleLag g = ((k.val-i.val : ℕ) : ℤ))
    (hn : u+(i.val+1) ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0) :
    2^(coefficientPrimeSet B (u+(i.val+1))).card ≤ B ∧
      2^(coefficientPrimeSet B (u+(k.val+1))).card ≤ B := by
  have hs := graphTriple_subsets hg
  have hr := graphTripleWeight_nonzero_regular hg hw
  have hbdiv : (∏ p ∈ g.2.2, p) ∣ u+(i.val+1) := (mem_filter.mp hn).2.1
  have hshift : (((u+(i.val+1) : ℕ) : ℤ)+graphTripleLag g).toNat = u+(k.val+1) := by
    rw [hlag,Int.ofNat_sub hik.le]
    omega
  have hsub := graph_endpoint_prime_subsets hik hg hlag hn
  have hadiv := (primeProduct_dvd_site_iff hs.2.1).mpr hsub.2
  have hlo := hcount g.2.2 _ hr.2.2.1 hr.2.2.2.1
  have hhi := hcount g.2.1 _ hr.2.1 hr.2.2.2.2
  rw [coefficientPrimeSet_union_quotient hs.2.2 hbdiv] at hlo
  rw [hshift,coefficientPrimeSet_union_quotient hs.2.1 hadiv] at hhi
  exact ⟨hlo,hhi⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphCandidateCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial graph multiplicity without excluding site squares -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem rawArithmeticGraphKernel_active (B L T N : ℕ) (τ C : ℝ) (j : ℤ) (n : ℕ) :
    rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) =
      ∑ g ∈ activeGraphTriples B L T N τ C j n, graphTripleWeight B L τ C T g n/(B : ℝ) := by
  unfold rawArithmeticGraphKernel activeGraphTriples
  rw [sum_div,sum_filter]
  apply sum_congr rfl
  intro g _
  by_cases hc : graphTripleLag g = j ∧ n ∈ graphTripleEdges N g
  · by_cases hw : graphTripleWeight B L τ C T g n = 0
    · simp [hc,hw]
    · simp [hc.1,hc.2,hw]
  · have hn : ¬ (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g ∧
        graphTripleWeight B L τ C T g n ≠ 0) := fun h => hc ⟨h.1,h.2.1⟩
    simp [hc,hn]

theorem activeGraphTriples_card {B L T M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T)
    (hcount : ∀ S R : Finset ℕ, RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
      2^(S ∪ R).card ≤ B)
    {i k : Fin M} (hik : i < k) :
    (activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))).card ≤ B^2 := by
  let G := activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))
  have hg (g : GraphCoefficientTriple) (h : g ∈ G) :
      g ∈ arithmeticGraphTriples B T ∧ graphTripleLag g = ((k.val-i.val : ℕ) : ℤ) ∧
      u+(i.val+1) ∈ graphTripleEdges N g ∧ graphTripleWeight B L τ C T g (u+(i.val+1)) ≠ 0 :=
    mem_filter.mp h
  change G.card ≤ B^2
  by_cases hne : G.Nonempty
  · obtain ⟨g0,hg0⟩ := hne
    obtain ⟨h0,hj0,hn0,hw0⟩ := hg g0 hg0
    have hcounts := graph_regular_endpoint_count hcount hik h0 hj0 hn0 hw0
    let S := (coefficientPrimeSet B (u+(i.val+1))).powerset ×ˢ
      (coefficientPrimeSet B (u+(k.val+1))).powerset
    have hmap : ∀ g ∈ G, (g.2.2,g.2.1) ∈ S := by
      intro g h
      obtain ⟨hgg,hj,hn,_⟩ := hg g h
      have hs := graph_endpoint_prime_subsets hik hgg hj hn
      exact mem_product.mpr ⟨mem_powerset.mpr hs.1,mem_powerset.mpr hs.2⟩
    have hinj : (G : Set GraphCoefficientTriple).InjOn (fun g => (g.2.2,g.2.1)) := by
      intro g h g' h' heq
      obtain ⟨hgg,hj,_,hw⟩ := hg g h
      obtain ⟨hgg',hj',_,hw'⟩ := hg g' h'
      have hr := graphBlockCandidate_roundtrip hik (graphTripleWeight_nonzero_supported hB hT τ C hgg hj hw)
      have hr' := graphBlockCandidate_roundtrip hik (graphTripleWeight_nonzero_supported hB hT τ C hgg' hj' hw')
      have he : graphBlockCandidate i k g = graphBlockCandidate i k g' := Prod.ext rfl heq
      exact hr.symm.trans ((congrArg (candidateGraphTriple B) he).trans hr')
    calc
      G.card ≤ S.card := card_le_card_of_injOn _ hmap hinj
      _ = 2^(coefficientPrimeSet B (u+(i.val+1))).card *
          2^(coefficientPrimeSet B (u+(k.val+1))).card := by simp [S]
      _ ≤ B*B := Nat.mul_le_mul hcounts.1 hcounts.2
      _ = B^2 := by ring
  · simp only [not_nonempty_iff_eq_empty.mp hne,card_empty]
    exact Nat.zero_le _

theorem rawArithmeticGraphKernel_forward_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T M N u : ℕ), 0 < T →
      ∀ (i k : Fin M), i < k →
      rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))/(B : ℝ) ≤
        (B : ℝ)^2 := by
  filter_upwards [regular_endpoint_subset_count hL hτ hτsmall,
    graphTripleWeight_le_one hL hτ hτsmall,eventually_gt_atTop 0] with B hcount hweight hB
  intro C T M N u hT i k hik
  rw [rawArithmeticGraphKernel_active]
  calc
    _ ≤ ∑ _g ∈ activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1)), (1 : ℝ) :=
      sum_le_sum (fun g _ => hweight C T _ g)
    _ = ((activeGraphTriples B L T N τ C ((k.val-i.val : ℕ) : ℤ) (u+(i.val+1))).card : ℝ) := by simp
    _ ≤ (B : ℝ)^2 := by exact_mod_cast activeGraphTriples_card hB hT (hcount C) hik

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphLagSwap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing a coefficient representation reverses its lag -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem graphTripleSwap_involutive : Function.Involutive graphTripleSwap := fun _ => rfl

theorem divisor_lag_coprime_swap {a b c : ℕ} {j : ℤ}
    (he : (a : ℤ)-b = j*c) (ha : a.Coprime j.natAbs) : b.Coprime j.natAbs := by
  apply Nat.coprime_of_dvd'
  intro p _ hpb hpj
  have hpj' : (p : ℤ) ∣ j := Int.natCast_dvd.mpr hpj
  have hpb' : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hpb
  have hd := dvd_add hpb' (dvd_mul_of_dvd_left hpj' (c : ℤ))
  have hpa' : (p : ℤ) ∣ (a : ℤ) := by
    have hae : (a : ℤ) = b+j*c := by linarith
    rwa [← hae] at hd
  have hpa : p ∣ a := by exact_mod_cast hpa'
  exact Nat.dvd_one.mpr (Nat.eq_one_of_dvd_coprimes ha hpa hpj)

theorem graphTripleSwap_lag {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleLag (graphTripleSwap i) = -graphTripleLag i := by
  classical
  have hs := graphTriple_subsets hi
  have hc : (∏ p ∈ i.1, p : ℕ) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).ne_zero)
  have he := (mem_filter.mp hi).2.2.2.2.1
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  have hflip : ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      (-graphTripleLag i)*(∏ p ∈ i.1, p : ℕ) := by linarith
  change (((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ)) /
      (∏ p ∈ i.1, p : ℕ) = -graphTripleLag i
  rw [hflip, Int.mul_ediv_cancel _ (by exact_mod_cast hc)]

theorem graphTripleSwap_mem {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) : graphTripleSwap i ∈ arithmeticGraphTriples B T := by
  classical
  have hs := graphTriple_subsets hi
  have hg := (mem_filter.mp hi).2
  have hlag := graphTripleSwap_lag hi
  apply mem_filter.mpr
  refine ⟨mem_product.mpr ⟨mem_powerset.mpr hs.1,
    mem_product.mpr ⟨mem_powerset.mpr hs.2.2,mem_powerset.mpr hs.2.1⟩⟩,?_⟩
  change i.2.2 ≠ i.2.1 ∧ graphTripleLag (graphTripleSwap i) ≠ 0 ∧
    (graphTripleLag (graphTripleSwap i)).natAbs < T ∧
    ((∏ p ∈ i.2.2, p : ℕ) : ℤ)-(∏ p ∈ i.2.1, p : ℕ) =
      graphTripleLag (graphTripleSwap i)*(∏ p ∈ i.1, p : ℕ) ∧
    (∏ p ∈ i.2.2, p).Coprime (graphTripleLag (graphTripleSwap i)).natAbs
  rw [hlag, Int.natAbs_neg, neg_ne_zero]
  refine ⟨Ne.symm hg.1,hg.2.1,hg.2.2.1,?_,?_⟩
  · have he := hg.2.2.2.1
    change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
      graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
    linarith
  · exact divisor_lag_coprime_swap hg.2.2.2.1 hg.2.2.2.2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgeSwap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing an arithmetic edge preserves its multiplier and weight -/

namespace JointDickman
open Finset Classical

theorem divisorEdge_swap {a b c N n : ℕ} {j : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (hn : n ∈ divisorEdgeNew a b c N j) :
    ((n : ℤ)+j).toNat ∈ divisorEdgeNew b a c N (-j) ∧
      divisorEdgeInverse b a c ((n : ℤ)+j).toNat = divisorEdgeInverse a b c n := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  have he' : (b : ℤ)-a = (-j)*c := by linarith
  have hm' : divisorEdgeInverse a b c n ∈ divisorEdgeOld b a c N := by
    simpa only [divisorEdgeOld,mem_filter,mem_range,and_assoc,and_left_comm,and_comm] using hm
  have hends := natural_divisor_edge_endpoints hc (mem_filter.mp hm).2.2.2.1
    (mem_filter.mp hm).2.2.2.2 he
  rw [hback] at hends
  have hends' : ((n : ℤ)+j).toNat = a*((b*divisorEdgeInverse a b c n+1)/c) := by
    rw [hends,Int.toNat_natCast]
  rw [hends']
  exact divisorEdge_forward_mem hb ha hc he' hm'

theorem graphTripleSwap_edge {B T N n : ℕ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (hn : n ∈ graphTripleEdges N g) :
    ((n : ℤ)+graphTripleLag g).toNat ∈ graphTripleEdges N (graphTripleSwap g) ∧
      divisorEdgeInverse (∏ p ∈ g.2.2, p) (∏ p ∈ g.2.1, p) (∏ p ∈ g.1, p)
        ((n : ℤ)+graphTripleLag g).toNat =
      divisorEdgeInverse (∏ p ∈ g.2.1, p) (∏ p ∈ g.2.2, p) (∏ p ∈ g.1, p) n := by
  have hs := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hb : 0 < ∏ p ∈ g.2.2, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.2 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have h := divisorEdge_swap ha hb hc hadm.2.2.2.1 hadm.2.2.2.2 hn
  change ((n : ℤ)+graphTripleLag g).toNat ∈ divisorEdgeNew
    (∏ p ∈ g.2.2, p) (∏ p ∈ g.2.1, p) (∏ p ∈ g.1, p) N (graphTripleLag (graphTripleSwap g)) ∧ _
  rw [graphTripleSwap_lag hg]
  exact h

theorem graphTripleSwap_weight {B L T N n : ℕ} {τ C : ℝ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (hn : n ∈ graphTripleEdges N g) :
    graphTripleWeight B L τ C T (graphTripleSwap g) ((n : ℤ)+graphTripleLag g).toNat =
      graphTripleWeight B L τ C T g n := by
  have hs := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.1 hp)).pos)
  have hb : 0 < ∏ p ∈ g.2.2, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.2.2 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hs.1 hp)).pos)
  have hadm := (mem_filter.mp hg).2
  have hswap := graphTripleSwap_edge hg hn
  have he' : ((∏ p ∈ g.2.2, p : ℕ) : ℤ)-(∏ p ∈ g.2.1, p) =
      (-graphTripleLag g)*(∏ p ∈ g.1, p) := by
    have he := hadm.2.2.2.1
    change ((∏ p ∈ g.2.1, p : ℕ) : ℤ)-(∏ p ∈ g.2.2, p) =
      graphTripleLag g*(∏ p ∈ g.1, p) at he
    linarith
  have hcop := divisor_lag_coprime_swap hadm.2.2.2.1 hadm.2.2.2.2
  have hw := firstFormPairWeight_graph (B := B) (L := L) τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    ha hb hc hadm.2.2.2.1 hadm.2.2.2.2 hn
  have hw' := firstFormPairWeight_graph (B := B) (L := L) τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    hb ha hc he' (by simpa only [Int.natAbs_neg,graphTripleLag] using hcop)
    (show ((n : ℤ)+graphTripleLag g).toNat ∈ divisorEdgeNew _ _ _ _ (-graphTripleLag g) from by
      have hh := hswap.1
      change _ ∈ divisorEdgeNew _ _ _ _ (graphTripleLag (graphTripleSwap g)) at hh
      rwa [graphTripleSwap_lag hg] at hh)
  unfold graphTripleWeight
  rw [graphTripleSwap_lag hg]
  change arithmeticGraphPairWeight B L τ C _ _ _ _ _ (-graphTripleLag g) _ = _
  dsimp only [graphTripleSwap]
  dsimp only [graphTripleLag] at *
  rw [← hw',← hw,hswap.2]
  unfold firstFormPairWeight
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticGraphSymmetry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetry of the original arithmetic graph at its two endpoints -/

namespace JointDickman
open Finset Classical

theorem graphTripleSwap_condition {B T N n n' : ℕ} {j : ℤ} {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (he : (n : ℤ)+j = n') :
    (graphTripleLag (graphTripleSwap g) = -j ∧ n' ∈ graphTripleEdges N (graphTripleSwap g)) ↔
      (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g) := by
  rw [graphTripleSwap_lag hg,neg_inj]
  constructor
  · rintro ⟨hlag,hn⟩
    have hs := (graphTripleSwap_edge (graphTripleSwap_mem hg) hn).1
    have hback : ((n' : ℤ)+graphTripleLag (graphTripleSwap g)).toNat = n := by
      rw [graphTripleSwap_lag hg,hlag]
      omega
    rw [hback,graphTripleSwap_involutive g] at hs
    exact ⟨hlag,hs⟩
  · rintro ⟨hlag,hn⟩
    have hs := (graphTripleSwap_edge hg hn).1
    have hforward : ((n : ℤ)+graphTripleLag g).toNat = n' := by rw [hlag,he,Int.toNat_natCast]
    rw [hforward] at hs
    exact ⟨hlag,hs⟩

theorem rawArithmeticGraphKernel_reverse {B L T N n n' : ℕ} {τ C : ℝ} {j : ℤ}
    (he : (n : ℤ)+j = n') :
    rawArithmeticGraphKernel B L τ C T N (-j) n' =
      rawArithmeticGraphKernel B L τ C T N j n := by
  unfold rawArithmeticGraphKernel
  symm
  apply sum_bij (fun g _ => graphTripleSwap g)
  · intro g hg
    exact graphTripleSwap_mem hg
  · intro g _ g' _ heq
    exact graphTripleSwap_involutive.injective heq
  · intro g hg
    exact ⟨graphTripleSwap g,graphTripleSwap_mem hg,graphTripleSwap_involutive g⟩
  · intro g hg
    have hc := graphTripleSwap_condition (N := N) hg he
    by_cases hh : graphTripleLag g = j ∧ n ∈ graphTripleEdges N g
    · have hs := hc.mpr hh
      rw [ite_eq_left hh,ite_eq_left hs]
      have hw := graphTripleSwap_weight (L := L) (τ := τ) (C := C) hg hh.2
      have hn : ((n : ℤ)+graphTripleLag g).toNat = n' := by rw [hh.1,he,Int.toNat_natCast]
      rw [hn] at hw
      exact hw.symm
    · rw [ite_eq_right hh,ite_eq_right (fun h => hh (hc.mp h))]

theorem rawArithmeticGraphKernel_block_reverse {B L T M N u : ℕ} {τ C : ℝ}
    (i k : Fin M) :
    rawArithmeticGraphKernel B L τ C T N ((i.val : ℤ)-k.val) (u+(k.val+1)) =
      rawArithmeticGraphKernel B L τ C T N ((k.val : ℤ)-i.val) (u+(i.val+1)) := by
  have he : ((u+(i.val+1) : ℕ) : ℤ)+((k.val : ℤ)-i.val) = (u+(k.val+1) : ℕ) := by
    push_cast
    ring
  simpa only [neg_sub] using rawArithmeticGraphKernel_reverse (B := B) (L := L)
    (T := T) (N := N) (τ := τ) (C := C) he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateArithmeticPeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-square periodicity of the actual candidate quotient data -/

namespace JointDickman
open Finset Classical

theorem affine_quotient_modEq_prime {a b c m m' n n' p : ℕ}
    (hp : p.Prime) (hsq : Squarefree (a*b))
    (he : a*b*m+b = c*n) (he' : a*b*m'+b = c*n')
    (hn : n ≡ n' [MOD p^2]) : p ∣ m ↔ p ∣ m' := by
  have hab : a*b*m ≡ a*b*m' [MOD p^2] :=
    Nat.ModEq.add_right_cancel' b (by simpa only [he,he'] using hn.mul_left c)
  by_cases hd : p ∣ a*b
  · have hdd : ¬ p^2 ∣ a*b := by
      simpa only [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hsq p hp)
    rw [← prime_square_product_iff hp hd hdd,← prime_square_product_iff hp hd hdd]
    exact hab.dvd_iff (dvd_refl _)
  · have h := hab.dvd_iff (dvd_pow_self p (by omega : 2 ≠ 0))
    have hna : ¬ p ∣ a := fun ha => hd (dvd_mul_of_dvd_left ha b)
    have hnb : ¬ p ∣ b := fun hb => hd (dvd_mul_of_dvd_right hb a)
    simpa only [hp.dvd_mul,hna,hnb,false_or] using h

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

theorem candidateLowHigh_squarefree {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B)
    {e : BlockCandidateIndex M} (he : e ∈ blockCandidates B L T H M τ C S) :
    Squarefree (candidateHigh e*candidateLow e) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlow := (mem_endpointSplits.mp hs.1).1.trans (hS e.1.1)
  have hhigh := (mem_endpointSplits.mp hs.2).1.trans (hS e.1.2)
  apply (Nat.squarefree_mul ha.2.2.2.2.2.1.symm).mpr
  exact ⟨primeProduct_squarefree _ (fun p hp => auxiliaryPrimes_prime B p (hhigh hp)),
    primeProduct_squarefree _ (fun p hp => auxiliaryPrimes_prime B p (hlow hp))⟩

theorem candidateArithmeticQuotient_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    coefficientPrimeSet B (candidateArithmeticQuotient u e) =
      coefficientPrimeSet B (candidateArithmeticQuotient v e) := by
  have hs := blockPrimeSites_modEq (M := M) h
  have he' := he
  rw [hs] at he'
  have hsq := candidateLowHigh_squarefree (fun _ => filter_subset _ _) he
  have heq := candidateArithmeticQuotient_equation hT he
  have heq' := candidateArithmeticQuotient_equation hT he'
  ext p
  by_cases hp : p ∈ auxiliaryPrimes B
  · have hprime := auxiliaryPrimes_prime B p hp
    have hn := (h.add_right (e.1.1.val+1)).of_dvd (auxiliarySquare_dvd_period hp)
    simp only [coefficientPrimeSet,mem_filter,hp,true_and]
    exact affine_quotient_modEq_prime hprime hsq heq heq' hn
  · simp [coefficientPrimeSet,hp]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticKernelPeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary long means of the actual candidate fluctuation kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem actualCandidateKernel_explicit (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) :
    actualCandidateKernel B L T H M τ C χ u =
      candidateMatrix
        (fun e : blockCandidates B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) => e.val.1.1)
        (fun e => e.val.1.2)
        (fun e => candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val
          (coefficientPrimeSet B (candidateArithmeticQuotient u e.val))) := by
  funext i k
  unfold actualCandidateKernel independentCandidateKernel candidateMatrix
  simp only [arithmeticCandidatePrimeFamily_transpose]

theorem actualCandidateKernel_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    (χ : BlockCandidateIndex M → ℝ) :
    actualCandidateKernel B L T H M τ C χ u = actualCandidateKernel B L T H M τ C χ v := by
  rw [actualCandidateKernel_explicit,actualCandidateKernel_explicit]
  have hs := blockPrimeSites_modEq (M := M) h
  rw [hs]
  funext i k
  unfold candidateMatrix
  apply sum_congr rfl
  intro e _
  have he : e.val ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))) := by
    rw [hs]
    exact e.property
  dsimp only
  rw [candidateArithmeticQuotient_modEq hT h he]

theorem actualCandidateCutError_modEq {B L T H M u v : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (h : u ≡ v [MOD auxiliarySquarePeriod B])
    (χ : BlockCandidateIndex M → ℝ) :
    actualCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C χ v := by
  unfold actualCandidateCutError
  rw [actualCandidateKernel_modEq hT h χ,blockPrimeSites_modEq h]

theorem residueCandidateCutError_natCast {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) (u : ℕ) :
    residueCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C χ u := by
  unfold residueCandidateCutError
  rw [ZMod.val_natCast]
  exact actualCandidateCutError_modEq hT (Nat.mod_modEq u _) χ

theorem actualCandidateCutError_mean_tendsto {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) :
    Tendsto (fun N : ℕ => (∑ u ∈ range N, actualCandidateCutError B L T H M τ C χ u)/(N : ℝ))
      atTop (𝓝 (arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ))) := by
  let f := residueCandidateCutError B L T H M τ C χ
  have hf (u : ℕ) : f u = actualCandidateCutError B L T H M τ C χ u :=
    residueCandidateCutError_natCast hT χ u
  have ht := real_periodic_moment_tendsto f 1
  simp only [pow_one,hf] at ht
  have hs := residue_sum_eq_range (fun a : ZMod (auxiliarySquarePeriod B) => (f a : ℂ))
  have hs' : (∑ a : ZMod (auxiliarySquarePeriod B), f a) =
      ∑ u ∈ range (auxiliarySquarePeriod B), actualCandidateCutError B L T H M τ C χ u := by
    simp only [hf] at hs
    exact_mod_cast hs
  have hQ : auxiliarySquarePeriod B = ∏ p ∈ auxiliaryPrimes B, p^2 := by
    unfold auxiliarySquarePeriod
    exact (prod_pow _ _ _).symm
  have hQr : (auxiliarySquarePeriod B : ℝ) = ∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2 := by
    rw [hQ]
    simp only [Nat.cast_prod,Nat.cast_pow]
  rw [hs',hQr,hQ] at ht
  exact ht

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateFiniteCutoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counting-scale edge condition is a single monotone cutoff -/

namespace JointDickman
open Finset Classical

theorem divisorEdgeNew_iff_threshold {a b c n m N : ℕ} {j : ℤ}
    (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hba : b ≤ a)
    (hn : 0 < n) (hbn : b ∣ n) (han : (a : ℤ) ∣ (n : ℤ)+j)
    (hm : divisorEdgeInverse a b c n = m) (he : c*n = a*b*m+b) :
    n ∈ divisorEdgeNew a b c N j ↔ c*n < b*(N+1) := by
  have hcut : c*n < b*(N+1) ↔ a*m < N := by
    rw [he]
    constructor <;> intro h <;> nlinarith
  rw [hcut]
  constructor
  · intro h
    simpa only [hm] using (mem_filter.mp h).2.2.2.1
  · intro h
    have hbm : b*m < N := (Nat.mul_le_mul_right m hba).trans_lt h
    have hnN : n ≤ b*N := by
      have h1 : a*m+1 ≤ N := h
      have h2 : c*n ≤ b*N := by nlinarith
      have h3 : n ≤ c*n := Nat.le_mul_of_pos_left n hc
      exact h3.trans h2
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn,hnN⟩,hbn,han,
      by simpa only [hm] using h,by simpa only [hm] using hbm⟩

theorem candidateGraphTriple_edge_iff {B L T H M u N : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) {e : BlockCandidateIndex M}
    (he : e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) :
    u+(e.1.1.val+1) ∈ graphTripleEdges N (candidateGraphTriple B e) ↔
      candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1) := by
  obtain ⟨hs,ha⟩ := mem_blockCandidates.mp he
  have hlo := (mem_endpointSplits.mp hs.1).1
  have hhi := (mem_endpointSplits.mp hs.2).1
  have hloP := hlo.trans (show coefficientPrimeSet B (u+(e.1.1.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hhiP := hhi.trans (show coefficientPrimeSet B (u+(e.1.2.val+1)) ⊆ auxiliaryPrimes B
    from filter_subset _ _)
  have hb : 0 < candidateLow e := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hloP hp)).pos)
  have haa : 0 < candidateHigh e := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hhiP hp)).pos)
  have hbd : candidateLow e ∣ u+(e.1.1.val+1) := (primeProduct_dvd_site_iff hloP).mpr hlo
  have had : candidateHigh e ∣ u+(e.1.2.val+1) := (primeProduct_dvd_site_iff hhiP).mpr hhi
  have hshift : ((u+(e.1.1.val+1) : ℕ) : ℤ)+(candidateLag e : ℤ) =
      (u+(e.1.2.val+1) : ℕ) := by
    rw [show (candidateLag e : ℤ) = (e.1.2.val : ℤ)-e.1.1.val from Int.ofNat_sub ha.1.le]
    push_cast
    ring
  have hcoeff := ha.2.2.2.2.2.2.2.2.1
  unfold graphTripleEdges
  rw [candidateGraphTriple_lag ha]
  change _ ∈ divisorEdgeNew (candidateHigh e) (candidateLow e)
    (∏ p ∈ coefficientPrimeSet B (candidateQuotient e), p) N (candidateLag e) ↔ _
  rw [← hcoeff]
  apply divisorEdgeNew_iff_threshold haa hb ha.2.2.2.1
    (by have := ha.2.2.2.2.1; omega) (by omega) hbd
    (by rw [hshift]; exact_mod_cast had) rfl
  exact (candidateArithmeticQuotient_equation hT he).symm

theorem finiteCandidateCutoff_bounds {M : ℕ} (B T N u : ℕ) (e : BlockCandidateIndex M) :
    0 ≤ finiteCandidateCutoff B T N u e ∧ finiteCandidateCutoff B T N u e ≤ 1 := by
  unfold finiteCandidateCutoff candidateCutoff amplificationOuterWeight amplificationInnerWeight
  split_ifs
  · have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    exact ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1,
      (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num)) h3.2 h3.1 (by norm_num)).trans_eq (by norm_num)⟩
  · exact ⟨le_rfl,by norm_num⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicProfileMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform periodic means under finitely many interval cutoffs -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem real_periodic_prefix_error {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C) (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ)*((∑ a, f a)/(q : ℝ))| ≤ (q : ℝ)*C := by
  by_cases hN : N = 0
  · simp only [hN,range_zero,sum_empty,Nat.cast_zero,zero_mul,sub_self,abs_zero]
    positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  let fc : ZMod q → ℂ := fun a => f a
  have hfc : ‖fc‖ ≤ C := (pi_norm_le_iff_of_nonneg hC).mpr (fun a => by
    simpa only [fc,Complex.norm_real,Real.norm_eq_abs] using hf a)
  have herr := periodicAverage_error fc (Nat.pos_of_ne_zero hN)
  have heq : periodicAverage fc N-residueMean fc =
      (((∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ) : ℝ) : ℂ) := by
    simp [periodicAverage,residueMean,fc]
  rw [heq,Complex.norm_real,Real.norm_eq_abs] at herr
  have hh := mul_le_mul_of_nonneg_right herr hNr.le
  have halg : |(∑ n ∈ range N, f n)-(N : ℝ)*((∑ a, f a)/(q : ℝ))| =
      |(∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ)| * (N : ℝ) := by
    calc
      _ = |((∑ n ∈ range N, f n)/(N : ℝ)-(∑ a, f a)/(q : ℝ))*(N : ℝ)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul,abs_of_pos hNr]
  rw [halg]
  calc
    _ ≤ ((q : ℝ)*‖fc‖/(N : ℝ))*(N : ℝ) := hh
    _ = (q : ℝ)*‖fc‖ := div_mul_cancel₀ _ hNr.ne'
    _ ≤ (q : ℝ)*C := mul_le_mul_of_nonneg_left hfc (Nat.cast_nonneg q)

theorem real_periodic_interval_error {q : ℕ} [NeZero q]
    (f : ZMod q → ℝ) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ a, |f a| ≤ C)
    {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, f n) - ((b-a : ℕ) : ℝ)*((∑ x, f x)/(q : ℝ))| ≤ 2*q*C := by
  have ha := real_periodic_prefix_error f hC hf a
  have hb := real_periodic_prefix_error f hC hf b
  rw [sum_Ico_eq_sub _ hab,Nat.cast_sub hab]
  calc
    _ = |((∑ n ∈ range b, f n)-(b : ℝ)*((∑ x, f x)/(q : ℝ)))-
        ((∑ n ∈ range a, f n)-(a : ℝ)*((∑ x, f x)/(q : ℝ)))| := by congr 1; ring
    _ ≤ |(∑ n ∈ range b, f n)-(b : ℝ)*((∑ x, f x)/(q : ℝ))|+
        |(∑ n ∈ range a, f n)-(a : ℝ)*((∑ x, f x)/(q : ℝ))| := abs_sub _ _
    _ ≤ (q : ℝ)*C+(q : ℝ)*C := add_le_add hb ha
    _ = _ := by ring

theorem finite_nat_convex_eq_interval (S : Finset ℕ)
    (hc : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S) :
    ∃ a b, a ≤ b ∧ S = Ico a b := by
  by_cases hs : S.Nonempty
  · refine ⟨S.min' hs,S.max' hs+1,?_,?_⟩
    · exact (min'_le S _ (max'_mem S hs)).trans (Nat.le_succ _)
    · ext n
      constructor
      · intro hn
        exact mem_Ico.mpr ⟨min'_le S n hn,Nat.lt_succ_of_le (le_max' S n hn)⟩
      · intro hn
        obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
        exact hc _ (min'_mem S hs) _ (max'_mem S hs) n hlo (Nat.le_of_lt_succ hhi)
  · exact ⟨0,0,le_rfl,by simp [not_nonempty_iff_eq_empty.mp hs]⟩

/-- Only the boundary error depends on the number of cutoff profiles.
The main term retains the uniform mean bound E. -/
theorem periodic_interval_profile_bound {q : ℕ} [NeZero q]
    {α : Type*} [Fintype α] (F : α → ZMod q → ℝ)
    {C E : ℝ} (hC : 0 ≤ C) (hF : ∀ a r, |F a r| ≤ C)
    (hmean : ∀ a, (∑ r, F a r)/(q : ℝ) ≤ E)
    (profile : ℕ → α)
    (hconv : ∀ u v w, u ≤ v → v ≤ w → profile u = profile w → profile v = profile u)
    (N : ℕ) :
    (∑ n ∈ range N, F (profile n) n) ≤
      (N : ℝ)*E+(Fintype.card α : ℝ)*(2*q*C) := by
  let S : α → Finset ℕ := fun a => (range N).filter (fun n => profile n = a)
  have hlocal (a : α) : (∑ n ∈ S a, F a n) ≤ (S a).card*E+2*q*C := by
    obtain ⟨lo,hi,hle,hI⟩ := finite_nat_convex_eq_interval (S a) (by
      intro u hu w hw v huv hvw
      obtain ⟨huN,hua⟩ := mem_filter.mp hu
      obtain ⟨hwN,hwa⟩ := mem_filter.mp hw
      exact mem_filter.mpr ⟨mem_range.mpr (hvw.trans_lt (mem_range.mp hwN)),
        (hconv u v w huv hvw (hua.trans hwa.symm)).trans hua⟩)
    rw [hI,Nat.card_Ico]
    have herr := (le_abs_self _).trans (real_periodic_interval_error (F a) hC (hF a) hle)
    have hm := mul_le_mul_of_nonneg_left (hmean a) (Nat.cast_nonneg (hi-lo))
    linarith
  have hsum : (∑ a, ∑ n ∈ S a, F a n) = ∑ n ∈ range N, F (profile n) n := by
    dsimp only [S]
    convert sum_fiberwise_of_maps_to (g := profile) (s := range N) (t := univ)
      (fun _ _ => mem_univ _) (fun n => F (profile n) n) using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro n hn
    rw [(mem_filter.mp hn).2]
  have hcard : (∑ a, (S a).card) = N := by
    exact (card_eq_sum_card_fiberwise (s := range N) (t := univ) (f := profile)
      (fun _ _ => mem_univ _)).symm.trans (card_range N)
  rw [← hsum]
  calc
    _ ≤ ∑ a, ((S a).card*E+2*q*C) := sum_le_sum (fun a _ => hlocal a)
    _ = (N : ℝ)*E+(Fintype.card α : ℝ)*(2*q*C) := by
      rw [sum_add_distrib,← sum_mul,← Nat.cast_sum,hcard]
      simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteArithmeticKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite graph and its arithmetic candidate matrix -/

namespace JointDickman
open Finset Classical

theorem candidateMatrix_forward {M : ℕ} (I : Finset (BlockCandidateIndex M))
    (hI : ∀ e ∈ I, e.1.1 < e.1.2) (w : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hik : i < k) :
    candidateMatrix (fun e : I => e.val.1.1) (fun e : I => e.val.1.2)
      (fun e => w e.val) i k = ∑ e ∈ I, if e.1 = (i,k) then w e else 0 := by
  unfold candidateMatrix
  change (∑ e : I, (fun e : BlockCandidateIndex M =>
    ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
      (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0))) e.val) = _
  trans ∑ e ∈ I, ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
    (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0))
  · exact sum_coe_sort I (fun e : BlockCandidateIndex M =>
      ((if i = e.1.1 then if k = e.1.2 then w e else 0 else 0)+
        (if i = e.1.2 then if k = e.1.1 then w e else 0 else 0)))
  · apply sum_congr rfl
    intro e he
    have hord := hI e he
    have hback : ¬ (i = e.1.2 ∧ k = e.1.1) := by
      rintro ⟨hi,hk⟩
      rw [← hi,← hk] at hord
      exact (not_lt_of_ge hik.le) hord
    have hpair : e.1 = (i,k) ↔ i = e.1.1 ∧ k = e.1.2 := by
      simp only [Prod.ext_iff]
      exact and_congr eq_comm eq_comm
    by_cases hi : i = e.1.1 <;> by_cases hk : k = e.1.2 <;>
      by_cases hi' : i = e.1.2 <;> by_cases hk' : k = e.1.1 <;>
      simp_all only [ite_true, if_true,ite_false, if_false,add_zero,not_true_eq_false,and_self,
        and_false,false_and,not_false_eq_true]

theorem actualCandidateKernel_pair {B L T H M u : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (hik : i < k) :
    actualCandidateKernel B L T H M τ C χ u i k =
      ∑ e ∈ blockCandidates B L T H M τ C
        (fun l => coefficientPrimeSet B (u+(l.val+1))),
        if e.1 = (i,k) then candidateRootWeight B L τ C
          (fun l => coefficientPrimeSet B (u+(l.val+1))) χ e
          (coefficientPrimeSet B (candidateArithmeticQuotient u e)) else 0 := by
  rw [actualCandidateKernel_explicit]
  exact candidateMatrix_forward
    (blockCandidates B L T H M τ C (fun l => coefficientPrimeSet B (u+(l.val+1))))
    (fun e he => (mem_blockCandidates.mp he).2.1)
    (fun e => candidateRootWeight B L τ C (fun l => coefficientPrimeSet B (u+(l.val+1)))
      χ e (coefficientPrimeSet B (candidateArithmeticQuotient u e))) i k hik

theorem rawArithmeticGraphKernel_finiteCandidate {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    {i k : Fin M} (hik : i < k) (hH : H < k.val-i.val)
    (hsq : ¬ BlockSquareHit B M u) :
    rawArithmeticGraphKernel B L τ C T N ((k.val-i.val : ℕ) : ℤ)
      (u+(i.val+1))/(B : ℝ) =
      actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k := by
  rw [rawArithmeticGraphKernel_candidate_sum hB hT hTP hik hH hsq,
    actualCandidateKernel_pair _ i k hik]
  apply sum_congr rfl
  intro e he
  by_cases hp : e.1 = (i,k)
  · have hi : e.1.1 = i := congrArg Prod.fst hp
    simp only [hp,true_and,ite_true, if_true]
    have hedge := candidateGraphTriple_edge_iff hTP he (N := N)
    rw [hi] at hedge
    simp only [hedge]
    by_cases hc : candidateQuotient e*(u+(e.1.1.val+1)) < candidateLow e*(N+1)
    · have hci : candidateQuotient e*(u+(i.val+1)) < candidateLow e*(N+1) := by
        simpa only [hi] using hc
      simp only [hci,ite_true, if_true]
      unfold arithmeticCandidateWeight candidateRootWeight finiteCandidateCutoff
      simp only [hc,ite_true, if_true]
      rfl
    · have hci : ¬ candidateQuotient e*(u+(i.val+1)) < candidateLow e*(N+1) := by
        simpa only [hi] using hc
      simp only [hci,ite_false, if_false]
      unfold candidateRootWeight finiteCandidateCutoff
      simp only [hc,ite_false, if_false,mul_zero]
  · simp only [hp,false_and,ite_false, if_false]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteCutoffProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite interval profiles for the original graph cutoffs -/

namespace JointDickman
open Finset Classical

theorem blockCandidates_subset_primePool {B L T H M : ℕ} {τ C : ℝ}
    {S : Fin M → Finset ℕ} (hS : ∀ i, S i ⊆ auxiliaryPrimes B) :
    blockCandidates B L T H M τ C S ⊆ primeCandidatePool B M := by
  intro e he
  have hs := (mem_blockCandidates.mp he).1
  exact mem_product.mpr ⟨mem_univ _,mem_product.mpr
    ⟨mem_powerset.mpr ((mem_endpointSplits.mp hs.1).1.trans (hS _)),
      mem_powerset.mpr ((mem_endpointSplits.mp hs.2).1.trans (hS _))⟩⟩

theorem profileCandidateCutoff_bounds (B T M : ℕ) (s : primeCandidatePool B M → Bool)
    (e : BlockCandidateIndex M) :
    0 ≤ profileCandidateCutoff B T M s e ∧ profileCandidateCutoff B T M s e ≤ 1 := by
  unfold profileCandidateCutoff
  split_ifs
  · unfold candidateCutoff amplificationOuterWeight amplificationInnerWeight
    have h1 := amplificationBump_bounds (Real.log (candidateQuotient e)/(B : ℝ))
    have h2 := amplificationBump_bounds ((candidateHigh e : ℝ)/(T*candidateQuotient e))
    have h3 := amplificationBump_bounds ((candidateLow e : ℝ)/(T*candidateQuotient e))
    exact ⟨mul_nonneg (mul_nonneg h1.1 h2.1) h3.1,
      (mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num)) h3.2 h3.1
        (by norm_num)).trans_eq (by norm_num)⟩
  all_goals exact ⟨le_rfl,by norm_num⟩

theorem finiteCutProfile_intervals (B M N : ℕ) (u v w : ℕ) (huv : u ≤ v) (hvw : v ≤ w)
    (he : finiteCutProfile B M N u = finiteCutProfile B M N w) :
    finiteCutProfile B M N v = finiteCutProfile B M N u := by
  funext e
  have he' := congrFun he e
  dsimp only [finiteCutProfile] at he' ⊢
  have hlo : candidateQuotient e.val*(u+(e.val.1.1.val+1)) ≤
      candidateQuotient e.val*(v+(e.val.1.1.val+1)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right huv _)
  have hhi : candidateQuotient e.val*(v+(e.val.1.1.val+1)) ≤
      candidateQuotient e.val*(w+(e.val.1.1.val+1)) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hvw _)
  by_cases hu : candidateQuotient e.val*(u+(e.val.1.1.val+1)) < candidateLow e.val*(N+1)
  · have hw : candidateQuotient e.val*(w+(e.val.1.1.val+1)) < candidateLow e.val*(N+1) := by
      have hh : decide (candidateQuotient e.val*(w+(e.val.1.1.val+1)) < candidateLow e.val*(N+1)) = true := by
        simpa only [hu,decide_true] using he'.symm
      exact of_decide_eq_true hh
    simp only [hu,hhi.trans_lt hw,decide_true]
  · have hv : ¬ candidateQuotient e.val*(v+(e.val.1.1.val+1)) < candidateLow e.val*(N+1) :=
      fun h => hu (hlo.trans_lt h)
    simp only [hu,hv,decide_false]

theorem profileCandidateCutoff_finite {B T M N u : ℕ} {e : BlockCandidateIndex M}
    (he : e ∈ primeCandidatePool B M) :
    profileCandidateCutoff B T M (finiteCutProfile B M N u) e = finiteCandidateCutoff B T N u e := by
  simp [profileCandidateCutoff,he,finiteCutProfile,finiteCandidateCutoff]

theorem actualCandidateCutError_congr {B L T H M u : ℕ} {τ C : ℝ}
    {χ ψ : BlockCandidateIndex M → ℝ}
    (hχ : ∀ e ∈ blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))), χ e = ψ e) :
    actualCandidateCutError B L T H M τ C χ u = actualCandidateCutError B L T H M τ C ψ u := by
  have hroot (e : blockCandidates B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1)))) (R : Finset ℕ) :
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val R =
      candidateRootWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ e.val R := by
    unfold candidateRootWeight
    rw [hχ e.val e.property]
  have hactual : actualCandidateKernel B L T H M τ C χ u =
      actualCandidateKernel B L T H M τ C ψ u := by
    rw [actualCandidateKernel_explicit,actualCandidateKernel_explicit]
    funext i k
    unfold candidateMatrix
    apply sum_congr rfl
    intro e _
    dsimp only
    rw [hroot]
  have hlatent : latentCandidateKernel B L T H M τ C
      (fun i => coefficientPrimeSet B (u+(i.val+1))) χ =
      latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ := by
    funext i k
    unfold latentCandidateKernel candidateMatrix
    apply sum_congr rfl
    intro e _
    have hw : candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) χ e.val =
        candidateMeanWeight B L τ C (fun i => coefficientPrimeSet B (u+(i.val+1))) ψ e.val := by
      unfold candidateMeanWeight finiteExpectation
      apply sum_congr rfl
      intro R _
      dsimp only
      rw [hroot]
    dsimp only
    rw [hw]
  unfold actualCandidateCutError
  rw [hactual,hlatent]

theorem actualCandidateCutError_finiteProfile (B L T H M N u : ℕ) (τ C : ℝ) :
    actualCandidateCutError B L T H M τ C
      (profileCandidateCutoff B T M (finiteCutProfile B M N u)) u =
    actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u := by
  apply actualCandidateCutError_congr
  intro e he
  exact profileCandidateCutoff_finite (blockCandidates_subset_primePool (fun _ => filter_subset _ _) he)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteCutoffMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph cutoffs preserve the vanishing arithmetic error -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem residueCandidateCutError_mean {B L T H M : ℕ} {τ C : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (χ : BlockCandidateIndex M → ℝ) :
    (∑ r : ZMod (auxiliarySquarePeriod B), residueCandidateCutError B L T H M τ C χ r)/
        (auxiliarySquarePeriod B : ℝ) =
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) := by
  have ht := real_periodic_moment_tendsto (residueCandidateCutError B L T H M τ C χ) 1
  simp only [pow_one,residueCandidateCutError_natCast hT χ] at ht
  exact tendsto_nhds_unique ht (actualCandidateCutError_mean_tendsto hT χ)

theorem finite_cutoff_sum_bound {B L T H M : ℕ} {τ C A E : ℝ}
    (hT : T ≤ auxiliaryCutoff B) (hA : 0 ≤ A)
    (hcap : ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ u, |actualCandidateCutError B L T H M τ C χ u| ≤ A)
    (hmean : ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤ E)
    (N K : ℕ) :
    (∑ u ∈ range K, actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u) ≤
      (K : ℝ)*E+(Fintype.card (primeCandidatePool B M → Bool) : ℝ)*
        (2*(auxiliarySquarePeriod B : ℝ)*A) := by
  let F := fun (s : primeCandidatePool B M → Bool) =>
    residueCandidateCutError B L T H M τ C (profileCandidateCutoff B T M s)
  have hf (s : primeCandidatePool B M → Bool) (r : ZMod (auxiliarySquarePeriod B)) :
      |F s r| ≤ A := hcap _ (profileCandidateCutoff_bounds B T M s) r.val
  have hm (s : primeCandidatePool B M → Bool) :
      (∑ r, F s r)/(auxiliarySquarePeriod B : ℝ) ≤ E := by
    rw [show (∑ r, F s r)/(auxiliarySquarePeriod B : ℝ) =
      arithmeticSquareMean B (actualCandidateCutError B L T H M τ C
        (profileCandidateCutoff B T M s)) from residueCandidateCutError_mean hT _]
    exact hmean _ (profileCandidateCutoff_bounds B T M s)
  have hh := periodic_interval_profile_bound F hA hf hm (finiteCutProfile B M N)
    (finiteCutProfile_intervals B M N) K
  have heq u : F (finiteCutProfile B M N u) (u : ZMod (auxiliarySquarePeriod B)) =
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u := by
    dsimp only [F]
    rw [residueCandidateCutError_natCast hT,actualCandidateCutError_finiteProfile]
  simpa only [heq] using hh

theorem finite_cutoff_arithmetic_decay
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
          (∑ u ∈ range K, actualCandidateCutError B L T H M τ C
            (finiteCandidateCutoff B T N u) u)/(K : ℝ) < E B+ε := by
  obtain ⟨E,hE,hm⟩ := actual_arithmetic_fluctuation_decay hFord hMertens hL hτ hτsmall
  refine ⟨E,hE,?_⟩
  filter_upwards [hm,candidate_root_error_cap hL hτ hτsmall] with B hm hcap
  intro C T H M hT hTs hTP hM0 hM hMexp ε hε
  let A : ℝ := (Fintype.card (primeCandidatePool B M → Bool) : ℝ)*
    (2*(auxiliarySquarePeriod B : ℝ)*(B : ℝ)^10)
  have hlim : Tendsto (fun K : ℕ => A/(K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat A
  filter_upwards [hlim.eventually (Iio_mem_nhds hε),eventually_gt_atTop 0] with K hK hK0
  intro N
  have hs := finite_cutoff_sum_bound (L := L) (H := H) (τ := τ) (C := C) hTP
    (pow_nonneg (Nat.cast_nonneg B) 10)
    (fun χ hχ u => hcap C T H M hM0 hM (fun i => coefficientPrimeSet B (u+(i.val+1)))
      χ hχ (primeSiteTranspose _ (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u))))
    (fun χ hχ => hm C T H M hT hTs hTP hM0 hM hMexp χ hχ) N K
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  calc
    _ ≤ ((K : ℝ)*E B+A)/(K : ℝ) := div_le_div_of_nonneg_right hs hKr.le
    _ = E B+A/(K : ℝ) := by field_simp
    _ < E B+ε := by linarith only [hK]

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

theorem kernelCutNorm_sub_triangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K A L : ι → ι → ℝ) :
    kernelCutNorm (fun i k => K i k-L i k) ≤
      kernelCutNorm (fun i k => K i k-A i k)+kernelCutNorm (fun i k => A i k-L i k) := by
  convert kernelCutNorm_add (fun i k => K i k-A i k) (fun i k => A i k-L i k) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext i k
  ring

theorem kernelCutNorm_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    kernelCutNorm (fun _ _ : ι => (0 : ℝ)) = 0 := by
  simp [kernelCutNorm,kernelCutMaximum,realBilinear]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FiniteGraphKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both orientations of the original finite graph kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem finiteGraphKernel_symm (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) :
    finiteGraphKernel B L T H M N u τ C i k = finiteGraphKernel B L T H M N u τ C k i := by
  have habs : ((i.val : ℤ)-k.val).natAbs = ((k.val : ℤ)-i.val).natAbs := by
    rw [show (i.val : ℤ)-k.val = -((k.val : ℤ)-i.val) by ring,Int.natAbs_neg]
  unfold finiteGraphKernel
  rw [habs]
  split_ifs
  · exact congrArg (fun x : ℝ => x/(B : ℝ)) (rawArithmeticGraphKernel_block_reverse i k).symm
  · rfl

theorem actualCandidateKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) (i k : Fin M) :
    actualCandidateKernel B L T H M τ C χ u i k = actualCandidateKernel B L T H M τ C χ u k i := by
  rw [actualCandidateKernel_explicit]
  unfold candidateMatrix
  apply sum_congr rfl
  intro e _
  dsimp only
  split_ifs <;> simp_all

theorem actualCandidateKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) (i : Fin M) :
    actualCandidateKernel B L T H M τ C χ u i i = 0 := by
  rw [actualCandidateKernel_explicit]
  unfold candidateMatrix
  apply sum_eq_zero
  intro e _
  have hord := (mem_blockCandidates.mp e.property).2.1
  dsimp only
  by_cases hi : i = e.val.1.1 <;> by_cases hk : i = e.val.1.2
  · have hh : e.val.1.1 = e.val.1.2 := hi.symm.trans hk
    rw [hh] at hord
    exact False.elim (lt_irrefl _ hord)
  all_goals simp [hi,hk,ne_of_lt hord,Ne.symm (ne_of_lt hord)]

theorem actualCandidateKernel_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (u : ℕ) {i k : Fin M}
    (hik : i < k) (hH : k.val-i.val ≤ H) :
    actualCandidateKernel B L T H M τ C χ u i k = 0 := by
  rw [actualCandidateKernel_pair χ i k hik]
  apply sum_eq_zero
  intro e he
  have ha := (mem_blockCandidates.mp he).2
  have hp : e.1 ≠ (i,k) := by
    intro hp
    have heH := ha.2.1
    change H < e.1.2.val-e.1.1.val at heH
    rw [hp] at heH
    dsimp only at heH
    omega
  exact ite_eq_right hp

theorem finiteGraphKernel_eq_candidate {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hsq : ¬ BlockSquareHit B M u) :
    finiteGraphKernel B L T H M N u τ C =
      actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u := by
  have hforward (i k : Fin M) (hik : i < k) :
      finiteGraphKernel B L T H M N u τ C i k =
        actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u i k := by
    have hdiff : ((k.val : ℤ)-i.val) = ((k.val-i.val : ℕ) : ℤ) := (Int.ofNat_sub hik.le).symm
    unfold finiteGraphKernel
    rw [hdiff,Int.natAbs_natCast]
    split_ifs with hh
    · exact rawArithmeticGraphKernel_finiteCandidate hB hT hTP hik hh hsq
    · exact (actualCandidateKernel_short _ u hik (Nat.le_of_not_gt hh)).symm
  funext i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hforward i k hik
  · simp only [finiteGraphKernel,sub_self,Int.natAbs_zero,not_lt_zero,ite_false, if_false,
      actualCandidateKernel_diag]
  · rw [finiteGraphKernel_symm,actualCandidateKernel_symm]
    exact hforward k i hki

theorem finiteGraphKernel_entry_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M N u : ℕ), 0 < T →
      ∀ i k : Fin M, |finiteGraphKernel B L T H M N u τ C i k| ≤ (B : ℝ)^2 := by
  filter_upwards [rawArithmeticGraphKernel_forward_cap hL hτ hτsmall] with B hcap
  intro C T H M N u hT
  have hf (i k : Fin M) (hik : i < k) :
      |finiteGraphKernel B L T H M N u τ C i k| ≤ (B : ℝ)^2 := by
    have hdiff : ((k.val : ℤ)-i.val) = ((k.val-i.val : ℕ) : ℤ) := (Int.ofNat_sub hik.le).symm
    unfold finiteGraphKernel
    split_ifs
    · rw [abs_of_nonneg (div_nonneg (rawArithmeticGraphKernel_nonneg _ _ _ _ _ _ _ _)
        (Nat.cast_nonneg B)),hdiff]
      exact hcap C T M N u hT i k hik
    · simp only [abs_zero]
      positivity
  intro i k
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact hf i k hik
  · simp only [finiteGraphKernel,sub_self,Int.natAbs_zero,not_lt_zero,ite_false, if_false,abs_zero]
    positivity
  · rw [finiteGraphKernel_symm]
    exact hf k i hki

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphSquareRemoval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing square-hit blocks from the original finite graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem finiteGraphCandidateError_zero {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hsq : ¬ BlockSquareHit B M u) :
    finiteGraphCandidateError B L T H M N u τ C = 0 := by
  unfold finiteGraphCandidateError
  rw [finiteGraphKernel_eq_candidate hB hT hTP hsq]
  simp only [sub_self]
  exact kernelCutNorm_zero

theorem finiteGraphCandidateError_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M N u : ℕ), 0 < T → 0 < M → M ≤ B^2 →
      finiteGraphCandidateError B L T H M N u τ C ≤ (B : ℝ)^10 := by
  filter_upwards [finiteGraphKernel_entry_cap hL hτ hτsmall,
    candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2] with B hfg hmass hB
  intro C T H M N u hT hM0 hM
  let G := finiteGraphKernel B L T H M N u τ C
  let A := actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u
  have hg : (∑ i, ∑ k, |G i k|) ≤ (M : ℝ)^2*(B : ℝ)^2 := by
    calc
      _ ≤ ∑ _i : Fin M, ∑ _k : Fin M, (B : ℝ)^2 :=
        sum_le_sum (fun i _ => sum_le_sum (fun k _ => hfg C T H M N u hT i k))
      _ = _ := by simp [pow_two,mul_assoc]
  have ha : (∑ i, ∑ k, |A i k|) ≤ 2*(M : ℝ)^2*(B : ℝ)^2 :=
    (hmass C T H M (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u) (finiteCandidateCutoff_bounds B T N u)).2
      (primeSiteTranspose _ (auxiliaryPrimes B)
        (arithmeticCandidatePrimeFamily B _ (candidateArithmeticQuotient u)))
  have hd : (∑ i, ∑ k, |G i k-A i k|) ≤ 3*(M : ℝ)^2*(B : ℝ)^2 :=
    (kernel_difference_absolute_mass G A).trans (by linarith)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
  have hm2 : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hb2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hb1 : (1 : ℝ) ≤ B := by linarith
  have hb4 : (3 : ℝ) ≤ (B : ℝ)^4 := by
    have hs : (4 : ℝ) ≤ (B : ℝ)^2 := by nlinarith
    exact (by linarith : (3 : ℝ) ≤ (B : ℝ)^2).trans
      (pow_le_pow_right₀ hb1 (by norm_num : 2 ≤ 4))
  change kernelCutNorm (fun i k => G i k-A i k) ≤ _
  calc
    _ ≤ kernelAbsoluteMass (fun i k => G i k-A i k) := kernelCutNorm_le_absolute_mass _
    _ ≤ (3*(M : ℝ)^2*(B : ℝ)^2)/(M : ℝ) := by
      simpa only [kernelAbsoluteMass,Fintype.card_fin] using
        div_le_div_of_nonneg_right hd (Nat.cast_nonneg M)
    _ ≤ 3*(M : ℝ)^2*(B : ℝ)^2 := div_le_self (by positivity) hm1
    _ ≤ 3*((B : ℝ)^2)^2*(B : ℝ)^2 := by gcongr
    _ = 3*(B : ℝ)^6 := by ring
    _ ≤ (B : ℝ)^4*(B : ℝ)^6 := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = _ := by ring

theorem finiteGraphLatentError_pointwise {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hTP : T ≤ auxiliaryCutoff B)
    (hcap : finiteGraphCandidateError B L T H M N u τ C ≤ (B : ℝ)^10) :
    finiteGraphLatentError B L T H M N u τ C ≤
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u+
        (B : ℝ)^10*(if BlockSquareHit B M u then 1 else 0) := by
  have ht := kernelCutNorm_sub_triangle (finiteGraphKernel B L T H M N u τ C)
    (actualCandidateKernel B L T H M τ C (finiteCandidateCutoff B T N u) u)
    (latentCandidateKernel B L T H M τ C (fun i => coefficientPrimeSet B (u+(i.val+1)))
      (finiteCandidateCutoff B T N u))
  change finiteGraphLatentError B L T H M N u τ C ≤
    finiteGraphCandidateError B L T H M N u τ C+
      actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u at ht
  by_cases hs : BlockSquareHit B M u
  · simp only [hs,ite_true, if_true,mul_one]
    linarith
  · rw [finiteGraphCandidateError_zero hB hT hTP hs] at ht
    simpa only [hs,ite_false, if_false,mul_zero,add_zero,zero_add] using ht

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockSquarePeriod
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary long means of square-hit blocks -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem blockSquareHit_modEq {B M u v : ℕ} (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    BlockSquareHit B M u ↔ BlockSquareHit B M v := by
  have hd (i : Fin M) (p : ℕ) (hp : p ∈ auxiliaryPrimes B) :
      p^2 ∣ u+(i.val+1) ↔ p^2 ∣ v+(i.val+1) :=
    ((h.of_dvd (auxiliarySquare_dvd_period hp)).add_right (i.val+1)).dvd_iff (dvd_refl _)
  constructor
  · rintro ⟨i,p,hp,hpu⟩
    exact ⟨i,p,hp,(hd i p hp).mp hpu⟩
  · rintro ⟨i,p,hp,hpv⟩
    exact ⟨i,p,hp,(hd i p hp).mpr hpv⟩

theorem residueBlockSquareWeight_natCast (B M u : ℕ) :
    residueBlockSquareWeight B M u = blockSquareWeight B M u := by
  unfold residueBlockSquareWeight blockSquareWeight
  rw [ZMod.val_natCast]
  simp only [blockSquareHit_modEq (Nat.mod_modEq u (auxiliarySquarePeriod B))]

theorem blockSquareWeight_long_mean {B M : ℕ} (hB : 1 < B) (hM : M ≤ B^2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, (∑ u ∈ range K, blockSquareWeight B M u)/(K : ℝ) < 1/(B : ℝ)+ε := by
  let f := residueBlockSquareWeight B M
  have ht := real_periodic_moment_tendsto f 1
  have hf (u : ℕ) : f u = blockSquareWeight B M u := residueBlockSquareWeight_natCast B M u
  simp only [pow_one,hf] at ht
  have hmean : (∑ r, f r)/(auxiliarySquarePeriod B : ℝ) ≤ 1/(B : ℝ) := by
    simpa only [f,residueBlockSquareWeight,blockSquareWeight,← mul_sum,mul_div_assoc]
      using block_squareHit_polynomial_bound hB hM
  exact ht.eventually (Iio_mem_nhds (lt_add_of_le_of_pos hmean hε))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteGraphFluctuation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing fluctuations of the original symmetric finite graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem finite_graph_arithmetic_fluctuation_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
          (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) < E B+ε := by
  obtain ⟨E,hE,hcut⟩ := finite_cutoff_arithmetic_decay hFord hMertens hL hτ hτsmall
  refine ⟨fun B => E B+1/(B : ℝ),?_,?_⟩
  · simpa only [add_zero] using hE.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
  filter_upwards [hcut,finiteGraphCandidateError_cap hL hτ hτsmall,eventually_gt_atTop 1]
    with B hcut hcap hB
  intro C T H M hT hTs hTP hM0 hM hMexp ε hε
  have heps : 0 < ε/2 := by linarith
  filter_upwards [hcut C T H M hT hTs hTP hM0 hM hMexp (ε/2) heps,
    blockSquareWeight_long_mean hB hM heps] with K hcut hsquare
  intro N
  have hsum : (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) ≤
      (∑ u ∈ range K, actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u)/(K : ℝ)+
        (∑ u ∈ range K, blockSquareWeight B M u)/(K : ℝ) := by
    rw [← add_div,← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    apply sum_le_sum
    intro u _
    exact finiteGraphLatentError_pointwise (by omega) hT hTP (hcap C T H M N u hT hM0 hM)
  have hcutN := hcut N
  linarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd_oai := @OAI.JointDickman.finite_graph_arithmetic_fluctuation_jd_oai
