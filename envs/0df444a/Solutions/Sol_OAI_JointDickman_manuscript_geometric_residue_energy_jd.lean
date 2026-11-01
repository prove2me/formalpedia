-- Prove2me | solution 1 for OAI.JointDickman.manuscript_geometric_residue_energy_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:45:31.048571+00:00
-- url     : https://prove2.me/submissions/7f620d80-5769-4ce5-9ca5-e2620060a536

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_primeChannelMarginal_upper_jd
import Theorems.Thm_OAI_JointDickman_primeCommonLogCell_upper_jd

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

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

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

theorem squarefreeWeight_isMultiplicative (z : ℝ) :
    (squarefreeWeight z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨squarefreeWeight_one z, fun {m n} hm hn hmn => ?_⟩
  simp only [squarefreeWeight, coe_mk, Nat.squarefree_mul hmn,
    ite_zero_mul_ite_zero, cardFactors_mul hm hn, pow_add]

theorem smoothCorrection_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (smoothCorrection E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨smoothCorrection_one E z, fun {m n} hm hn _ => ?_⟩
  simp only [smoothCorrection, coe_mk, hm, hn, mul_ne_zero hm hn,
    ↓reduceIte, Nat.primeFactors_mul hm hn, union_subset_iff,
    cardFactors_mul hm hn, pow_add, ite_zero_mul_ite_zero]

theorem roughSquarefreeWeight_isMultiplicative (E : Finset ℕ) (z : ℝ) :
    (roughSquarefreeWeight E z).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨roughSquarefreeWeight_one E z, fun {m n} hm hn hmn => ?_⟩
  simp only [roughSquarefreeWeight, coe_mk, Nat.primeFactors_mul hm hn,
    disjoint_union_left, (squarefreeWeight_isMultiplicative z).2 hmn,
    ite_zero_mul_ite_zero]

theorem squarefreeWeight_prime_pow (z : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    squarefreeWeight z (p ^ k) = if k = 1 then z else 0 := by
  by_cases hk1 : k = 1
  · simp [hk1, squarefreeWeight, hp.squarefree, cardFactors_apply_prime hp]
  · have hsq : ¬Squarefree (p ^ k) := by
      rw [Nat.squarefree_pow_iff hp.ne_one hk]
      simp [hk1]
    simp [squarefreeWeight, hsq, hk1]

theorem smoothCorrection_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    smoothCorrection E z (p ^ k) = if p ∈ E then (-z) ^ k else 0 := by
  rw [smoothCorrection, coe_mk, ite_eq_right (pow_ne_zero k hp.ne_zero),
    Nat.primeFactors_pow p hk, hp.primeFactors]
  simp [cardFactors_apply_prime_pow hp]

theorem roughSquarefreeWeight_prime_pow (E : Finset ℕ) (z : ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : k ≠ 0) :
    roughSquarefreeWeight E z (p ^ k) =
      if p ∈ E then 0 else if k = 1 then z else 0 := by
  simp [roughSquarefreeWeight, Nat.primeFactors_pow p hk, hp.primeFactors,
    squarefreeWeight_prime_pow z hp hk]

/-- Only the divisors `1` and `p` contribute from the squarefree weight. -/
theorem squarefreeWeight_convolution_prime_pow (z : ℝ) (h : ArithmeticFunction ℝ)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    (squarefreeWeight z * h) (p ^ k) = h (p ^ k) + z * h (p ^ (k - 1)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => squarefreeWeight z a * h b),
    Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ']
  simp only [pow_zero, squarefreeWeight_one, one_mul, Nat.div_one]
  have hpdiv : p ^ k / p = p ^ (k - 1) := by
    have hh := Nat.pow_div (m := k) (n := 1) (by omega : 1 ≤ k) hp.pos
    simpa only [pow_one] using hh
  simp_rw [squarefreeWeight_prime_pow z hp (Nat.succ_ne_zero _)]
  simp [hk, hpdiv, add_comm]

/-- Removing finitely many Euler factors is exact at every integer. -/
theorem squarefreeWeight_mul_smoothCorrection (E : Finset ℕ) (z : ℝ) :
    squarefreeWeight z * smoothCorrection E z = roughSquarefreeWeight E z := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((squarefreeWeight_isMultiplicative z).mul (smoothCorrection_isMultiplicative E z))
    _ (roughSquarefreeWeight_isMultiplicative E z)).mpr
  intro p k hp
  by_cases hk : k = 0
  · simp [hk]
  rw [squarefreeWeight_convolution_prime_pow z _ hp hk,
    smoothCorrection_prime_pow E z hp hk, roughSquarefreeWeight_prime_pow E z hp hk]
  by_cases hpE : p ∈ E
  · simp only [hpE, ite_eq_left]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp only [hpE, ite_eq_left]
      have hpow : k = (k - 1) + 1 := by omega
      nth_rw 1 [hpow]
      rw [pow_succ]
      ring
  · simp only [hpE, ↓reduceIte, zero_add]
    by_cases hk1 : k = 1
    · simp [hk1]
    · rw [smoothCorrection_prime_pow E z hp (by omega)]
      simp [hpE, hk1]

/-- Exact finite summatory identity used before the analytic truncation. -/
theorem roughSquarefreeWeight_summatory (E : Finset ℕ) (z : ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, roughSquarefreeWeight E z n) =
      ∑ v ∈ Ioc 0 N, smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m := by
  rw [← squarefreeWeight_mul_smoothCorrection, mul_comm]
  exact sum_Ioc_mul_eq_sum_sum _ _ _

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeMassApproximation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing the local odds correction from prime-product masses

For every event, the independent-subset mass differs from the uncorrected
Euler weight by at most the sum of squared selection probabilities.
The resulting prime-tail error is uniform over events.
-/

namespace JointDickman

open Finset

theorem uncorrectedSubsetMass_identity {P S : Finset ℕ} (q : ℕ → ℝ) (hS : S ⊆ P) :
    uncorrectedSubsetMass P q S = bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
  unfold uncorrectedSubsetMass bernoulliSubsetMass
  rw [← prod_sdiff hS (f := fun p => 1 - q p)]
  ring

theorem uncorrectedSubsetMass_le {P S : Finset ℕ} {q : ℕ → ℝ} (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    uncorrectedSubsetMass P q S ≤ bernoulliSubsetMass P q S := by
  rw [uncorrectedSubsetMass_identity q hS]
  have hp : (∏ p ∈ S, (1 - q p)) ≤ 1 := Finset.prod_le_one
    (fun p hp => sub_nonneg.mpr (hq p (hS hp)).2)
    (fun p hp => by linarith [(hq p (hS hp)).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (bernoulliSubsetMass_nonneg hS hq)

theorem uncorrectedSubsetMass_sum (P : Finset ℕ) (q : ℕ → ℝ) :
    (∑ S ∈ P.powerset, uncorrectedSubsetMass P q S) = ∏ p ∈ P, (1 - (q p) ^ 2) := by
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * ∏ p ∈ S, (1 - q p) := by
      apply sum_congr rfl
      intro S hS
      exact uncorrectedSubsetMass_identity q (mem_powerset.mp hS)
    _ = ∏ p ∈ P, (1 - q p + q p * (1 - q p)) := bernoulliSubsetMass_tilt P q _
    _ = _ := prod_congr rfl (fun p _ => by ring)

theorem one_sub_prod_le_sum (P : Finset ℕ) {f : ℕ → ℝ}
    (hf : ∀ p ∈ P, 0 ≤ f p ∧ f p ≤ 1) :
    1 - ∏ p ∈ P, (1 - f p) ≤ ∑ p ∈ P, f p := by
  rw [prod_one_sub_ordered, sub_sub_cancel]
  apply sum_le_sum
  intro p hp
  have hprod : (∏ q ∈ P with q < p, (1 - f q)) ≤ 1 := Finset.prod_le_one
    (fun q hq => sub_nonneg.mpr (hf q (mem_filter.mp hq).1).2)
    (fun q hq => by linarith [(hf q (mem_filter.mp hq).1).1])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (hf p hp).1

open Classical in
theorem uncorrectedSubsetMass_event_error (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P q S else 0)| ≤
      ∑ p ∈ P, (q p) ^ 2 := by
  have hδ (S : Finset ℕ) (hS : S ∈ P.powerset) :
      0 ≤ bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S :=
    sub_nonneg.mpr (uncorrectedSubsetMass_le (mem_powerset.mp hS) hq)
  calc
    _ = |∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0| := by
      congr 1
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro S _
      split_ifs <;> ring
    _ = ∑ S ∈ P.powerset, if E S then
        bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S else 0 :=
      abs_of_nonneg (sum_nonneg (fun S hS => by split_ifs <;> first | exact hδ S hS | rfl))
    _ ≤ ∑ S ∈ P.powerset, (bernoulliSubsetMass P q S - uncorrectedSubsetMass P q S) := by
      apply sum_le_sum
      intro S hS
      split_ifs <;> first | exact le_refl _ | exact hδ S hS
    _ = 1 - ∏ p ∈ P, (1 - (q p) ^ 2) := by
      rw [sum_sub_distrib, bernoulliSubsetMass_sum, uncorrectedSubsetMass_sum]
    _ ≤ _ := one_sub_prod_le_sum P (fun p hp => ⟨sq_nonneg _, by nlinarith [(hq p hp).1, (hq p hp).2]⟩)

open Classical in
/-- The local mass correction is uniformly small without any restriction
on the event or on the size of the selected prime product. -/
theorem primeSubsetMass_event_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (E : Finset ℕ → Prop) :
    |(∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P (fun p => z / p) S else 0) -
      (∑ S ∈ P.powerset, if E S then uncorrectedSubsetMass P (fun p => z / p) S else 0)| ≤
      z ^ 2 / (N : ℝ) := by
  have hq : ∀ p ∈ P, 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨div_nonneg hz hp0.le, (div_le_one hp0).mpr (hz1.trans hp1)⟩
  calc
    _ ≤ ∑ p ∈ P, (z / (p : ℝ)) ^ 2 := uncorrectedSubsetMass_event_error P _ hq E
    _ = z ^ 2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ z ^ 2 * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (sq_nonneg z)
    _ = _ := by ring

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

theorem uncorrectedSubsetMass_harmonic {P S E : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (hE : Disjoint S E) :
    uncorrectedSubsetMass P (fun p => z / p) S =
      primeNormalizer P z * roughSquarefreeWeight E z (∏ p ∈ S, p) / (∏ p ∈ S, p : ℕ) := by
  have hSP : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hrough : roughSquarefreeWeight E z (∏ p ∈ S, p) = z ^ S.card := by
    simp only [roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hSP,
      hE, ite_eq_left, squarefreeWeight, primeProduct_squarefree S hSP,
      primeProduct_cardFactors S hSP]
  rw [hrough]
  simp only [uncorrectedSubsetMass, primeNormalizer, prod_div_distrib, prod_const, Nat.cast_prod]
  ring

theorem uncorrectedPrimeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    uncorrectedPrimeProductMass P z (∏ p ∈ S, p) = uncorrectedSubsetMass P (fun p => z / p) S := by
  classical
  unfold uncorrectedPrimeProductMass
  rw [sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (mem_powerset.mpr hS))

theorem uncorrectedPrimeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    uncorrectedPrimeProductMass P z n = 0 := by
  classical
  apply sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq => hn (mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

theorem uncorrectedPrimeProductMass_harmonic {U : ℝ} {N n : ℕ}
    (hnU : (n : ℝ) ≤ U) (z : ℝ) :
    uncorrectedPrimeProductMass (largePrimeSet U N) z n =
      primeNormalizer (largePrimeSet U N) z * roughSquarefreeWeight (Nat.primesLE N) z n / n := by
  classical
  let P := largePrimeSet U N
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  by_cases hn : n ∈ P.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hn
    have hS : S ⊆ P := mem_powerset.mp hSP
    have hd : Disjoint S (Nat.primesLE N) := by
      apply disjoint_left.mpr
      intro p hp hsmall
      have hgt : (N : ℝ) < p := (mem_filter.mp (hS hp)).2
      have hle : p ≤ N := (Nat.mem_primesLE.mp hsmall).1
      exact (not_lt_of_ge (by exact_mod_cast hle)) hgt
    rw [← hSn, uncorrectedPrimeProductMass_at_product z hP hS]
    exact uncorrectedSubsetMass_harmonic z hP hS hd
  · rw [uncorrectedPrimeProductMass_eq_zero z n hn]
    by_cases hd : Disjoint n.primeFactors (Nat.primesLE N)
    · by_cases hsq : Squarefree n
      · have hsub : n.primeFactors ⊆ P := by
          intro p hp
          have hpprime := Nat.prime_of_mem_primeFactors hp
          have hpn : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hsq.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
          have hpU : (p : ℝ) ≤ U := (by exact_mod_cast hpn : (p : ℝ) ≤ n).trans hnU
          have hpN : N < p := by
            by_contra hnot
            exact disjoint_left.mp hd hp (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
          exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpU, hpprime⟩, by exact_mod_cast hpN⟩
        exact False.elim (hn (mem_image.mpr ⟨n.primeFactors, mem_powerset.mpr hsub,
          Nat.prod_primeFactors_of_squarefree hsq⟩))
      · simp [roughSquarefreeWeight, hd, squarefreeWeight, hsq]
    · simp [roughSquarefreeWeight, hd]

open Classical in
theorem primeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, primeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then bernoulliSubsetMass P (fun p => z / p) S else 0 := by
  unfold primeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

open Classical in
theorem uncorrectedPrimeProductMass_sum_event (P : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ n ∈ K, uncorrectedPrimeProductMass P z n) =
      ∑ S ∈ P.powerset, if (∏ p ∈ S, p) ∈ K then uncorrectedSubsetMass P (fun p => z / p) S else 0 := by
  unfold uncorrectedPrimeProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  simp only [eq_comm (a := ∏ p ∈ S, p)]
  simp

/-- The probability of any bounded set differs from its harmonic rough
weight by at most the reciprocal-square prime tail. -/
theorem primeProductMass_harmonic_error {U : ℝ} {N : ℕ} (hN : N ≠ 0)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (K : Finset ℕ)
    (hK : ∀ n ∈ K, (n : ℝ) ≤ U) :
    |(∑ n ∈ K, primeProductMass (largePrimeSet U N) z n) -
      primeNormalizer (largePrimeSet U N) z *
        ∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n| ≤ z ^ 2 / (N : ℝ) := by
  have heq : primeNormalizer (largePrimeSet U N) z *
      (∑ n ∈ K, roughSquarefreeWeight (Nat.primesLE N) z n / n) =
      ∑ n ∈ K, uncorrectedPrimeProductMass (largePrimeSet U N) z n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [uncorrectedPrimeProductMass_harmonic (hK n hn) z]
    ring
  classical
  have hP : ∀ p ∈ largePrimeSet U (N : ℝ), p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hcut : ∀ p ∈ largePrimeSet U (N : ℝ), N < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have h := primeSubsetMass_event_error (largePrimeSet U (N : ℝ)) hP hN hcut hz hz1
    (fun S : Finset ℕ => (∏ p ∈ S, p) ∈ K)
  rw [heq, primeProductMass_sum_event, uncorrectedPrimeProductMass_sum_event]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1 <;> apply sum_congr rfl <;> intro S _ <;> split_ifs <;> rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RpowTaylor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform power expansion for removing roughness

Taylor expansion is made on the fixed compact interval `[0, 1/2]`.
Its coefficients are independent of the expansion order and of the
moving logarithmic scale.
-/

namespace JointDickman

open Finset Set

theorem rpowShift_contDiff (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun t : ℝ => (1 - t) ^ a) (Icc 0 (1 / 2)) := by
  apply ContDiffOn.rpow_const_of_ne
  · exact contDiffOn_const.sub contDiffOn_id
  · intro t ht
    linarith [ht.2]

theorem rpowShift_taylor_eval (a t : ℝ) (H : ℕ) :
    taylorWithinEval (fun u : ℝ => (1 - u) ^ a) H (Icc 0 (1 / 2)) 0 t =
      ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro k _
  simp only [sub_zero, smul_eq_mul, rpowShiftCoeff]
  ring

theorem rpowShift_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 2 →
      |(1 - t) ^ a - ∑ k ∈ range (H + 1), rpowShiftCoeff a k * t ^ k| ≤
        C * t ^ (H + 1) := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (rpowShift_contDiff a (H + 1))
  refine ⟨max C 0, le_max_right _ _, fun t ht ht1 => ?_⟩
  have h := hC t ⟨ht, ht1⟩
  rw [Real.norm_eq_abs, rpowShift_taylor_eval, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht _))

theorem rpowShift_scaled_term (a L v : ℝ) (k : ℕ) (hL : 0 < L) :
    L ^ a * (rpowShiftCoeff a k * (v / L) ^ k) =
      rpowShiftCoeff a k * v ^ k * L ^ (a - k) := by
  rw [Real.rpow_sub hL, Real.rpow_natCast, div_pow]
  ring

/-- The power expansion with an error uniform throughout `0 ≤ v ≤ L/2`.
The exponent `a` is arbitrary; the application uses `a = z - 1 - j`. -/
theorem rpow_scaled_remainder (a : ℝ) (H : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L v : ℝ, 0 < L → 0 ≤ v → v ≤ L / 2 →
      |(L - v) ^ a - ∑ k ∈ range (H + 1),
        rpowShiftCoeff a k * v ^ k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * v ^ (H + 1) := by
  obtain ⟨C, hC, hbound⟩ := rpowShift_remainder a H
  refine ⟨C, hC, fun L v hL hv hvL => ?_⟩
  have ht : 0 ≤ v / L := div_nonneg hv hL.le
  have ht1 : v / L ≤ 1 / 2 := (div_le_iff₀ hL).mpr (by linarith)
  have hfactor : (L - v) ^ a = L ^ a * (1 - v / L) ^ a := by
    rw [← Real.mul_rpow hL.le (by linarith : 0 ≤ 1 - v / L)]
    congr 1
    field_simp
  have hsum : (∑ k ∈ range (H + 1), rpowShiftCoeff a k * v ^ k * L ^ (a - k)) =
      L ^ a * ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (v / L) ^ k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    exact (rpowShift_scaled_term a L v k hL).symm
  rw [hfactor, hsum, ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg hL.le a)]
  calc
    _ ≤ L ^ a * (C * (v / L) ^ (H + 1)) :=
      mul_le_mul_of_nonneg_left (hbound _ ht ht1) (Real.rpow_nonneg hL.le a)
    _ = _ := by
      rw [Real.rpow_sub hL,
        show (H : ℝ) + 1 = ((H + 1 : ℕ) : ℝ) by norm_cast,
        Real.rpow_natCast, div_pow]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ConvolutionTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite truncation estimates for roughness removal

The large-divisor part of the convolution is bounded before invoking any
Selberg–Delange input. The bound needs only the elementary `|g_z| ≤ 1`.
-/

namespace JointDickman

open Finset

theorem squarefreeWeight_abs_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  unfold squarefreeWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

theorem squarefreeWeight_sum_abs_le {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    |∑ n ∈ Ioc 0 N, squarefreeWeight z n| ≤ N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, |squarefreeWeight z n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := sum_le_sum fun n _ => squarefreeWeight_abs_le_one hz hz1 n
    _ = _ := by simp

theorem roughConvolutionTail_abs_le (E : Finset ℕ) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (N V : ℕ) :
    |roughConvolutionTail E z N V| ≤
      (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
  unfold roughConvolutionTail
  calc
    _ ≤ ∑ v ∈ Ioc V N, |smoothCorrection E z v *
        ∑ m ∈ Ioc 0 (N / v), squarefreeWeight z m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ Ioc V N, (N : ℝ) * (|smoothCorrection E z v| / v) := by
      apply sum_le_sum
      intro v hv
      have hvpos : 0 < v := (mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V)
      have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos').mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [abs_mul]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (squarefreeWeight_sum_abs_le hz hz1 _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ = _ := (mul_sum _ _ _).symm

/-- The elementary Rankin inequality for the harmonic tail. -/
theorem harmonic_tail_rankin {ι : Type*} (s : Finset ι) (v a : ι → ℝ)
    {V ε : ℝ} (hV : 0 < V) (hε : 0 ≤ ε)
    (hv : ∀ i ∈ s, V ≤ v i) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i / v i) ≤
      (∑ i ∈ s, a i / (v i) ^ (1 - ε)) / V ^ ε := by
  have hVpow : 0 < V ^ ε := Real.rpow_pos_of_pos hV _
  apply (le_div_iff₀ hVpow).mpr
  rw [sum_mul]
  apply sum_le_sum
  intro i hi
  have hvi : 0 < v i := hV.trans_le (hv i hi)
  have hpow : V ^ ε ≤ (v i) ^ ε := Real.rpow_le_rpow hV.le (hv i hi) hε
  calc
    a i / v i * V ^ ε ≤ a i / v i * (v i) ^ ε :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg (ha i hi) hvi.le)
    _ = a i / (v i) ^ (1 - ε) := by
      rw [Real.rpow_sub hvi, Real.rpow_one]
      field_simp

/-- Quantitative large-divisor truncation in terms of one weighted moment
of the correction coefficients. -/
theorem roughConvolutionTail_rankin (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    |roughConvolutionTail E z N V| ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have h := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) :=
      roughConvolutionTail_abs_le E hz hz1 N V
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by ring

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

/-- The same constant controls the actual large-divisor convolution error. -/
theorem roughConvolutionTail_shifted_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P N V : ℕ) (z : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |roughConvolutionTail (Nat.primesLE P) z N V| ≤
        (N : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hmoment⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P N V z hP hlog hV hz hzhalf => ?_⟩
  have hlogpos : 0 < Real.log P := by linarith
  exact (roughConvolutionTail_rankin (Nat.primesLE P) hz (by linarith)
    (by positivity) N V hV).trans
      (mul_le_mul_of_nonneg_left (hmoment P (Ioc V N) z hP hlog hz hzhalf)
        (by positivity))

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

/-- Grouping the Taylor terms by their total degree gives the actual
rough coefficients, with no discarded cross terms. -/
theorem roughCoefficient_expansion (c : ℕ → ℝ) (E : Finset ℕ)
    (z L : ℝ) (H : ℕ) :
    (∑ ν ∈ range (H + 1), roughCoefficient c E z ν * L ^ (z - 1 - ν)) =
      ∑ j ∈ range (H + 1), c j *
        ∑ k ∈ range (H - j + 1), rpowShiftCoeff (z - 1 - j) k *
          correctionLogMoment E z k * L ^ (z - 1 - j - k) := by
  let f := fun j k : ℕ => c j * rpowShiftCoeff (z - 1 - j) k *
    correctionLogMoment E z k * L ^ (z - 1 - j - k)
  calc
    _ = ∑ ν ∈ range (H + 1), ∑ j ∈ range (ν + 1), f j (ν - j) := by
      apply sum_congr rfl
      intro ν _
      rw [roughCoefficient, sum_mul]
      apply sum_congr rfl
      intro j hj
      have hjν : j ≤ ν := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      dsimp [f]
      rw [Nat.cast_sub hjν]
      congr 1
      congr 1
      ring
    _ = ∑ j ∈ range (H + 1), ∑ k ∈ range (H + 1 - j), f j k :=
      sum_range_diag_flip (H + 1) f
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
      rw [show H + 1 - j = H - j + 1 by omega, mul_sum]
      apply sum_congr rfl
      intro k _
      dsimp [f]
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

theorem hasDerivAt_logarithmic_model (c : ℕ → ℝ) (E : Finset ℕ) (z : ℝ) (H : ℕ)
    {Y : ℝ} (hY : 1 < Y) :
    HasDerivAt (fun X => X * ∑ j ∈ range (H + 1),
      roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j))
      (roughDensityPolynomial c E z H (Real.log Y)) Y := by
  have hY0 : 0 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hterm : ∀ j ∈ range (H + 1),
      HasDerivAt (fun X => X * (roughCoefficient c E z j * (Real.log X) ^ (z - 1 - j)))
        (roughCoefficient c E z j * ((Real.log Y) ^ (z - 1 - j) +
          (z - 1 - j) * (Real.log Y) ^ (z - 2 - j))) Y := by
    intro j _
    have hp := (Real.hasDerivAt_rpow_const (p := z - 1 - j) (Or.inl hlog.ne')).comp Y
      (Real.hasDerivAt_log hY0.ne')
    refine ((hasDerivAt_id Y).mul (hp.const_mul (roughCoefficient c E z j))).congr_deriv (Eq.symm ?_)
    · dsimp only [Function.comp_def, id_eq]
      rw [show z - 1 - (j : ℝ) - 1 = z - 2 - j by ring]
      field_simp
  refine ((HasDerivAt.fun_sum hterm).congr_of_eventuallyEq (Filter.Eventually.of_forall fun X => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    rw [mul_sum]
  · rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_HarmonicSummation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partial summation for the local prime-product law

Harmonic weighting of a counting estimate costs only the logarithmic
length of the interval. The finite counting function is kept explicit.
-/

namespace JointDickman

open Finset MeasureTheory
open scoped Interval

theorem sum_div_eq_boundary_add_integral (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) =
      finiteCountingFunction w b / b - finiteCountingFunction w a / a +
        ∫ t in a..b, finiteCountingFunction w t / t ^ 2 := by
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hi : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    simp only [deriv_inv']
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).neg.continuousWithinAt
  have h := sum_mul_eq_sub_sub_integral_mul (c := w) ha.le hab hd hi
  rw [← intervalIntegral.integral_of_le hab] at h
  simp only [deriv_inv] at h
  have heq : (fun t : ℝ => -(t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, w n) =
      (fun t => -(finiteCountingFunction w t / t ^ 2)) := by
    funext t
    unfold finiteCountingFunction
    ring
  rw [heq, intervalIntegral.integral_neg] at h
  simpa only [div_eq_mul_inv, mul_comm, finiteCountingFunction, sub_neg_eq_add] using h

theorem finiteCountingFunction_div_sq_integrable (w : ℕ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => finiteCountingFunction w t / t ^ 2) volume a b := by
  have hcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    exact ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0)).continuousWithinAt
  have hi := integrableOn_mul_sum_Icc (m := 0) w ha.le hcont.integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa only [finiteCountingFunction, div_eq_mul_inv, mul_comm] using hi

/-- The integrated counting error is controlled by the logarithmic length. -/
theorem integral_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| ≤ ε * Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  have hmajor : IntervalIntegrable (fun t => ε / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le (Set.uIcc_of_le hab ▸ ht).1)
    fun_prop
  have h := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun t => (finiteCountingFunction w t - F t) / t ^ 2)
    (g := fun t => ε / t) (Filter.Eventually.of_forall (fun t ht => ?_)) hmajor
  · simpa only [Real.norm_eq_abs, div_eq_mul_inv, intervalIntegral.integral_const_mul,
      integral_inv_of_pos ha hb] using h
  have ht0 : 0 < t := ha.trans_le ht.1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
  calc
    _ ≤ ε * t / t ^ 2 := div_le_div_of_nonneg_right (herr t ⟨ht.1.le, ht.2⟩) (sq_nonneg t)
    _ = ε / t := by field_simp

/-- Harmonic weighting loses at most two endpoint errors and one logarithm. -/
theorem harmonic_counting_error_le (w : ℕ → ℝ) (F : ℝ → ℝ) {a b ε : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (herr : ∀ t ∈ Set.Icc a b, |finiteCountingFunction w t - F t| ≤ ε * t) :
    |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, w n / (n : ℝ)) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2)| ≤
        ε * (2 + Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hF.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hGi := finiteCountingFunction_div_sq_integrable w ha hab
  have hint : (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (∫ t in a..b, F t / t ^ 2) =
      ∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2 := by
    rw [← intervalIntegral.integral_sub hGi hFi]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a b) :
      |(finiteCountingFunction w t - F t) / t| ≤ ε := by
    have ht0 : 0 < t := ha.trans_le ht.1
    rw [abs_div, abs_of_pos ht0]
    exact (div_le_iff₀ ht0).mpr (herr t ht)
  rw [sum_div_eq_boundary_add_integral w ha hab]
  have heq : finiteCountingFunction w b / b - finiteCountingFunction w a / a +
      (∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
      (F b / b - F a / a + ∫ t in a..b, F t / t ^ 2) =
      ((finiteCountingFunction w b - F b) / b - (finiteCountingFunction w a - F a) / a) +
        ((∫ t in a..b, finiteCountingFunction w t / t ^ 2) -
          (∫ t in a..b, F t / t ^ 2)) := by ring
  rw [heq, hint]
  calc
    _ ≤ |(finiteCountingFunction w b - F b) / b| + |(finiteCountingFunction w a - F a) / a| +
        |∫ t in a..b, (finiteCountingFunction w t - F t) / t ^ 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ ≤ ε + ε + ε * Real.log (b / a) :=
      add_le_add (add_le_add (hbound b ⟨hab, le_rfl⟩) (hbound a ⟨le_rfl, hab⟩))
        (integral_counting_error_le w F ha hab herr)
    _ = _ := by ring

/-- Integration of the model's derivative gives the same harmonic model. -/
theorem harmonic_model_integral (F M : ℝ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hF : ∀ t ∈ Set.Icc a b, HasDerivAt F (M t) t)
    (hM : ContinuousOn M (Set.Icc a b)) :
    (∫ t in a..b, M t / t) = F b / b - F a / a + ∫ t in a..b, F t / t ^ 2 := by
  have hFc : ContinuousOn F (Set.Icc a b) := fun t ht => (hF t ht).continuousAt.continuousWithinAt
  have hMi : IntervalIntegrable (fun t => M t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hM.div continuousOn_id (fun t ht => ne_of_gt (ha.trans_le ht.1))
  have hFi : IntervalIntegrable (fun t => F t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hFc.div (continuousOn_id.pow 2) (fun t ht => pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => F x / x) (M t / t - F t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ht.1)
    refine ((hF t ht).div (hasDerivAt_id t) ht0).congr_deriv (Eq.symm ?_)
    · dsimp only [id_eq]
      field_simp
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hMi.sub hFi)
  rw [intervalIntegral.integral_sub hMi hFi] at h
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughErrorLimits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Decay of the roughness-cutoff errors

The exponential Rankin error absorbs every fixed power of the scale
and of its logarithm. This is the limit needed after the explicit
moving-cutoff expansion.
-/

namespace JointDickman

open Filter Asymptotics
open scoped Topology

theorem rough_exponential_error_tendsto {a K C : ℝ}
    (ha : 0 < a) (hK : 0 < K) (hC : 0 ≤ C) (D : ℝ) :
    Tendsto (fun B : ℝ => B ^ D * (Real.log B) ^ C *
      Real.exp (-(B ^ a / (K * Real.log B)))) atTop (𝓝 0) := by
  have ha2 : 0 < a / 2 := by positivity
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((D + C) / (a / 2)) (1 / K) (by positivity)).comp (tendsto_rpow_atTop ha2)
  have hlim : Tendsto (fun B : ℝ => B ^ (D + C) *
      Real.exp (-(1 / K) * B ^ (a / 2))) atTop (𝓝 0) := by
    apply hbase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
    dsimp
    rw [← Real.rpow_mul hB.le]
    congr 2
    field_simp
  have hsmall := (isLittleO_log_rpow_atTop ha2).def (by norm_num : (0 : ℝ) < 1)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (Real.log_pos hB).le _))
      (Real.exp_pos _).le
  · filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with B hB hs
    have hB0 : 0 < B := by linarith
    have hlog : 0 < Real.log B := Real.log_pos hB
    have hlogpow : Real.log B ≤ B ^ (a / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hlog,
        abs_of_pos (Real.rpow_pos_of_pos hB0 _), one_mul] using hs
    have hlogB : Real.log B ≤ B := by linarith [Real.log_le_sub_one_of_pos hB0]
    have hlogC : (Real.log B) ^ C ≤ B ^ C :=
      Real.rpow_le_rpow hlog.le hlogB hC
    have hden : K * Real.log B ≤ K * B ^ (a / 2) :=
      mul_le_mul_of_nonneg_left hlogpow hK.le
    have hquot : (1 / K) * B ^ (a / 2) ≤ B ^ a / (K * Real.log B) := by
      calc
        _ = B ^ a / (K * B ^ (a / 2)) := by
          have hsquare : B ^ a = B ^ (a / 2) * B ^ (a / 2) := by
            rw [← Real.rpow_add hB0]
            congr 1
            ring
          rw [hsquare]
          field_simp
        _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hB0.le _)
          (mul_pos hK hlog) hden
    have hexp : Real.exp (-(B ^ a / (K * Real.log B))) ≤
        Real.exp (-(1 / K) * B ^ (a / 2)) := by
      apply Real.exp_le_exp.mpr
      linarith
    calc
      _ ≤ (B ^ D * B ^ C) * Real.exp (-(1 / K) * B ^ (a / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogC (Real.rpow_nonneg hB0.le _))
          hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by rw [← Real.rpow_add hB0]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CorrectionTails
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the logarithmic correction moments

Half of the exponential tilt absorbs the logarithmic moment; the other
half yields decay in the truncation point.
-/

namespace JointDickman

open Finset

theorem log_pow_tail_bound (k : ℕ) {v V ε : ℝ}
    (hv : 1 ≤ v) (hV : 0 < V) (hVv : V ≤ v) (hε : 0 < ε) :
    (Real.log v) ^ k ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * v ^ ε := by
  have hhalf : 0 < ε / 2 := by positivity
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hcut := Real.rpow_le_rpow hV.le hVv hhalf.le
  have hlog := log_pow_le_rpow k hv hhalf
  have hfact : 0 ≤ (k.factorial : ℝ) / (ε / 2) ^ k := by positivity
  have hmul := mul_le_mul hlog hcut (Real.rpow_nonneg hV.le _) (mul_nonneg hfact
    (Real.rpow_nonneg hv0.le _))
  have hsquare : v ^ (ε / 2) * v ^ (ε / 2) = v ^ ε := by
    rw [← Real.rpow_add hv0]
    congr 1
    ring
  have hquot := (le_div_iff₀ (Real.rpow_pos_of_pos hV _)).mpr hmul
  calc
    _ ≤ (((k.factorial : ℝ) / (ε / 2) ^ k * v ^ (ε / 2)) * v ^ (ε / 2)) /
        V ^ (ε / 2) := hquot
    _ = _ := by rw [mul_assoc, hsquare]; ring

theorem correctionLogTerm_tail_bound (E : Finset ℕ) (z : ℝ) (k : ℕ)
    {n : ℕ} {V ε : ℝ} (hV : 0 < V) (hn : V ≤ n) (hε : 0 < ε) :
    ‖correctionLogTerm E z k n‖ ≤
      ((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) *
        (|smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)) := by
  have hn0 : (0 : ℝ) < n := hV.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  rw [correctionLogTerm_norm]
  calc
    _ ≤ (|smoothCorrection E z n| / (n : ℝ)) *
        (((k.factorial : ℝ) / (ε / 2) ^ k / V ^ (ε / 2)) * (n : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left (log_pow_tail_bound k hn1 hV hn hε) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
      field_simp

/-- A uniform quantitative error when replacing a truncated correction
moment by its convergent full value. -/
theorem correctionLogMoment_tail_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P V : ℕ) (z : ℝ) (k : ℕ),
      2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 ≤ z → z ≤ 1 / 2 →
      |correctionLogMoment (Nat.primesLE P) z k -
        ∑ n ∈ range (V + 1), correctionLogTerm (Nat.primesLE P) z k n| ≤
          ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
            (V : ℝ) ^ ((1 / Real.log P) / 2)) *
              (A * (Real.log P) ^ (Real.exp 1)) := by
  obtain ⟨A, hA, hbound⟩ := smoothCorrection_shifted_bound hM
  refine ⟨A, hA, fun P V z k hP hlog hV hz hzhalf => ?_⟩
  let E := Nat.primesLE P
  let ε := 1 / Real.log (P : ℝ)
  let D := (k.factorial : ℝ) / (ε / 2) ^ k / (V : ℝ) ^ (ε / 2)
  let f := correctionLogTerm E z k
  let g := fun n : ℕ => |smoothCorrection E z n| / (n : ℝ) ^ (1 - ε)
  have hε : 0 < ε := by dsimp [ε] <;> positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by linarith)).mpr hlog
  have hVreal : (0 : ℝ) < V := by exact_mod_cast hV
  have hD : 0 ≤ D := by dsimp [D] <;> positivity
  have hg : Summable g :=
    (smoothCorrection_abs_hasSum E hz (by linarith) (by linarith : 0 ≤ 1 - ε)).summable
  have hf := correctionLogTerm_summable E hz (by linarith) k
  have hnorm : Summable (fun n : {n // n ∉ range (V + 1)} => ‖f n‖) := hf.subtype _
  have hgD : Summable (fun n => D * g n) := hg.mul_left D
  have hcomparison : (∑' n : {n // n ∉ range (V + 1)}, ‖f n‖) ≤
      ∑' n : ℕ, D * g n := by
    apply Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun n _ => mul_nonneg hD (by dsimp [g] <;> positivity)) _ hnorm hgD
    intro n
    have hnV : V < n.val := by
      have hnrange := n.property
      simp only [mem_range] at hnrange
      omega
    exact correctionLogTerm_tail_bound E z k hVreal (by exact_mod_cast hnV.le) hε
  have htotal : (∑' n, g n) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    apply hg.tsum_le_of_sum_le
    intro S
    exact hbound P S z hP hlog hz hzhalf
  have hsplit := hf.of_norm.sum_add_tsum_subtype_compl (range (V + 1))
  have heq : correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n =
      ∑' n : {n // n ∉ range (V + 1)}, f n := by
    change (∑' n, f n) - _ = _
    linarith [hsplit]
  change |correctionLogMoment E z k - ∑ n ∈ range (V + 1), f n| ≤ D * _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' n : {n // n ∉ range (V + 1)}, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, D * g n := hcomparison
    _ = D * ∑' n, g n := hg.tsum_mul_left D
    _ ≤ _ := mul_le_mul_of_nonneg_left htotal hD

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedPowerExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Taylor expansion inside the correction convolution

This is the finite-sum expansion before the truncated moments are
replaced by their convergent infinite-series values.
-/

namespace JointDickman

open Finset

theorem truncatedLogMoment_eq_range (E : Finset ℕ) (z : ℝ) (V k : ℕ) :
    truncatedLogMoment E z V k = ∑ v ∈ range (V + 1), correctionLogTerm E z k v := by
  have hset : insert 0 (Ioc 0 V) = range (V + 1) := by
    ext n
    simp only [mem_insert, mem_Ioc, mem_range]
    omega
  rw [← hset, sum_insert (by simp)]
  simp [truncatedLogMoment, correctionLogTerm]

theorem correction_expansion_reindex (E : Finset ℕ) (z a L : ℝ) (V H : ℕ) :
    (∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        ∑ k ∈ range (H + 1), rpowShiftCoeff a k * (Real.log v) ^ k * L ^ (a - k) := by
  unfold truncatedLogMoment correctionLogTerm
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro k _
  ring

/-- Expansion using the full correction moments. Both errors are explicit:
the Taylor remainder and the exponentially tilted tails of the moments. -/
theorem correction_power_expansion_full
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ A : ℝ, 0 < A ∧ ∀ (z a : ℝ) (H : ℕ), 0 ≤ z → z ≤ 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (P V : ℕ) (L : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 0 < L →
        (∀ v ∈ Ioc 0 V, Real.log v ≤ L / 2) →
        |(∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
            (L - Real.log v) ^ a) -
          ∑ k ∈ range (H + 1), rpowShiftCoeff a k *
            correctionLogMoment (Nat.primesLE P) z k * L ^ (a - k)| ≤
          C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            A * (Real.log P) ^ (Real.exp 1) *
              ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
                ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
                  (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨A, hA, htail⟩ := correctionLogMoment_tail_bound hM
  obtain ⟨B, hB, hmom⟩ := smoothCorrection_log_moments_bound hM
  refine ⟨A, hA, fun z a H hz hzhalf => ?_⟩
  -- The Taylor constant depends only on the exponent and order.
  obtain ⟨C₀, hC₀, hunit⟩ := rpow_scaled_remainder a H
  refine ⟨C₀ * B * ((H + 1).factorial : ℝ), by positivity,
    fun P V L hP hlog hV hL hsmall => ?_⟩
  let E := Nat.primesLE P
  let T := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k)
  let F := ∑ k ∈ range (H + 1), rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k)
  have hfirst : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      C₀ * L ^ (a - (H + 1)) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) * (Real.log v) ^ (H + 1) := by
    dsimp only [T]
    rw [correction_expansion_reindex, ← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    rw [← mul_sub, abs_mul, abs_div, abs_of_pos hv0]
    exact (mul_le_mul_of_nonneg_left
      (hunit L (Real.log v) hL (Real.log_natCast_nonneg v) (hsmall v hv))
        (by positivity)).trans_eq (by ring)
  have hfirst' : |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - T| ≤
      (C₀ * B * ((H + 1).factorial : ℝ)) * L ^ (a - (H + 1)) *
        (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply hfirst.trans
    have h := mul_le_mul_of_nonneg_left
      (hmom P (Ioc 0 V) z (H + 1) hP hlog hz hzhalf)
      (mul_nonneg hC₀ (Real.rpow_nonneg hL.le (a - ((H : ℝ) + 1))))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hsecond : |T - F| ≤ A * (Real.log P) ^ (Real.exp 1) *
      ∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
        ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
          (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
    dsimp [T, F]
    rw [← sum_sub_distrib, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k _
    have hk := htail P V z k hP hlog hV hz hzhalf
    rw [← truncatedLogMoment_eq_range, abs_sub_comm] at hk
    have heq : rpowShiftCoeff a k * truncatedLogMoment E z V k * L ^ (a - k) -
        rpowShiftCoeff a k * correctionLogMoment E z k * L ^ (a - k) =
        (rpowShiftCoeff a k * L ^ (a - k)) *
          (truncatedLogMoment E z V k - correctionLogMoment E z k) := by ring
    rw [heq, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hL _)]
    exact (mul_le_mul_of_nonneg_left hk (by positivity)).trans_eq (by ring)
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      (L - Real.log v) ^ a) - F =
      ((∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - T) +
        (T - F) := by ring
  change |(∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) * (L - Real.log v) ^ a) - F| ≤ _
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hfirst' hsecond)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughSelbergDelange
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Applying the published expansion inside the roughness convolution

The expansion is inserted only below the truncation, where its endpoint
and logarithmic hypotheses hold. The complementary terms remain the
actual convolution tail, already controlled by Rankin's bound.
-/

namespace JointDickman

open Finset

/-- The usual square-root truncation meets both local expansion conditions. -/
theorem square_root_truncation_conditions {Y : ℝ} {V : ℕ}
    (hY : 9 ≤ Y) (hV : (V : ℝ) ^ 2 ≤ Y) :
    V ≤ ⌊Y⌋₊ ∧ ∀ v ∈ Ioc 0 V,
      3 ≤ Y / (v : ℝ) ∧ Real.log Y / 2 ≤ Real.log (Y / (v : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg V
  refine ⟨Nat.le_floor (by nlinarith), fun v hv => ?_⟩
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hvV : (v : ℝ) ≤ V := by exact_mod_cast (mem_Ioc.mp hv).2
  have hv2 : (v : ℝ) ^ 2 ≤ Y := by nlinarith
  constructor
  · apply (le_div_iff₀ hv0).mpr
    nlinarith
  · have hlog := Real.log_le_log (sq_pos_of_pos hv0) hv2
    rw [Real.log_pow] at hlog
    rw [Real.log_div hY0.ne' hv0.ne']
    norm_num at hlog
    linarith

theorem roughSquarefreeSummatory_split (E : Finset ℕ) (z Y : ℝ)
    (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughSquarefreeSummatory E z Y =
      (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) +
        roughConvolutionTail E z ⌊Y⌋₊ V := by
  unfold roughSquarefreeSummatory
  rw [roughSquarefreeWeight_summatory,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  apply sum_congr rfl
  intro v _
  simp only [squarefreeSummatory, Nat.floor_div_natCast]

theorem smallConvolution_SD_error (E : Finset ℕ) (c : ℕ → ℝ)
    (z Y : ℝ) (H V : ℕ) {C : ℝ} (hC : 0 ≤ C) (hY : 1 < Y)
    (hz : z ≤ 1)
    (hSD : ∀ X : ℝ, 3 ≤ X →
      |squarefreeSummatory z X - X * sdPolynomial c z H (Real.log X)| ≤
        C * X * (Real.log X) ^ (z - 2 - H))
    (hsize : ∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) :
    |(∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v))| ≤
      C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
        ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have heq : (∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
      Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
        sdPolynomial c z H (Real.log (Y / v)) =
      ∑ v ∈ Ioc 0 V, smoothCorrection E z v *
        (squarefreeSummatory z (Y / v) -
          (Y / v) * sdPolynomial c z H (Real.log (Y / v))) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro v _
    ring
  rw [heq, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) hexp
  rw [abs_mul]
  calc
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log (Y / v)) ^ (z - 2 - H)) :=
      mul_le_mul_of_nonneg_left (hSD _ (hsize v hv)) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| *
        (C * (Y / v) * (Real.log Y / 2) ^ (z - 2 - H)) := by
      gcongr
    _ = _ := by ring

/-- Direct consequence of the published fixed-order expansion, with an
explicit remaining tail and no assumed moving-cutoff estimate. -/
theorem roughSelbergDelange_truncated
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
        1 < Y → V ≤ ⌊Y⌋₊ →
        (∀ v ∈ Ioc 0 V, 3 ≤ Y / (v : ℝ)) →
        (∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / (v : ℝ))) →
        |roughSquarefreeSummatory E z Y -
          Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
            sdPolynomial c z H (Real.log (Y / v))| ≤
          C * Y * (Real.log Y / 2) ^ (z - 2 - H) *
            (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
              |roughConvolutionTail E z ⌊Y⌋₊ V| := by
  obtain ⟨c, hc0, hcpos, horders⟩ := hSD z hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨C, hC, hbound⟩ := horders H
  refine ⟨C, hC, fun E Y V hY hV hsize hlog => ?_⟩
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hsmall := smallConvolution_SD_error E c z Y H V hC hY hz1 hbound hsize hlog
  rw [roughSquarefreeSummatory_split E z Y V hV]
  calc
    _ = |((∑ v ∈ Ioc 0 V, smoothCorrection E z v * squarefreeSummatory z (Y / v)) -
        Y * ∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
          sdPolynomial c z H (Real.log (Y / v))) +
            roughConvolutionTail E z ⌊Y⌋₊ V| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingRoughExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion with explicit errors

The classical expansion, Taylor approximation, and correction-moment
tails are now combined for the actual rough squarefree summatory function.
No moving-cutoff asymptotic is used as an input.
-/

namespace JointDickman

open Finset

/-- For the nonpositive powers occurring here, the moment-tail sum is
bounded by a single fixed logarithmic power. -/
theorem powerExpansionError_le {A C a L : ℝ} {H P V : ℕ}
    (hA : 0 ≤ A) (ha : a ≤ 0) (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C a H P V L ≤
      C * L ^ (a - (H + 1)) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hV0 : (0 : ℝ) < V := by exact_mod_cast hV
  have hVpow : 0 < (V : ℝ) ^ ((1 / Real.log P) / 2) := Real.rpow_pos_of_pos hV0 _
  have hsum : (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * L ^ (a - k) *
      ((k.factorial : ℝ) / ((1 / Real.log P) / 2) ^ k /
        (V : ℝ) ^ ((1 / Real.log P) / 2))) ≤
      (∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
        (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
    rw [sum_mul, sum_div]
    apply sum_le_sum
    intro k hk
    have hkH : k ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hk
    have hpow : (Real.log P) ^ k ≤ (Real.log P) ^ H := pow_le_pow_right₀ hlog hkH
    have hunit : L ^ (a - k) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith [Nat.cast_nonneg k (α := ℝ)])
    have hc : 0 ≤ |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k := by positivity
    calc
      _ = (|rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          ((Real.log P) ^ k * L ^ (a - k)) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
        simp only [div_pow, one_pow]
        field_simp
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hVpow.le
        apply mul_le_mul_of_nonneg_left _ hc
        simpa using mul_le_mul hpow hunit (Real.rpow_nonneg hL0.le _) (by positivity : (0 : ℝ) ≤ (Real.log P) ^ H)
  unfold powerExpansionError
  refine add_le_add (le_refl _) ?_
  calc
    _ ≤ A * (Real.log P) ^ (Real.exp 1) *
        ((∑ k ∈ range (H + 1), |rpowShiftCoeff a k| * (k.factorial : ℝ) * 2 ^ k) *
          (Real.log P) ^ H / (V : ℝ) ^ ((1 / Real.log P) / 2)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA (Real.rpow_nonneg hlog0.le _))
    _ = _ := by
      rw [Real.rpow_add hlog0, Real.rpow_natCast]
      ring

theorem correction_sdPolynomial_reindex (c : ℕ → ℝ) (E : Finset ℕ)
    (z Y : ℝ) (H V : ℕ) (hY : 0 < Y) :
    (∑ v ∈ Ioc 0 V, smoothCorrection E z v / (v : ℝ) *
      sdPolynomial c z H (Real.log (Y / v))) =
      ∑ j ∈ range (H + 1), c j * ∑ v ∈ Ioc 0 V,
        smoothCorrection E z v / (v : ℝ) * (Real.log Y - Real.log v) ^ (z - 1 - j) := by
  unfold sdPolynomial
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro v hv
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [Real.log_div hY.ne' hv0.ne']
  ring

/-- The actual expansion with separately identified classical, Rankin,
Taylor, and moment-tail errors. Its coefficients are the defined moments. -/
theorem moving_rough_expansion_explicit
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ A : ℝ, 0 < A ∧ ∀ H : ℕ, ∃ Csd : ℝ, ∃ C : ℕ → ℝ,
        0 ≤ Csd ∧ (∀ j, 0 ≤ C j) ∧ ∀ (P V : ℕ) (Y : ℝ),
          2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → (V : ℝ) ^ 2 ≤ Y →
          |roughSquarefreeSummatory (Nat.primesLE P) z Y -
            Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤
            Csd * Y * (Real.log Y / 2) ^ (z - 2 - H) *
              (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) +
              |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| +
              Y * ∑ j ∈ range (H + 1), |c j| *
                powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
  obtain ⟨c, hc0, hcpos, hclassical⟩ := roughSelbergDelange_truncated hSD hz
  obtain ⟨A, hA, hexp⟩ := correction_power_expansion_full hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, A, hA, fun H => ?_⟩
  obtain ⟨Csd, hCsd, hraw⟩ := hclassical H
  have hexists := fun j : ℕ => hexp z (z - 1 - j) (H - j) hz0 hzhalf
  choose C hC hpower using hexists
  refine ⟨Csd, C, hCsd, hC, fun P V Y hP hlogP hV hY hV2 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have hL : 0 < Real.log Y := Real.log_pos hY1
  obtain ⟨hVfloor, hcut⟩ := square_root_truncation_conditions hY hV2
  have hsmall : ∀ v ∈ Ioc 0 V, Real.log v ≤ Real.log Y / 2 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
    have hh := (hcut v hv).2
    rw [Real.log_div hY0.ne' hv0.ne'] at hh
    linarith
  let W := ∑ v ∈ Ioc 0 V, smoothCorrection (Nat.primesLE P) z v / (v : ℝ) *
    sdPolynomial c z H (Real.log (Y / v))
  let Q := ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
    (Real.log Y) ^ (z - 1 - ν)
  have hfirst := hraw (Nat.primesLE P) Y V hY1 hVfloor
    (fun v hv => (hcut v hv).1) (fun v hv => (hcut v hv).2)
  have hsecond : |W - Q| ≤ ∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V (Real.log Y) := by
    dsimp [W, Q]
    rw [correction_sdPolynomial_reindex c _ z Y H V hY0,
      roughCoefficient_expansion, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j hj
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hpower j P V (Real.log Y) hP hlogP hV hL hsmall
  have heq : roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q =
      (roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W) + Y * (W - Q) := by ring
  change |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * Q| ≤ _
  rw [heq]
  calc
    _ ≤ |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + |Y * (W - Q)| :=
      abs_add_le _ _
    _ = |roughSquarefreeSummatory (Nat.primesLE P) z Y - Y * W| + Y * |W - Q| := by
      rw [abs_mul, abs_of_pos hY0]
    _ ≤ _ := add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hY0.le)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughUniformExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform remainder for removal of small primes

The four explicit errors are bounded by one algebraic remainder and one
Rankin remainder. All constants are independent of the cutoff and endpoint.
-/

namespace JointDickman

open Finset

theorem powerTailConstant_nonneg (a : ℝ) (H : ℕ) :
    0 ≤ powerTailConstant a H := sum_nonneg (fun _ _ => by positivity)

theorem powerExpansionError_le_uniform {A C z L : ℝ} {H j P V : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hz : z ≤ 1) (hj : j ≤ H)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log P) (hV : 0 < V) :
    powerExpansionError A C (z - 1 - j) (H - j) P V L ≤
      C * L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        A * powerTailConstant (z - 1 - j) (H - j) *
          (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsub : ((H - j : ℕ) : ℝ) = H - j := Nat.cast_sub hj
  have hexp : z - 1 - j - ((H - j : ℕ) + 1) = z - 2 - H := by
    rw [hsub]
    ring
  have hpow1 : (Real.log P) ^ (Real.exp 1 + (H - j + 1 : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j + 1 : ℕ) : ℝ) ≤ (H + 1 : ℕ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le H j) 1
    linarith
  have hpow2 : (Real.log P) ^ (Real.exp 1 + (H - j : ℕ)) ≤
      (Real.log P) ^ (Real.exp 1 + H) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hcast : ((H - j : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H j
    linarith
  have h := powerExpansionError_le (C := C) (H := H - j) hA (by linarith : z - 1 - j ≤ 0) hL hlog hV
  rw [hexp] at h
  refine h.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_left hpow1 (by positivity)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hpow2
      (mul_nonneg hA (powerTailConstant_nonneg _ _))

/-- A single cutoff-independent bound for the complete moving expansion. -/
theorem moving_rough_expansion_uniform
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P V : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 0 < V → 9 ≤ Y → 1 ≤ Real.log Y →
        (V : ℝ) ^ 2 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)) := by
  obtain ⟨c, hc0, hcpos, A, hA, hraw⟩ := moving_rough_expansion_explicit hSD hM hz
  obtain ⟨M, hMpos, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨T, hTpos, htail⟩ := roughConvolutionTail_shifted_bound hM
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzhalf : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨Csd, C, hCsd, hC, hbound⟩ := hraw H
  let E := Csd * M * (2 : ℝ) ^ (-(z - 2 - H))
  let F := ∑ j ∈ range (H + 1), |c j| * C j
  let G := ∑ j ∈ range (H + 1), |c j| * A * powerTailConstant (z - 1 - j) (H - j)
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hF : 0 ≤ F := sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC j))
  have hG : 0 ≤ G := sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (abs_nonneg _) hA.le) (powerTailConstant_nonneg _ _))
  refine ⟨E + F + T + G, by positivity, fun P V Y hP hlog hV hY hLY hV2 => ?_⟩
  let L := Real.log Y
  let U := L ^ (z - 2 - H) * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))
  let W := (Real.log P) ^ (Real.exp 1 + H) / (V : ℝ) ^ ((1 / Real.log P) / 2)
  have hL : 0 < L := by dsimp [L] <;> linarith
  have hlog0 : 0 < Real.log P := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hU : 0 ≤ U := by dsimp [U] <;> positivity
  have hW : 0 ≤ W := by dsimp [W] <;> positivity
  have hm := hmom P (Ioc 0 V) z 0 hP hlog hz0 hzhalf
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, add_zero] at hm
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤
      (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hlog
    have hn : (0 : ℝ) ≤ (H + 1 : ℕ) := Nat.cast_nonneg _
    linarith
  have hclassical : Csd * Y * (L / 2) ^ (z - 2 - H) *
      (∑ v ∈ Ioc 0 V, |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤
      Y * E * U := by
    calc
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ Csd * Y * (L / 2) ^ (z - 2 - H) *
          (M * (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ))) := by gcongr
      _ = _ := by
        dsimp [E, U]
        rw [Real.div_rpow hL.le (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
  have htail' : |roughConvolutionTail (Nat.primesLE P) z ⌊Y⌋₊ V| ≤ Y * T * W := by
    have h := htail P ⌊Y⌋₊ V z hP hlog hV hz0 hzhalf
    have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
    have hp : (V : ℝ) ^ ((1 / Real.log P) / 2) ≤ (V : ℝ) ^ (1 / Real.log P) := by
      apply Real.rpow_le_rpow_of_exponent_le hV1
      have hpos : 0 < 1 / Real.log P := by positivity
      linarith
    have hlogpow' : (Real.log P) ^ (Real.exp 1) ≤
        (Real.log P) ^ (Real.exp 1 + H) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      linarith [Nat.cast_nonneg H (α := ℝ)]
    calc
      _ ≤ (⌊Y⌋₊ : ℝ) / (V : ℝ) ^ (1 / Real.log P) *
          (T * (Real.log P) ^ (Real.exp 1)) := h
      _ ≤ Y / (V : ℝ) ^ ((1 / Real.log P) / 2) *
          (T * (Real.log P) ^ (Real.exp 1 + H)) := by
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact div_le_div₀ (by positivity) (Nat.floor_le hY0) (by positivity) hp
        · exact mul_le_mul_of_nonneg_left hlogpow' hTpos.le
      _ = _ := by dsimp [W] <;> ring
  have hpowers : (∑ j ∈ range (H + 1), |c j| *
      powerExpansionError A (C j) (z - 1 - j) (H - j) P V L) ≤ F * U + G * W := by
    calc
      _ ≤ ∑ j ∈ range (H + 1), |c j| * (C j * U +
          A * powerTailConstant (z - 1 - j) (H - j) * W) := by
        apply sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hjH : j ≤ H := by simpa only [mem_range, Nat.lt_succ_iff] using hj
        simpa only [U, W, mul_div_assoc, mul_assoc] using
          powerExpansionError_le_uniform hA.le (hC j) (by linarith : z ≤ 1) hjH hLY hlog hV
      _ = _ := by
        dsimp [F, G]
        simp only [mul_add, sum_add_distrib, sum_mul]
        apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intro j _ <;> ring
  have h := hbound P V Y hP hlog hV hY hV2
  change _ ≤ Y * (E + F + T + G) * (U + W)
  refine h.trans ?_
  change _ + _ + Y * _ ≤ _
  have hsum := add_le_add (add_le_add hclassical htail')
    (mul_le_mul_of_nonneg_left hpowers hY0)
  refine hsum.trans ?_
  nlinarith [mul_nonneg hY0 (mul_nonneg (add_nonneg hE hF) hW),
    mul_nonneg hY0 (mul_nonneg (add_nonneg hTpos.le hG) hU)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughCutoffTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Choosing the roughness truncation

An integer square-root truncation turns the remaining Rankin error into
an explicit exponential in the endpoint logarithm.
-/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_bounds {Y : ℝ} (hY : 0 < Y) (hL : 16 ≤ Real.log Y) :
    0 < roughTruncation Y ∧ (roughTruncation Y : ℝ) ^ 2 ≤ Y ∧
      Real.log Y / 4 ≤ Real.log (roughTruncation Y) := by
  let t := Real.exp (Real.log Y / 2)
  have ht0 : 0 < t := Real.exp_pos _
  have ht2 : 2 ≤ t := by
    have h := Real.add_one_le_exp (Real.log Y / 2)
    dsimp [t]
    linarith
  have ht1 : 1 ≤ t := by linarith
  have hV : 0 < roughTruncation Y := Nat.floor_pos.mpr ht1
  have hVle : (roughTruncation Y : ℝ) ≤ t := Nat.floor_le ht0.le
  have hVhalf : t / 2 ≤ (roughTruncation Y : ℝ) := by
    have h := Nat.lt_floor_add_one t
    change t < (roughTruncation Y : ℝ) + 1 at h
    linarith
  refine ⟨hV, ?_, ?_⟩
  · have heq : t ^ 2 = Y := by
      dsimp [t]
      rw [sq, ← Real.exp_add, add_halves, Real.exp_log hY]
    have hV0 : (0 : ℝ) ≤ roughTruncation Y := Nat.cast_nonneg _
    nlinarith
  · have h := Real.log_le_log (div_pos ht0 (by norm_num)) hVhalf
    rw [Real.log_div ht0.ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at h
    have hlog2 := Real.log_two_lt_d9
    linarith

theorem roughTruncation_rankin {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ ((1 / Real.log P) / 2) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ (1 / Real.log P) / 2 by positivity)
  have heq : (Real.log Y / 4) * ((1 / Real.log P) / 2) =
      Real.log Y / (8 * Real.log P) := by ring
  rw [heq] at h
  linarith

/-- The complete roughness expansion before substituting `P = B^1000`. -/
theorem moving_rough_expansion_exponential
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∀ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
        2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
        |roughSquarefreeSummatory (Nat.primesLE P) z Y -
          Y * ∑ ν ∈ range (H + 1), roughCoefficient c (Nat.primesLE P) z ν *
            (Real.log Y) ^ (z - 1 - ν)| ≤
          Y * K * ((Real.log Y) ^ (z - 2 - H) *
            (Real.log P) ^ (Real.exp 1 + (H + 1 : ℕ)) +
            (Real.log P) ^ (Real.exp 1 + H) *
              Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_uniform hSD hM hz
  refine ⟨c, hc0, hcpos, fun H => ?_⟩
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨K, hK, fun P Y hP hlog hY hL => ?_⟩
  have hY0 : 0 < Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  refine (hbound P (roughTruncation Y) Y hP hlog hV hY (by linarith) hV2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hY0.le hK)
  apply add_le_add (le_refl _)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (roughTruncation_rankin hY0 hL (by linarith))
    (Real.rpow_nonneg (by linarith) _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughAuxiliaryExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The moving-cutoff expansion on the manuscript's auxiliary scale

The remainder is uniform once `log Y ≥ B^0.89`. Its decay is derived
from the explicit expansion, rather than assumed as an analytic input.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughErrorEnvelope_tendsto {z D : ℝ} {H : ℕ}
    (hH : D + (89 / 100 : ℝ) * (z - 2 - H) < 0) :
    Tendsto (fun B : ℝ => B ^ D * roughErrorEnvelope z H B) atTop (𝓝 0) := by
  let a : ℝ := D + (89 / 100 : ℝ) * (z - 2 - H)
  let C : ℝ := Real.exp 1 + (H + 1 : ℕ)
  have ha : 0 < -a := by dsimp [a] <;> linarith
  have hfirst := (log_power_div_power_tendsto_zero C ha).const_mul ((1000 : ℝ) ^ C)
  have hsecond := (rough_exponential_error_tendsto (by norm_num : (0 : ℝ) < 89 / 100)
    (by norm_num : (0 : ℝ) < 8000)
    (by positivity : 0 ≤ Real.exp 1 + H) D).const_mul
      ((1000 : ℝ) ^ (Real.exp 1 + H))
  have hsum := hfirst.add hsecond
  simp only [mul_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := (Real.log_pos hB).le
  dsimp [roughErrorEnvelope, a, C]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) hlog,
    Real.rpow_neg hB0.le, div_inv_eq_mul, ← Real.rpow_mul hB0.le]
  rw [mul_add, ← mul_assoc (B ^ D), ← Real.rpow_add hB0]
  congr 1 <;> ring

theorem rough_error_at_auxiliaryCutoff {z Y : ℝ} {B H : ℕ}
    (hB : 1 < B) (hz : z ≤ 1) (hY : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y) :
    (Real.log Y) ^ (z - 2 - H) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope z H B := by
  have hBreal : (1 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlog : 0 < Real.log B := Real.log_pos hBreal
  have hcut : Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
    simp only [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]
    norm_num
  have hexp : z - 2 - (H : ℝ) ≤ 0 := by linarith [Nat.cast_nonneg H (α := ℝ)]
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hB0 _) hY hexp
  rw [hcut]
  unfold roughErrorEnvelope
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
    apply Real.exp_le_exp.mpr
    have hdiv := div_le_div_of_nonneg_right hY (by positivity : 0 ≤ 8000 * Real.log B)
    convert neg_le_neg hdiv using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

/-- The full untwisted moving-cutoff estimate, conditional only on the
classical fixed-order expansion and the cited reciprocal-prime estimate. -/
theorem moving_rough_auxiliary_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y -
          Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)| ≤ K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, horders⟩ := moving_rough_expansion_exponential hSD hM hz
  obtain ⟨H, hH⟩ := exists_nat_gt (D / (89 / 100 : ℝ))
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have hgap : D + (89 / 100 : ℝ) * (z - 2 - H) < 0 := by
    have hHD : D < (H : ℝ) * (89 / 100 : ℝ) :=
      (div_lt_iff₀ (by norm_num : (0 : ℝ) < 89 / 100)).mp hH
    linarith
  obtain ⟨K, hK, hbound⟩ := horders H
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope z H B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, eventually_gt_atTop 1] with B hs hl hp hlogP hB
  intro Y hY hY9
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope z H B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (z - 2 - H) *
          (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + (H + 1 : ℕ)) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + H) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY)
    _ ≤ Y * K * roughErrorEnvelope z H B :=
      mul_le_mul_of_nonneg_left (rough_error_at_auxiliaryCutoff hB hz1 hY)
        (mul_nonneg (by linarith) hK)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughHarmonicLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The harmonic rough coefficient law

Partial summation of the proved moving-cutoff expansion gives the
weighted interval law needed for the independent prime-product model.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughDensityPolynomial_continuousAt (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (roughDensityPolynomial c E z H) L := by
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply ContinuousAt.add
  · exact continuousAt_id.rpow_const (Or.inl hL.ne')
  · exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hL.ne'))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductLogLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-product intervals in logarithmic coordinates

The logarithmic density is the exact change of variables in the harmonic
interval formula, not an independent smoothness assumption.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem scaledRoughDensity_integral (c : ℕ → ℝ) (z : ℝ) (H B : ℕ)
    (hB : 0 < B) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, scaledRoughDensity c z H B s) =
      primeNormalizer (auxiliaryPrimes B) z *
        ∫ t in Real.exp (B * a)..Real.exp (B * b),
          roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let D := roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
  let f := fun s : ℝ => Real.exp (B * s)
  let f' := fun s : ℝ => (B : ℝ) * Real.exp (B * s)
  let g := fun t : ℝ => D (Real.log t) / t
  have hd : ∀ s ∈ Set.uIcc a b, HasDerivAt f (f' s) s := by
    intro s _
    convert ((hasDerivAt_id s).const_mul (B : ℝ)).exp using 1 <;> first | (with_reducible_and_instances rfl) | (simp [f, f', mul_comm])
  have hc : ContinuousOn f' (Set.uIcc a b) := by dsimp [f']; fun_prop
  have hg : ContinuousOn g (f '' Set.uIcc a b) := by
    rintro t ⟨s, hs, rfl⟩
    rw [Set.uIcc_of_le hab] at hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have hpos : 0 < f s := Real.exp_pos _
    have hlog : 0 < Real.log (f s) := by dsimp [f]; rw [Real.log_exp]; positivity
    exact (((roughDensityPolynomial_continuousAt c _ z H hlog).comp
      (Real.continuousAt_log hpos.ne')).div continuousAt_id hpos.ne').continuousWithinAt
  have hchange := intervalIntegral.integral_comp_mul_deriv' hd hc hg
  calc
    _ = ∫ s in a..b, primeNormalizer (auxiliaryPrimes B) z * ((g ∘ f) s * f' s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      have hs0 : 0 < s := ha.trans_le hs.1
      rw [scaledRoughDensity_eq c z H B hB hs0]
      dsimp [g, f, f', D]
      rw [Real.log_exp]
      field_simp
    _ = primeNormalizer (auxiliaryPrimes B) z * ∫ s in a..b, (g ∘ f) s * f' s :=
      intervalIntegral.integral_const_mul _ _
    _ = _ := by rw [hchange]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform local prime-product law without residue restrictions

This is the modulus-one case of the manuscript's local product law, with
its stated `B^(-80)` absolute error on the shrinking lower-endpoint range.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliary_log_endpoint_conditions {B : ℕ} {a : ℝ}
    (hB : 1 ≤ B) (ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a)
    (hlarge : 9 ≤ (B : ℝ) ^ (9 / 10 : ℝ)) :
    0 < a ∧ 9 ≤ Real.exp (B * a) ∧ (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hpow : (B : ℝ) * (B : ℝ) ^ (-(1 / 10 : ℝ)) = (B : ℝ) ^ (9 / 10 : ℝ) := by
    rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num, Real.rpow_add hB0, Real.rpow_one]
  have hBa : (B : ℝ) ^ (9 / 10 : ℝ) ≤ B * a := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left ha hB0.le
  refine ⟨(Real.rpow_pos_of_pos hB0 _).trans_le ha, ?_, ?_⟩
  · have h := Real.add_one_le_exp ((B : ℝ) * a)
    linarith
  · exact (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (89 / 100 : ℝ) ≤ 9 / 10)).trans hBa

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterConvolution
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact character-twisted roughness convolution -/

namespace JointDickman

open Finset ArithmeticFunction

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℝ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext n
  simp only [characterTwist_apply, mul_apply, Complex.ofReal_sum]
  rw [sum_mul]
  apply sum_congr rfl
  intro ab hab
  have hmul : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← hmul, Nat.cast_mul, map_mul, Complex.ofReal_mul]
  ring

theorem roughCharacterSum_split {q : ℕ} (χ : DirichletCharacter ℂ q)
    (E : Finset ℕ) (z Y : ℝ) (V : ℕ) (hV : V ≤ ⌊Y⌋₊) :
    roughCharacterSum χ E z Y =
      (∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
        squarefreeCharacterSum χ z (Y / v)) +
      characterConvolutionTail χ E z ⌊Y⌋₊ V := by
  have hconv := congrArg (characterTwist χ) (squarefreeWeight_mul_smoothCorrection E z)
  rw [characterTwist_mul, mul_comm] at hconv
  change (∑ n ∈ Ioc 0 ⌊Y⌋₊, characterTwist χ (roughSquarefreeWeight E z) n) = _
  rw [← hconv, sum_Ioc_mul_eq_sum_sum,
    ← Ioc_union_Ioc_eq_Ioc (Nat.zero_le V) hV, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1
  · apply sum_congr rfl
    intro v _
    simp only [characterTwist_apply, squarefreeCharacterSum, Nat.floor_div_natCast]
  · simp only [characterConvolutionTail, squarefreeCharacterSum, Nat.floor_natCast,
      characterTwist_apply]

theorem squarefreeCharacterSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (N : ℕ) :
    ‖squarefreeCharacterSum χ z N‖ ≤ N := by
  unfold squarefreeCharacterSum
  rw [Nat.floor_natCast]
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(squarefreeWeight z n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ioc 0 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (squarefreeWeight_abs_le_one hz hz1 n)
          (χ.norm_le_one _) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    _ = _ := by simp

/-- Twisting cannot enlarge the Rankin remainder. -/
theorem characterConvolutionTail_rankin {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) {z ε : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hε : 0 ≤ ε) (N V : ℕ) (hV : 0 < V) :
    ‖characterConvolutionTail χ E z N V‖ ≤
      ((N : ℝ) / (V : ℝ) ^ ε) *
        ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) ^ (1 - ε) := by
  have hV' : (0 : ℝ) < V := by exact_mod_cast hV
  have htail := harmonic_tail_rankin (Ioc V N) (fun v : ℕ => (v : ℝ))
    (fun v => |smoothCorrection E z v|) hV' hε
    (fun v hv => by exact_mod_cast (mem_Ioc.mp hv).1.le)
    (fun _ _ => abs_nonneg _)
  calc
    _ ≤ (N : ℝ) * ∑ v ∈ Ioc V N, |smoothCorrection E z v| / (v : ℝ) := by
      unfold characterConvolutionTail
      rw [mul_sum]
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro v hv
      have hvpos : (0 : ℝ) < v := by exact_mod_cast
        ((mem_Ioc.mp hv).1.trans_le' (Nat.zero_le V))
      have hfloor : ((N / v : ℕ) : ℝ) ≤ (N : ℝ) / v := by
        apply (le_div_iff₀ hvpos).mpr
        exact_mod_cast Nat.div_mul_le_self N v
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        _ ≤ |smoothCorrection E z v| * ((N / v : ℕ) : ℝ) :=
          mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
            (squarefreeCharacterSum_norm_le χ hz hz1 _) (norm_nonneg _) (abs_nonneg _)
        _ ≤ |smoothCorrection E z v| * ((N : ℝ) / v) :=
          mul_le_mul_of_nonneg_left hfloor (abs_nonneg _)
        _ = _ := by ring
    _ ≤ (N : ℝ) * ((∑ v ∈ Ioc V N, |smoothCorrection E z v| /
        (v : ℝ) ^ (1 - ε)) / (V : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterTruncation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the published character bound below the square-root cutoff -/

namespace JointDickman

open Finset

theorem smallCharacterConvolution_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (E : Finset ℕ) (z Y D : ℝ) (V : ℕ)
    {K : ℝ} (hK : 0 ≤ K) (hY : 1 < Y) (hD : 0 ≤ D)
    (hbound : ∀ v ∈ Ioc 0 V,
      ‖squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * (Y / v) * (Real.log (Y / v)) ^ (-D))
    (hlog : ∀ v ∈ Ioc 0 V, Real.log Y / 2 ≤ Real.log (Y / v)) :
    ‖∑ v ∈ Ioc 0 V, (smoothCorrection E z v : ℂ) * χ (v : ZMod q) *
      squarefreeCharacterSum χ z (Y / v)‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          ∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ) := by
  have hlogpos : 0 < Real.log Y / 2 := div_pos (Real.log_pos hY) (by norm_num)
  rw [mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro v hv
  have hpow := Real.rpow_le_rpow_of_nonpos hlogpos (hlog v hv) (neg_nonpos.mpr hD)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (mem_Ioc.mp hv).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log (Y / v)) ^ (-D)) :=
      mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _))
        (hbound v hv) (norm_nonneg _) (abs_nonneg _)
    _ ≤ |smoothCorrection E z v| * (K * (Y / v) * (Real.log Y / 2) ^ (-D)) := by
      gcongr
    _ = _ := by ring

/-- Uniformity in the modulus is inherited from the published input.
The large-divisor remainder is the actual, already bounded convolution tail. -/
theorem roughCharacterSum_truncated
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (E : Finset ℕ) (Y : ℝ) (V : ℕ),
      9 ≤ Y → (V : ℝ) ^ 2 ≤ Y → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log Y / 2) ^ C → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ E z Y‖ ≤
        K * Y * (Real.log Y / 2) ^ (-D) *
          (∑ v ∈ Ioc 0 V, |smoothCorrection E z v| / (v : ℝ)) +
        ‖characterConvolutionTail χ E z ⌊Y⌋₊ V‖ := by
  obtain ⟨K, hK, hbound⟩ := hSW z hz C D hC hD
  refine ⟨K, hK, fun E Y V hY hV q _ hq χ hχ => ?_⟩
  obtain ⟨hVN, hsize⟩ := square_root_truncation_conditions hY hV
  have hY1 : 1 < Y := by linarith
  have hsmall := smallCharacterConvolution_bound χ E z Y D V hK hY1 hD
    (fun v hv => hbound (Y / v) (hsize v hv).1 q
      (hq.trans (Real.rpow_le_rpow (by positivity [Real.log_pos hY1])
        (hsize v hv).2 hC.le)) χ hχ)
    (fun v hv => (hsize v hv).2)
  rw [roughCharacterSum_split χ E z Y V hVN]
  exact (norm_add_le _ _).trans (add_le_add hsmall (le_refl _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_MovingCharacterBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonprincipal character estimate after removing the small primes -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem roughTruncation_rankin_full {Y : ℝ} {P : ℕ}
    (hY : 0 < Y) (hL : 16 ≤ Real.log Y) (hP : 0 < Real.log P) :
    1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P) ≤
      Real.exp (-(Real.log Y / (8 * Real.log P))) := by
  obtain ⟨hV, _, hlogV⟩ := roughTruncation_bounds hY hL
  have hV0 : (0 : ℝ) < roughTruncation Y := by exact_mod_cast hV
  rw [Real.rpow_def_of_pos hV0, one_div, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hlogV
    (show 0 ≤ 1 / Real.log P by positivity)
  have hpos : 0 ≤ Real.log Y / (8 * Real.log P) := by positivity
  have heq : (Real.log Y / 4) * (1 / Real.log P) =
      2 * (Real.log Y / (8 * Real.log P)) := by ring
  rw [heq] at h
  linarith

/-- Every fixed logarithmic saving survives the convolution, at the
cost of a fixed power of the cutoff logarithm and an explicit Rankin error. -/
theorem roughCharacterSum_exponential
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : ℕ) (Y : ℝ),
      2 ≤ P → 1 ≤ Real.log P → 9 ≤ Y → 16 ≤ Real.log Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (Real.log Y / 2) ^ (200 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE P) z Y‖ ≤
        Y * K * ((Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
          (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P)))) := by
  obtain ⟨C, hC, hbound⟩ := roughCharacterSum_truncated hSW hz (by norm_num : (0 : ℝ) < 200) hD
  obtain ⟨A, hA, hmom⟩ := smoothCorrection_log_moments_bound hM
  obtain ⟨A', hA', hshift⟩ := smoothCorrection_shifted_bound hM
  let K := C * A * (2 : ℝ) ^ D + A'
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hzh : z ≤ 1 / 2 := by rcases hz with rfl | rfl <;> norm_num
  have hK : 0 ≤ K := by dsimp [K] <;> positivity
  refine ⟨K, hK, fun P Y hP hlogP hY hL q _ hq χ hχ => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hLP : 0 < Real.log P := by linarith
  have hLY : 0 < Real.log Y := by linarith
  obtain ⟨hV, hV2, _⟩ := roughTruncation_bounds hY0 hL
  have hmain := hbound (Nat.primesLE P) Y (roughTruncation Y) hY hV2 q hq χ hχ
  have habs : (∑ v ∈ Ioc 0 (roughTruncation Y),
      |smoothCorrection (Nat.primesLE P) z v| / (v : ℝ)) ≤ A * (Real.log P) ^ (Real.exp 1) := by
    simpa using hmom P (Ioc 0 (roughTruncation Y)) z 0 hP hlogP hz0 hzh
  have htail : ‖characterConvolutionTail χ (Nat.primesLE P) z ⌊Y⌋₊ (roughTruncation Y)‖ ≤
      Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
    have ht := characterConvolutionTail_rankin χ (Nat.primesLE P) hz0 (by linarith)
      (by positivity : 0 ≤ 1 / Real.log P) ⌊Y⌋₊ (roughTruncation Y) hV
    calc
      _ ≤ ((⌊Y⌋₊ : ℝ) / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) :=
        ht.trans (mul_le_mul_of_nonneg_left
          (hshift P (Ioc (roughTruncation Y) ⌊Y⌋₊) z hP hlogP hz0 hzh) (by positivity))
      _ ≤ (Y / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) *
          (A' * (Real.log P) ^ (Real.exp 1)) := by
        gcongr
        exact Nat.floor_le hY0.le
      _ = Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          (1 / (roughTruncation Y : ℝ) ^ (1 / Real.log P)) := by ring
      _ ≤ Y * (A' * (Real.log P) ^ (Real.exp 1)) *
          Real.exp (-(Real.log Y / (8 * Real.log P))) :=
        mul_le_mul_of_nonneg_left (roughTruncation_rankin_full hY0 hL hLP) (by positivity)
      _ = _ := by ring
  have hfactor : (Real.log Y / 2) ^ (-D) = (2 : ℝ) ^ D * (Real.log Y) ^ (-D) := by
    rw [Real.div_rpow hLY.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    ring
  have hlogpow : (Real.log P) ^ (Real.exp 1) ≤ (Real.log P) ^ (Real.exp 1 + 1) :=
    Real.rpow_le_rpow_of_exponent_le hlogP (by linarith)
  have hK1 : C * A * (2 : ℝ) ^ D ≤ K := by dsimp [K] <;> linarith
  have hK2 : A' ≤ K := by
    dsimp [K]
    have hpos : 0 ≤ C * A * (2 : ℝ) ^ D := by positivity
    linarith
  calc
    _ ≤ C * Y * (Real.log Y / 2) ^ (-D) * (A * (Real.log P) ^ (Real.exp 1)) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) :=
      hmain.trans (add_le_add (mul_le_mul_of_nonneg_left habs (by positivity)) htail)
    _ = Y * (C * A * (2 : ℝ) ^ D) * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1) +
        Y * A' * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      rw [hfactor]
      ring
    _ ≤ Y * K * (Real.log Y) ^ (-D) * (Real.log P) ^ (Real.exp 1 + 1) +
        Y * K * (Real.log P) ^ (Real.exp 1) * Real.exp (-(Real.log Y / (8 * Real.log P))) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK1 hY0.le) (by positivity)) hlogpow (by positivity) (by positivity)
      · gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterAuxiliaryBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform character cancellation on the manuscript's scale -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_bound : ∀ᶠ B : ℕ in atTop,
    ∀ L : ℝ, (B : ℝ) ^ (89 / 100 : ℝ) ≤ L →
      (B : ℝ) ^ (100 : ℝ) ≤ (L / 2) ^ (200 : ℝ) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, (2 : ℝ) ≤ (B : ℝ) ^ (39 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 39 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_gt_atTop 0] with B hlargeB hB
  intro L hL
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ (1 / 2 : ℝ) ≤ L / 2 := by
    have heq : (B : ℝ) ^ (89 / 100 : ℝ) =
        (B : ℝ) ^ (1 / 2 : ℝ) * (B : ℝ) ^ (39 / 100 : ℝ) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq] at hL
    nlinarith [Real.rpow_pos_of_pos hB0 (1 / 2 : ℝ)]
  calc
    _ = ((B : ℝ) ^ (1 / 2 : ℝ)) ^ (200 : ℝ) := by
      rw [← Real.rpow_mul hB0.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hpow (by norm_num)

/-- Cancellation after moving small-prime removal holds for all
nonprincipal characters of modulus at most `B^100`. -/
theorem moving_rough_character_bound
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖roughCharacterSum χ (Nat.primesLE (auxiliaryCutoff B)) z Y‖ ≤
        K * Y * (B : ℝ) ^ (-D) := by
  let E : ℝ := 2 * (D + 1)
  have hE : 0 ≤ E := by dsimp [E] <;> linarith
  obtain ⟨K, hK, hbound⟩ := roughCharacterSum_exponential hSW hM hz hE
  refine ⟨K, hK, ?_⟩
  have hgap : D + (89 / 100 : ℝ) * ((2 - E) - 2 - (0 : ℕ)) < 0 := by
    dsimp [E]
    norm_num
    linarith
  have hlim := (roughErrorEnvelope_tendsto hgap).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ D * roughErrorEnvelope (2 - E) 0 B ≤ 1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ B : ℕ in atTop, (16 : ℝ) ≤ (B : ℝ) ^ (89 / 100 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 89 / 100)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 16)
  have hP : ∀ᶠ B : ℕ in atTop, 2 ≤ auxiliaryCutoff B :=
    auxiliaryCutoff_tendsto.eventually (eventually_ge_atTop 2)
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlarge, hP, hlog, auxiliary_modulus_bound,
    eventually_gt_atTop 1] with B hs hl hp hlogP hmod hB
  intro Y hY hY9 q _ hq χ hχ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have henv : roughErrorEnvelope (2 - E) 0 B ≤ (B : ℝ) ^ (-D) := by
    rw [Real.rpow_neg hB0.le, ← one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr (by simpa [mul_comm] using hs)
  have hpoint : (Real.log Y) ^ (-E) *
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
      (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
        Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B)))) ≤
      roughErrorEnvelope (2 - E) 0 B := by
    have h := rough_error_at_auxiliaryCutoff (H := 0) (z := 2 - E) hB
      (by dsimp [E] <;> linarith) hY
    simp only [Nat.cast_zero, sub_zero, Nat.reduceAdd, Nat.cast_one, add_zero] at h
    rw [show 2 - E - 2 = -E by ring] at h
    exact h
  calc
    _ ≤ Y * K * ((Real.log Y) ^ (-E) *
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1 + 1) +
        (Real.log (auxiliaryCutoff B)) ^ (Real.exp 1) *
          Real.exp (-(Real.log Y / (8 * Real.log (auxiliaryCutoff B))))) :=
      hbound (auxiliaryCutoff B) Y hp hlogP hY9 (hl.trans hY) q
        (hq.trans (hmod (Real.log Y) hY)) χ hχ
    _ ≤ Y * K * roughErrorEnvelope (2 - E) 0 B :=
      mul_le_mul_of_nonneg_left hpoint (by positivity)
    _ ≤ Y * K * (B : ℝ) ^ (-D) := mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CharacterResidues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Character orthogonality for the actual rough coefficients -/

namespace JointDickman

open Finset

open Classical in
theorem progressionSum_characters {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) :
    (q.totient : ℂ) * (progressionSum S w (r : ZMod q) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ (r⁻¹ : (ZMod q)ˣ) *
        ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
  rw [progressionSum, Complex.ofReal_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  calc
    _ = (w n : ℂ) * (if (r : ZMod q) = (n : ZMod q) then (q.totient : ℂ) else 0) := by
      split_ifs <;> simp_all
      ring
    _ = (w n : ℂ) * ∑ χ : DirichletCharacter ℂ q,
        χ (r⁻¹ : (ZMod q)ˣ) * χ (n : ZMod q) := by
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ r.isUnit, ZMod.inv_coe_unit]
    _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro χ _; ring

open Classical in
/-- The normalized character average loses no factor depending on the modulus. -/
theorem progressionSum_error_le {q : ℕ} [NeZero q]
    (S : Finset ℕ) (w : ℕ → ℝ) (r : (ZMod q)ˣ) {E : ℝ} (hE : 0 ≤ E)
    (hunit : ∀ n ∈ S, w n ≠ 0 → IsUnit (n : ZMod q))
    (hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ‖∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤ E) :
    |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| ≤ E := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hprincipal : (∑ n ∈ S, (w n : ℂ) * (1 : DirichletCharacter ℂ q) (n : ZMod q)) =
      (∑ n ∈ S, w n : ℝ) := by
    rw [Complex.ofReal_sum]
    apply sum_congr rfl
    intro n hn
    by_cases hw : w n = 0
    · simp [hw]
    · rw [MulChar.one_apply (hunit n hn hw), mul_one]
  have hid : (q.totient : ℂ) *
      ((progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)) =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
        χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q) := by
    have hφ0 : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    rw [mul_sub, mul_div_cancel₀ _ hφ0, progressionSum_characters]
    rw [← sum_erase_add _ _ (mem_univ (1 : DirichletCharacter ℂ q)), hprincipal,
      MulChar.one_apply_coe, one_mul, add_sub_cancel_right]
  have hsum : ‖∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ ≤
      (q.totient : ℝ) * E := by
    calc
      _ ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1,
          ‖χ (r⁻¹ : (ZMod q)ˣ) * ∑ n ∈ S, (w n : ℂ) * χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, E := by
        apply sum_le_sum
        intro χ hχ
        rw [norm_mul, χ.unit_norm_eq_one, one_mul]
        exact hbound χ (ne_of_mem_erase hχ)
      _ ≤ ∑ _χ : DirichletCharacter ℂ q, E :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => hE)
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  rw [← hid, norm_mul, Complex.norm_natCast] at hsum
  have heq : ‖(progressionSum S w (r : ZMod q) : ℂ) - (∑ n ∈ S, w n : ℝ) / (q.totient : ℂ)‖ =
      |progressionSum S w (r : ZMod q) - (∑ n ∈ S, w n) / (q.totient : ℝ)| := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at hsum
  exact (mul_le_mul_iff_right₀ hφ).mp hsum

theorem roughSquarefreeWeight_coprime {P q n : ℕ} (hq : q ≠ 0) (hqP : q ≤ P)
    (z : ℝ) (hn : roughSquarefreeWeight (Nat.primesLE P) z n ≠ 0) : n.Coprime q := by
  have hn0 : n ≠ 0 := by intro h; subst n; simp at hn
  have hd : Disjoint n.primeFactors (Nat.primesLE P) := by
    by_contra h
    simp [roughSquarefreeWeight, h] at hn
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact disjoint_left.mp hd (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hpq).trans hqP, hp⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueSummatory
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform progression estimate for rough squarefree integers -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem auxiliary_modulus_le_cutoff {B q : ℕ} (hB : 1 ≤ B)
    (hq : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ)) : q ≤ auxiliaryCutoff B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcut : (auxiliaryCutoff B : ℝ) = (B : ℝ) ^ (1000 : ℝ) := by
    norm_num [auxiliaryCutoff]
  have hle := hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (100 : ℝ) ≤ 1000))
  rw [← hcut] at hle
  exact_mod_cast hle

/-- Equidistribution in the unit classes, before partial summation. -/
theorem roughResidueSummatory_error
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ r : (ZMod q)ˣ,
      |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| ≤
        K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨K, hK, hbound⟩ := moving_rough_character_bound hSW hM hz hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro Y hY hY9 q _ hq r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  exact progressionSum_error_le (Ioc 0 ⌊Y⌋₊)
    (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z) r (by positivity)
    (fun n _ hn => (ZMod.isUnit_iff_coprime n q).mpr
      (roughSquarefreeWeight_coprime (NeZero.ne q) hqP z hn))
    (fun χ hχ => hboundB Y hY hY9 q hq χ hχ)

/-- The same actual coefficients as the untwisted expansion serve in
all unit progressions; the error is uniform in every modulus up to `B^100`. -/
theorem roughResidueSummatory_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
          (Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)) / q.totient| ≤
          K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  obtain ⟨K', hK', hres⟩ := roughResidueSummatory_error hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K + K', add_nonneg hK hK', ?_⟩
  filter_upwards [hbound, hres] with B hboundB hresB
  intro Y hY hY9 q _ hq r
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  have hu := hboundB Y hY hY9
  have hr := hresB Y hY hY9 q hq r
  let T := Y * ∑ ν ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν * (Real.log Y) ^ (z - 1 - ν)
  have hdiv : |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
      T / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
    rw [← sub_div, abs_div, abs_of_pos hφ0]
    exact (div_le_self (abs_nonneg _) hφ).trans hu
  calc
    _ ≤ |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| +
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
          T / q.totient| := abs_sub_le _ _ _
    _ ≤ K' * Y * (B : ℝ) ^ (-D) + K * Y * (B : ℝ) ^ (-D) := add_le_add hr hdiv
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughResidueHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation in the unit residue classes -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem finiteCountingFunction_roughResidue {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z t : ℝ) :
    finiteCountingFunction (roughResidueWeight r E z) t = roughResidueSummatory r E z t := by
  unfold finiteCountingFunction roughResidueSummatory progressionSum roughResidueWeight
  rw [← Ioc_insert_left (Nat.zero_le ⌊t⌋₊), sum_insert left_notMem_Ioc]
  simp

theorem rough_residue_harmonic_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
            roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
            (Real.log t) / t) / q.totient| ≤
          K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := roughResidueSummatory_expansion hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound] with B hB
  intro a b ha hab hlog q _ hq r
  have ha0 : 0 < a := by linarith
  let E := Nat.primesLE (auxiliaryCutoff B)
  let F := fun t : ℝ => (t * ∑ j ∈ range (H + 1),
    roughCoefficient c E z j * (Real.log t) ^ (z - 1 - j)) / (q.totient : ℝ)
  let M := fun t : ℝ => roughDensityPolynomial c E z H (Real.log t) / (q.totient : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (M t) t :=
    (hasDerivAt_logarithmic_model c E z H (by linarith [ht.1])).div_const _
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact (((roughDensityPolynomial_continuousAt c E z H (Real.log_pos ht1)).comp
      (Real.continuousAt_log (by linarith : t ≠ 0))).div_const _).continuousWithinAt
  have herr : ∀ t ∈ Set.Icc a b,
      |finiteCountingFunction (roughResidueWeight (r : ZMod q) E z) t - F t| ≤
        (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log t :=
      hlog.trans (Real.log_le_log ha0 ht.1)
    simpa only [finiteCountingFunction_roughResidue, F, E, mul_assoc, mul_left_comm, mul_comm] using
      hB t hlogt (ha.trans ht.1) q hq r
  have h := harmonic_counting_error_le (roughResidueWeight (r : ZMod q) E z) F ha0 hab hFc herr
  rw [← harmonic_model_integral F M ha0 hab hd hMc] at h
  have hint : (∫ t in a..b, M t / t) =
      (∫ t in a..b, roughDensityPolynomial c E z H (Real.log t) / t) / q.totient := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [M]
    ring
  rw [hint] at h
  exact h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductResidueInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime-product interval probabilities with a unit residue restriction -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem sum_roughResidueWeight_div {q : ℕ} (S : Finset ℕ) (r : ZMod q)
    (E : Finset ℕ) (z : ℝ) :
    (∑ n ∈ S.filter (fun (n : ℕ) => (n : ZMod q) = r), roughSquarefreeWeight E z n / (n : ℝ)) =
      ∑ n ∈ S, roughResidueWeight r E z n / (n : ℝ) := by
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases h : (n : ZMod q) = r <;> simp [roughResidueWeight, h]

open Classical in
theorem primeProduct_residue_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → b ≤ auxiliaryUpper B →
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          primeNormalizer (auxiliaryPrimes B) z *
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) +
            K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hrough⟩ := rough_residue_harmonic_interval_law hSD hSW hM hz hD
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hrough, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hlog q _ hq r
  have hb0 : 0 ≤ b := by linarith
  have hcut : auxiliaryCutoff B ≠ 0 := pow_ne_zero 1000 (Nat.ne_of_gt hB0)
  have hmass := primeProductMass_harmonic_error (U := auxiliaryUpper B) hcut hz0 hz1
    ((Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun n => (n : ZMod q) = (r : ZMod q))) (fun n hn =>
      ((by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2 : (n : ℝ) ≤ ⌊b⌋₊).trans
        (Nat.floor_le hb0)).trans hb)
  rw [sum_roughResidueWeight_div] at hmass
  have hQ := primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hz0 hz1
  have hweighted : |primeNormalizer (auxiliaryPrimes B) z *
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
          roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
        (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
          (Real.log t) / t) / q.totient)| ≤
      K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    simpa only [one_mul] using mul_le_mul hQ.2 (hB a b ha hab hlog q hq r)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ = |((∑ n ∈ (Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
          primeProductMass (auxiliaryPrimes B) z n) - primeNormalizer (auxiliaryPrimes B) z *
            ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) +
        primeNormalizer (auxiliaryPrimes B) z *
          ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
              roughResidueWeight (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
            (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H
              (Real.log t) / t) / q.totient)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hmass hweighted)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductResidueLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform residue-restricted local prime-product law -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability of a log-coordinate interval in a unit class. -/
theorem primeProduct_residue_log_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) {D : ℝ} (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        0 < a → a ≤ b → b ≤ 4 →
        9 ≤ Real.exp (B * a) → (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) + K * (B : ℝ) ^ (-D) * (2 + B * (b - a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_interval_law hSD hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hsize hscale q _ hq r
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hexp : Real.exp (B * a) ≤ Real.exp (B * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hupper : Real.exp (B * b) ≤ auxiliaryUpper B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := hB (Real.exp (B * a)) (Real.exp (B * b)) hsize hexp hupper
    (by simpa only [Real.log_exp] using hscale) q hq r
  rw [← scaledRoughDensity_integral c z H B hB0 ha hab] at h
  have hlog : Real.log (Real.exp (B * b) / Real.exp (B * a)) = B * (b - a) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  simpa only [hlog] using h


open Classical in
/-- All intervals in the range have the same absolute error constant. -/
theorem primeProduct_residue_local_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ n ∈ (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q)),
            primeProductMass (auxiliaryPrimes B) z n) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_residue_log_interval_law hSD hSW hM hz (by norm_num : (0 : ℝ) ≤ 81)
  refine ⟨c, hc0, hcpos, H, 1 + 6 * K, by positivity, ?_⟩
  have hlarge : ∀ᶠ B : ℕ in atTop, (9 : ℝ) ≤ (B : ℝ) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 9)
  filter_upwards [hbound, hlarge, eventually_ge_atTop 1] with B hB hlargeB hB1
  intro a b ha hab hb q _ hq r
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨ha0, hsize, hscale⟩ := auxiliary_log_endpoint_conditions hB1 ha hlargeB
  have h := hB a b ha0 hab (by linarith) hsize hscale q hq r
  have hzsq : z ^ 2 ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  have htail : z ^ 2 / (auxiliaryCutoff B : ℝ) ≤ (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ 1 / (auxiliaryCutoff B : ℝ) :=
        div_le_div_of_nonneg_right hzsq (by positivity)
      _ = (B : ℝ) ^ (-(1000 : ℝ)) := by
        rw [Real.rpow_neg hB0.le]
        norm_num [auxiliaryCutoff]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hBreal (by norm_num)
  have hlen : 2 + (B : ℝ) * (b - a) ≤ 6 * B := by nlinarith
  have hpoly : K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + (B : ℝ) * (b - a)) ≤
      6 * K * (B : ℝ) ^ (-(80 : ℝ)) := by
    calc
      _ ≤ K * (B : ℝ) ^ (-(81 : ℝ)) * (6 * B) :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = _ := by
        have heq : (B : ℝ) ^ (-(81 : ℝ)) * B = (B : ℝ) ^ (-(80 : ℝ)) := by
          rw [show (-(80 : ℝ)) = -81 + 1 by norm_num, Real.rpow_add hB0, Real.rpow_one]
        nlinarith [heq]
  calc
    _ ≤ z ^ 2 / (auxiliaryCutoff B : ℝ) +
        K * (B : ℝ) ^ (-(81 : ℝ)) * (2 + B * (b - a)) := h
    _ ≤ (B : ℝ) ^ (-(80 : ℝ)) + 6 * K * (B : ℝ) ^ (-(80 : ℝ)) := add_le_add htail hpoly
    _ = _ := by ring


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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FlatExclusiveKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Flattening the retained exclusive-product kernel

Conditioned on the common variable, the two retained exclusive outputs
are independent. An additive local-law error for each cell therefore
gives an explicit error for their product and for the integrated kernel.
The approximating profile may be signed: its required bound follows from
the local law and the fact that the actual cell probabilities lie in `[0,1]`.
-/

namespace JointDickman

open scoped BigOperators

theorem local_profile_abs_le {a v η : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hlocal : |a - v| ≤ η) : |v| ≤ 1 + η := by
  calc
    |v| = |a + (v - a)| := by congr 1; ring
    _ ≤ |a| + |v - a| := abs_add_le _ _
    _ = a + |a - v| := by rw [abs_of_nonneg ha₀, abs_sub_comm]
    _ ≤ 1 + η := add_le_add ha₁ hlocal

/-- Product error from two genuine cell probabilities and their additive
local laws. No separate size bound for the profile is assumed. -/
theorem exclusive_probability_product_error {a b u v η : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hη : 0 ≤ η) (ha : |a - u| ≤ η) (hb : |b - v| ≤ η) :
    |a * b - u * v| ≤ 2 * η + η ^ 2 := by
  have hu := local_profile_abs_le ha₀ ha₁ ha
  have hbabs : |b| ≤ 1 := by simpa only [abs_of_nonneg hb₀] using hb₁
  calc
    |a * b - u * v| = |(a - u) * b + u * (b - v)| := by congr 1; ring
    _ ≤ |(a - u) * b| + |u * (b - v)| := abs_add_le _ _
    _ = |a - u| * |b| + |u| * |b - v| := by rw [abs_mul, abs_mul]
    _ ≤ η * 1 + (1 + η) * η := add_le_add
      (mul_le_mul ha hbabs (abs_nonneg _) hη)
      (mul_le_mul hu hb (abs_nonneg _) (by linarith))
    _ = 2 * η + η ^ 2 := by ring

/-- Integrating the local-law product error against the actual common law
does not increase it. -/
theorem exclusiveProductKernel_flat_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (v : C → D → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hwnorm : ∑ c, w c = 1)
    (hμ : ∀ d, 0 < μ d) (hp₀ : ∀ c a, 0 ≤ p c a) (hp₁ : ∀ c a, p c a ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hlocal : ∀ c d r, |p c (d, r) - v c d| ≤ η) (d e : D) (r s : R) :
    |exclusiveProductKernel w μ p (d, r) (e, s) - flatExclusiveKernel w μ v d e| ≤
      (2 * η + η ^ 2) / (μ d * μ e) := by
  have hnum : |(∑ c, w c * p c (d, r) * p c (e, s)) -
      ∑ c, w c * v c d * v c e| ≤ 2 * η + η ^ 2 := by
    calc
      _ = |∑ c, w c * (p c (d, r) * p c (e, s) - v c d * v c e)| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ ∑ c, |w c * (p c (d, r) * p c (e, s) - v c d * v c e)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c, w c * |p c (d, r) * p c (e, s) - v c d * v c e| := by
        simp_rw [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ c, w c * (2 * η + η ^ 2) := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left
          (exclusive_probability_product_error (hp₀ c _) (hp₁ c _) (hp₀ c _) (hp₁ c _)
            hη (hlocal c d r) (hlocal c e s)) (hw c)
      _ = 2 * η + η ^ 2 := by rw [← Finset.sum_mul, hwnorm, one_mul]
  unfold exclusiveProductKernel flatExclusiveKernel
  rw [← sub_div, abs_div, abs_of_pos (mul_pos (hμ d) (hμ e))]
  exact div_le_div_of_nonneg_right hnum (mul_nonneg (hμ d).le (hμ e).le)

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

omit [Fintype C] in
theorem highExclusiveCell_eq_sum (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (c : C) (a : A) :
    highExclusiveCell v cell low c a =
      ∑ e, if ¬low e ∧ cell c e = some a then v e else 0 := by
  unfold highExclusiveCell optionCellMass
  apply Finset.sum_congr rfl
  intro e _
  by_cases hl : low e <;> by_cases hc : cell c e = some a <;> simp [hl, hc]

omit [Fintype C] in
theorem highExclusiveCell_nonneg (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (hv : ∀ e, 0 ≤ v e) (c : C) (a : A) :
    0 ≤ highExclusiveCell v cell low c a := by
  apply optionCellMass_nonneg
  intro e
  split_ifs <;> [exact le_rfl; exact hv e]

omit [Fintype C] in
theorem highExclusiveCell_le_one (v : E → ℝ) (cell : C → E → Option A)
    (low : E → Prop) [DecidablePred low] (hv : ∀ e, 0 ≤ v e) (hv1 : ∑ e, v e = 1)
    (c : C) (a : A) : highExclusiveCell v cell low c a ≤ 1 := by
  rw [highExclusiveCell_eq_sum, ← hv1]
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> [exact le_rfl; exact hv e]

/-- The high-high complement factors after conditioning on the common variable. -/
theorem independentPairMass_cutoff (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (a b : A) :
    independentPairMass w v cell a b = lowUnionExclusiveMass w v cell low a b +
      ∑ c, w c * highExclusiveCell v cell low c a * highExclusiveCell v cell low c b := by
  rw [independentPairMass_eq_triple]
  unfold lowUnionExclusiveMass
  simp_rw [highExclusiveCell_eq_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm (f := fun e₂ e₁ =>
    w c * (if ¬low e₁ ∧ cell c e₁ = some a then v e₁ else 0) *
      (if ¬low e₂ ∧ cell c e₂ = some b then v e₂ else 0))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e₁ _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e₂ _
  by_cases hl₁ : low e₁ <;> by_cases hl₂ : low e₂ <;>
    by_cases ha : cell c e₁ = some a <;> by_cases hb : cell c e₂ = some b <;>
    simp [hl₁, hl₂, ha, hb]

theorem lowUnionExclusiveMass_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low]
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (a b : A) :
    0 ≤ lowUnionExclusiveMass w v cell low a b := by
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro e₁ _
  apply Finset.sum_nonneg
  intro e₂ _
  split_ifs <;> [exact mul_nonneg (mul_nonneg (hw c) (hv e₁)) (hv e₂); exact le_rfl]

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

theorem lowUnionExclusiveKernel_nonneg (w : C → ℝ) (v : E → ℝ)
    (cell : C → E → Option A) (low : E → Prop) [DecidablePred low] (μ : A → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hv : ∀ e, 0 ≤ v e) (hμ : ∀ a, 0 ≤ μ a) (a b : A) :
    0 ≤ lowUnionExclusiveKernel w v cell low μ a b :=
  div_nonneg (lowUnionExclusiveMass_nonneg w v cell low hw hv a b)
    (mul_nonneg (hμ a) (hμ b))

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

/-- Normalize the exact cutoff identity by the actual output cell masses. -/
theorem independentPairKernel_cutoff {C E D R : Type*}
    [Fintype C] [Fintype E] [DecidableEq D] [DecidableEq R]
    (w : C → ℝ) (v : E → ℝ) (cell : C → E → Option (D × R))
    (low : E → Prop) [DecidablePred low] (μ : D → ℝ) (a b : D × R) :
    independentPairMass w v cell a b / (μ a.1 * μ b.1) =
      lowUnionExclusiveKernel w v cell low (fun a : D × R => μ a.1) a b +
      exclusiveProductKernel w μ (highExclusiveCell v cell low) a b := by
  rw [independentPairMass_cutoff w v cell low a b]
  exact add_div _ _ _

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


open Classical in
theorem primeSiteMass_event (Q : Finset ℕ) (z : ℝ) (K : Finset ℕ) :
    (∑ x : Q → Bool, if retainedPrimeProduct Q x ∈ K then
      bernoulliSiteMass (fun p : Q => z / p.val) x else 0) =
      ∑ n ∈ K, primeProductMass Q z n := by
  rw [primeProductMass_sum_event]
  have h := bernoulliPrimeSite_event Q (fun p : ℕ => z / p) (fun n => n ∈ K)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply sum_congr rfl <;> intro n _ <;> split_ifs <;> rfl)

theorem quarterPrimeMass_eq (Q : Finset ℕ) (x : Q → Bool) :
    quarterPrimeMass Q x = bernoulliSiteMass (fun p : Q => (1 / 4 : ℝ) / p.val) x := by
  unfold quarterPrimeMass
  congr 1
  funext p
  ring

theorem retainedPrimeProduct_pos (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (x : Q → Bool) :
    0 < retainedPrimeProduct Q x := by
  rw [retainedPrimeProduct_selected]
  exact prod_pos (fun p hp => (hQ p (selectedPrimeSubset_subset Q x hp)).pos)

theorem retainedPrimeProduct_coprime (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    {q : ℕ} (hq : q ≠ 0) (hcut : ∀ p ∈ Q, q < p) (x : Q → Bool) :
    (retainedPrimeProduct Q x).Coprime q := by
  rw [retainedPrimeProduct_selected, Nat.coprime_prod_left_iff]
  intro p hp
  have hpQ := selectedPrimeSubset_subset Q x hp
  apply (hQ p hpQ).coprime_iff_not_dvd.mpr
  intro hdiv
  exact (not_le_of_gt (hcut p hpQ)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdiv)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local product laws for the actual Boolean prime sites -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) -
          (∫ s in a..b, scaledRoughDensity c z H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc, hcpos, H, C, hC, hbound⟩ := primeProduct_residue_local_interval_law hSD hSW hM hz
  refine ⟨c, hc, hcpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hboundB hB
  intro a b ha hab hb q _ hq r
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let K := (Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊).filter
    (fun (n : ℕ) => (n : ZMod q) = (r : ZMod q))
  have hevent (x : auxiliaryPrimes B → Bool) :
      (Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
        (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r) ↔
      retainedPrimeProduct (auxiliaryPrimes B) x ∈ K := by
    have hnpos : (0 : ℝ) < retainedPrimeProduct (auxiliaryPrimes B) x := by
      exact_mod_cast retainedPrimeProduct_pos (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    simp only [K, mem_filter, mem_Ioc, Set.mem_Ioc]
    rw [Nat.floor_lt (by positivity : 0 ≤ Real.exp (B * a)), Nat.le_floor_iff (by positivity : 0 ≤ Real.exp (B * b))]
    rw [lt_div_iff₀ hB0, div_le_iff₀ hB0]
    rw [Real.lt_log_iff_exp_lt hnpos, Real.log_le_iff_le_exp hnpos]
    ring_nf
  have hsum : (∑ x : auxiliaryPrimes B → Bool,
      if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
        bernoulliSiteMass (fun p : auxiliaryPrimes B => z / p.val) x else 0) =
        ∑ n ∈ K, primeProductMass (auxiliaryPrimes B) z n := by
    simp_rw [hevent]
    exact primeSiteMass_event (auxiliaryPrimes B) z K
  rw [hsum]
  exact hboundB a b ha hab hb q hq r


open Classical in
theorem quarterPrimeSite_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |(∑ x : auxiliaryPrimes B → Bool,
          if Real.log (retainedPrimeProduct (auxiliaryPrimes B) x) / B ∈ Set.Ioc a b ∧
              (retainedPrimeProduct (auxiliaryPrimes B) x : ZMod q) = r then
            quarterPrimeMass (auxiliaryPrimes B) x else 0) -
          (∫ s in a..b, scaledRoughDensity c (1 / 4) H B s) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  have h := primeSite_local_law hSD hSW hM
    (Or.inl rfl : (1 / 4 : ℝ) = 1 / 4 ∨ (1 / 4 : ℝ) = 1 / 2)
  simpa only [quarterPrimeMass_eq] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductLogCells
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- Multiplication by the common product translates the log cell and
permutes the unit residue. The high-exclusive cutoff changes only the
lower endpoint. -/
theorem high_product_cell_iff {B c n q : ℕ} (hc : 0 < c) (hn : 0 < n)
    (u r : (ZMod q)ˣ) (hu : (c : ZMod q) = u) (a b θ : ℝ) :
    (θ < Real.log n / B ∧
      Real.log (c * n : ℕ) / B ∈ Set.Ioc a b ∧ ((c * n : ℕ) : ZMod q) = (r : ZMod q)) ↔
    (Real.log n / B ∈ Set.Ioc (max θ (a - Real.log c / B)) (b - Real.log c / B) ∧
      (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (c * n : ℕ) / B = Real.log c / B + Real.log n / B := by
    rw [Nat.cast_mul, Real.log_mul hc0.ne' hn0.ne', add_div]
  have hmod : ((c * n : ℕ) : ZMod q) = r ↔ (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) := by
    rw [Nat.cast_mul, hu]
    constructor
    · intro h
      have h' := congrArg (fun t : ZMod q => (u⁻¹ : (ZMod q)ˣ) * t) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h]
      simp [← Units.val_mul]
  rw [hlog, hmod]
  simp only [Set.mem_Ioc, max_lt_iff]
  constructor
  · rintro ⟨hθ, hab, hr⟩
    exact ⟨⟨⟨hθ, by linarith [hab.1]⟩, by linarith [hab.2]⟩, hr⟩
  · rintro ⟨⟨⟨hθ, ha⟩, hb⟩, hr⟩
    exact ⟨hθ, ⟨by linarith, by linarith⟩, hr⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighExclusiveLocalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local laws for the high-exclusive part of the actual prime channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem highExclusiveLogCell_eq {D : Type*} [DecidableEq D]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (θ : ℝ) (c : Q → Bool) (u r : (ZMod q)ˣ)
    (hu : (retainedPrimeProduct Q c : ZMod q) = u) (d : D) :
    highExclusiveCell (quarterPrimeMass Q)
      (primeProductCell Q (logResidueCell B q lower upper)) (lowPrimeLog Q B θ) c (d, r) =
      ∑ e : Q → Bool,
        if Real.log (retainedPrimeProduct Q e) / B ∈
            Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
              (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
          (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) then
          quarterPrimeMass Q e else 0 := by
  rw [highExclusiveCell_eq_sum]
  apply sum_congr rfl
  intro e _
  have hiff : (¬lowPrimeLog Q B θ e ∧
      primeProductCell Q (logResidueCell B q lower upper) c e = some (d, r)) ↔
      (Real.log (retainedPrimeProduct Q e) / B ∈
        Set.Ioc (max θ (lower d - Real.log (retainedPrimeProduct Q c) / B))
          (upper d - Real.log (retainedPrimeProduct Q c) / B) ∧
        (retainedPrimeProduct Q e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
    dsimp only [lowPrimeLog, primeProductCell]
    rw [not_le, logResidueCell_eq_some B q lower upper hdisjoint]
    exact high_product_cell_iff (retainedPrimeProduct_pos Q hQ c)
      (retainedPrimeProduct_pos Q hQ e) u r hu (lower d) (upper d) θ
  simp only [hiff]

open Classical in
/-- The retained exclusive cell is approximated by a residue-independent
integral, uniformly even for a partial cell at the high cutoff. -/
theorem highExclusiveLogCell_local_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ v : ℕ → ℝ, v 0 = squarefreeLeadingConstant (1 / 4) ∧ 0 < v 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ lower upper : D → ℝ,
        (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
        (∀ d, upper d ≤ 16 / 5) → ∀ c : auxiliaryPrimes B → Bool, ∀ d : D, ∀ r : (ZMod q)ˣ,
        |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
            (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper))
            (lowPrimeLog (auxiliaryPrimes B) B ((B : ℝ) ^ (-(1 / 10 : ℝ)))) c (d, r) -
          clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
            ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
            (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient| ≤
          C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨v, hv, hvpos, H, C, hC, hbound⟩ := quarterPrimeSite_local_law hSD hSW hM
  refine ⟨v, hv, hvpos, H, C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro D _ q _ hq lower upper hdisjoint hupper c d r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  have hcut : ∀ p ∈ auxiliaryPrimes B, q < p := by
    intro p hp
    have hP : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
    exact hqP.trans_lt hP
  let u := ZMod.unitOfCoprime (retainedPrimeProduct (auxiliaryPrimes B) c)
    (retainedPrimeProduct_coprime (auxiliaryPrimes B) (auxiliaryPrimes_prime B) (NeZero.ne q) hcut c)
  rw [highExclusiveLogCell_eq (auxiliaryPrimes B) (auxiliaryPrimes_prime B) B q lower upper
    hdisjoint _ c u r rfl d]
  let t := Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / (B : ℝ)
  have ht : 0 ≤ t := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  let a := max ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d - t)
  let b := upper d - t
  by_cases hab : a ≤ b
  · have ha : (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a := le_max_left _ _
    have hb : b ≤ 16 / 5 := by dsimp [b] <;> linarith [hupper d]
    have hh := hboundB a b ha hab hb q hq (u⁻¹ * r)
    simpa only [clippedIntervalIntegral, t, a, b, ite_eq_left hab] using hh
  · have hempty : ∀ e : auxiliaryPrimes B → Bool,
        ¬(Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
      rintro e ⟨he, _⟩
      exact hab (le_trans he.1.le he.2)
    have hsum : (∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) = 0 := by
      apply sum_eq_zero
      intro e _
      exact ite_eq_right (hempty e)
    change |(∑ e : auxiliaryPrimes B → Bool,
        if Real.log (retainedPrimeProduct (auxiliaryPrimes B) e) / B ∈ Set.Ioc a b ∧
          (retainedPrimeProduct (auxiliaryPrimes B) e : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)
        then quarterPrimeMass (auxiliaryPrimes B) e else 0) - _| ≤ _
    have hclip : clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
        ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
        (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) = 0 := by
      change (if a ≤ b then _ else 0) = 0
      exact ite_eq_right hab
    rw [hsum, hclip]
    simp only [zero_div, sub_self, abs_zero]
    positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PartialPrimeChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- A local profile independent of the residue yields a flat retained
kernel for the partial output channel. -/
theorem partialFairPrimeKernel_flat_error {D R : Type*} [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m η : ℝ} (hm : 0 < m) (hη : 0 ≤ η)
    (hlocal : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low c (d, r) -
        profile c d| ≤ η) (d e : D) (r s : R) :
    |(finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
        (d, r) (e, s) -
      lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s)) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e| ≤
      (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by
  have hw := quarterPrimeMass_nonneg Q hQ
  have hind := independentPairKernel_cutoff (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) low (fun _ : D => m) (d, r) (e, s)
  have herr := partialFairPrimeKernel_independent_error Q hQ hN hcut cell hm (d, r) (e, s)
  have hhigh := exclusiveProductKernel_flat_error (quarterPrimeMass Q) (fun _ => m)
    (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) profile hw
    (quarterPrimeMass_sum Q) (fun _ => hm)
    (fun c a => highExclusiveCell_nonneg _ _ _ hw c a)
    (fun c a => highExclusiveCell_le_one _ _ _ hw (quarterPrimeMass_sum Q) c a)
    hη hlocal d e r s
  rw [hind] at herr
  have heq : (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) (d, r) (e, s) -
      lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s)) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e =
    (finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m)
      (partialFairPrimeTransition Q cell) (d, r) (e, s) -
      (lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
        (primeProductCell Q cell) low (fun _ => m) (d, r) (e, s) +
      exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
        (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) (d, r) (e, s))) +
      (exclusiveProductKernel (quarterPrimeMass Q) (fun _ => m)
        (highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low) (d, r) (e, s) -
      flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile d e) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add herr hhigh).trans_eq (add_comm _ _))

/-- Residue centering for the actual channel with discarded outputs. -/
theorem partialFairPrimeResidueChannel_square_bound {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq R]
    (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) {N : ℕ} (hN : N ≠ 0)
    (hcut : ∀ p ∈ Q, N < p) (cell : ℕ → Option (D × R))
    (low : (Q → Bool) → Prop) [DecidablePred low] (profile : (Q → Bool) → D → ℝ)
    {m H η : ℝ} (hm : 0 < m) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hmarginal : ∀ a, independentCellMarginal (quarterPrimeMass Q) (quarterPrimeMass Q)
      (primeProductCell Q cell) a ≤ H * m)
    (hcommon : ∀ e, low e → ∀ a,
      optionCellMass (quarterPrimeMass Q) (fun c => primeProductCell Q cell c e) a ≤ H * m)
    (hlocal : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass Q) (primeProductCell Q cell) low c (d, r) -
        profile c d| ≤ η)
    (f : (Q → Bool) → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell) f a -
        finiteResidueAverage (fun r =>
          finiteChannel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
            f (a.1, r))) ^ 2) ≤
      (8 * lowExclusiveProbability (quarterPrimeMass Q) low * H +
        4 * ((2 * η + η ^ 2 + 9 / (8 * N : ℝ)) / (m * m)) * ∑ _a : D × R, m) *
          ∑ x, fullPrimeMass Q x * f x ^ 2 := by
  have hquarter := quarterPrimeMass_nonneg Q hQ
  have hσ := lowExclusiveProbability_nonneg (quarterPrimeMass Q) low hquarter
  let K := finiteTwoSplitKernel (fullPrimeMass Q) (fun _ => m) (partialFairPrimeTransition Q cell)
  let L := lowUnionExclusiveKernel (quarterPrimeMass Q) (quarterPrimeMass Q)
    (primeProductCell Q cell) low (fun _ => m)
  have hL (a b : D × R) : 0 ≤ L a b :=
    lowUnionExclusiveKernel_nonneg _ _ _ _ _ hquarter hquarter (fun _ => hm.le) a b
  have hrows (a : D × R) : (∑ b : D × R, m * L a b) ≤
      2 * lowExclusiveProbability (quarterPrimeMass Q) low * H :=
    lowUnionExclusiveKernel_weighted_rows _ _ _ _ hquarter hquarter
      (quarterPrimeMass_sum Q) hm hmarginal hcommon a
  have hflat := partialFairPrimeKernel_flat_error Q hQ hN hcut cell low profile hm hη hlocal
  have hε : 0 ≤ (2 * η + η ^ 2) / (m * m) + (9 / (8 * N : ℝ)) / (m * m) := by positivity
  have hbound := residueChannel_square_of_discarded (fullPrimeMass Q) (fun _ : D => m)
    (partialFairPrimeTransition Q cell) L (fun a b => K a b - L a b)
    (flatExclusiveKernel (quarterPrimeMass Q) (fun _ => m) profile)
    (fullPrimeMass_nonneg Q hQ) (fun _ => hm) hL
    (fun a b => by dsimp [K] <;> ring)
    (mul_nonneg (mul_nonneg (by norm_num) hσ) hH) hε hrows hflat f
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PublishedResidueChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual residue-channel estimate from published analytic inputs

No marginal, conditional-cell, or high-exclusive approximation is assumed
here: all three are derived from the cited input estimates.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The bound is uniform in the number of cells, their endpoints, the
modulus and the real input. It uses only structural conditions on the cells. -/
theorem primeResidueChannel_from_published
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C T : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < T ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [Fintype D] [DecidableEq D],
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 2 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ δ : ℝ, 0 < δ → (∀ d, upper d - lower d = δ) →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      let m := δ / (q.totient : ℝ)
      let U := finiteChannel (fullPrimeMass (auxiliaryPrimes B)) (fun _ => m)
        (partialFairPrimeTransition (auxiliaryPrimes B) (logResidueCell B q lower upper)) f
      (∑ a : D × (ZMod q)ˣ, m * (U a - finiteResidueAverage (fun r => U (a.1, r))) ^ 2) ≤
        residueChannelError M C T B m (∑ _a : D × (ZMod q)ˣ, m) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨v, _, _, H, C₀, hC₀, hhigh⟩ := highExclusiveLogCell_local_law hSD hSW hM
  obtain ⟨M₁, C₁, hM₁, hC₁, hcommon⟩ := primeCommonLogCell_upper_jd hSD hSW hM hMP
  obtain ⟨M₂, C₂, hM₂, hC₂, hmarginal⟩ := primeChannelMarginal_upper_jd hSD hSW hM hMP
  obtain ⟨T, hT, htail⟩ := quarterPrimeMass_small_log_tail hM
  let M := M₁ + M₂
  let C := C₀ + C₁ + C₂
  have hM0 : 0 ≤ M := add_nonneg hM₁ hM₂
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hsmall : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 4 := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      tendsto_natCast_atTop_atTop
    exact (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono
      (fun _ h => h.le)
  refine ⟨M, C, T, hM0, hC, hT, ?_⟩
  filter_upwards [hhigh, hcommon, hmarginal, htail, hsmall, eventually_ge_atTop 2]
    with B hhighB hcommonB hmarginalB htailB hsmallB hB
  intro D _ _ q _ hq lower upper hdisjoint hlower horder hupper δ hδ hwidth f
  let m := δ / (q.totient : ℝ)
  let E := C * (B : ℝ) ^ (-(80 : ℝ))
  let κ := 9 / (8 * (auxiliaryCutoff B : ℝ))
  let A := M + (E + κ) / m
  let low := lowPrimeLog (auxiliaryPrimes B) B ((B : ℝ) ^ (-(1 / 10 : ℝ)))
  let profile (c : auxiliaryPrimes B → Bool) (d : D) :=
    clippedIntervalIntegral (scaledRoughDensity v (1 / 4) H B)
      ((B : ℝ) ^ (-(1 / 10 : ℝ))) (lower d) (upper d)
      (Real.log (retainedPrimeProduct (auxiliaryPrimes B) c) / B) / q.totient
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hm : 0 < m := div_pos hδ hφ
  have hE : 0 ≤ E := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg B) _)
  have hκ : 0 ≤ κ := by dsimp [κ] <;> positivity
  have hA : 0 ≤ A := add_nonneg hM0 (div_nonneg (add_nonneg hE hκ) hm.le)
  have hAM : A * m = M * m + E + κ := by dsimp [A]; field_simp <;> ring
  have hN : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have hcut : ∀ p ∈ auxiliaryPrimes B, auxiliaryCutoff B < p := by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2
  have hmar : ∀ a : D × (ZMod q)ˣ,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B))
        (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) a ≤ A * m := by
    rintro ⟨d, r⟩
    have hb := hmarginalB D q hq lower upper hdisjoint (fun d => by linarith [hlower d])
      horder hupper d r
    rw [hwidth d] at hb
    have hMC : M₂ * δ / (q.totient : ℝ) ≤ M * m := by
      have hle : M₂ ≤ M := by dsimp [M] <;> linarith
      simpa only [m, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hle (div_nonneg hδ.le hφ.le)
    have hEC : C₂ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      dsimp [C]
      linarith
    rw [hAM]
    linarith
  have hcom : ∀ e, low e → ∀ a : D × (ZMod q)ˣ,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c e) a ≤ A * m := by
    intro e he
    rintro ⟨d, r⟩
    have he' : lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e := le_trans he hsmallB
    have hb := hcommonB D q hq lower upper hdisjoint hlower horder hupper e he' d r
    rw [hwidth d] at hb
    have hMC : M₁ * δ / (q.totient : ℝ) ≤ M * m := by
      have hle : M₁ ≤ M := by dsimp [M] <;> linarith
      simpa only [m, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hle (div_nonneg hδ.le hφ.le)
    have hEC : C₁ * (B : ℝ) ^ (-(80 : ℝ)) ≤ E := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      dsimp [C]
      linarith
    rw [hAM]
    linarith
  have hloc : ∀ c d r,
      |highExclusiveCell (quarterPrimeMass (auxiliaryPrimes B))
          (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) low c (d, r) -
        profile c d| ≤ E := by
    intro c d r
    refine (hhighB D q hq lower upper hdisjoint hupper c d r).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
    dsimp [C]
    linarith
  have hout := partialFairPrimeResidueChannel_square_bound (auxiliaryPrimes B)
    (auxiliaryPrimes_prime B) hN hcut (logResidueCell B q lower upper) low profile hm hA hE
    hmar hcom hloc f
  have hσ : lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low ≤
      T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) :=
    htailB _ (Real.rpow_nonneg (Nat.cast_nonneg B) _) (hsmallB.trans (by norm_num))
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  refine hout.trans (mul_le_mul_of_nonneg_right ?_ hin)
  change 8 * lowExclusiveProbability (quarterPrimeMass (auxiliaryPrimes B)) low * A + _ ≤ _
  dsimp only [residueChannelError]
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 8)) hA) le_rfl

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

theorem residueChannelError_at_min (M C T : ℝ) {B : ℕ} (hB : 0 < B) :
    residueChannelError M C T B ((B : ℝ) ^ (-(3 : ℝ))) 3 =
      residueDecayEnvelope M C T B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hdiv (a b : ℝ) : (B : ℝ) ^ a / (B : ℝ) ^ b = (B : ℝ) ^ (a - b) :=
    (Real.rpow_sub hB0 a b).symm
  have hfirst : (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) /
      (B : ℝ) ^ (-(3 : ℝ)) = C * (B : ℝ) ^ (-(77 : ℝ)) +
        (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ)) := by
    rw [primeComparisonError_power hB, add_div, mul_div_assoc, mul_div_assoc, hdiv, hdiv]
    norm_num only [show (-(80 : ℝ)) - -3 = -77 by norm_num,
      show (-(1000 : ℝ)) - -3 = -997 by norm_num]
  have hs : ((B : ℝ) ^ (-(3 : ℝ))) * (B : ℝ) ^ (-(3 : ℝ)) =
      (B : ℝ) ^ (-(6 : ℝ)) := by rw [← Real.rpow_add hB0]; congr 1; norm_num
  have hp : (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 = C ^ 2 * (B : ℝ) ^ (-(160 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hB0.le]
    congr 2
    norm_num
  have hsecond : (2 * (C * (B : ℝ) ^ (-(80 : ℝ))) +
      (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 + 9 / (8 * (auxiliaryCutoff B : ℝ))) /
      ((B : ℝ) ^ (-(3 : ℝ)) * (B : ℝ) ^ (-(3 : ℝ))) =
      2 * C * (B : ℝ) ^ (-(74 : ℝ)) + C ^ 2 * (B : ℝ) ^ (-(154 : ℝ)) +
        (9 / 8 : ℝ) * (B : ℝ) ^ (-(994 : ℝ)) := by
    rw [hs, hp, primeComparisonError_power hB, add_div, add_div, ← mul_assoc]
    simp only [mul_div_assoc, hdiv]
    norm_num only [show (-(80 : ℝ)) - -6 = -74 by norm_num,
      show (-(160 : ℝ)) - -6 = -154 by norm_num,
      show (-(1000 : ℝ)) - -6 = -994 by norm_num]
  unfold residueChannelError residueDecayEnvelope
  rw [hfirst, hsecond]
  ring

theorem residueChannelError_le_envelope {M C T m mass : ℝ} {B : ℕ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 < B)
    (hm : (B : ℝ) ^ (-(3 : ℝ)) ≤ m) (hmass0 : 0 ≤ mass) (hmass : mass ≤ 3) :
    residueChannelError M C T B m mass ≤ residueDecayEnvelope M C T B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hm0 : 0 < (B : ℝ) ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hB0 _
  have hmpos : 0 < m := hm0.trans_le hm
  have hE : 0 ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by positivity
  have hκ : 0 ≤ 9 / (8 * (auxiliaryCutoff B : ℝ)) := by positivity
  have h1 := div_le_div_of_nonneg_left (add_nonneg hE hκ) hm0 hm
  have hnum : 0 ≤ 2 * (C * (B : ℝ) ^ (-(80 : ℝ))) +
      (C * (B : ℝ) ^ (-(80 : ℝ))) ^ 2 + 9 / (8 * (auxiliaryCutoff B : ℝ)) := by positivity
  have h2 := div_le_div_of_nonneg_left hnum
    (mul_pos hm0 hm0) (mul_self_le_mul_self hm0.le hm)
  have hR : 0 ≤ 1 / auxiliaryRatio B := one_div_nonneg.mpr
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B)))
  have hbase : 0 ≤ (B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B :=
    add_nonneg (Real.rpow_nonneg hB0.le _) hR
  have htail : 0 ≤ 8 * (T * ((B : ℝ) ^ (-(1 / 10 : ℝ)) +
      1 / auxiliaryRatio B) ^ (1 / 4 : ℝ)) :=
    mul_nonneg (by norm_num) (mul_nonneg hT (Real.rpow_nonneg hbase _))
  rw [← residueChannelError_at_min M C T hB]
  unfold residueChannelError
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h1) htail
  · exact mul_le_mul
      (mul_le_mul_of_nonneg_left h2 (by norm_num)) hmass
      hmass0
      (mul_nonneg (by norm_num) (div_nonneg hnum (mul_nonneg hm0.le hm0.le)))

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

theorem channel_total_mass {n q : ℕ} [NeZero q] (hn : 0 < n) :
    (∑ _a : Fin n × (ZMod q)ˣ, channelMesh n / (q.totient : ℝ)) = 5 / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hq0 : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin,
    ZMod.card_units_eq_totient, Nat.cast_mul, channelMesh]
  field_simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_UniformResidueChannel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform residue attenuation on the actual refining grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- Residue dependence tends to zero uniformly on the unit ball, including
inputs varying with B and the modulus. All arithmetic hypotheses are the
precise previously published inputs. -/
theorem manuscriptChannel_residue_envelope
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C T : ℝ, 0 ≤ M ∧ 0 < C ∧ 0 < T ∧
      ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          (manuscriptChannel m₁ B q f a -
            finiteResidueAverage (fun r => manuscriptChannel m₁ B q f (a.1, r))) ^ 2) ≤
        residueDecayEnvelope M C T B * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, T, hM0, hC, hT, hbound⟩ := primeResidueChannel_from_published hSD hSW hM hMP
  refine ⟨M, C, T, hM0, hC, hT, ?_⟩
  intro m₁ hm₁
  filter_upwards [hbound, channelFineCount_eventually_le_square hm₁, eventually_ge_atTop 1]
    with B hboundB hnB hB
  intro q _ hq f
  have hBpos : 0 < B := by omega
  have hn := channelFineCount_pos hm₁ hBpos
  have hqB : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) := by
    have hreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
    calc
      (q : ℝ) ≤ B := by exact_mod_cast hq
      _ = (B : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hreal (by norm_num)
  have hδ := channelMesh_pos hn
  have hmain := hboundB (Fin (channelFineCount m₁ B)) q hqB
    (channelLower (channelFineCount m₁ B)) (channelUpper (channelFineCount m₁ B))
    (channelCells_disjoint hn) (channelLower_ge _)
    (fun i => by linarith [channel_width _ i])
    (fun i => (channelUpper_le hn i).trans (by norm_num))
    (channelMesh (channelFineCount m₁ B)) hδ (channel_width _) f
  have hmass := channel_total_mass (q := q) hn
  have herr := residueChannelError_le_envelope (M := M) hC.le hT.le hBpos
    (channel_atom_lower hBpos hn hnB hq)
    (show 0 ≤ ∑ _a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
      channelMesh (channelFineCount m₁ B) / (q.totient : ℝ) by rw [hmass]; norm_num)
    (show (∑ _a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
      channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) ≤ 3 by rw [hmass]; norm_num)
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  exact hmain.trans (mul_le_mul_of_nonneg_right herr hin)

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueChannelRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The quantitative residue-decay rate -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliary_inv_ratio_eventually_le :
    ∀ᶠ B : ℕ in atTop, 1 / auxiliaryRatio B ≤ (B : ℝ) ^ (-(1 / 10 : ℝ)) := by
  have ht : Tendsto (fun B : ℕ => 1000 * (Real.log B / (B : ℝ) ^ (9 / 10 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def, mul_zero] using
      ((log_power_div_power_tendsto_zero 1 (by norm_num : (0 : ℝ) < 9 / 10)).comp
        tendsto_natCast_atTop_atTop).const_mul 1000
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hlim hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hp : (B : ℝ) ^ (9 / 10 : ℝ) = B * (B : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num, Real.rpow_add hB0, Real.rpow_one]
  have heq : (1 / auxiliaryRatio B) / (B : ℝ) ^ (-(1 / 10 : ℝ)) =
      1000 * (Real.log B / (B : ℝ) ^ (9 / 10 : ℝ)) := by
    rw [hp]
    simp only [auxiliaryRatio, one_div, inv_div]
    ring
  apply (div_le_one (Real.rpow_pos_of_pos hB0 _)).mp
  rw [heq]
  exact hlim.le

theorem residueDecayEnvelope_power_bound {M C T : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      residueDecayEnvelope M C T B ≤ K * (B : ℝ) ^ (-(1 / 40 : ℝ)) := by
  let K := 8 * T * (2 : ℝ) ^ (1 / 4 : ℝ) * (M + C + 9 / 8) +
    12 * (2 * C + C ^ 2 + 9 / 8)
  refine ⟨K, by dsimp [K] <;> positivity, ?_⟩
  filter_upwards [auxiliary_inv_ratio_eventually_le, eventually_ge_atTop 1] with B hR hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hp1 (p : ℝ) (hp : 0 ≤ p) : (B : ℝ) ^ (-p) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hB1 (neg_nonpos.mpr hp)
  have hpdec (p : ℝ) (hp : 1 / 40 ≤ p) :
      (B : ℝ) ^ (-p) ≤ (B : ℝ) ^ (-(1 / 40 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB1 (neg_le_neg hp)
  have hR0 : 0 ≤ 1 / auxiliaryRatio B := one_div_nonneg.mpr
    (div_nonneg (Nat.cast_nonneg B) (mul_nonneg (by norm_num) (Real.log_natCast_nonneg B)))
  have htail : ((B : ℝ) ^ (-(1 / 10 : ℝ)) + 1 / auxiliaryRatio B) ^ (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (1 / 4 : ℝ) * (B : ℝ) ^ (-(1 / 40 : ℝ)) := by
    calc
      _ ≤ (2 * (B : ℝ) ^ (-(1 / 10 : ℝ))) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hB0.le _), ← Real.rpow_mul hB0.le]
        congr 2
        norm_num
  have hsecond : M + C * (B : ℝ) ^ (-(77 : ℝ)) +
      (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ)) ≤ M + C + 9 / 8 := by
    have h77 := mul_le_mul_of_nonneg_left (hp1 77 (by norm_num)) hC
    have h997 := mul_le_mul_of_nonneg_left (hp1 997 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 9 / 8)
    linarith
  have hfirst := mul_le_mul htail hsecond (by positivity : (0 : ℝ) ≤
      M + C * (B : ℝ) ^ (-(77 : ℝ)) + (9 / 8 : ℝ) * (B : ℝ) ^ (-(997 : ℝ))) (by positivity)
  have h74 := mul_le_mul_of_nonneg_left (hpdec 74 (by norm_num)) (by positivity : 0 ≤ 2 * C)
  have h154 := mul_le_mul_of_nonneg_left (hpdec 154 (by norm_num)) (sq_nonneg C)
  have h994 := mul_le_mul_of_nonneg_left (hpdec 994 (by norm_num)) (by norm_num : (0 : ℝ) ≤ 9 / 8)
  unfold residueDecayEnvelope
  have hscaled := mul_le_mul_of_nonneg_left hfirst (by positivity : 0 ≤ 8 * T)
  dsimp [K]
  nlinarith

open Classical in
/-- The squared residue norm has the stronger rate B^(-1/40), so taking
square roots also gives the manuscript's weaker B^(-1/200) norm rate. -/
theorem manuscriptChannel_residue_rate
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ m₁ : ℕ, 0 < m₁ → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin (channelFineCount m₁ B) × (ZMod q)ˣ,
        (channelMesh (channelFineCount m₁ B) / (q.totient : ℝ)) *
          (manuscriptChannel m₁ B q f a -
            finiteResidueAverage (fun r => manuscriptChannel m₁ B q f (a.1, r))) ^ 2) ≤
        (K * (B : ℝ) ^ (-(1 / 40 : ℝ))) *
          ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨M, C, T, hM0, hC, hT, hbound⟩ := manuscriptChannel_residue_envelope hSD hSW hM hMP
  obtain ⟨K, hK, hrate⟩ := residueDecayEnvelope_power_bound hM0 hC.le hT.le
  refine ⟨K, hK, ?_⟩
  intro m₁ hm₁
  filter_upwards [hbound m₁ hm₁, hrate] with B hboundB hrateB
  intro q _ hq f
  exact (hboundB q hq f).trans (mul_le_mul_of_nonneg_right hrateB
    (Finset.sum_nonneg (fun x _ => mul_nonneg
      (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_HistogramBoxEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual histogram energies over geometric boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem geometric_histogram_window_length {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B)
    {t L U : ℝ} (hLU : L ≤ U) (k : ℤ) :
    ((histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B)
      (((k : ℝ)*t+U)/B)).card : ℝ)*channelMesh (channelFineCount m B) ≤ (U-L+2)/B := by
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have horder : ((k : ℝ)*t+L)/B ≤ ((k : ℝ)*t+U)/B :=
    div_le_div_of_nonneg_right (by linarith) hB0.le
  have hh := histogramWindowCells_length (channelFineCount_pos hm hBpos) horder
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 := by
    refine (channelMesh_scale_bound hm hBpos).trans ?_
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0)
  refine hh.trans ?_
  apply (le_div_iff₀ hB0).mpr
  have he : (((k : ℝ)*t+U)/B-((k : ℝ)*t+L)/B)*(B : ℝ) = U-L := by field_simp <;> ring
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ResidueBoxEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing local residue errors using the same geometric overlap -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem sum_selected_cells_le_overlap {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset κ) (J : κ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (K : ℝ) (hK : ∀ i, ((S.filter (fun k => i ∈ J k)).card : ℝ) ≤ K) :
    (∑ k ∈ S, ∑ i ∈ J k, w i) ≤ K*∑ i, w i := by
  classical
  have he (k : κ) : (∑ i ∈ J k, w i) = ∑ i, if i ∈ J k then w i else 0 := by
    rw [← sum_filter]
    simp
  simp_rw [he]
  rw [sum_comm,mul_sum]
  apply sum_le_sum
  intro i _
  have hc : (∑ k ∈ S, if i ∈ J k then w i else 0) =
      ((S.filter (fun k => i ∈ J k)).card : ℝ)*w i := by
    rw [← sum_filter,sum_const,nsmul_eq_mul]
  rw [hc]
  exact mul_le_mul_of_nonneg_right (hK i) (hw i)

theorem manuscript_geometric_residue_energy_jd_oai
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ t L U : ℝ, 0 < t → L ≤ U → ∀ S : Finset ℤ,
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ k ∈ S, manuscriptResidueEnergy m B q
        (histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)) g) ≤
        ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*C*((1+U-L)/t+1)*
          (B : ℝ)^(-(1/40 : ℝ))*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
  obtain ⟨C,hC,hbound⟩ := manuscriptChannel_residue_rate hSD hSW hM hMP
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [hbound m hm,eventually_ge_atTop 1] with B hboundB hB
  intro q _ hq t L U ht hLU S g
  have hBpos : 0 < B := by omega
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  let J := fun k : ℤ => histogramWindowCells (channelFineCount m B)
    (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)
  let w := fun i : Fin (channelFineCount m B) => ∑ r : (ZMod q)ˣ,
    (channelMesh (channelFineCount m B)/(q.totient : ℝ))*
      (manuscriptChannel m B q g (i,r)-finiteResidueAverage (fun s => manuscriptChannel m B q g (i,s)))^2
  have hδ := (channelMesh_pos (channelFineCount_pos hm hBpos)).le
  have hw : ∀ i, 0 ≤ w i := fun i => by dsimp [w] <;> positivity
  have hmesh : (B : ℝ)*channelMesh (channelFineCount m B) ≤ 1 := by
    refine (channelMesh_scale_bound hm hBpos).trans ?_
    simpa using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ B by exact_mod_cast hB) (by norm_num : (-(1/10 : ℝ)) ≤ 0)
  have hK : ∀ i, ((S.filter (fun k => i ∈ J k)).card : ℝ) ≤ (1+U-L)/t+1 := by
    intro i
    refine (histogramWindow_overlap hB0 ht hLU (channelFineCount_pos hm hBpos) S i).trans ?_
    exact add_le_add (div_le_div_of_nonneg_right (by linarith) ht.le) le_rfl
  have hsum := sum_selected_cells_le_overlap S J w hw _ hK
  have hglobal : (∑ i, w i) ≤ C*(B : ℝ)^(-(1/40 : ℝ))*
      (∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
    simpa only [w,Fintype.sum_prod_type] using hboundB q hq g
  have hκ : 0 ≤ (1+U-L)/t+1 := by
    have : 0 ≤ 1+U-L := by linarith
    positivity
  have hlocal (k : ℤ) : manuscriptResidueEnergy m B q (J k) g ≤
      ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*(∑ i ∈ J k, w i) := by
    unfold manuscriptResidueEnergy
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (geometric_histogram_window_length hm hB hLU k) (by positivity))
      (sum_nonneg (fun i _ => hw i))
  calc
    _ ≤ ∑ k ∈ S, ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*(∑ i ∈ J k, w i) :=
      sum_le_sum (fun k _ => hlocal k)
    _ = ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*(∑ k ∈ S, ∑ i ∈ J k, w i) :=
      (mul_sum _ _ _).symm
    _ ≤ ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*(((1+U-L)/t+1)*
        (C*(B : ℝ)^(-(1/40 : ℝ))*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2))) := by
      have hpref : 0 ≤ ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B) := by
        have : 0 ≤ U-L+2 := by linarith
        positivity
      exact mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left hglobal hκ)) hpref
    _ = _ := by ring

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.manuscript_geometric_residue_energy_jd_oai := @OAI.JointDickman.manuscript_geometric_residue_energy_jd_oai
