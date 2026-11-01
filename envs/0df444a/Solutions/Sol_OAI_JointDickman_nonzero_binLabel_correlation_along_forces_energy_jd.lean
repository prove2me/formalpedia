-- Prove2me | solution 1 for OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:48:53.473677+00:00
-- url     : https://prove2.me/submissions/36951315-08e1-4542-810e-bc47ebfc5abc

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_amplification_regularity_loss_jd
import Theorems.Thm_OAI_JointDickman_weightedAmplification_second_bound_jd

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

/-- The coefficient and remaining-site weight convert a sum over divisors
into a fair-split expectation, with total normalization `L * R`. -/
theorem fairSplit_weight_identity {α : Type*} [DecidableEq α]
    {S T : Finset α} (hT : T ⊆ S) (L R : ℝ) (hR : 0 ≤ R) :
    (L * Real.sqrt R * (1 / 2 : ℝ) ^ T.card) *
        (Real.sqrt R * (1 / 2 : ℝ) ^ (S \ T).card) =
      L * R * (1 / 2 : ℝ) ^ S.card := by
  calc
    _ = L * (Real.sqrt R * Real.sqrt R) *
        ((1 / 2 : ℝ) ^ T.card * (1 / 2 : ℝ) ^ (S \ T).card) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt hR, ← pow_add, add_comm T.card,
        Finset.card_sdiff_add_card_eq_card hT]

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

/-- Finite `L¹` error controls every bounded complex test. -/
theorem finiteMass_test_bound_of_l1 {Ω : Type*} [Fintype Ω]
    (a b : Ω → ℝ) (F : Ω → ℂ) {L ε : ℝ} (hL : 0 ≤ L)
    (hF : ∀ x, ‖F x‖ ≤ L) (hε : (∑ x, |a x - b x|) ≤ ε) :
    ‖(∑ x, (a x : ℂ) * F x) - (∑ x, (b x : ℂ) * F x)‖ ≤ L * ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, ‖(a x : ℂ) * F x - (b x : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |a x - b x| * L := by
      apply Finset.sum_le_sum
      intro x _
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = L * ∑ x, |a x - b x| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hε hL

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

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

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

/-- Chinese remaindering factors the exact uniform mean at coprime moduli. -/
theorem residueMean_crt {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m.Coprime q) (f : ZMod m → ℂ) (g : ZMod q → ℂ) :
    residueMean (fun a : ZMod (m * q) =>
      f ((ZMod.chineseRemainder hmq) a).1 * g ((ZMod.chineseRemainder hmq) a).2) =
      residueMean f * residueMean g := by
  unfold residueMean
  have hsum := Fintype.sum_equiv (ZMod.chineseRemainder hmq).toEquiv
    (fun a => f ((ZMod.chineseRemainder hmq) a).1 * g ((ZMod.chineseRemainder hmq) a).2)
    (fun ab => f ab.1 * g ab.2) (fun _ => rfl)
  rw [hsum, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  push_cast
  ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularPrimeSets
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's regular prime sets and truncated weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryOdds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded odds corrections at the manuscript's auxiliary scale -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_mul_sqrt_ratio {B : ℕ} (hB : 1 < B) :
    coefficientScale B * auxiliaryRatio B ^ (1 / 2 : ℝ) = B := by
  unfold coefficientScale
  rw [mul_assoc, ← Real.rpow_add (auxiliaryRatio_pos hB)]
  norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [mul_comm, auxiliaryRatio_mul_log hB]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimePairPushforward
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact pushforward for two independent prime products -/

namespace JointDickman

open Finset

theorem primeProductPair_weighted_sum (P : Finset ℕ) (z : ℝ)
    (S : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) :
    (∑ ac ∈ S, f ac * (primeProductMass P z ac.1 * primeProductMass P z ac.2)) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          f (∏ p ∈ A, p, ∏ p ∈ D, p) *
            (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
        else 0 := by
  classical
  unfold primeProductMass
  simp_rw [sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  have hpoint (ac : ℕ × ℕ) :
      f ac * ((if (∏ p ∈ A, p) = ac.1 then bernoulliSubsetMass P (fun p => z / p) A else 0) *
        (if (∏ p ∈ D, p) = ac.2 then bernoulliSubsetMass P (fun p => z / p) D else 0)) =
      if ac = (∏ p ∈ A, p, ∏ p ∈ D, p) then
        f ac * (bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D)
      else 0 := by
    rcases ac with ⟨a, c⟩
    by_cases ha : (∏ p ∈ A, p) = a <;> by_cases hc : (∏ p ∈ D, p) = c
    all_goals simp only [ha, hc, ite_true, if_true, ite_false, if_false, zero_mul, mul_zero, Prod.mk.injEq]
    all_goals simp_all only [eq_comm, and_self, and_true, and_false, ite_false, if_false]
  simp_rw [hpoint]
  simp

theorem primeProductPair_sum_event (P : Finset ℕ) (z : ℝ) (S : Finset (ℕ × ℕ)) :
    (∑ ac ∈ S, primeProductMass P z ac.1 * primeProductMass P z ac.2) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        if (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ S then
          bernoulliSubsetMass P (fun p => z / p) A * bernoulliSubsetMass P (fun p => z / p) D
        else 0 := by
  simpa only [one_mul] using primeProductPair_weighted_sum P z S (fun _ => 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IndependentRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss for two independent coefficient weights -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularCoefficientWeight_le (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    regularCoefficientWeight B L τ C n ≤ coefficientWeight B n := by
  unfold regularCoefficientWeight
  split_ifs
  · exact le_rfl
  · exact coefficientWeight_nonneg B n

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProbabilityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic probability bounds for nonregular coefficient pairs -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryHalfMass_nonneg (B n : ℕ) :
    0 ≤ primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  classical
  unfold primeProductMass
  apply sum_nonneg
  intro S hS
  split_ifs
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hS)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    exact ⟨div_nonneg (by norm_num) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalFairSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact conditional law of the remaining half of a prime site -/

namespace JointDickman

open Finset

private theorem subsetMass_prod_ite {P S : Finset ℕ} (hS : S ⊆ P) (q : ℕ → ℝ) :
    bernoulliSubsetMass P q S = ∏ p ∈ P, if p ∈ S then q p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno]
  rfl

private theorem subsetMass_tilt_product {P S : Finset ℕ} (hS : S ⊆ P) (q v : ℕ → ℝ) :
    bernoulliSubsetMass P q S * (∏ p ∈ S, v p) =
      ∏ p ∈ P, if p ∈ S then q p * v p else 1 - q p := by
  classical
  rw [prod_ite]
  have hyes : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hno : P.filter (fun p => p ∉ S) = P \ S := by ext p; simp
  rw [hyes, hno, prod_mul_distrib]
  unfold bernoulliSubsetMass
  ring

/-- The exact joint mass factors into the selected marginal and the
independent remaining indicators, including the zero probabilities at A. -/
theorem fairSelectedRemainingMass_factor {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    fairSelectedRemainingMass P A R =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      bernoulliSubsetMass P (remainingPrimeParameter A) R := by
  classical
  by_cases hd : Disjoint A R
  · rw [fairSelectedRemainingMass, ite_eq_left hd,
      show (1 / 2 : ℝ)^(A ∪ R).card = ∏ _p ∈ A ∪ R, (1 / 2 : ℝ) by simp,
      subsetMass_tilt_product (union_subset hA hR), subsetMass_prod_ite hA,
      subsetMass_prod_ite hR, ← prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hden : 2 * (p : ℝ) - 1 ≠ 0 := by linarith only [hp2]
    have hden' : -1 + (p : ℝ) * 2 ≠ 0 := by linarith only [hp2]
    by_cases ha : p ∈ A <;> by_cases hr : p ∈ R
    · exact False.elim ((disjoint_left.mp hd) ha hr)
    · simp only [mem_union, ha, hr, true_or, ite_true, if_true, ite_false, if_false, remainingPrimeParameter]
      ring
    · simp only [mem_union, ha, hr, false_or, ite_true, if_true, ite_false, if_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination - (mul_inv_cancel₀ hden')
    · simp only [mem_union, ha, hr, false_or, ite_false, if_false, remainingPrimeParameter]
      field_simp [hp0, hden, hden']
      linear_combination mul_inv_cancel₀ hden'
  · rw [fairSelectedRemainingMass, ite_eq_right hd]
    obtain ⟨p, hpA, hpR⟩ := not_disjoint_iff.mp hd
    have hzero : bernoulliSubsetMass P (remainingPrimeParameter A) R = 0 := by
      unfold bernoulliSubsetMass
      have hz : (∏ p ∈ R, remainingPrimeParameter A p) = 0 := by
        apply prod_eq_zero hpR
        simp only [remainingPrimeParameter, hpA, ite_true, if_true]
      rw [hz, zero_mul]
    rw [hzero, mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FairSplitPairRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two remaining subsets in the amplification model -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem fairSelectedRemainingMass_nonneg {P A R : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hR : R ⊆ P) :
    0 ≤ fairSelectedRemainingMass P A R := by
  unfold fairSelectedRemainingMass
  split_ifs
  · apply mul_nonneg _ (by positivity)
    apply bernoulliSubsetMass_nonneg (union_subset hA hR)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  · exact le_rfl

theorem fairSelectedRemainingMass_sum {P A : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) :
    (∑ R ∈ P.powerset, fairSelectedRemainingMass P A R) =
      bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A := by
  calc
    _ = ∑ R ∈ P.powerset,
        bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
          bernoulliSubsetMass P (remainingPrimeParameter A) R := by
      apply sum_congr rfl
      intro R hR
      exact fairSelectedRemainingMass_factor hP hA (mem_powerset.mp hR)
    _ = _ := by rw [← mul_sum, bernoulliSubsetMass_sum, mul_one]

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RoughHarmonicLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem finiteCountingFunction_rough (E : Finset ℕ) (z t : ℝ) :
    finiteCountingFunction (roughSquarefreeWeight E z) t = roughSquarefreeSummatory E z t := by
  unfold finiteCountingFunction roughSquarefreeSummatory
  rw [← Ioc_insert_left (Nat.zero_le ⌊t⌋₊), sum_insert left_notMem_Ioc]
  simp

theorem roughDensityPolynomial_continuousAt (c : ℕ → ℝ) (E : Finset ℕ)
    (z : ℝ) (H : ℕ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (roughDensityPolynomial c E z H) L := by
  apply tendsto_finsetSum
  intro j _
  apply continuousAt_const.mul
  apply ContinuousAt.add
  · exact continuousAt_id.rpow_const (Or.inl hL.ne')
  · exact continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl hL.ne'))

/-- Uniformity includes arbitrarily short intervals: the error is absolute. -/
theorem rough_harmonic_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t| ≤
          K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound] with B hB
  intro a b ha hab hlog
  have ha0 : 0 < a := by linarith
  let E := Nat.primesLE (auxiliaryCutoff B)
  let F := fun t : ℝ => t * ∑ j ∈ range (H + 1), roughCoefficient c E z j * (Real.log t) ^ (z - 1 - j)
  let M := fun t : ℝ => roughDensityPolynomial c E z H (Real.log t)
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt F (M t) t :=
    hasDerivAt_logarithmic_model c E z H (by linarith [ht.1])
  have hFc : ContinuousOn F (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hMc : ContinuousOn M (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    exact ((roughDensityPolynomial_continuousAt c E z H (Real.log_pos ht1)).comp
      (Real.continuousAt_log (by linarith : t ≠ 0))).continuousWithinAt
  have herr : ∀ t ∈ Set.Icc a b,
      |finiteCountingFunction (roughSquarefreeWeight E z) t - F t| ≤
        (K * (B : ℝ) ^ (-D)) * t := by
    intro t ht
    have hlogt : (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log t :=
      hlog.trans (Real.log_le_log ha0 ht.1)
    simpa only [finiteCountingFunction_rough, F, E, mul_assoc, mul_left_comm, mul_comm] using
      hB t hlogt (ha.trans ht.1)
  have h := harmonic_counting_error_le (roughSquarefreeWeight E z) F ha0 hab hFc herr
  rw [← harmonic_model_integral F M ha0 hab hd hMc] at h
  exact h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductIntervalLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual independent prime-product interval law

The harmonic rough counting estimate is transferred to the probability
law with an explicit, event-uniform local mass correction.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem primeProduct_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        9 ≤ a → a ≤ b → b ≤ auxiliaryUpper B →
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log a →
        |(∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
          primeNormalizer (auxiliaryPrimes B) z *
            ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) +
            K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hrough⟩ := rough_harmonic_interval_law hSD hM hz D
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hz1 : z ≤ 1 := by rcases hz with rfl | rfl <;> norm_num
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hrough, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hlog
  have hb0 : 0 ≤ b := by linarith
  have hcut : auxiliaryCutoff B ≠ 0 := by exact pow_ne_zero 1000 (Nat.ne_of_gt hB0)
  have hmass := primeProductMass_harmonic_error (U := auxiliaryUpper B) hcut hz0 hz1
    (Ioc ⌊a⌋₊ ⌊b⌋₊) (fun n hn =>
      ((by exact_mod_cast (mem_Ioc.mp hn).2 : (n : ℝ) ≤ ⌊b⌋₊).trans (Nat.floor_le hb0)).trans hb)
  have hQ := primeNormalizer_bounds (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hz0 hz1
  have hweighted : |primeNormalizer (auxiliaryPrimes B) z *
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
        ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t)| ≤
      K * (B : ℝ) ^ (-D) * (2 + Real.log (b / a)) := by
    rw [abs_mul, abs_of_nonneg hQ.1]
    simpa only [one_mul] using mul_le_mul hQ.2 (hB a b ha hab hlog) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have heq : (∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
      primeNormalizer (auxiliaryPrimes B) z *
        (∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t) =
      ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, primeProductMass (auxiliaryPrimes B) z n) -
        primeNormalizer (auxiliaryPrimes B) z *
          ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) +
      primeNormalizer (auxiliaryPrimes B) z *
        ((∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z n / (n : ℝ)) -
          ∫ t in a..b, roughDensityPolynomial c (Nat.primesLE (auxiliaryCutoff B)) z H (Real.log t) / t) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmass hweighted)

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

/-- The actual prime-product probability of a log-coordinate interval. -/
theorem primeProduct_log_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (D : ℝ) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        0 < a → a ≤ b → b ≤ 4 →
        9 ≤ Real.exp (B * a) → (B : ℝ) ^ (89 / 100 : ℝ) ≤ B * a →
        |(∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
            primeProductMass (auxiliaryPrimes B) z n) -
          ∫ s in a..b, scaledRoughDensity c z H B s| ≤
          z ^ 2 / (auxiliaryCutoff B : ℝ) + K * (B : ℝ) ^ (-D) * (2 + B * (b - a)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_interval_law hSD hM hz D
  refine ⟨c, hc0, hcpos, H, K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hB hB0
  intro a b ha hab hb hsize hscale
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB0
  have hexp : Real.exp (B * a) ≤ Real.exp (B * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hupper : Real.exp (B * b) ≤ auxiliaryUpper B := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := hB (Real.exp (B * a)) (Real.exp (B * b)) hsize hexp hupper
    (by simpa only [Real.log_exp] using hscale)
  rw [← scaledRoughDensity_integral c z H B hB0 ha hab] at h
  have hlog : Real.log (Real.exp (B * b) / Real.exp (B * a)) = B * (b - a) := by
    rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    ring
  simpa only [hlog] using h

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

/-- All intervals in the range have the same absolute error constant. -/
theorem primeProduct_local_interval_law
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
        (B : ℝ) ^ (-(1 / 10 : ℝ)) ≤ a → a ≤ b → b ≤ 16 / 5 →
        |(∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
            primeProductMass (auxiliaryPrimes B) z n) -
          ∫ s in a..b, scaledRoughDensity c z H B s| ≤ C * (B : ℝ) ^ (-(80 : ℝ)) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := primeProduct_log_interval_law hSD hM hz 81
  refine ⟨c, hc0, hcpos, H, 1 + 6 * K, by positivity, ?_⟩
  have hlarge : ∀ᶠ B : ℕ in atTop, (9 : ℝ) ≤ (B : ℝ) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 9)
  filter_upwards [hbound, hlarge, eventually_ge_atTop 1] with B hB hlargeB hB1
  intro a b ha hab hb
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB0 : (0 : ℝ) < B := by linarith
  obtain ⟨ha0, hsize, hscale⟩ := auxiliary_log_endpoint_conditions hB1 ha hlargeB
  have h := hB a b ha0 hab (by linarith) hsize hscale
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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductIntervalLower
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive local mass for the selected coefficient product -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

theorem half_density_compact_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1 / 2)) (H : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, 1 ≤ s → s ≤ 3 →
      d ≤ scaledRoughDensity c (1 / 2) H B s := by
  let k := (4 : ℝ)^(-(1 / 2 : ℝ)) *
    (Real.exp (-Real.eulerMascheroniConstant * (1 / 2)) / Real.Gamma (1 / 2))
  let d := k * (3 : ℝ)^(-(1 / 2 : ℝ)) / 2
  have hk : 0 < k := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos (by norm_num)))
  have hd : 0 < d := by dsimp [d] <;> positivity
  refine ⟨d, hd, ?_⟩
  have hu := scaledRoughDensity_tendstoUniformlyOn hM hMP c hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) < 1) H
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) d hd
  filter_upwards [he] with B hb
  intro s hs hs3
  have hc' := hb s hs
  rw [Real.dist_eq] at hc'
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith only [hs] : 0 < s) hs3
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hm := mul_le_mul_of_nonneg_left hp hk.le
  have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
  rw [hexp] at hc'
  change |k * s^(-(1 / 2 : ℝ)) - scaledRoughDensity c (1 / 2) H B s| < d at hc'
  dsimp only [d] at hc' ⊢
  nlinarith only [hm, (abs_lt.mp hc').2]

/-- Uniform lower mass on every logarithmic interval inside [1,3]. The
fixed B⁻⁸⁰ error is retained so the theorem also applies to intervals of
length comparable to 1/B. -/
theorem half_primeProduct_interval_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d E : ℝ, 0 < d ∧ 0 < E ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
      1 ≤ a → a ≤ b → b ≤ 3 →
      d * (b - a) - E * (B : ℝ)^(-(80 : ℝ)) ≤
        ∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
          primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  obtain ⟨c, hc, _, H, E, hE, hlocal⟩ := primeProduct_local_interval_law hSD hM
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2)
  obtain ⟨d, hd, hdensity⟩ := half_density_compact_lower hM hMP c hc H
  refine ⟨d, E, hd, hE, ?_⟩
  filter_upwards [hlocal, hdensity, eventually_ge_atTop 1] with B hl hdB hB
  intro a b ha hab hb
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp : (B : ℝ)^(-(1 / 10 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hB1 (by norm_num)
  have hloc := hl a b (hp.trans ha) hab (by linarith only [hb])
  have hi : IntervalIntegrable (scaledRoughDensity c (1 / 2) H B) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact (hasDerivAt_scaledRoughDensity c (1 / 2) H B
      (by linarith only [ha, hs.1] : 0 < s)).continuousAt.continuousWithinAt
  have hilow := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := d)) hi (fun s hs => hdB s (ha.trans hs.1) (hs.2.trans hb))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hilow
  nlinarith only [hilow, (abs_le.mp hloc).1]

/-- Positive mass persists at the multiplicative-window scale: an interval
of logarithmic width at least h/B has mass at least a fixed multiple of 1/B. -/
theorem half_primeProduct_short_interval_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {h : ℝ} (hh : 0 < h) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
      1 ≤ a → a ≤ b → b ≤ 3 → h / B ≤ b - a →
      d / B ≤ ∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
        primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  obtain ⟨d, E, hd, _, hbound⟩ := half_primeProduct_interval_lower hSD hM hMP
  refine ⟨d * h / 2, by positivity, ?_⟩
  have hlim : Tendsto (fun B : ℕ => E * (B : ℝ)^(-(79 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 79)).comp
        tendsto_natCast_atTop_atTop).const_mul E)
  have hsmall := hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d * h / 2))
  filter_upwards [hbound, hsmall, eventually_gt_atTop 0] with B hb hs hB
  intro a b ha hab hb3 hwidth
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hw := mul_le_mul_of_nonneg_left ((div_le_iff₀ hB0).mp hwidth) hd.le
  have hmain := mul_le_mul_of_nonneg_right (hb a b ha hab hb3) hB0.le
  have heq : E * (B : ℝ)^(-(80 : ℝ)) * B = E * (B : ℝ)^(-(79 : ℝ)) := by
    rw [show (-(79 : ℝ)) = -80 + 1 by norm_num, Real.rpow_add hB0, Real.rpow_one]
    ring
  rw [sub_mul, heq] at hmain
  apply (div_le_iff₀ hB0).mpr
  nlinarith only [hw, hmain, hs]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AmplificationWindows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive rectangle inside the coefficient size-and-ratio support -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem amplificationLowerC_bounds {B c : ℕ} (hc : c ∈ amplificationLowerC B) :
    Real.exp (B : ℝ) < c ∧ (c : ℝ) ≤ Real.exp ((3 / 2 : ℝ) * B) := by
  have h := mem_Ioc.mp hc
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h.1,
    (Nat.le_floor_iff (Real.exp_pos _).le).mp h.2⟩

theorem amplificationLowerPair_mem {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationLowerC B) (ha : a ∈ amplificationLowerA T c) :
    (a, c) ∈ amplificationCoefficientPairs B T := by
  obtain ⟨hcl, hcu⟩ := amplificationLowerC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have ha' := mem_Ioc.mp ha
  have hau : (a : ℝ) ≤ (3 / 2 : ℝ) * T * c :=
    (Nat.le_floor_iff (by positivity)).mp ha'.2
  apply (mem_amplificationCoefficientPairs hB).mpr
  refine ⟨hcl.le, hcu.trans (Real.exp_le_exp.mpr ?_), ha'.1.le, ?_⟩
  · have : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    linarith only [this]
  · have hprod : (0 : ℝ) < (T : ℝ) * c := mul_pos hT0 hc0
    have hh : (a : ℝ) < (2 * T * c : ℕ) := by push_cast; nlinarith only [hau, hprod]
    exact_mod_cast hh

theorem amplificationWindow_log_bounds {B T c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hTsize : (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B))
    (hc : c ∈ amplificationLowerC B) :
    1 ≤ Real.log ((T : ℝ) * c) / B ∧
      Real.log ((3 / 2 : ℝ) * T * c) / B ≤ 3 := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  obtain ⟨hcl, hcu⟩ := amplificationLowerC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hTC : (0 : ℝ) < (T : ℝ) * c := mul_pos (by linarith only [hT1]) hc0
  constructor
  · apply (le_div_iff₀ hB0).mpr
    have hmul : (c : ℝ) ≤ (T : ℝ) * c := by
      nlinarith only [mul_le_mul_of_nonneg_right hT1 hc0.le]
    have hh := Real.log_le_log (Real.exp_pos (B : ℝ))
      (hcl.le.trans hmul)
    simpa only [Real.log_exp, one_mul] using hh
  · have hTu : (T : ℝ) ≤ Real.exp ((1 / 2 : ℝ) * B) :=
      hTsize.trans (Real.exp_le_exp.mpr (by linarith only [hB0]))
    have hTCu : (T : ℝ) * c ≤ Real.exp (2 * (B : ℝ)) := by
      calc
        _ ≤ Real.exp ((1 / 2 : ℝ) * B) * Real.exp ((3 / 2 : ℝ) * B) :=
          mul_le_mul hTu hcu hc0.le (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hconst : (3 / 2 : ℝ) ≤ Real.exp (B : ℝ) := by
      have hh := Real.add_one_le_exp (B : ℝ)
      linarith only [hh, hB1]
    have hhi : (3 / 2 : ℝ) * T * c ≤ Real.exp (3 * (B : ℝ)) := by
      calc
        _ = (3 / 2 : ℝ) * ((T : ℝ) * c) := by ring
        _ ≤ Real.exp (B : ℝ) * Real.exp (2 * B) :=
          mul_le_mul hconst hTCu hTC.le (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    apply (div_le_iff₀ hB0).mpr
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (3 / 2 : ℝ) * T * c) hhi
    simpa only [Real.log_exp] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularAmplificationMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive first moment after all four regularity cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem fairRegularAmplificationAt_complement (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    fairRegularAmplificationAt B L τ C A D + fairFourSubsetFailureAt B L τ C A D =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D := by
  unfold fairRegularAmplificationAt fairFourSubsetFailureAt
  rw [← sum_add_distrib]
  calc
    _ = ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ Q ∈ (auxiliaryPrimes B).powerset,
        fairSelectedRemainingMass (auxiliaryPrimes B) A R *
          fairSelectedRemainingMass (auxiliaryPrimes B) D Q := by
      apply sum_congr rfl
      intro R _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro Q _
      split_ifs <;> simp only [zero_add, add_zero]
    _ = _ := by
      rw [← sum_mul_sum, fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hA,
        fairSelectedRemainingMass_sum (auxiliaryPrimes_prime B) hD]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing a site and its first split by the two disjoint parts -/

namespace JointDickman

open Finset

/-- The site-first and coefficient-first descriptions of one fair split
have identical finite expectations, with no asymptotic error. -/
theorem first_split_reindex (P A : Finset ℕ) (hA : A ⊆ P) (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      subsetRetentionMass S A * F (S \ A)) =
      ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R * F R := by
  classical
  calc
    _ = ∑ S ∈ P.powerset.filter (fun S => A ⊆ S),
        bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S * (1 / 2 : ℝ)^S.card * F (S \ A) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro S _
      unfold subsetRetentionMass
      split_ifs <;> ring
    _ = ∑ R ∈ P.powerset.filter (fun R => Disjoint A R), fairSelectedRemainingMass P A R * F R := by
      apply sum_bij (fun S _ => S \ A)
      · intro S hS
        obtain ⟨hSP, _⟩ := mem_filter.mp hS
        exact mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset.trans (mem_powerset.mp hSP)),
          disjoint_sdiff_self_right⟩
      · intro S hS T hT heq
        have hAS := (mem_filter.mp hS).2
        have hAT := (mem_filter.mp hT).2
        calc
          S = A ∪ (S \ A) := (union_sdiff_of_subset hAS).symm
          _ = A ∪ (T \ A) := congrArg (fun R => A ∪ R) heq
          _ = T := union_sdiff_of_subset hAT
      · intro R hR
        obtain ⟨hRP, hd⟩ := mem_filter.mp hR
        refine ⟨A ∪ R, mem_filter.mpr ⟨mem_powerset.mpr
          (union_subset hA (mem_powerset.mp hRP)), subset_union_left⟩, ?_⟩
        ext p
        have hn : p ∈ R → p ∉ A := fun hr ha => disjoint_left.mp hd ha hr
        simp only [mem_sdiff, mem_union]
        tauto
      · intro S hS
        have hAS := (mem_filter.mp hS).2
        have hd : Disjoint A (S \ A) := disjoint_sdiff_self_right
        rw [fairSelectedRemainingMass, ite_eq_left hd, union_sdiff_of_subset hAS]
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro R _
      by_cases hd : Disjoint A R
      · simp only [hd, ite_true, if_true]
      · simp only [hd, ite_false, if_false, fairSelectedRemainingMass, zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SymmetricSplitLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The symmetric two-split law and its coefficient-first disintegration -/

namespace JointDickman

open Finset

theorem subsetRetentionMass_sum_support {P S : Finset ℕ} (hS : S ⊆ P)
    (F : Finset ℕ → ℝ) :
    (∑ D ∈ P.powerset, subsetRetentionMass S D * F D) =
      ∑ D ∈ S.powerset, subsetRetentionMass S D * F D := by
  classical
  symm
  apply sum_subset (powerset_mono.mpr hS)
  intro D _ hD
  have hn : ¬ D ⊆ S := fun h => hD (mem_powerset.mpr h)
  simp only [subsetRetentionMass, hn, ite_false, if_false, zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteSplitModel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two independent sites with two fair splits at each site -/

namespace JointDickman

open Finset

theorem subsetRetentionMass_nonneg (S T : Finset ℕ) : 0 ≤ subsetRetentionMass S T := by
  unfold subsetRetentionMass
  split_ifs <;> positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalCoinAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common finite expectation for the conditional second split -/

namespace JointDickman
open Finset

theorem bernoulliHalf_eq_retention {P S : Finset ℕ} (hS : S ⊆ P) :
    bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) S = subsetRetentionMass P S := by
  classical
  simp only [bernoulliSubsetMass, prod_const, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    ← pow_add, card_sdiff_of_subset hS, Nat.add_sub_of_le (card_le_card hS),
    subsetRetentionMass, ite_eq_left hS]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationPointBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bounds for the normalized fair-split envelope -/

namespace JointDickman
open Finset

theorem subsetRetentionMass_sum {P S : Finset ℕ} (hS : S ⊆ P) :
    (∑ A ∈ P.powerset, subsetRetentionMass S A) = 1 := by
  have hs := subsetRetentionMass_sum_support hS (fun _ => 1)
  simp only [mul_one] at hs
  rw [hs]
  calc
    _ = ∑ A ∈ S.powerset, bernoulliSubsetMass S (fun _ => (1 / 2 : ℝ)) A := by
      apply sum_congr rfl
      intro A hA
      exact (bernoulliHalf_eq_retention (mem_powerset.mp hA)).symm
    _ = 1 := bernoulliSubsetMass_sum _ _

theorem sitePairSplitAverage_const_one {P S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P) :
    sitePairSplitAverage P S T (fun _ _ => 1) = 1 := by
  unfold sitePairSplitAverage
  simp only [mul_one, ← sum_mul_sum, subsetRetentionMass_sum hS, subsetRetentionMass_sum hT]

theorem sitePairSplitAverage_mono (P S T : Finset ℕ) (F G : Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ A ⊆ P, ∀ D ⊆ P, F A D ≤ G A D) :
    sitePairSplitAverage P S T F ≤ sitePairSplitAverage P S T G := by
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (hFG A (mem_powerset.mp hA) D (mem_powerset.mp hD))
    (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedAmplification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded coefficient cutoffs in the independent amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem independentWeightedAmplification_nonneg (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c) (S R : Finset ℕ) :
    0 ≤ independentWeightedAmplification B L τ C w S R := by
  unfold independentWeightedAmplification sitePairSplitAverage
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  apply mul_nonneg (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))
  dsimp only
  split_ifs
  · exact hw _ _
  · exact le_rfl

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

theorem auxiliarySubset_disjoint_small {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : Disjoint A (Nat.primesLE (auxiliaryCutoff B)) := by
  apply disjoint_left.mpr
  intro p hp hsmall
  have hp0 : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp (hA hp)).2
  exact (not_lt_of_ge (Nat.mem_primesLE.mp hsmall).1) hp0

theorem coefficientPrimeSet_primeProduct {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : coefficientPrimeSet B (∏ p ∈ A, p) = A := by
  have hp : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hn : (∏ p ∈ A, p) ≠ 0 := prod_ne_zero_iff.mpr (fun p h => (hp p h).ne_zero)
  rw [coefficientPrimeSet_eq_inter hn, Nat.primeFactors_prod hp, inter_eq_left.mpr hA]

theorem coefficientWeight_primeProduct {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientWeight B (∏ p ∈ A, p) = Real.log (auxiliaryCutoff B) * residueBaseWeight B A := by
  have hp : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  simp only [coefficientWeight, coefficientScale, residueBaseWeight,
    roughSquarefreeWeight, ArithmeticFunction.coe_mk, Nat.primeFactors_prod hp,
    auxiliarySubset_disjoint_small hA, ite_true, if_true, squarefreeWeight,
    primeProduct_squarefree A hp, primeProduct_cardFactors A hp]
  ring

open Classical in
theorem regularCoefficientWeight_primeProduct {B L : ℕ} {τ C : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) =
      Real.log (auxiliaryCutoff B) * regularResidueWeight B L τ C A := by
  rw [regularCoefficientWeight, coefficientPrimeSet_primeProduct hA]
  by_cases hr : RegularPrimeSet B L τ C A <;>
    simp only [regularResidueWeight, hr, ite_true, if_true, ite_false, if_false, mul_zero]
  exact coefficientWeight_primeProduct hA

open Classical in
/-- On a squarefree site, the arithmetic divisor and quotient weights are
exactly B times the fair-retention mass with its two regularity indicators. -/
theorem regular_arithmetic_split_identity {B L : ℕ} {τ C : ℝ} {S A : Finset ℕ}
    (hB : 1 < B) (hS : S ⊆ auxiliaryPrimes B) (hA : A ⊆ S) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) * regularResidueWeight B L τ C (S \ A) =
      (B : ℝ) * subsetRetentionMass S A *
        (if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C (S \ A) then 1 else 0) := by
  rw [regularCoefficientWeight_primeProduct (hA.trans hS)]
  have he := fairSplit_weight_identity hA (Real.log (auxiliaryCutoff B)) (auxiliaryRatio B)
    (auxiliaryRatio_pos hB).le
  have he' : (Real.log (auxiliaryCutoff B) * residueBaseWeight B A) *
      residueBaseWeight B (S \ A) = (B : ℝ) * subsetRetentionMass S A := by
    unfold residueBaseWeight subsetRetentionMass
    rw [ite_eq_left hA, ← Real.sqrt_eq_rpow]
    calc
      _ = Real.log (auxiliaryCutoff B) * auxiliaryRatio B * (1 / 2 : ℝ)^S.card := by
        convert he using 1 <;> first | rfl | ring
      _ = _ := by rw [mul_comm (Real.log _) _, auxiliaryRatio_mul_log hB]
  by_cases ha : RegularPrimeSet B L τ C A <;>
    by_cases hr : RegularPrimeSet B L τ C (S \ A)
  all_goals simp only [regularResidueWeight, ha, hr, and_self, and_false, false_and,
    ite_true, if_true, ite_false, if_false, mul_zero, zero_mul, mul_one]
  exact he'

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticAmplification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor weight equals the fair-split model away from square hits -/

namespace JointDickman
open Finset

open Classical in
theorem arithmeticSubsetAmplification_eq_model {B L n : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ)
    (hno₁ : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n)
    (hno₂ : ∀ p ∈ auxiliaryPrimes B, ¬ p^2 ∣ n + 1) :
    arithmeticSubsetAmplification B L τ C w n =
      independentWeightedAmplification B L τ C w
        (coefficientPrimeSet B n) (coefficientPrimeSet B (n + 1)) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have hS : coefficientPrimeSet B n ⊆ auxiliaryPrimes B := filter_subset _ _
  have hR : coefficientPrimeSet B (n + 1) ⊆ auxiliaryPrimes B := filter_subset _ _
  unfold arithmeticSubsetAmplification independentWeightedAmplification sitePairSplitAverage
  simp only [mul_sum]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  have hAP := mem_powerset.mp hA
  have hDP := mem_powerset.mp hD
  by_cases hd : (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1
  · rw [ite_eq_left hd,
      coefficientPrimeSet_quotient hAP hd.1 hno₁, coefficientPrimeSet_quotient hDP hd.2 hno₂]
    have hAS := (primeProduct_dvd_site_iff hAP).mp hd.1
    have hDR := (primeProduct_dvd_site_iff hDP).mp hd.2
    rw [regular_arithmetic_split_identity hB hS hAS, regular_arithmetic_split_identity hB hR hDR]
    by_cases h₁ : RegularPrimeSet B L τ C A <;>
    by_cases h₂ : RegularPrimeSet B L τ C D <;>
    by_cases h₃ : RegularPrimeSet B L τ C (coefficientPrimeSet B n \ A) <;>
    by_cases h₄ : RegularPrimeSet B L τ C (coefficientPrimeSet B (n + 1) \ D)
    all_goals simp only [h₁, h₂, h₃, h₄, and_self, and_false, and_true,
      ite_true, if_true, ite_false, if_false, mul_zero, zero_mul, mul_one]
    field_simp
  · rw [ite_eq_right hd, mul_zero]
    by_cases ha : A ⊆ coefficientPrimeSet B n
    · have hdn : ¬ D ⊆ coefficientPrimeSet B (n + 1) := fun hh =>
        hd ⟨(primeProduct_dvd_site_iff hAP).mpr ha, (primeProduct_dvd_site_iff hDP).mpr hh⟩
      simp only [subsetRetentionMass, hdn, ite_false, if_false, mul_zero, zero_mul]
    · simp only [subsetRetentionMass, ha, ite_false, if_false, mul_zero, zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite reindexing of the amplification divisor sum -/

namespace JointDickman
open Finset

/-- Reindex a divisibility condition by its quotient, retaining the exact
finite endpoint and allowing the harmless zero term. -/
theorem sum_divisors_reindex {M : Type*} [AddCommMonoid M]
    {a : ℕ} (ha : 0 < a) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ (range N).filter (fun n => a ∣ n), F n) =
      ∑ m ∈ (range N).filter (fun m => a*m < N), F (a*m) := by
  classical
  apply sum_bij (fun n _ => n/a)
  · intro n hn
    obtain ⟨hnN,hd⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    constructor
    · exact mem_range.mpr ((Nat.div_le_self n a).trans_lt (mem_range.mp hnN))
    · simpa only [Nat.mul_div_cancel' hd] using mem_range.mp hnN
  · intro n hn k hk hnk
    have hd := (mem_filter.mp hn).2
    have he := (mem_filter.mp hk).2
    calc
      n = a*(n/a) := (Nat.mul_div_cancel' hd).symm
      _ = a*(k/a) := by rw [hnk]
      _ = k := Nat.mul_div_cancel' he
  · intro m hm
    have ham := (mem_filter.mp hm).2
    refine ⟨a*m,mem_filter.mpr ⟨mem_range.mpr ham, dvd_mul_right a m⟩,?_⟩
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

/-- The same identity in indicator form, convenient inside coefficient sums. -/
theorem sum_dvd_ite_reindex {M : Type*} [AddCommMonoid M]
    {a : ℕ} (ha : 0 < a) (N : ℕ) (F : ℕ → M) :
    (∑ n ∈ range N, if a ∣ n then F n else 0) =
      ∑ m ∈ range N, if a*m < N then F (a*m) else 0 := by
  classical
  simpa only [sum_filter] using sum_divisors_reindex ha N F

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the actual arithmetic amplification into a divisor form -/

namespace JointDickman
open Finset

theorem sum_two_divisors_reindex {a c : ℕ} (ha : 0 < a) (N : ℕ)
    (H : ℕ → ℂ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ range N, if a ∣ n ∧ c ∣ n+1 then H n * F (n/a) ((n+1)/c) else 0) =
      ∑ m ∈ range N, if a*m < N ∧ c ∣ a*m+1 then H (a*m) * F m ((a*m+1)/c) else 0 := by
  classical
  have h := sum_dvd_ite_reindex ha N
    (fun n => if c ∣ n+1 then H n * F (n/a) ((n+1)/c) else 0)
  simpa only [ite_and, Nat.mul_div_cancel_left _ ha, ite_self] using h

/-- The finite first-form identity, including the precise endpoint. -/
theorem arithmeticAmplification_reindex (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (H : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, H n * (arithmeticSubsetAmplification B L τ C w n : ℂ)) =
      (1 / (B : ℂ)) * amplificationDivisorForm B L τ C w H N := by
  classical
  let F (n : ℕ) (A D : Finset ℕ) : ℂ :=
    if (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n+1 then
      H n * (((regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        arithmeticResidueWeight B L τ C (n/(∏ p ∈ A, p))) *
        (regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
          arithmeticResidueWeight B L τ C ((n+1)/(∏ p ∈ D, p))) *
        w (∏ p ∈ A, p) (∏ p ∈ D, p) : ℝ) : ℂ) else 0
  have he (n : ℕ) : H n * (arithmeticSubsetAmplification B L τ C w n : ℂ) =
      (1 / (B : ℂ)) * ∑ A ∈ (auxiliaryPrimes B).powerset,
        ∑ D ∈ (auxiliaryPrimes B).powerset, F n A D := by
    unfold arithmeticSubsetAmplification
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, Complex.ofReal_sum]
    rw [mul_left_comm, mul_sum]
    congr 1
    apply sum_congr rfl
    intro A _
    rw [mul_sum]
    apply sum_congr rfl
    intro D _
    dsimp only [F, arithmeticResidueWeight]
    split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero, mul_zero]
  simp_rw [he]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  unfold amplificationDivisorForm
  apply sum_congr rfl
  intro A hA
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  have ha : 0 < ∏ p ∈ A, p := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hA hp)).pos)
  exact sum_two_divisors_reindex ha N H
    (fun m l => (((regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      arithmeticResidueWeight B L τ C m) *
      (regularCoefficientWeight B L τ C (∏ p ∈ D, p) * arithmeticResidueWeight B L τ C l) *
      w (∏ p ∈ A, p) (∏ p ∈ D, p) : ℝ) : ℂ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_InteriorAmplificationWindows
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive coefficient windows strictly inside the smooth cutoff support -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem amplificationInteriorC_bounds {B c : ℕ} (hc : c ∈ amplificationInteriorC B) :
    Real.exp ((5 / 4 : ℝ) * B) < c ∧ (c : ℝ) ≤ Real.exp ((3 / 2 : ℝ) * B) := by
  have h := mem_Ioc.mp hc
  exact ⟨(Nat.floor_lt (Real.exp_pos _).le).mp h.1,
    (Nat.le_floor_iff (Real.exp_pos _).le).mp h.2⟩

theorem amplificationInteriorC_subset (B : ℕ) : amplificationInteriorC B ⊆ amplificationLowerC B := by
  intro c hc
  obtain ⟨hlo,hhi⟩ := amplificationInteriorC_bounds hc
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (Real.exp_pos _).le).mpr
    exact (Real.exp_le_exp.mpr (by have := Nat.cast_nonneg (α := ℝ) B; linarith)).trans_lt hlo
  · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr hhi

theorem amplificationInteriorA_subset (T c : ℕ) : amplificationInteriorA T c ⊆ amplificationLowerA T c := by
  intro a ha
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp ha
  apply mem_Ioc.mpr
  refine ⟨?_, hhi⟩
  have hfloor : T*c ≤ ⌊(5 / 4 : ℝ)*T*c⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    push_cast
    have ht : (0 : ℝ) ≤ (T : ℝ)*c := by positivity
    nlinarith
  exact hfloor.trans_lt hlo

theorem amplificationInteriorPair_mem {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationInteriorC B) (ha : a ∈ amplificationInteriorA T c) :
    (a,c) ∈ amplificationCoefficientPairs B T :=
  amplificationLowerPair_mem hB hT (amplificationInteriorC_subset B hc) (amplificationInteriorA_subset T c ha)

theorem amplification_interior_row_mass_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ T c : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ)*B) → c ∈ amplificationInteriorC B →
      d / B ≤ ∑ a ∈ amplificationInteriorA T c, primeProductMass (auxiliaryPrimes B) (1 / 2) a := by
  have hlog : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨d,hd,hbound⟩ := half_primeProduct_short_interval_lower hSD hM hMP hlog
  refine ⟨d,hd,?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T c hT hTsize hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans (amplificationInteriorC_bounds hc).1
  have hTC0 : (0 : ℝ) < (T : ℝ)*c := mul_pos hT0 hc0
  obtain ⟨hlo,hhi⟩ := amplificationWindow_log_bounds hB hT hTsize (amplificationInteriorC_subset B hc)
  have hlo' : 1 ≤ Real.log ((5 / 4 : ℝ)*T*c) / B := hlo.trans
    (div_le_div_of_nonneg_right (Real.log_le_log hTC0 (by nlinarith)) hB0.le)
  have hlogs : Real.log ((3 / 2 : ℝ)*T*c) / B - Real.log ((5 / 4 : ℝ)*T*c) / B =
      Real.log (6 / 5 : ℝ) / B := by
    rw [mul_assoc (3 / 2 : ℝ), mul_assoc (5 / 4 : ℝ),
      Real.log_mul (by norm_num) hTC0.ne', Real.log_mul (by norm_num) hTC0.ne']
    have hl : Real.log (6 / 5 : ℝ) = Real.log (3 / 2 : ℝ) - Real.log (5 / 4 : ℝ) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    rw [hl]
    ring
  have hwidth : Real.log ((5 / 4 : ℝ)*T*c) / B ≤ Real.log ((3 / 2 : ℝ)*T*c) / B := by
    have := div_nonneg hlog.le hB0.le
    linarith only [hlogs, this]
  have he1 : Real.exp ((B : ℝ)*(Real.log ((5 / 4 : ℝ)*T*c) / B)) = (5 / 4 : ℝ)*T*c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log (by positivity)]
  have he2 : Real.exp ((B : ℝ)*(Real.log ((3 / 2 : ℝ)*T*c) / B)) = (3 / 2 : ℝ)*T*c := by
    rw [mul_div_cancel₀ _ hB0.ne', Real.exp_log (by positivity)]
  have hh := hb _ _ hlo' hwidth hhi hlogs.ge
  rw [he1,he2] at hh
  exact hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_InteriorAmplificationMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive first moment strictly inside both coefficient cutoffs -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem amplificationInteriorPairs_subset {B T : ℕ} (hB : 0 < B) (hT : 0 < T) :
    amplificationInteriorPairs B T ⊆ amplificationCoefficientPairs B T := by
  intro ac hac
  obtain ⟨c, hc, hca⟩ := mem_biUnion.mp hac
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hca
  exact amplificationInteriorPair_mem hB hT hc ha

theorem amplificationInteriorPairs_sum (B T : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ ac ∈ amplificationInteriorPairs B T, f ac) =
      ∑ c ∈ amplificationInteriorC B, ∑ a ∈ amplificationInteriorA T c, f (a, c) := by
  unfold amplificationInteriorPairs
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro c _
    apply sum_image
    intro a _ b _ hab
    exact (Prod.mk.inj hab).1
  · intro c _ d _ hcd
    apply disjoint_left.mpr
    intro ac hac hdc
    obtain ⟨a, _, rfl⟩ := mem_image.mp hac
    obtain ⟨b, _, hb⟩ := mem_image.mp hdc
    exact hcd (congrArg Prod.snd hb).symm

theorem amplification_interior_c_mass
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop,
      d ≤ ∑ c ∈ amplificationInteriorC B, primeProductMass (auxiliaryPrimes B) (1 / 2) c := by
  obtain ⟨d, E, hd, _, hbound⟩ := half_primeProduct_interval_lower hSD hM hMP
  refine ⟨d / 8, by positivity, ?_⟩
  have hlim : Tendsto (fun B : ℕ => E * (B : ℝ)^(-(80 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 80)).comp
        tendsto_natCast_atTop_atTop).const_mul E)
  filter_upwards [hbound, hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d / 8))]
    with B hb hs
  have hh := hb (5 / 4) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_comm (B : ℝ) (5 / 4), mul_comm (B : ℝ) (3 / 2), amplificationInteriorC] at hh ⊢
  nlinarith only [hh, hs]

/-- The size-and-ratio event has a positive B-normalized first moment,
uniformly in every admissible amplification scale T. -/
theorem interior_amplification_first_moment_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      d ≤ (B : ℝ) * (∑ ac ∈ amplificationInteriorPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) := by
  obtain ⟨da, hda, ha⟩ := amplification_interior_row_mass_lower hSD hM hMP
  obtain ⟨dc, hdc, hc⟩ := amplification_interior_c_mass hSD hM hMP
  refine ⟨da * dc, mul_pos hda hdc, ?_⟩
  filter_upwards [ha, hc, eventually_gt_atTop 0] with B haB hcB hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hrows : da / (B : ℝ) *
      (∑ c ∈ amplificationInteriorC B, primeProductMass (auxiliaryPrimes B) (1 / 2) c) ≤
      ∑ ac ∈ amplificationInteriorPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
    rw [mul_sum, amplificationInteriorPairs_sum]
    apply sum_le_sum
    intro c hc
    dsimp only
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (haB T c hT hTsize hc) (auxiliaryHalfMass_nonneg B c)
  calc
    da * dc = (B : ℝ) * (da / B * dc) := by field_simp
    _ ≤ (B : ℝ) * (da / B * (∑ c ∈ amplificationInteriorC B,
        primeProductMass (auxiliaryPrimes B) (1 / 2) c)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hrows hB0.le

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

theorem amplificationBump_one {x : ℝ} (hx : x ∈ Set.Icc (5/4 : ℝ) (3/2)) :
    amplificationBump x = 1 := by
  apply amplificationBump.one_of_mem_closedBall
  change dist x (11/8 : ℝ) ≤ (1/8 : ℝ)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1,hx.2]

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

theorem amplificationSmoothWeight_bounds (B T a c : ℕ) :
    0 ≤ amplificationSmoothWeight B T a c ∧ amplificationSmoothWeight B T a c ≤ 1 := by
  obtain ⟨h0,h1⟩ := amplificationBump_bounds (Real.log c / B)
  obtain ⟨h0',h1'⟩ := amplificationBump_bounds ((a : ℝ) / ((T : ℝ)*c))
  exact ⟨mul_nonneg h0 h0', (mul_le_mul h1 h1' h0' (by norm_num)).trans_eq (by norm_num)⟩

theorem amplificationSmoothWeight_one {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationInteriorC B) (ha : a ∈ amplificationInteriorA T c) :
    amplificationSmoothWeight B T a c = 1 := by
  obtain ⟨hcl,hcu⟩ := amplificationInteriorC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 := mul_pos hT0 hc0
  have hlog : Real.log c / B ∈ Set.Icc (5/4 : ℝ) (3/2) := by
    constructor
    · apply (le_div_iff₀ hB0).mpr
      have hh := Real.log_le_log (Real.exp_pos _) hcl.le
      simpa only [Real.log_exp] using hh
    · apply (div_le_iff₀ hB0).mpr
      have hh := Real.log_le_log hc0 hcu
      simpa only [Real.log_exp] using hh
  have hr : (a : ℝ) / ((T : ℝ)*c) ∈ Set.Icc (5/4 : ℝ) (3/2) := by
    obtain ⟨hal,hau⟩ := mem_Ioc.mp ha
    constructor
    · apply (le_div_iff₀ hTC0).mpr
      have hh := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ (5/4 : ℝ)*T*c)).mp hal
      nlinarith only [hh]
    · apply (div_le_iff₀ hTC0).mpr
      have hh := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (3/2 : ℝ)*T*c)).mp hau
      nlinarith only [hh]
  rw [amplificationSmoothWeight, amplificationBump_one hlog, amplificationBump_one hr, one_mul]

theorem amplificationSmoothWeight_one_on_interior {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (h : (a,c) ∈ amplificationInteriorPairs B T) : amplificationSmoothWeight B T a c = 1 := by
  obtain ⟨d,hd,he⟩ := mem_biUnion.mp h
  obtain ⟨b,hb,he⟩ := mem_image.mp he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact amplificationSmoothWeight_one hB hT hd hb

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem coefficient_residue_base_product {B : ℕ} {A : Finset ℕ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (Q : Finset ℕ) :
    coefficientWeight B (∏ p ∈ A, p) * residueBaseWeight B Q =
      (B : ℝ) * (1 / 2 : ℝ)^(A.card + Q.card) := by
  rw [coefficientWeight_primeProduct hA]
  unfold residueBaseWeight
  rw [← Real.sqrt_eq_rpow, pow_add]
  calc
    _ = (Real.log (auxiliaryCutoff B) *
        (Real.sqrt (auxiliaryRatio B) * Real.sqrt (auxiliaryRatio B))) *
        ((1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^Q.card) := by ring
    _ = _ := by
      rw [Real.mul_self_sqrt (auxiliaryRatio_pos hB).le,
        mul_comm (Real.log _) _, auxiliaryRatio_mul_log hB]

open Classical in
theorem arithmetic_split_weight_le {B L n : ℕ} {τ C : ℝ} {A : Finset ℕ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (ha : (∏ p ∈ A, p) ∣ n) :
    regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      regularResidueWeight B L τ C (coefficientPrimeSet B (n / (∏ p ∈ A, p))) ≤
      (B : ℝ) * (1 / 2 : ℝ)^(coefficientPrimeSet B n).card := by
  let Q := coefficientPrimeSet B (n / (∏ p ∈ A, p))
  have hcard : (coefficientPrimeSet B n).card ≤ A.card + Q.card := by
    rw [← coefficientPrimeSet_union_quotient hA ha]
    exact card_union_le _ _
  have hpow : (1 / 2 : ℝ)^(A.card + Q.card) ≤ (1 / 2 : ℝ)^(coefficientPrimeSet B n).card :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hn : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  rw [regularCoefficientWeight, coefficientPrimeSet_primeProduct hA]
  unfold regularResidueWeight
  split_ifs
  · exact (coefficient_residue_base_product hB hA Q).le.trans (mul_le_mul_of_nonneg_left hpow hn)
  all_goals simp only [mul_zero, zero_mul]
  all_goals positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticAmplificationBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the actual arithmetic amplification -/

namespace JointDickman
open Finset

open Classical in
theorem arithmeticSiteWeight_nonneg (B L n : ℕ) (τ C : ℝ) :
    0 ≤ arithmeticSiteWeight B L τ C n := by
  apply sum_nonneg
  intro A _
  split_ifs
  · exact mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..)
  · exact le_rfl

open Classical in
theorem arithmeticSiteWeight_le {B L n : ℕ} (τ C : ℝ) (hB : 1 < B) :
    arithmeticSiteWeight B L τ C n ≤ B := by
  let S := coefficientPrimeSet B n
  have hS : S ⊆ auxiliaryPrimes B := filter_subset _ _
  have hf : (auxiliaryPrimes B).powerset.filter (fun A => A ⊆ S) = S.powerset := by
    ext A
    simp only [mem_filter, mem_powerset]
    exact and_iff_right_of_imp (fun h => h.trans hS)
  calc
    _ ≤ ∑ A ∈ (auxiliaryPrimes B).powerset,
        if A ⊆ S then (B : ℝ) * (1 / 2 : ℝ)^S.card else 0 := by
      apply sum_le_sum
      intro A hA
      have hAP := mem_powerset.mp hA
      have he : A ⊆ S ↔ (∏ p ∈ A, p) ∣ n := (primeProduct_dvd_site_iff hAP).symm
      simp only [he]
      split_ifs with ha
      · exact arithmetic_split_weight_le hB hAP ha
      · exact le_rfl
    _ = (2 : ℝ)^S.card * ((B : ℝ) * (1 / 2 : ℝ)^S.card) := by
      rw [← sum_filter, hf]
      simp
    _ = B := by
      calc
        _ = (B : ℝ) * ((2 : ℝ) * (1 / 2))^S.card := by rw [mul_pow]; ring
        _ = _ := by norm_num

open Classical in
theorem arithmeticSubsetAmplification_nonneg (B L n : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c) :
    0 ≤ arithmeticSubsetAmplification B L τ C w n := by
  unfold arithmeticSubsetAmplification
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  split_ifs
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))
      (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))) (hw _ _)
  · exact le_rfl

open Classical in
theorem arithmeticSubsetAmplification_le {B L n : ℕ} (τ C : ℝ)
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1) :
    arithmeticSubsetAmplification B L τ C w n ≤ B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hs := arithmeticSiteWeight_nonneg B L n τ C
  have ht := arithmeticSiteWeight_nonneg B L (n + 1) τ C
  calc
    _ ≤ (1 / (B : ℝ)) * (arithmeticSiteWeight B L τ C n *
        arithmeticSiteWeight B L τ C (n + 1)) := by
      unfold arithmeticSubsetAmplification arithmeticSiteWeight
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sum_mul]
      simp only [mul_sum]
      apply sum_le_sum
      intro A _
      apply sum_le_sum
      intro D _
      split_ifs
      · exact mul_le_of_le_one_right (mul_nonneg
          (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..))
          (mul_nonneg (regularCoefficientWeight_nonneg ..) (regularResidueWeight_nonneg ..)))
          (hw _ _)
      all_goals simp_all only [and_self, and_true, and_false, mul_zero, zero_mul, not_true_eq_false, le_refl]
    _ ≤ (1 / (B : ℝ)) * ((B : ℝ) * B) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (arithmeticSiteWeight_le τ C hB) (arithmeticSiteWeight_le τ C hB)
          ht hB0.le) (by positivity)
    _ = B := by field_simp

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

theorem auxiliaryProduct_dvd_period {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : (∏ p ∈ A, p) ∣ auxiliarySquarePeriod B := by
  exact (prod_dvd_prod_of_subset A (auxiliaryPrimes B) id hA).trans (dvd_pow_self _ (by omega))

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

open Classical in
theorem arithmeticSubsetAmplification_modEq {B L n m : ℕ} (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (h : n ≡ m [MOD auxiliarySquarePeriod B]) :
    arithmeticSubsetAmplification B L τ C w n =
      arithmeticSubsetAmplification B L τ C w m := by
  unfold arithmeticSubsetAmplification
  congr 1
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  have hAP := mem_powerset.mp hA
  have hDP := mem_powerset.mp hD
  have ha := h.dvd_iff (auxiliaryProduct_dvd_period hAP)
  have hd := (h.add_right 1).dvd_iff (auxiliaryProduct_dvd_period hDP)
  by_cases hn : (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n + 1
  · have hm := And.intro (ha.mp hn.1) (hd.mp hn.2)
    rw [ite_eq_left hn, ite_eq_left hm,
      coefficientPrimeSet_quotient_modEq h hAP hn.1 hm.1,
      coefficientPrimeSet_quotient_modEq (h.add_right 1) hDP hn.2 hm.2]
  · have hm : ¬ ((∏ p ∈ A, p) ∣ m ∧ (∏ p ∈ D, p) ∣ m + 1) :=
      fun hm => hn ⟨ha.mpr hm.1, hd.mpr hm.2⟩
    rw [ite_eq_right hn, ite_eq_right hm]

theorem residueAmplification_natCast (B L n : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    residueAmplification B L τ C w n = arithmeticSubsetAmplification B L τ C w n := by
  unfold residueAmplification
  rw [ZMod.val_natCast]
  exact arithmeticSubsetAmplification_modEq τ C w (Nat.mod_modEq _ _)

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
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

open Classical in
theorem squareHit_indicator_le (B n : ℕ) :
    (if AuxiliarySquareHit B n then (1 : ℝ) else 0) ≤
      ∑ p ∈ auxiliaryPrimes B,
        ((if p^2 ∣ n then (1 : ℝ) else 0) + (if p^2 ∣ n+1 then (1 : ℝ) else 0)) := by
  have hn (p : ℕ) : 0 ≤ (if p^2 ∣ n then (1 : ℝ) else 0) +
      (if p^2 ∣ n+1 then (1 : ℝ) else 0) := by positivity
  by_cases h : AuxiliarySquareHit B n
  · rw [ite_eq_left h]
    obtain ⟨p, hp, hd⟩ := h
    have ht : (1 : ℝ) ≤ (if p^2 ∣ n then (1 : ℝ) else 0) +
        (if p^2 ∣ n+1 then (1 : ℝ) else 0) := by
      rcases hd with hd | hd <;> simp only [hd, ite_true, if_true] <;> split_ifs <;> norm_num
    exact ht.trans (single_le_sum (fun p _ => hn p) hp)
  · rw [ite_eq_right h]
    exact sum_nonneg (fun p _ => hn p)

open Classical in
theorem residue_squareHit_mean_bound (B : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B),
      if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) ≤
        2 * ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  calc
    _ ≤ (∑ a : ZMod (auxiliarySquarePeriod B), ∑ p ∈ auxiliaryPrimes B,
        ((if p^2 ∣ a.val then (1 : ℝ) else 0) +
          (if p^2 ∣ a.val+1 then (1 : ℝ) else 0))) / (auxiliarySquarePeriod B : ℝ) :=
      div_le_div_of_nonneg_right (sum_le_sum (fun a _ => squareHit_indicator_le B a.val))
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [sum_comm, sum_div]
      simp_rw [sum_add_distrib, add_div]
      have h0 (p : ℕ) (hp : p ∈ auxiliaryPrimes B) := residue_square_divisor_mean hp 0
      simp only [add_zero] at h0
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [h0 p hp, residue_square_divisor_mean hp 1]
      ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConsecutivePrimeHits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two-hit law at one prime for consecutive integers -/

namespace JointDickman
open Finset

open Classical in
theorem consecutivePrimeHit_fiber {p : ℕ} (hp : p.Prime) (v : Bool × Bool) :
    let : NeZero p := ⟨hp.ne_zero⟩
    (∑ r : ZMod p, if consecutivePrimeHit r = v then (1 / (p : ℝ)) else 0) =
      consecutiveHitMass (1 / (p : ℝ)) v := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hne : (0 : ZMod p) ≠ -1 := by
    intro h
    have : (1 : ZMod p) = 0 := by simpa using congrArg Neg.neg h.symm
    exact hp.ne_one (ZMod.one_eq_zero_iff.mp this)
  rcases v with ⟨b,c⟩
  cases b <;> cases c
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (false, false) then (1 / (p : ℝ)) else 0) =
          (1 / (p : ℝ)) - (if r = 0 then (1 / (p : ℝ)) else 0) -
            (if r = -1 then (1 / (p : ℝ)) else 0) := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp only [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
      sum_ite_eq', mem_univ, ite_true, if_true, consecutiveHitMass, Bool.false_eq_true, ite_false, if_false]
    field_simp
    ring
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (false, true) then (1 / (p : ℝ)) else 0) =
          if r = -1 then (1 / (p : ℝ)) else 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (true, false) then (1 / (p : ℝ)) else 0) =
          if r = 0 then (1 / (p : ℝ)) else 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]
  · have he (r : ZMod p) :
        (if consecutivePrimeHit r = (true, true) then (1 / (p : ℝ)) else 0) = 0 := by
      by_cases h0 : r = 0 <;> by_cases h1 : r = -1
      · exact False.elim (hne (h0.symm.trans h1))
      all_goals simp [consecutivePrimeHit, h0, h1, hne, Ne.symm hne]
    simp_rw [he]
    simp [consecutiveHitMass]

theorem consecutiveHitMass_nonneg {q : ℝ} (hq : 0 ≤ q) (h2 : 2*q ≤ 1)
    (v : Bool × Bool) : 0 ≤ consecutiveHitMass q v := by
  rcases v with ⟨b,c⟩
  cases b <;> cases c <;> simp only [consecutiveHitMass, Bool.false_eq_true,
    ite_false, if_false, ite_true, if_true] <;> linarith

theorem consecutiveHitMass_sum (q : ℝ) : ∑ v, consecutiveHitMass q v = 1 := by
  simp [Fintype.sum_prod_type, consecutiveHitMass]
  ring

theorem independentHitMass_sum (q : ℝ) : ∑ v, independentHitMass q v = 1 := by
  simp [Fintype.sum_prod_type, independentHitMass, bernoulliBitMass]
  ring

theorem consecutiveHitMass_l1 (q : ℝ) :
    (∑ v, |consecutiveHitMass q v - independentHitMass q v|) = 4*q^2 := by
  have hneg : 1 - 2*q - (1-q)*(1-q) = -q^2 := by ring
  have hpos : q - (1-q)*q = q^2 := by ring
  have hpos' : q - q*(1-q) = q^2 := by ring
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, consecutiveHitMass,
    independentHitMass, bernoulliBitMass, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
    zero_sub, abs_neg, hneg, hpos, hpos', abs_of_nonneg (sq_nonneg q)]
  simp only [← pow_two, abs_of_nonneg (sq_nonneg q)]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConsecutiveCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact CRT law of the prime hits of two consecutive integers -/

namespace JointDickman
open Finset

theorem consecutive_crt_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : (P → Bool × Bool) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p), F (fun p => consecutivePrimeHit (n : ZMod p.val))) /
        (∏ p ∈ P, (p : ℝ)) =
      ∑ x, finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x * F x := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).ne_zero⟩
  have hcop : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hc := crt_uniform_mean (fun p : P => p.val) hcop
    (fun x => F (fun p => consecutivePrimeHit (x p)))
  have hl (p : P) : finitePushMass (fun (_ : ZMod p.val) => 1 / (p.val : ℝ))
      consecutivePrimeHit = consecutiveHitMass (1 / (p.val : ℝ)) := by
    funext v
    simpa only [finitePushMass] using consecutivePrimeHit_fiber (hP p.val p.property) v
  have hp := finiteProductMass_pushforward_test (fun (p : P) (_ : ZMod p.val) => 1 / (p.val : ℝ))
    (fun (_p : P) => consecutivePrimeHit) (fun x => (F x : ℂ))
  simp only [hl] at hp
  have hp' : (∑ x, finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x * F x) =
      ∑ x, finiteProductMass (fun (p : P) (_ : ZMod p.val) => 1 / (p.val : ℝ)) x *
        F (fun p => consecutivePrimeHit (x p)) := by exact_mod_cast hp
  rw [P.prod_coe_sort (fun p : ℕ => p), P.prod_coe_sort (fun p : ℕ => (p : ℝ))] at hc
  exact hc.trans hp'.symm

theorem consecutive_prime_product_l1 (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ x, |finiteProductMass (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ))) x -
      finiteProductMass (fun (p : P) => independentHitMass (1 / (p.val : ℝ))) x|) ≤
      4 * ∑ p ∈ P, 1 / (p : ℝ)^2 := by
  classical
  have hq (p : P) : 0 ≤ 1 / (p.val : ℝ) ∧ 1 / (p.val : ℝ) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ p.val := by exact_mod_cast (hP p.val p.property).one_le
    exact ⟨by positivity, by simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1⟩
  have htwo (p : P) : 2 * (1 / (p.val : ℝ)) ≤ 1 := by
    have h2 : (2 : ℝ) ≤ p.val := by exact_mod_cast (hP p.val p.property).two_le
    have hp : (0 : ℝ) < p.val := by linarith
    calc
      2 * (1 / (p.val : ℝ)) = 2 / (p.val : ℝ) := by ring
      _ ≤ 1 := (div_le_one hp).mpr h2
  have h := finiteProductMass_l1_le
    (fun (p : P) => consecutiveHitMass (1 / (p.val : ℝ)))
    (fun (p : P) => independentHitMass (1 / (p.val : ℝ)))
    (fun p v => consecutiveHitMass_nonneg (hq p).1 (htwo p) v)
    (fun p v => mul_nonneg (bernoulliBitMass_nonneg (hq p) v.1)
      (bernoulliBitMass_nonneg (hq p) v.2))
    (fun p => consecutiveHitMass_sum _) (fun p => independentHitMass_sum _)
  simp only [consecutiveHitMass_l1, one_div_pow, ← mul_sum] at h
  rw [P.sum_coe_sort (fun p : ℕ => 1 / (p : ℝ)^2)] at h
  exact h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_PairHitSites
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing two prime-hit vectors as two prime subsets -/

namespace JointDickman
open Finset

theorem pairHitMass_eq (P : Finset ℕ) (q : ℕ → ℝ) (S D : P.powerset) :
    finiteProductMass (fun p : P => independentHitMass (q p.val)) (pairHitEquiv P (S,D)) =
      bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D.val := by
  change (∏ p : P, bernoulliBitMass (q p.val) (subsetHitEquiv P S p) *
    bernoulliBitMass (q p.val) (subsetHitEquiv P D p)) = _
  rw [prod_mul_distrib]
  exact congrArg₂ (· * ·) (bernoulliSubsetMass_eq_product P q S)
    (bernoulliSubsetMass_eq_product P q D)

theorem pairHitSites_sum (P : Finset ℕ) (q : ℕ → ℝ) (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ x, finiteProductMass (fun p : P => independentHitMass (q p.val)) x *
      F (hitSites P x).1.val (hitSites P x).2.val) =
      ∑ S ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P q S * bernoulliSubsetMass P q D * F S D := by
  rw [← (pairHitEquiv P).sum_comp]
  simp only [hitSites, Equiv.symm_apply_apply, Fintype.sum_prod_type, pairHitMass_eq]
  calc
    _ = ∑ S : P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D * F S.val D := by
      apply sum_congr rfl
      intro S _
      exact P.powerset.sum_coe_sort (fun D =>
        bernoulliSubsetMass P q S.val * bernoulliSubsetMass P q D * F S.val D)
    _ = _ := P.powerset.sum_coe_sort (fun S => ∑ D ∈ P.powerset,
      bernoulliSubsetMass P q S * bernoulliSubsetMass P q D * F S D)

theorem hitSites_consecutive (P : Finset ℕ) (n : ℕ) :
    hitSites P (fun p => consecutivePrimeHit (n : ZMod p.val)) =
      (⟨P.filter (fun p => p ∣ n), mem_powerset.mpr (filter_subset _ _)⟩,
       ⟨P.filter (fun p => p ∣ n+1), mem_powerset.mpr (filter_subset _ _)⟩) := by
  apply (pairHitEquiv P).injective
  rw [show pairHitEquiv P (hitSites P (fun p => consecutivePrimeHit (n : ZMod p.val))) =
      (fun p => consecutivePrimeHit (n : ZMod p.val)) from (pairHitEquiv P).apply_symm_apply _]
  funext p
  apply Prod.ext
  · simp [pairHitEquiv, subsetHitEquiv, consecutivePrimeHit, p.property, ZMod.natCast_eq_zero_iff]
  · have he : (n : ZMod p.val) = -1 ↔ p.val ∣ n+1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      simp only [Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg]
    simp [pairHitEquiv, subsetHitEquiv, consecutivePrimeHit, p.property, he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConsecutiveSiteMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the actual consecutive prime sites by independent sites -/

namespace JointDickman
open Finset

theorem consecutive_site_mean_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hF : ∀ S ∈ P.powerset, ∀ D ∈ P.powerset, |F S D| ≤ L) :
    |(∑ n ∈ range (∏ p ∈ P, p), F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1))) /
        (∏ p ∈ P, (p : ℝ)) -
      ∑ S ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
          bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) D * F S D| ≤
      4*L*∑ p ∈ P, 1 / (p : ℝ)^2 := by
  classical
  let G (x : P → Bool × Bool) := F (hitSites P x).1.val (hitSites P x).2.val
  have hG (x : P → Bool × Bool) : |G x| ≤ L :=
    hF _ (hitSites P x).1.property _ (hitSites P x).2.property
  have hc := consecutive_crt_mean P hP G
  simp only [G, hitSites_consecutive] at hc
  have hi := pairHitSites_sum P (fun p => 1 / (p : ℝ)) F
  have ht := finiteMass_test_bound_of_l1
    (fun x => finiteProductMass (fun p : P => consecutiveHitMass (1 / (p.val : ℝ))) x)
    (fun x => finiteProductMass (fun p : P => independentHitMass (1 / (p.val : ℝ))) x)
    (fun x => (G x : ℂ)) hL
    (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hG x)
    (consecutive_prime_product_l1 P hP)
  have ht' : |(∑ x, finiteProductMass (fun p : P => consecutiveHitMass (1 / (p.val : ℝ))) x * G x) -
      (∑ x, finiteProductMass (fun p : P => independentHitMass (1 / (p.val : ℝ))) x * G x)| ≤
        L*(4*∑ p ∈ P, 1 / (p : ℝ)^2) := by
    simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using ht
  rw [hc, ← hi]
  convert ht' using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeSiteResidues
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enlarging the residue period preserves the prime-site mean -/

namespace JointDickman
open Finset

theorem primeSite_modEq {P : Finset ℕ} {q n m : ℕ}
    (hP : ∀ p ∈ P, p ∣ q) (h : n ≡ m [MOD q]) :
    P.filter (fun p => p ∣ n) = P.filter (fun p => p ∣ m) := by
  ext p
  simp only [mem_filter]
  exact and_congr_right (fun hp => h.dvd_iff (hP p hp))

theorem consecutive_site_mean_at_multiple (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} [NeZero q] (hd : (∏ p ∈ P, p) ∣ q)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ a : ZMod q, F (P.filter (fun p => p ∣ a.val)) (P.filter (fun p => p ∣ a.val+1))) / (q : ℝ) =
      (∑ n ∈ range (∏ p ∈ P, p), F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1))) /
        (∏ p ∈ P, (p : ℝ)) := by
  classical
  let d := ∏ p ∈ P, p
  let : NeZero d := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  let G (a : ZMod d) := F (P.filter (fun p => p ∣ a.val)) (P.filter (fun p => p ∣ a.val+1))
  have hpd : ∀ p ∈ P, p ∣ d := fun p hp => dvd_prod_of_mem id hp
  have hG (n : ℕ) : G (n : ZMod d) =
      F (P.filter (fun p => p ∣ n)) (P.filter (fun p => p ∣ n+1)) := by
    dsimp only [G]
    rw [ZMod.val_natCast, primeSite_modEq hpd (Nat.mod_modEq n d),
      primeSite_modEq hpd ((Nat.mod_modEq n d).add_right 1)]
  have h := residue_quotient_mean hd G
  simp only [hG] at h
  have hs := residue_sum_eq_range (fun a => (G a : ℂ))
  have hs' : (∑ a : ZMod d, G a) = ∑ n ∈ range d, G n := by exact_mod_cast hs
  rw [hs'] at h
  simp only [hG] at h
  simpa only [d, Nat.cast_prod] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticModelError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The arithmetic and fair-split weights differ only at rare square hits -/

namespace JointDickman
open Finset

open Classical in
theorem independentWeightedAmplification_le {B L : ℕ} {τ C : ℝ}
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1) {S R : Finset ℕ}
    (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    independentWeightedAmplification B L τ C w S R ≤ B := by
  have hh := sitePairSplitAverage_mono (auxiliaryPrimes B) S R
    (fun A D => if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
      then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0)
    (fun _ _ => 1) (by intros; split_ifs; exact hw _ _; norm_num)
  rw [sitePairSplitAverage_const_one hS hR] at hh
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg B)).trans_eq (mul_one _)

open Classical in
theorem arithmetic_model_power_error {B L n : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |(arithmeticSubsetAmplification B L τ C w n)^k -
      (independentWeightedAmplification B L τ C w
        (coefficientPrimeSet B n) (coefficientPrimeSet B (n+1)))^k| ≤
      (B : ℝ)^k * (if AuxiliarySquareHit B n then 1 else 0) := by
  by_cases h : AuxiliarySquareHit B n
  · rw [ite_eq_left h, mul_one]
    have ha0 := arithmeticSubsetAmplification_nonneg B L n τ C w (fun a c => (hw a c).1)
    have ha1 := arithmeticSubsetAmplification_le (L := L) τ C hB w (fun a c => (hw a c).2) (n := n)
    have hb0 := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1)
      (coefficientPrimeSet B n) (coefficientPrimeSet B (n+1))
    have hb1 := independentWeightedAmplification_le (B := B) (L := L) (τ := τ) (C := C) w (fun a c => (hw a c).2)
      (S := coefficientPrimeSet B n) (R := coefficientPrimeSet B (n+1))
      (filter_subset _ _) (filter_subset _ _)
    have ha := pow_le_pow_left₀ ha0 ha1 k
    have hb := pow_le_pow_left₀ hb0 hb1 k
    have ha' := pow_nonneg ha0 k
    have hb' := pow_nonneg hb0 k
    rw [abs_le]
    constructor <;> linarith
  · have hn : ∀ p ∈ auxiliaryPrimes B, ¬p^2 ∣ n :=
      fun p hp hd => h ⟨p, hp, Or.inl hd⟩
    have hn' : ∀ p ∈ auxiliaryPrimes B, ¬p^2 ∣ n+1 :=
      fun p hp hd => h ⟨p, hp, Or.inr hd⟩
    rw [arithmeticSubsetAmplification_eq_model hB w hn hn', sub_self, abs_zero,
      ite_eq_right h, mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticMomentComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Arithmetic amplification moments and the independent model -/

namespace JointDickman
open Finset

open Classical in
theorem arithmeticMoment_square_error {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |arithmeticAmplificationMoment B L τ C w k -
      (∑ a : ZMod (auxiliarySquarePeriod B),
        (independentWeightedAmplification B L τ C w
          (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k) /
            (auxiliarySquarePeriod B : ℝ)| ≤
      2*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  have hM : (0 : ℝ) < auxiliarySquarePeriod B := by exact_mod_cast auxiliarySquarePeriod_pos B
  unfold arithmeticAmplificationMoment
  rw [← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hM]
  calc
    _ ≤ (∑ a : ZMod (auxiliarySquarePeriod B),
        |(arithmeticSubsetAmplification B L τ C w a.val)^k -
          (independentWeightedAmplification B L τ C w
            (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k|) /
              (auxiliarySquarePeriod B : ℝ) :=
      div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hM.le
    _ ≤ ((B : ℝ)^k * ∑ a : ZMod (auxiliarySquarePeriod B),
        if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ) := by
      apply div_le_div_of_nonneg_right _ hM.le
      rw [mul_sum]
      exact sum_le_sum (fun a _ => arithmetic_model_power_error hB w hw k)
    _ = (B : ℝ)^k * ((∑ a : ZMod (auxiliarySquarePeriod B),
        if AuxiliarySquareHit B a.val then (1 : ℝ) else 0) / (auxiliarySquarePeriod B : ℝ)) := by ring
    _ ≤ (B : ℝ)^k * (2 * ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (residue_squareHit_mean_bound B) (by positivity)
    _ = _ := by ring

theorem siteMoment_independent_error {B L : ℕ} {τ C : ℝ}
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |(∑ a : ZMod (auxiliarySquarePeriod B),
        (independentWeightedAmplification B L τ C w
          (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1)))^k) /
            (auxiliarySquarePeriod B : ℝ) -
      independentAmplificationMoment B L τ C w k| ≤
      4*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  classical
  let F (S R : Finset ℕ) := (independentWeightedAmplification B L τ C w S R)^k
  have hF (S : Finset ℕ) (hS : S ∈ (auxiliaryPrimes B).powerset)
      (R : Finset ℕ) (hR : R ∈ (auxiliaryPrimes B).powerset) : |F S R| ≤ (B : ℝ)^k := by
    have h0 := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1) S R
    have h1 := independentWeightedAmplification_le (B := B) (L := L) (τ := τ) (C := C) w (fun a c => (hw a c).2)
      (mem_powerset.mp hS) (mem_powerset.mp hR)
    rw [abs_of_nonneg (pow_nonneg h0 k)]
    exact pow_le_pow_left₀ h0 h1 k
  have hc := consecutive_site_mean_bound (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    F (by positivity : 0 ≤ (B : ℝ)^k) hF
  have hm := consecutive_site_mean_at_multiple (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (auxiliaryProduct_dvd_period (Subset.refl (auxiliaryPrimes B))) F
  change |(∑ a : ZMod (auxiliarySquarePeriod B),
      F (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1))) /
      (auxiliarySquarePeriod B : ℝ) - _| ≤ _
  rw [show ((∑ a : ZMod (auxiliarySquarePeriod B),
      F (coefficientPrimeSet B a.val) (coefficientPrimeSet B (a.val+1))) /
      (auxiliarySquarePeriod B : ℝ)) = _ from hm]
  convert hc using 2
  all_goals try with_reducible_and_instances rfl
  unfold independentAmplificationMoment
  congr 1
  apply sum_congr rfl
  intro S _
  rw [mul_sum]
  apply sum_congr rfl
  intro R _
  dsimp [F]
  ring

theorem arithmeticMoment_independent_error {B L : ℕ} {τ C : ℝ}
    (hB : 1 < B) (w : ℕ → ℕ → ℝ) (hw : ∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) (k : ℕ) :
    |arithmeticAmplificationMoment B L τ C w k - independentAmplificationMoment B L τ C w k| ≤
      6*(B : ℝ)^k*∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by
  have h1 := arithmeticMoment_square_error (L := L) (τ := τ) (C := C) hB w hw k
  have h2 := siteMoment_independent_error (B := B) (L := L) (τ := τ) (C := C) w hw k
  exact (abs_sub_le _ _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticMomentDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite arithmetic moment error tends to zero at the auxiliary cutoff -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_quadratic_error_bound {B : ℕ} (hB : 1 < B) :
    6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) ≤ 6 / (B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hc0 : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B) hc0 (by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2)
  have hp : (B : ℝ)^3 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff, Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 3 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 3) hp)
  calc
    _ ≤ 6*(B : ℝ)^2*(1 / (B : ℝ)^3) :=
      mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = _ := by field_simp

theorem amplification_quadratic_error_tendsto :
    Tendsto (fun B : ℕ => 6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun _ => by positivity))
    ((eventually_gt_atTop 1).mono (fun _ h => amplification_quadratic_error_bound h))
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticSecondMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded second moment of the actual divisor amplification -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticAmplification_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
      (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
      arithmeticAmplificationMoment B L τ C w 2 ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := weightedAmplification_second_bound_jd hFord hM L τ C
  have he := amplification_quadratic_error_tendsto.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  refine ⟨K+1, by linarith, ?_⟩
  filter_upwards [hb, he, eventually_gt_atTop 1] with B hB hE hB1
  intro T w hT hTsize hw hsupp
  have hi : independentAmplificationMoment B L τ C w 2 ≤ K := hB T w hT hTsize hw hsupp
  have hc := arithmeticMoment_independent_error (L := L) (τ := τ) (C := C) hB1 w hw 2
  have hu := (le_abs_self _).trans (hc.trans hE)
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_InteriorRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interior positive mass survives all four regularity cutoffs -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem fairFourSubsetFailureAt_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairFourSubsetFailureAt B L τ C A D := by
  unfold fairFourSubsetFailureAt
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact le_rfl
  · exact mul_nonneg
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))

open Classical in
theorem interior_mass_regular_loss {B L T : ℕ} (τ C : ℝ) (hB : 0 < B) (hT : 0 < T) :
    (∑ ac ∈ amplificationInteriorPairs B T,
      primeProductMass (auxiliaryPrimes B) (1/2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1/2) ac.2) ≤
      fairRegularInteriorMass B L T τ C + fairFourSubsetFailure B L T τ C := by
  rw [primeProductPair_sum_event]
  unfold fairRegularInteriorMass fairFourSubsetFailure
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro A hA
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro D hD
  have hfail := fairFourSubsetFailureAt_nonneg B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T
  · have hp' := amplificationInteriorPairs_subset hB hT hp
    simp only [hp, hp', ite_true, if_true]
    exact (fairRegularAmplificationAt_complement B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)).symm.le
  · simp only [hp, ite_false, if_false, zero_add]
    split_ifs
    · exact hfail
    · exact le_rfl

theorem interior_regular_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        d ≤ (B : ℝ)*fairRegularInteriorMass B L T τ C := by
  obtain ⟨d,hd,hpositive⟩ := interior_amplification_first_moment_lower hSD hM hMP
  obtain ⟨K,hK,hloss⟩ := amplification_regularity_loss_jd hFord hM
  refine ⟨d/2, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε,_,hε,hlarge⟩ := hloss L τ hL hτ
  let C₀ := max 0 (10*Real.log (4*K/d))
  have hC₀ : 0 ≤ C₀ := le_max_left _ _
  have htail : ∀ C : ℝ, C₀ ≤ C → K*Real.exp (-(1/10 : ℝ)*C) ≤ d/4 := by
    intro C hC
    have hlog : 10*Real.log (4*K/d) ≤ C := (le_max_right _ _).trans hC
    have harg : -(1/10 : ℝ)*C ≤ -Real.log (4*K/d) := by linarith only [hlog]
    calc
      _ ≤ K*Real.exp (-Real.log (4*K/d)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hK.le
      _ = d/4 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 4*K/d)]
        field_simp
  refine ⟨C₀,hC₀,?_⟩
  have hsmall := hε.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d/(4*K)))
  filter_upwards [hpositive,hlarge,hsmall,eventually_gt_atTop 0] with B hp hl he hB
  intro C T hC hT hTsize
  have hpos := hp T hT hTsize
  have hlos := hl C T (hC₀.trans hC) hT hTsize
  have htails := htail C hC
  have heps : K*ε B ≤ d/4 := by
    have hh := mul_le_mul_of_nonneg_left he hK.le
    have heq : K*(d/(4*K)) = d/4 := by field_simp
    rwa [heq] at hh
  have hc := mul_le_mul_of_nonneg_left (interior_mass_regular_loss (L := L) τ C hB hT) (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  rw [mul_add] at hc
  nlinarith only [hpos,hlos,htails,heps,hc]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SitePairFirstLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first coefficient and remaining sets at two independent sites -/

namespace JointDickman
open Finset

theorem sitePair_first_law (P : Finset ℕ)
    (H : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
        sitePairSplitAverage P S T (fun A D => H A (S \ A) D (T \ D))) =
    ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      ∑ R ∈ P.powerset, ∑ Q ∈ P.powerset,
        fairSelectedRemainingMass P A R * fairSelectedRemainingMass P D Q * H A R D Q := by
  unfold sitePairSplitAverage
  simp only [mul_sum]
  conv_lhs => arg 2; ext S; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext A; arg 2; ext S; rw [sum_comm]
  conv_lhs => arg 2; ext A; rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro D hD
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
        subsetRetentionMass S A * (∑ T ∈ P.powerset,
          bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T * subsetRetentionMass T D * H A (S \ A) D (T \ D)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro T _
      ring
    _ = ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        (∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
          subsetRetentionMass T D * H A R D (T \ D)) :=
      first_split_reindex P A (mem_powerset.mp hA) (fun R =>
        ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
          subsetRetentionMass T D * H A R D (T \ D))
    _ = ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        (∑ Q ∈ P.powerset, fairSelectedRemainingMass P D Q * H A R D Q) := by
      apply sum_congr rfl
      intro R _
      rw [first_split_reindex P D (mem_powerset.mp hD) (fun Q => H A R D Q)]
    _ = _ := by simp only [mul_sum, mul_assoc]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_WeightedFirstMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive first moment for weights equal to one on the interior rectangle -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem fairRegularAmplificationAt_nonneg (B L : ℕ) (τ C : ℝ) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    0 ≤ fairRegularAmplificationAt B L τ C A D := by
  unfold fairRegularAmplificationAt
  apply sum_nonneg
  intro R hR
  apply sum_nonneg
  intro Q hQ
  split_ifs
  · exact mul_nonneg
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hA (mem_powerset.mp hR))
      (fairSelectedRemainingMass_nonneg (auxiliaryPrimes_prime B) hD (mem_powerset.mp hQ))
  · exact le_rfl

open Classical in
theorem independentWeighted_first_identity (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    independentAmplificationMoment B L τ C w 1 = (B : ℝ) *
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        fairRegularAmplificationAt B L τ C A D * w (∏ p ∈ A, p) (∏ p ∈ D, p) := by
  let H := fun A R D Q => if RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
    RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q then w (∏ p ∈ A, p) (∏ p ∈ D, p) else 0
  have he := sitePair_first_law (auxiliaryPrimes B) H
  have he' : (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) =
      ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
        fairRegularAmplificationAt B L τ C A D * w (∏ p ∈ A, p) (∏ p ∈ D, p) := by
    rw [he]
    unfold fairRegularAmplificationAt
    simp only [sum_mul]
    apply sum_congr rfl
    intro A _
    apply sum_congr rfl
    intro D _
    apply sum_congr rfl
    intro R _
    apply sum_congr rfl
    intro Q _
    dsimp only [H]
    simp only [and_assoc]
    split_ifs <;> ring
  calc
    _ = (B : ℝ) * (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
        ∑ R ∈ (auxiliaryPrimes B).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
          sitePairSplitAverage (auxiliaryPrimes B) S R (fun A D => H A (S \ A) D (R \ D))) := by
      simp only [independentAmplificationMoment, pow_one, independentWeightedAmplification, mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      dsimp only [H]
      ac_rfl
    _ = _ := congrArg (fun x : ℝ => (B : ℝ)*x) he'

open Classical in
theorem interior_mass_le_weighted_first (B L T : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ a c, 0 ≤ w a c)
    (hi : ∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) :
    (B : ℝ)*fairRegularInteriorMass B L T τ C ≤ independentAmplificationMoment B L τ C w 1 := by
  rw [independentWeighted_first_identity]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  have hn := fairRegularAmplificationAt_nonneg B L τ C (mem_powerset.mp hA) (mem_powerset.mp hD)
  by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationInteriorPairs B T
  · rw [ite_eq_left hp]
    exact le_mul_of_one_le_right hn (hi _ _ hp)
  · rw [ite_eq_right hp]
    exact mul_nonneg hn (hw _ _)

theorem independentWeighted_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ) (w : ℕ → ℕ → ℝ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        (∀ a c, 0 ≤ w a c) → (∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) →
        d ≤ independentAmplificationMoment B L τ C w 1 := by
  obtain ⟨d,hd,hl⟩ := interior_regular_first_lower hFord hSD hM hMP
  refine ⟨d,hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb] with B hB
  intro C T w hC hT hTsize hw hi
  exact (hB C T hC hT hTsize).trans (interior_mass_le_weighted_first B L T τ C w hw hi)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticFirstMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive first moment for the actual arithmetic divisor weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticWeighted_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ) (w : ℕ → ℕ → ℝ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
        (∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) →
        d ≤ arithmeticAmplificationMoment B L τ C w 1 := by
  obtain ⟨d,hd,hfirst⟩ := independentWeighted_first_lower hFord hSD hM hMP
  refine ⟨d/2, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hfirst L τ hL hτ
  have he := amplification_quadratic_error_tendsto.eventually
    (eventually_le_nhds (by positivity : (0 : ℝ) < d/2))
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb,he,eventually_gt_atTop 1] with B hB hE hB1
  intro C T w hC hT hTsize hw hi
  have hpos := hB C T w hC hT hTsize (fun a c => (hw a c).1) hi
  have herr := arithmeticMoment_independent_error (L := L) (τ := τ) (C := C) hB1 w hw 1
  have hBN : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hpow : (B : ℝ) ≤ (B : ℝ)^2 := by nlinarith
  have htail : 0 ≤ ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by positivity
  have hcompare : 6*(B : ℝ)^1*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) ≤
      6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) := by
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) htail
  have habs := herr.trans (hcompare.trans hE)
  have hl := neg_le_abs (arithmeticAmplificationMoment B L τ C w 1 -
    independentAmplificationMoment B L τ C w 1)
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothAmplificationMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two arithmetic moments for a concrete smooth amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem smooth_arithmetic_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        d ≤ arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 := by
  obtain ⟨d,hd,hl⟩ := arithmeticWeighted_first_lower hFord hSD hM hMP
  refine ⟨d,hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with B hB hB0
  intro C T hC hT hTsize
  exact hB C T (amplificationSmoothWeight B T) hC hT hTsize
    (amplificationSmoothWeight_bounds B T)
    (fun a c hac => (amplificationSmoothWeight_one_on_interior hB0 hT hac).ge)

theorem smooth_arithmetic_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 2 ≤ K := by
  intro L τ C
  obtain ⟨K,hK,hb⟩ := arithmeticAmplification_second_bound hFord hM L τ C
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with B hB hB0
  intro T hT hTsize
  exact hB T (amplificationSmoothWeight B T) hT hTsize
    (amplificationSmoothWeight_bounds B T)
    (amplificationSmoothWeight_support hB0 hT)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MovingPrimeIndependence
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact independence from every fixed residue coordinate -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem auxiliarySquarePeriod_eventually_coprime (q : ℕ) (hq : 0 < q) :
    ∀ᶠ B : ℕ in atTop, (auxiliarySquarePeriod B).Coprime q := by
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop q] with B hB
  unfold auxiliarySquarePeriod
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.prod_left
  intro p hp
  apply (auxiliaryPrimes_prime B p hp).coprime_iff_not_dvd.mpr
  intro hd
  have hpq := Nat.le_of_dvd hq hd
  have hcut : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hp).2
  omega

theorem residueAmplification_mean (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    residueMean (fun a => (residueAmplification B L τ C w a : ℂ)) =
      (arithmeticAmplificationMoment B L τ C w 1 : ℂ) := by
  unfold residueMean arithmeticAmplificationMoment residueAmplification
  simp only [pow_one, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueHilbert
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Hilbert estimates for residue profiles

Only uniform finite residue means are needed for the profile-preservation
argument. Their compatible refinements replace an explicit construction of
Haar measure on the profinite integers.
-/

namespace JointDickman
open Finset

theorem residueEnergy_nonneg {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    0 ≤ residueEnergy f := div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

theorem residueEnergy_lift {d q : ℕ} [NeZero d] [NeZero q]
    (hd : d ∣ q) (f : ZMod d → ℂ) :
    residueEnergy (residueLift (q := q) f) = residueEnergy f :=
  residue_quotient_mean hd (fun a => ‖f a‖ ^ 2)

theorem residueMean_mul_norm_sq {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    ‖residueMean (fun a => f a * g a)‖ ^ 2 ≤ residueEnergy f * residueEnergy g := by
  have hn := norm_sum_le (univ : Finset (ZMod q)) (fun a => f a * g a)
  simp only [norm_mul] at hn
  have hs := sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod q))
    (fun a => ‖f a‖) (fun a => ‖g a‖)
  have hsq : ‖∑ a, f a * g a‖ ^ 2 ≤
      (∑ a, ‖f a‖ ^ 2) * (∑ a, ‖g a‖ ^ 2) :=
    (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hs
  unfold residueMean residueEnergy
  rw [norm_div, Complex.norm_natCast, div_pow, div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right hsq (sq_nonneg (q : ℝ))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCauchy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted Cauchy inequality used to eliminate the first label -/

namespace JointDickman
open Finset

/-- The first label needs only the unit-disc bound; its multiplicativity
is used solely in the preceding divisor reindexing. -/
theorem weighted_complex_cauchy {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (g F : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∑ i ∈ s, (w i : ℂ) * g i * F i‖ ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * ‖F i‖ ^ 2 := by
  have hn : ‖∑ i ∈ s, (w i : ℂ) * g i * F i‖ ≤ ∑ i ∈ s, w i * ‖F i‖ := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro i hi
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    nlinarith [norm_nonneg (F i), mul_nonneg (hw i hi) (norm_nonneg (F i)), hg i hi]
  have hcs := sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := w) (g := fun i => w i * ‖F i‖^2) (r := fun i => w i * ‖F i‖)
    hw (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
    (fun i _ => by ring_nf; exact le_rfl)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs

/-- Factoring a common positive normalization from the finite inequality. -/
theorem normalized_weighted_complex_cauchy {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (g F : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) {N : ℝ} (hN : 0 ≤ N) :
    ‖(∑ i ∈ s, (w i : ℂ) * g i * F i) / (N : ℂ)‖ ^ 2 ≤
      ((∑ i ∈ s, w i) / N) * ((∑ i ∈ s, w i * ‖F i‖ ^ 2) / N) := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    div_pow, div_mul_div_comm, ← pow_two]
  exact div_le_div_of_nonneg_right (weighted_complex_cauchy s w g F hw hg) (sq_nonneg N)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationFirstForm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first divisor form and its quadratic energy -/

namespace JointDickman
open Finset

theorem amplification_first_form (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (g J : ℕ → ℂ) (N : ℕ)
    (hg : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ m : ℕ, g ((∏ p ∈ A, p)*m) = g m) :
    amplificationDivisorForm B L τ C (fun a c => u c * v a c)
      (fun n => star (g n) * J n) N / (N : ℂ) = firstDivisorForm B L τ C u v g J N := by
  unfold amplificationDivisorForm firstDivisorForm
  congr 1
  rw [sum_product, sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  unfold firstFormInner
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  dsimp only
  by_cases h : (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1
  · rw [ite_eq_left h, ite_eq_left h, hg A hA m]
    unfold firstFormWeight
    push_cast
    ring
  · simp only [ite_eq_right h, mul_zero]

theorem firstFormWeight_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (hu : ∀ c, 0 ≤ u c) (D : Finset ℕ) (m : ℕ) :
    0 ≤ firstFormWeight B L τ C u D m :=
  mul_nonneg (mul_nonneg (hu _) (regularCoefficientWeight_nonneg B L τ C _))
    (regularResidueWeight_nonneg B L τ C _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveFirstForm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the Cauchy volume to the actual multiplier range -/

namespace JointDickman
open Finset

theorem firstFormInner_eq_zero_of_inactive (B L : ℕ) (τ C : ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (T N : ℕ)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a) (D : Finset ℕ) (m : ℕ)
    (hm : ¬ T*(∏ p ∈ D, p)*m < N) : firstFormInner B L τ C v J N D m = 0 := by
  classical
  unfold firstFormInner
  apply sum_eq_zero
  intro A _
  dsimp only
  split_ifs with h
  · have hz : v (∏ p ∈ A, p) (∏ p ∈ D, p) = 0 := by
      by_contra hn
      have hle := Nat.mul_le_mul_right m (hv _ _ hn)
      exact hm (hle.trans_lt h.1)
    simp only [hz, mul_zero, Complex.ofReal_zero, zero_mul]
  · rfl

theorem activeFirstFormWeight_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (hu : ∀ c, 0 ≤ u c) (T N : ℕ) (D : Finset ℕ) (m : ℕ) :
    0 ≤ activeFirstFormWeight B L τ C u T N D m := by
  unfold activeFirstFormWeight
  split_ifs
  · exact firstFormWeight_nonneg B L τ C u hu D m
  · rfl

/-- The Cauchy volume only counts multipliers permitted by the smooth
coefficient window, giving the factor 1/(Tc) in its later mean estimate. -/
theorem firstDivisorForm_active_cauchy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (g J : ℕ → ℂ) (T N : ℕ)
    (hu : ∀ c, 0 ≤ u c) (hg : ∀ m, ‖g m‖ ≤ 1)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a) :
    ‖firstDivisorForm B L τ C u v g J N‖^2 ≤
      activeFirstFormVolume B L τ C u T N * firstFormEnergy B L τ C u v J N := by
  classical
  have hp (D : Finset ℕ) (m : ℕ) :
      (activeFirstFormWeight B L τ C u T N D m : ℂ) * star (g m) *
        firstFormInner B L τ C v J N D m =
      (firstFormWeight B L τ C u D m : ℂ) * star (g m) *
        firstFormInner B L τ C v J N D m := by
    unfold activeFirstFormWeight
    split_ifs with hm
    · rfl
    · rw [firstFormInner_eq_zero_of_inactive B L τ C v J T N hv D m hm]
      simp
  have he (D : Finset ℕ) (m : ℕ) :
      activeFirstFormWeight B L τ C u T N D m * ‖firstFormInner B L τ C v J N D m‖^2 =
      firstFormWeight B L τ C u D m * ‖firstFormInner B L τ C v J N D m‖^2 := by
    unfold activeFirstFormWeight
    split_ifs with hm
    · rfl
    · rw [firstFormInner_eq_zero_of_inactive B L τ C v J T N hv D m hm]
      simp
  have h := normalized_weighted_complex_cauchy (ι := Finset ℕ × ℕ)
    ((auxiliaryPrimes B).powerset ×ˢ range N)
    (fun i => activeFirstFormWeight B L τ C u T N i.1 i.2) (fun i => star (g i.2))
    (fun i => firstFormInner B L τ C v J N i.1 i.2)
    (fun i _ => activeFirstFormWeight_nonneg B L τ C u hu T N i.1 i.2)
    (fun i _ => by simpa only [norm_star] using hg i.2) (N := (N : ℝ)) (Nat.cast_nonneg N)
  simpa only [hp, he, firstDivisorForm, activeFirstFormVolume, firstFormEnergy,
    Complex.ofReal_natCast] using h

/-- The concrete bump has the required lower support condition. -/
theorem amplificationBump_ratio_lower (T a c : ℕ)
    (h : amplificationBump (((a : ℝ) / ((T : ℝ)*c))) ≠ 0) : T*c ≤ a := by
  have hs := (amplificationBump_support h).1
  by_cases hc : T*c = 0
  · omega
  have hc0 : (0 : ℝ) < (T : ℝ)*c := by exact_mod_cast (Nat.pos_of_ne_zero hc)
  have ha := (lt_div_iff₀ hc0).mp hs
  norm_num at ha
  exact_mod_cast ha.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact means of finite prime-divisor products -/

namespace JointDickman
open Finset

open Classical in
theorem residue_divisor_mean {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q) :
    (∑ a : ZMod q, if d ∣ a.val then (1 : ℝ) else 0) / (q : ℝ) = 1 / (d : ℝ) := by
  have h := residue_quotient_mean hd (fun a : ZMod d => if a = 0 then (1 : ℝ) else 0)
  simpa only [ZMod.natCast_eq_zero_iff, sum_ite_eq', mem_univ, ite_true, if_true] using h

open Classical in
/-- Uniform residues give the exact finite Euler-product mean. -/
theorem residue_divisor_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {q : ℕ} [NeZero q] (hdiv : (∏ p ∈ P, p) ∣ q) (b : ℕ → ℝ) :
    (∑ a : ZMod q, ∏ p ∈ P, if p ∣ a.val then 1+b p else 1) / (q : ℝ) =
      ∏ p ∈ P, (1+b p/(p : ℝ)) := by
  simp_rw [divisor_product_expansion P hP b]
  rw [sum_comm, sum_div]
  rw [prod_one_add]
  apply sum_congr rfl
  intro D hD
  have hDP := mem_powerset.mp hD
  have hd : (∏ p ∈ D, p) ∣ q := (prod_dvd_prod_of_subset _ _ id hDP).trans hdiv
  let : NeZero (∏ p ∈ D, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p (hDP hp)).ne_zero)⟩
  have he : (∑ a : ZMod q, if (∏ p ∈ D, p) ∣ a.val then ∏ p ∈ D, b p else 0) =
      (∏ p ∈ D, b p) * ∑ a : ZMod q, if (∏ p ∈ D, p) ∣ a.val then (1 : ℝ) else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [he, mul_div_assoc, residue_divisor_mean hd, prod_div_distrib, Nat.cast_prod]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationVolumeProducts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient harmonic mass cancels the residue-weight mean -/

namespace JointDickman
open Finset

theorem baseArithmeticResidueWeight_product (B n : ℕ) :
    baseArithmeticResidueWeight B n = auxiliaryRatio B ^ (1/2 : ℝ) *
      ∏ p ∈ auxiliaryPrimes B, if p ∣ n then (1/2 : ℝ) else 1 := by
  unfold baseArithmeticResidueWeight residueBaseWeight coefficientPrimeSet
  rw [← prod_const, prod_filter]

theorem baseArithmeticResidueWeight_mean (B : ℕ) :
    (∑ a : ZMod (auxiliarySquarePeriod B), baseArithmeticResidueWeight B a.val) /
      (auxiliarySquarePeriod B : ℝ) = baseArithmeticResidueMean B := by
  have hd : (∏ p ∈ auxiliaryPrimes B, p) ∣ auxiliarySquarePeriod B := by
    unfold auxiliarySquarePeriod
    exact dvd_pow_self _ (by norm_num : 2 ≠ 0)
  have h := residue_divisor_product_mean (auxiliaryPrimes B) (auxiliaryPrimes_prime B) hd
    (fun _ => (-1/2 : ℝ))
  simp only [show (1 : ℝ) + -1/2 = 1/2 by norm_num] at h
  simp_rw [baseArithmeticResidueWeight_product]
  rw [← mul_sum, mul_div_assoc, h]
  unfold baseArithmeticResidueMean primeNormalizer
  congr 1
  apply prod_congr rfl
  intro p _
  ring

theorem coefficient_harmonic_product (B : ℕ) :
    (∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p) / (∏ p ∈ D, (p : ℝ))) =
      coefficientScale B * ∏ p ∈ auxiliaryPrimes B, (1 + (1/2 : ℝ)/p) := by
  rw [prod_one_add, mul_sum]
  apply sum_congr rfl
  intro D hD
  rw [coefficientWeight_primeProduct (mem_powerset.mp hD)]
  simp only [residueBaseWeight, coefficientScale, prod_div_distrib, prod_const, one_div]
  ring

/-- This exact finite cancellation bounds the Cauchy volume without a
further interval asymptotic: the leftover Euler factors are at most one. -/
theorem coefficient_harmonic_mul_residueMean_le {B : ℕ} (hB : 1 < B) :
    (∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p) / (∏ p ∈ D, (p : ℝ))) *
      baseArithmeticResidueMean B ≤ B := by
  rw [coefficient_harmonic_product, baseArithmeticResidueMean]
  have he : (coefficientScale B * ∏ p ∈ auxiliaryPrimes B, (1+(1/2 : ℝ)/p)) *
      (auxiliaryRatio B^(1/2 : ℝ) * primeNormalizer (auxiliaryPrimes B) (1/2)) =
      (B : ℝ) * ∏ p ∈ auxiliaryPrimes B, (1 - ((1/2 : ℝ)/p)^2) := by
    rw [mul_mul_mul_comm, coefficientScale_mul_sqrt_ratio hB]
    unfold primeNormalizer
    rw [← prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro p _
    ring
  rw [he]
  apply mul_le_of_le_one_right (Nat.cast_nonneg B)
  apply Finset.prod_le_one
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hd : (1/2 : ℝ)/p ≤ 1 := (div_le_one hp0).mpr (by linarith)
    have hn : 0 ≤ (1/2 : ℝ)/p := by positivity
    nlinarith
  · intro p _
    exact sub_le_self _ (sq_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ScaledPeriodicMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic means on the multiplier interval -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem quotient_endpoint_ratio {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N/d+1 : ℕ) : ℝ)/(N : ℝ)) atTop (nhds (1/(d : ℝ))) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (tendsto_nat_floor_mul_div_atTop (show 0 ≤ 1/(d : ℝ) by positivity)).comp
    tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => ((N/d : ℕ) : ℝ)/(N : ℝ)) atTop (nhds (1/(d : ℝ))) := by
    simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_natCast, Nat.floor_natCast] using h
  have hh := he.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hh

theorem mean_scaled_prefix {f : ℕ → ℝ} {μ : ℝ}
    (h : Tendsto (fun N => (∑ n ∈ range N, f n)/(N : ℝ)) atTop (nhds μ))
    {d : ℕ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (∑ n ∈ range (N/d+1), f n)/(N : ℝ)) atTop (nhds (μ/(d : ℝ))) := by
  have he : Tendsto (fun N : ℕ => N/d+1) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_add_right (N/d) 1)
      (Nat.tendsto_div_const_atTop (ne_of_gt hd))
  have hm := (h.comp he).mul (quotient_endpoint_ratio hd)
  have hid (N : ℕ) : ((∑ n ∈ range (N/d+1), f n)/((N/d+1 : ℕ) : ℝ)) *
      (((N/d+1 : ℕ) : ℝ)/(N : ℝ)) = (∑ n ∈ range (N/d+1), f n)/(N : ℝ) := by
    have hn : ((N/d+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [Function.comp_def, hid, mul_one_div] using hm

theorem baseArithmeticResidueWeight_natCast (B n : ℕ) :
    baseArithmeticResidueWeight B (n : ZMod (auxiliarySquarePeriod B)).val =
      baseArithmeticResidueWeight B n := by
  unfold baseArithmeticResidueWeight
  have hp (p : ℕ) (hp : p ∈ auxiliaryPrimes B) : p ∣ auxiliarySquarePeriod B := by
    simpa only [prod_singleton] using
      (auxiliaryProduct_dvd_period (singleton_subset_iff.mpr hp))
  rw [ZMod.val_natCast]
  congr 1
  exact primeSite_modEq hp (Nat.mod_modEq n (auxiliarySquarePeriod B))

theorem baseArithmeticResidueWeight_mean_tendsto (B : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, baseArithmeticResidueWeight B n)/(N : ℝ))
      atTop (nhds (baseArithmeticResidueMean B)) := by
  have h := real_periodic_moment_tendsto
    (fun a : ZMod (auxiliarySquarePeriod B) => baseArithmeticResidueWeight B a.val) 1
  simpa only [pow_one, baseArithmeticResidueWeight_natCast, baseArithmeticResidueWeight_mean] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveVolumeMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A periodic majorant for the active Cauchy volume -/

namespace JointDickman
open Finset

theorem baseArithmeticResidueWeight_nonneg (B n : ℕ) : 0 ≤ baseArithmeticResidueWeight B n := by
  unfold baseArithmeticResidueWeight residueBaseWeight
  exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)

theorem arithmeticResidueWeight_le_base (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    arithmeticResidueWeight B L τ C n ≤ baseArithmeticResidueWeight B n := by
  unfold arithmeticResidueWeight regularResidueWeight baseArithmeticResidueWeight
  split_ifs
  · rfl
  · exact baseArithmeticResidueWeight_nonneg B n

theorem active_residue_prefix_le (B L : ℕ) (τ C : ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ m ∈ range N, if d*m < N then arithmeticResidueWeight B L τ C m else 0) ≤
      ∑ m ∈ range (N/d+1), baseArithmeticResidueWeight B m := by
  classical
  have hs : (range N).filter (fun m => d*m < N) ⊆ range (N/d+1) := by
    intro m hm
    have hmul : m*d ≤ N := by simpa only [mul_comm] using (mem_filter.mp hm).2.le
    have hdiv := (Nat.le_div_iff_mul_le hd).mpr hmul
    exact mem_range.mpr (by omega)
  rw [← sum_filter]
  calc
    _ ≤ ∑ m ∈ (range N).filter (fun m => d*m < N), baseArithmeticResidueWeight B m :=
      sum_le_sum (fun m _ => arithmeticResidueWeight_le_base B L τ C m)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => baseArithmeticResidueWeight_nonneg B m)

theorem activeFirstFormVolume_le_majorant (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    {T : ℕ} (hT : 0 < T) (N : ℕ) (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    activeFirstFormVolume B L τ C u T N ≤ activeVolumeMajorant B T N := by
  classical
  unfold activeFirstFormVolume activeVolumeMajorant
  rw [sum_product, sum_div]
  apply sum_le_sum
  intro D hD
  let c := ∏ p ∈ D, p
  have hcpos : 0 < c := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).pos)
  have hs := active_residue_prefix_le B L τ C (Nat.mul_pos hT hcpos) N
  have hc : u c * regularCoefficientWeight B L τ C c ≤ coefficientWeight B c :=
    (mul_le_of_le_one_left (regularCoefficientWeight_nonneg B L τ C c) (hu c).2).trans
      (regularCoefficientWeight_le B L τ C c)
  have he : (∑ m ∈ range N, activeFirstFormWeight B L τ C u T N D m) =
      (u c * regularCoefficientWeight B L τ C c) *
        ∑ m ∈ range N, if T*c*m < N then arithmeticResidueWeight B L τ C m else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    unfold activeFirstFormWeight firstFormWeight
    dsimp only [c]
    split_ifs <;> simp only [mul_zero]
  rw [he, mul_div_assoc]
  apply mul_le_mul hc (div_le_div_of_nonneg_right hs (Nat.cast_nonneg N))
  · apply div_nonneg _ (Nat.cast_nonneg N)
    apply sum_nonneg
    intro m _
    split_ifs
    · exact regularResidueWeight_nonneg B L τ C _
    · rfl
  · exact coefficientWeight_nonneg B c

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ActiveVolumeBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The active Cauchy volume is eventually at most 2 B / T -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem activeVolumeMajorant_limit (B : ℕ) {T : ℕ} (hT : 0 < T) :
    Tendsto (activeVolumeMajorant B T) atTop (nhds
      (((∑ D ∈ (auxiliaryPrimes B).powerset,
        coefficientWeight B (∏ p ∈ D, p)/(∏ p ∈ D, (p : ℝ))) * baseArithmeticResidueMean B)/(T : ℝ))) := by
  have hlim : Tendsto (activeVolumeMajorant B T) atTop (nhds
      (∑ D ∈ (auxiliaryPrimes B).powerset, coefficientWeight B (∏ p ∈ D, p) *
        (baseArithmeticResidueMean B / ((T*(∏ p ∈ D, p) : ℕ) : ℝ)))) := by
    apply tendsto_finsetSum
    intro D hD
    have hd : 0 < ∏ p ∈ D, p := prod_pos (fun p hp =>
      (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).pos)
    exact (mean_scaled_prefix (baseArithmeticResidueWeight_mean_tendsto B) (Nat.mul_pos hT hd)).const_mul _
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  rw [sum_mul, sum_div]
  apply sum_congr rfl
  intro D hD
  have hd : (∏ p ∈ D, (p : ℝ)) ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).ne_zero)
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
  rw [Nat.cast_mul, Nat.cast_prod]
  field_simp

theorem activeFirstFormVolume_bound {B : ℕ} (hB : 1 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) {T : ℕ} (hT : 0 < T) (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᶠ N : ℕ in atTop, activeFirstFormVolume B L τ C u T N ≤ 2*(B : ℝ)/(T : ℝ) := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hb := div_le_div_of_nonneg_right (coefficient_harmonic_mul_residueMean_le hB) hTp.le
  have hstrict : ((∑ D ∈ (auxiliaryPrimes B).powerset,
      coefficientWeight B (∏ p ∈ D, p)/(∏ p ∈ D, (p : ℝ))) * baseArithmeticResidueMean B)/(T : ℝ) <
      2*(B : ℝ)/(T : ℝ) := by
    apply lt_of_le_of_lt hb
    rw [mul_div_assoc]
    have := div_pos hBp hTp
    linarith
  filter_upwards [(activeVolumeMajorant_limit B hT).eventually (eventually_le_nhds hstrict)] with N hN
  exact (activeFirstFormVolume_le_majorant B L τ C u hT N hu).trans hN

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
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueProfiles
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible finite residue profiles

A profile records the conditional averages on every finite residue space.
Compatibility is tested against all functions on a coarser residue space.
The energy identity below is the finite conditional-expectation identity.
-/

namespace JointDickman
open Finset

theorem residueMean_re {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (residueMean f).re = (∑ a, (f a).re) / (q : ℝ) := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  simp [residueMean, Complex.div_re, Complex.normSq]
  field_simp

theorem residueMean_self_conj_re {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (residueMean (fun a => f a * star (f a))).re = residueEnergy f := by
  rw [residueMean_re]
  unfold residueEnergy
  congr 1
  apply sum_congr rfl
  intro a _
  simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re]

theorem residueEnergy_sub {q : ℕ} [NeZero q] (f g : ZMod q → ℂ) :
    residueEnergy (fun a => f a - g a) = residueEnergy f + residueEnergy g -
      2 * (residueMean (fun a => f a * star (g a))).re := by
  have he (z w : ℂ) : ‖z-w‖^2 = ‖z‖^2 + ‖w‖^2 - 2*(z * star w).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  simp only [residueEnergy, residueMean_re, he, sum_sub_distrib, sum_add_distrib]
  rw [← mul_sum]
  ring

namespace ResidueProfile

theorem refinement_energy (W : ResidueProfile) {d q : ℕ+} (hd : (d : ℕ) ∣ (q : ℕ)) :
    residueEnergy (fun a => W.value q a - residueLift (W.value d) a) =
      residueEnergy (W.value q) - residueEnergy (W.value d) := by
  rw [residueEnergy_sub, residueEnergy_lift hd]
  have hc := W.compatible d q hd (fun a => star (W.value d a))
  have he : residueMean (fun a : ZMod (q : ℕ) =>
      W.value q a * star (residueLift (W.value d) a)) =
      residueMean (fun a => W.value d a * star (W.value d a)) := hc
  rw [he, residueMean_self_conj_re]
  ring

/-- One finite residue coordinate approximates every refinement in mean square. -/
theorem exists_approximation (W : ResidueProfile) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ+, ∀ q : ℕ+, (d : ℕ) ∣ (q : ℕ) →
      residueEnergy (fun a => W.value q a - residueLift (W.value d) a) < ε := by
  have hn : (Set.range fun q => residueEnergy (W.value q)).Nonempty :=
    Set.range_nonempty _
  obtain ⟨x, hx, hclose⟩ := exists_lt_of_lt_csSup hn
    (sub_lt_self (sSup (Set.range fun q => residueEnergy (W.value q))) hε)
  obtain ⟨d, rfl⟩ := hx
  refine ⟨d, fun q hd => ?_⟩
  rw [W.refinement_energy hd]
  have hq := le_csSup W.energy_bounded (Set.mem_range_self q)
  linarith

end ResidueProfile
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProfilePreservation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preservation of every bounded residue profile by moving-prime weights -/

namespace JointDickman
open Finset Filter
open scoped Topology

namespace ResidueProfile

theorem mean_eq (W : ResidueProfile) (q : ℕ+) : residueMean (W.value q) = W.mean := by
  have h := W.compatible 1 q (one_dvd _) (fun _ => 1)
  simpa only [residueLift, mul_one, mean] using h

theorem correlation_error (W : ResidueProfile) (d q : ℕ+) (f : ZMod (q : ℕ) → ℂ)
    (hcop : (d : ℕ).Coprime q) :
    W.correlation q f - W.mean * residueMean f =
      residueMean (fun a : ZMod ((d*q : ℕ+) : ℕ) =>
        (W.value (d*q) a - residueLift (W.value d) a) * residueLift f a) := by
  have hc := W.compatible q (d*q) (dvd_mul_left _ _) f
  have hi := residueMean_crt hcop (W.value d) f
  have he (a : ZMod ((d : ℕ) * (q : ℕ))) :
      (ZMod.chineseRemainder hcop) a = ((a.val : ZMod (d : ℕ)), (a.val : ZMod (q : ℕ))) := by
    calc
      _ = (ZMod.chineseRemainder hcop) (a.val : ZMod ((d : ℕ) * (q : ℕ))) :=
        congrArg _ (ZMod.natCast_zmod_val a).symm
      _ = _ := by simp only [map_natCast]; rfl
  simp only [he] at hi
  rw [W.mean_eq d] at hi
  change residueMean (fun a => W.value q a * f a) - W.mean * residueMean f = _
  rw [← hc, ← hi]
  simp only [residueMean, residueLift, sub_mul, sum_sub_distrib, sub_div, PNat.mul_coe]
  rfl

theorem preservation (W : ResidueProfile) (Q : ℕ → ℕ+)
    (f : (B : ℕ) → ZMod (Q B : ℕ) → ℂ)
    (hcop : ∀ d : ℕ+, ∀ᶠ B : ℕ in atTop, (d : ℕ).Coprime (Q B))
    (hmoment : ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, residueEnergy (f B) ≤ K) :
    Tendsto (fun B => W.correlation (Q B) (f B) - W.mean * residueMean (f B))
      atTop (nhds 0) := by
  obtain ⟨K,hK,hb⟩ := hmoment
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨d,hd⟩ := W.exists_approximation (div_pos (sq_pos_of_pos hε) hK)
  filter_upwards [hcop d, hb] with B hcopB hB
  rw [dist_zero_right, W.correlation_error d (Q B) (f B) hcopB]
  have hcs := residueMean_mul_norm_sq
    (fun a : ZMod ((d*Q B : ℕ+) : ℕ) =>
      W.value (d*Q B) a - residueLift (W.value d) a)
    (residueLift (q := ((d*Q B : ℕ+) : ℕ)) (f B))
  have hel : residueEnergy (residueLift (q := ((d*Q B : ℕ+) : ℕ)) (f B)) =
      residueEnergy (f B) := residueEnergy_lift (d := (Q B : ℕ))
        (q := ((d*Q B : ℕ+) : ℕ)) (dvd_mul_left _ _) (f B)
  rw [hel] at hcs
  have he := hd (d*Q B) (dvd_mul_right _ _)
  have hm := mul_le_mul_of_nonneg_left hB
    (residueEnergy_nonneg (fun a => W.value (d*Q B) a - residueLift (W.value d) a))
  have hlt := mul_lt_mul_of_pos_right he hK
  rw [div_mul_cancel₀ _ (ne_of_gt hK)] at hlt
  nlinarith [norm_nonneg (residueMean (fun a : ZMod ((d*Q B : ℕ+) : ℕ) =>
    (W.value (d*Q B) a - residueLift (W.value d) a) * residueLift (f B) a))]

end ResidueProfile
end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticProfilePreservation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Profile preservation for the manuscript's actual smooth divisor weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem smoothResidueAmplification_energy (B L : ℕ) (τ C : ℝ) (T : ℕ) :
    residueEnergy (smoothResidueAmplification B L τ C T) =
      arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 2 := by
  unfold residueEnergy smoothResidueAmplification arithmeticAmplificationMoment
    residueAmplification amplificationPeriod
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rfl

theorem smoothResidueAmplification_mean (B L : ℕ) (τ C : ℝ) (T : ℕ) :
    residueMean (smoothResidueAmplification B L τ C T) =
      (arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 : ℂ) :=
  residueAmplification_mean B L τ C (amplificationSmoothWeight B T)

/-- The precise preservation statement, using the actual arithmetic weight.
Only the previously cited sieve and Mertens inputs enter its moment bound. -/
theorem smooth_arithmetic_profile_preservation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (W : ResidueProfile) (L : ℕ) (τ C : ℝ) (T : ℕ → ℕ)
    (hT : ∀ᶠ B : ℕ in atTop, 0 < T B ∧ (T B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B)) :
    Tendsto (fun B => W.correlation (amplificationPeriod B)
      (smoothResidueAmplification B L τ C (T B)) - W.mean *
        (arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B (T B)) 1 : ℂ))
      atTop (nhds 0) := by
  have hcop (d : ℕ+) : ∀ᶠ B : ℕ in atTop,
      (d : ℕ).Coprime (amplificationPeriod B) := by
    filter_upwards [auxiliarySquarePeriod_eventually_coprime d d.pos] with B hB
    exact hB.symm
  obtain ⟨K,hK,hb⟩ := smooth_arithmetic_second_bound hFord hM L τ C
  have hm : ∀ᶠ B : ℕ in atTop,
      residueEnergy (smoothResidueAmplification B L τ C (T B)) ≤ K := by
    filter_upwards [hb,hT] with B hB hTB
    rw [smoothResidueAmplification_energy]
    exact hB (T B) hTB.1 hTB.2
  simpa only [smoothResidueAmplification_mean] using
    W.preservation amplificationPeriod (fun B => smoothResidueAmplification B L τ C (T B))
      hcop ⟨K,hK,hm⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_EmpiricalResidueProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite residue coefficients of a bounded arithmetic correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem empiricalResidueCoefficient_test (H : ℕ → ℕ → ℂ) (N : ℕ)
    (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    residueMean (fun a => empiricalResidueCoefficient H N q a * f a) =
      empiricalResidueTest H N f := by
  classical
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
  have hs : (∑ a : ZMod (q : ℕ),
      (∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0) * f a) =
      ∑ n ∈ range N, H N n * f (n : ZMod (q : ℕ)) := by
    simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    simp only [ite_mul, zero_mul]
    simp
  unfold residueMean empiricalResidueCoefficient empiricalResidueTest
  have hf (a : ZMod (q : ℕ)) :
      (((q : ℕ) : ℂ) * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then H N n else 0) / (N : ℂ))) * f a =
      (((q : ℕ) : ℂ) / N) * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then H N n else 0) * f a) := by ring
  simp_rw [hf]
  rw [← mul_sum, hs]
  field_simp

theorem empiricalResidueCoefficient_norm_le (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (N : ℕ) (q : ℕ+)
    (a : ZMod (q : ℕ)) : ‖empiricalResidueCoefficient H N q a‖ ≤ (q : ℕ) * C := by
  classical
  have hs : ‖∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤ (N : ℝ)*C := by
    have h := norm_sum_le_of_le (range N) (fun n _ => show
        ‖if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤ C from by
      split_ifs
      · exact hH N n
      · simpa using hC)
    simpa using h
  by_cases hN : N = 0
  · simp [empiricalResidueCoefficient, hN, mul_nonneg (Nat.cast_nonneg _) hC]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  unfold empiricalResidueCoefficient
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hNpos).mpr (by simpa only [mul_comm] using hs)) (Nat.cast_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ResidueProfileLimits
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded arithmetic arrays give compatible bounded residue profiles -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- A sharper coefficient bound retains the density of the residue class. -/
theorem empiricalResidueCoefficient_density_bound (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hH : ∀ N n, ‖H N n‖ ≤ C) (N : ℕ) (q : ℕ+) (a : ZMod (q : ℕ)) :
    ‖empiricalResidueCoefficient H N q a‖ ≤
      (q : ℕ) * C * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (N : ℝ)) := by
  classical
  have hs := norm_sum_le_of_le (range N) (fun n _ => show
      ‖if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤
        C * (if (n : ZMod (q : ℕ)) = a then 1 else 0) from by
    split_ifs <;> simp_all)
  rw [← mul_sum] at hs
  unfold empiricalResidueCoefficient
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  calc
    _ ≤ (q : ℕ) * ((C * ∑ n ∈ range N,
      if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (N : ℝ)) := by
      gcongr
    _ = _ := by ring

theorem residueCoefficient_limit_bound (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hH : ∀ N n, ‖H N n‖ ≤ C) {s : ℕ → ℕ} (hs : StrictMono s)
    {q : ℕ+} {a : ZMod (q : ℕ)} {z : ℂ}
    (hz : Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds z)) :
    ‖z‖ ≤ C := by
  classical
  have hcnt := real_periodic_moment_tendsto
    (fun b : ZMod (q : ℕ) => if b = a then (1 : ℝ) else 0) 1
  simp only [pow_one, sum_ite_eq', mem_univ, ite_true, if_true] at hcnt
  have hlim : Tendsto (fun N => ((q : ℕ) : ℝ)*C *
      ((∑ n ∈ range (s N), if (n : ZMod (q : ℕ)) = a then (1 : ℝ) else 0) / (s N : ℝ)))
      atTop (nhds (((q : ℕ) : ℝ)*C * (1 / ((q : ℕ) : ℝ)))) :=
    tendsto_const_nhds.mul (hcnt.comp hs.tendsto_atTop)
  have hle := le_of_tendsto_of_tendsto' hz.norm hlim
    (fun N => empiricalResidueCoefficient_density_bound H hH (s N) q a)
  have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  convert hle using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)

theorem residueCoefficient_test_limit (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ)
    (V : (q : ℕ+) → ZMod (q : ℕ) → ℂ)
    (hV : ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds (V q a)))
    (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    Tendsto (fun N => empiricalResidueTest H (s N) f) atTop
      (nhds (residueMean (fun a => V q a * f a))) := by
  have h := (tendsto_finsetSum univ (fun a _ => (hV q a).mul_const (f a))).div_const
    (((q : ℕ) : ℂ))
  change Tendsto (fun N => residueMean (fun a => empiricalResidueCoefficient H (s N) q a * f a))
    atTop (nhds (residueMean (fun a => V q a * f a))) at h
  simpa only [empiricalResidueCoefficient_test] using h

theorem residueLift_natCast {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (f : ZMod d → ℂ) (n : ℕ) : residueLift (q := q) f (n : ZMod q) = f (n : ZMod d) := by
  unfold residueLift
  congr 1
  rw [ZMod.val_natCast, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd n hd]

theorem residueCoefficient_limit_compatible (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ)
    (V : (q : ℕ+) → ZMod (q : ℕ) → ℂ)
    (hV : ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds (V q a)))
    (d q : ℕ+) (hd : (d : ℕ) ∣ (q : ℕ)) (f : ZMod (d : ℕ) → ℂ) :
    residueMean (fun a => V q a * residueLift f a) = residueMean (fun a => V d a * f a) := by
  have hq := residueCoefficient_test_limit H s V hV q (residueLift f)
  have hd' := residueCoefficient_test_limit H s V hV d f
  have he (N : ℕ) : empiricalResidueTest H (s N) (residueLift (q := (q : ℕ)) f) =
      empiricalResidueTest H (s N) f := by
    unfold empiricalResidueTest
    simp only [residueLift_natCast hd]
  simp only [he] at hq
  exact tendsto_nhds_unique hq hd'

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplifiedProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero arithmetic correlations survive smooth amplification -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_norm_lower {β : ℂ} (hβ : β ≠ 0) {d : ℝ} (hd : 0 < d)
    (u : ℕ → ℂ) (m : ℕ → ℝ)
    (hm : ∀ᶠ B : ℕ in atTop, d ≤ m B)
    (he : Tendsto (fun B => u B - β * (m B : ℂ)) atTop (nhds 0)) :
    ∀ᶠ B : ℕ in atTop, d/2 * ‖β‖ ≤ ‖u B‖ := by
  have hpos : 0 < d/2 * ‖β‖ := mul_pos (half_pos hd) (norm_pos_iff.mpr hβ)
  have he' := (Metric.tendsto_nhds.mp he) (d/2 * ‖β‖) hpos
  filter_upwards [hm,he'] with B hB heB
  rw [dist_zero_right] at heB
  have hm0 : 0 ≤ m B := le_trans hd.le hB
  have ht := norm_sub_le (u B) (u B - β * (m B : ℂ))
  have hid : u B - (u B - β * (m B : ℂ)) = β * (m B : ℂ) := by ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0] at ht
  nlinarith [mul_le_mul_of_nonneg_right hB (norm_nonneg β)]

/-- The positive lower constant is independent of the later fixed regularity
cutoff. The outer limit is still conditional only on the cited analytic inputs. -/
theorem smooth_amplified_profile_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (W : ResidueProfile) (hW : W.mean ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ T : ℕ → ℕ,
        (∀ᶠ B : ℕ in atTop, 0 < T B ∧ (T B : ℝ) ≤ Real.exp ((1/10 : ℝ)*B)) →
        ∀ᶠ B : ℕ in atTop, d * ‖W.mean‖ ≤
          ‖W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C (T B))‖ := by
  obtain ⟨d,hd,hl⟩ := smooth_arithmetic_first_lower hFord hSD hM hMP
  refine ⟨d/2,half_pos hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC T hT
  apply amplification_norm_lower hW hd
    (fun B => W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C (T B)))
    (fun B => arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B (T B)) 1)
  · filter_upwards [hb,hT] with B hB hTB
    exact hB C (T B) hC hTB.1 hTB.2
  · exact smooth_arithmetic_profile_preservation hFord hM W L τ C T hT

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabels
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Multiplicative bin labels and real interpolation

The count in a finite prime bin includes multiplicity. Its additivity gives
complete multiplicativity of the uncentered labels. Centering is performed
only after evaluating a label; no multiplicativity is claimed for it.

A tensor product of finite Vandermonde inverses expresses every function of
bounded count vectors as a fixed finite linear combination of real,
nonnegative, 1-bounded multiplicative interpolants.
-/

namespace JointDickman

open Finset

theorem binCount_mul (E : Finset ℕ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    binCount E (m * n) = binCount E m + binCount E n := by
  simp [binCount, Nat.factorization_mul hm hn, Finset.sum_add_distrib]

theorem binCount_eq_zero_of_no_factor (E : Finset ℕ) (n : ℕ)
    (h : ∀ p ∈ E, ¬p ∣ n) : binCount E n = 0 := by
  exact Finset.sum_eq_zero fun p hp => Nat.factorization_eq_zero_of_not_dvd (h p hp)

section Labels

variable {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]

theorem binLabel_apply {n : ℕ} (hn : n ≠ 0) (E : ι → Finset ℕ) (z : ι → R) :
    binLabel E z n = ∏ i, z i ^ binCount (E i) n := by simp [binLabel, hn]

/-- Complete multiplicativity, without a coprimality requirement. -/
theorem binLabel_mul (E : ι → Finset ℕ) (z : ι → R) (m n : ℕ) :
    binLabel E z (m * n) = binLabel E z m * binLabel E z n := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  simp only [binLabel_apply (mul_ne_zero hm hn), binLabel_apply hm,
    binLabel_apply hn, binCount_mul _ hm hn, pow_add, Finset.prod_mul_distrib]

theorem binLabel_eq_one_of_no_factor (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) :
    binLabel E z u = 1 := by
  simp only [binLabel_apply hu]
  apply Finset.prod_eq_one
  intro i _
  rw [binCount_eq_zero_of_no_factor _ _ (h i), pow_zero]

theorem binLabel_mul_invariant (E : ι → Finset ℕ) (z : ι → R)
    {u : ℕ} (hu : u ≠ 0) (h : ∀ i p, p ∈ E i → ¬p ∣ u) (n : ℕ) :
    binLabel E z (u * n) = binLabel E z n := by
  rw [binLabel_mul, binLabel_eq_one_of_no_factor E z hu h, one_mul]

end Labels

section Bounds

variable {ι : Type*} [Fintype ι] (E : ι → Finset ℕ)

theorem norm_binLabel_eq_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {n : ℕ} (hn : n ≠ 0) : ‖binLabel E z n‖ = 1 := by
  simp [binLabel_apply hn, norm_prod, norm_pow, hz]

theorem norm_binLabel_le_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (n : ℕ) :
    ‖binLabel E z n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  exact (norm_binLabel_eq_one E z hz hn).le

end Bounds

/-- A fixed nonzero integer eventually has no factor in any of the large-prime
bins. The first bin index is at least one, as in the manuscript. -/
theorem primeBin_eventually_no_factor {ι : Type*} (J : ℕ) (hJ : 0 < J)
    (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i p, p ∈ primeBin x J (k i) → ¬p ∣ u := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hlarge := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (Filter.eventually_ge_atTop (u : ℝ))
  filter_upwards [hlarge, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxone
  intro i p hp hpdiv
  have hplower : x ^ ((k i : ℝ) / J) < (p : ℝ) :=
    Nat.lt_of_floor_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
  have hexp : (1 : ℝ) / J ≤ (k i : ℝ) / J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hk i) hJreal.le
  have hpower := Real.rpow_le_rpow_of_exponent_le hxone hexp
  have hpupper : (p : ℝ) ≤ u := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hu) hpdiv
  linarith

/-- The exact eventual multiplier invariance used for uncentered labels. -/
theorem binLabel_eventually_mul_invariant {ι R : Type*} [Fintype ι] [CommMonoidWithZero R]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → R) {u : ℕ} (hu : u ≠ 0) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ n : ℕ,
      binLabel (fun i => primeBin x J (k i)) z (u * n) =
        binLabel (fun i => primeBin x J (k i)) z n := by
  filter_upwards [primeBin_eventually_no_factor J hJ k hk hu] with x hx n
  exact binLabel_mul_invariant _ z hu hx n


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinLabelAmplification
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first form for actual large-prime bin labels -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem binLabel_auxiliary_multipliers {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (B : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ m : ℕ,
      binLabel (fun i => primeBin x J (k i)) z ((∏ p ∈ A, p)*m) =
        binLabel (fun i => primeBin x J (k i)) z m := by
  apply (eventually_all_finset (auxiliaryPrimes B).powerset).mpr
  intro A hA
  have ha : 0 < ∏ p ∈ A, p := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hA hp)).pos)
  exact binLabel_eventually_mul_invariant J hJ k hk z (ne_of_gt ha)

/-- The exact normalized first-form identity holds at all sufficiently
large integer scales; no multiplicativity of the centered second factor
is used. -/
theorem binLabel_amplification_first_form {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i) (z : ι → ℂ)
    (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (H : ℕ → ℕ → ℂ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (star (binLabel (fun i => primeBin (N : ℝ) J (k i)) z n) * H N n) *
        (arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n : ℂ)) / (N : ℂ) =
      (1 / (B : ℂ)) * firstDivisorForm B L τ C u v
        (binLabel (fun i => primeBin (N : ℝ) J (k i)) z) (H N) N := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (binLabel_auxiliary_multipliers J hJ k hk z B)] with N hN
  rw [arithmeticAmplification_reindex]
  have h := amplification_first_form B L τ C u v
    (binLabel (fun i => primeBin (N : ℝ) J (k i)) z) (H N) N hN
  rw [mul_div_assoc, h]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsequenceAmplifiedProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Amplification profiles along a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Countable residue compactness can be taken inside any given sequence. -/
theorem empiricalResidueCoefficient_subsequence_along (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (r : ℕ → ℕ) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ V : (q : ℕ+) → ZMod (q : ℕ) → ℂ,
      ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (r (s N)) q a)
        atTop (nhds (V q a)) := by
  let K : Set ((q : ℕ+) → ZMod (q : ℕ) → ℂ) :=
    {V | ∀ (q : ℕ+) (a : ZMod (q : ℕ)), V q a ∈ Metric.closedBall 0 ((q : ℕ)*C)}
  have hK : IsCompact K := isCompact_pi_infinite fun (q : ℕ+) =>
    isCompact_pi_infinite fun (_ : ZMod (q : ℕ)) => isCompact_closedBall 0 ((q : ℕ)*C)
  have hx (N : ℕ) : empiricalResidueCoefficient H (r N) ∈ K := by
    intro q a
    rw [Metric.mem_closedBall,dist_zero_right]
    exact empiricalResidueCoefficient_norm_le H hC hH (r N) q a
  obtain ⟨V,_,s,hs,hlim⟩ := hK.tendsto_subseq hx
  exact ⟨s,hs,V,fun q a => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim q)) a⟩

/-- The profile is constructed on a further subsequence of the originally
chosen scales. The correlation limit and every amplification test survive. -/
theorem exists_arithmetic_amplification_profile_along (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (r : ℕ → ℕ) (hr : StrictMono r)
    {β : ℂ} (hmean : Tendsto (fun N => (∑ n ∈ range (r N), H (r N) n)/(r N : ℂ))
      atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ W : ResidueProfile, W.mean = β ∧
      ∀ (B L : ℕ) (τ C' : ℝ) (T : ℕ),
        Tendsto (fun N => (∑ n ∈ range (r (s N)), H (r (s N)) n *
          (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ)) /
            (r (s N) : ℂ)) atTop
          (nhds (W.correlation (amplificationPeriod B) (smoothResidueAmplification B L τ C' T))) := by
  obtain ⟨s,hs,V,hV⟩ := empiricalResidueCoefficient_subsequence_along H hC hH r
  let t : ℕ → ℕ := r ∘ s
  have ht : StrictMono t := hr.comp hs
  have hbound (q : ℕ+) (a : ZMod (q : ℕ)) : ‖V q a‖ ≤ C :=
    residueCoefficient_limit_bound H hH ht (hV q a)
  have henergy (q : ℕ+) : residueEnergy (V q) ≤ C^2 := by
    unfold residueEnergy
    have hq : (0 : ℝ) < (q : ℕ) := by exact_mod_cast q.pos
    apply (div_le_iff₀ hq).mpr
    calc
      _ ≤ ∑ _a : ZMod (q : ℕ), C^2 := sum_le_sum fun a _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hbound q a) 2
      _ = _ := by simp [mul_comm]
  let W : ResidueProfile := {
    value := V
    compatible := residueCoefficient_limit_compatible H t V hV
    energy_bounded := ⟨C^2, by rintro _ ⟨q,rfl⟩; exact henergy q⟩ }
  have hW (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) := residueCoefficient_test_limit H t V hV q f
  have hm := hW 1 (fun _ => 1)
  simp only [empiricalResidueTest,mul_one] at hm
  have hβ : W.mean = β := tendsto_nhds_unique hm (hmean.comp hs.tendsto_atTop)
  refine ⟨s,hs,W,hβ,?_⟩
  intro B L τ C' T
  have h := hW (amplificationPeriod B) (smoothResidueAmplification B L τ C' T)
  have he (n : ℕ) : smoothResidueAmplification B L τ C' T (n : ZMod (amplificationPeriod B : ℕ)) =
      (arithmeticSubsetAmplification B L τ C' (amplificationSmoothWeight B T) n : ℂ) := by
    exact congrArg (fun x : ℝ => (x : ℂ))
      (residueAmplification_natCast B L n τ C' (amplificationSmoothWeight B T))
  simpa only [empiricalResidueTest,he,ResidueProfile.correlation,t,Function.comp_def] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PositiveFirstFormEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive quadratic energy from a surviving mixed correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormEnergy_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (hu : ∀ c, 0 ≤ u c) :
    0 ≤ firstFormEnergy B L τ C u v J N := by
  apply div_nonneg _ (Nat.cast_nonneg N)
  exact sum_nonneg (fun i _ => mul_nonneg (firstFormWeight_nonneg B L τ C u hu i.1 i.2)
    (sq_nonneg _))

/-- The numerical Cauchy estimate with the normalization used for the graph. -/
theorem normalized_energy_lower {B T δ E V r : ℝ} (hB : 0 < B) (hT : 0 < T)
    (hδ : 0 ≤ δ) (hE : 0 ≤ E) (hr : B*δ ≤ r) (hr0 : 0 ≤ r)
    (hC : r^2 ≤ V*E) (hV : V ≤ 2*B/T) : δ^2/2 ≤ E/(B*T) := by
  have hs : (B*δ)^2 ≤ r^2 := (sq_le_sq₀ (mul_nonneg hB.le hδ) hr0).mpr hr
  have he := hs.trans (hC.trans (mul_le_mul_of_nonneg_right hV hE))
  have het := mul_le_mul_of_nonneg_right he hT.le
  have hid : (2*B/T*E)*T = B*(2*E) := by field_simp
  rw [hid] at het
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (mul_pos hB hT)).mpr
  apply (mul_le_mul_iff_right₀ hB).mp
  nlinarith only [het]

/-- No bound for the first label is lost in the active Cauchy step. -/
theorem firstFormEnergy_lower {B T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (g J : ℕ → ℂ) (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ c, 0 ≤ u c) (hg : ∀ m, ‖g m‖ ≤ 1)
    (hv : ∀ a c, v a c ≠ 0 → T*c ≤ a)
    (hfirst : (B : ℝ)*δ ≤ ‖firstDivisorForm B L τ C u v g J N‖)
    (hvol : activeFirstFormVolume B L τ C u T N ≤ 2*(B : ℝ)/(T : ℝ)) :
    δ^2/2 ≤ firstFormEnergy B L τ C u v J N / ((B : ℝ)*T) := by
  exact normalized_energy_lower (by exact_mod_cast hB) (by exact_mod_cast hT) hδ
    (firstFormEnergy_nonneg B L τ C u v J N hu) hfirst (norm_nonneg _)
    (firstDivisorForm_active_cauchy B L τ C u v g J T N hu hg hv) hvol

/-- A nonzero limiting correlation gives an eventual lower bound with room
for the later Cauchy estimate. -/
theorem norm_eventually_lower {f : ℕ → ℂ} {w : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hw : 2*δ ≤ ‖w‖) (hf : Tendsto f atTop (nhds w)) :
    ∀ᶠ n : ℕ in atTop, δ ≤ ‖f n‖ := by
  exact hf.norm.eventually (eventually_ge_nhds (by linarith))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BinLabelPositiveEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive energy forced by a nonzero mixed bin-label correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem binLabel_energy_of_amplified_limit {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (s : ℕ → ℕ) (hs : StrictMono s)
    {B T : ℕ} (hB : 1 < B) (hT : 0 < T) (L : ℕ) (τ C : ℝ)
    {δ : ℝ} (hδ : 0 < δ) {w : ℂ} (hw : 2*δ ≤ ‖w‖)
    (hl : Tendsto (fun N => (∑ n ∈ range (s N),
      (star (movingBinLabel J k z (s N) n) * H (s N) n) *
        (arithmeticSubsetAmplification B L τ C (amplificationSmoothWeight B T) n : ℂ)) /
        (s N : ℂ)) atTop (nhds w)) :
    ∀ᶠ N : ℕ in atTop, δ^2/2 ≤
      firstFormEnergy B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight T) (H (s N)) (s N) / ((B : ℝ)*T) := by
  have hv := activeFirstFormVolume_bound hB L τ C (amplificationOuterWeight B) hT
    (fun c => amplificationBump_bounds _)
  have hf := binLabel_amplification_first_form J hJ k hk z B L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight T) H
  filter_upwards [norm_eventually_lower hδ hw hl, hs.tendsto_atTop.eventually hv,
    hs.tendsto_atTop.eventually hf] with N hlow hvol hform
  apply firstFormEnergy_lower (Nat.zero_lt_of_lt hB) hT L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight T)
    (movingBinLabel J k z (s N)) (H (s N)) (s N) hδ.le
    (fun c => (amplificationBump_bounds _).1)
    (fun m => norm_binLabel_le_one _ z hz m)
    (fun a c h => amplificationBump_ratio_lower T a c h) _ hvol
  change δ ≤ ‖(∑ n ∈ range (s N),
    (star (binLabel (fun i => primeBin (s N : ℝ) J (k i)) z n) * H (s N) n) *
      (arithmeticSubsetAmplification B L τ C
        (fun a c => amplificationOuterWeight B c * amplificationInnerWeight T a c) n : ℂ)) /
        (s N : ℂ)‖ at hlow
  rw [hform, norm_mul, norm_div, norm_one, Complex.norm_natCast,
    one_div_mul_eq_div] at hlow
  have hBr : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hgfun : movingBinLabel J k z (s N) =
      (binLabel (fun i => primeBin (s N : ℝ) J (k i)) z : ℕ → ℂ) := by
    funext n
    rfl
  rw [hgfun]
  simpa only [mul_comm] using (le_div_iff₀ hBr).mp hlow

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SubsequencePositiveEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive amplification energy inside a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_energy_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (H : ℕ → ℕ → ℂ) (hH : ∀ N n, ‖H N n‖ ≤ 2)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J k z (r N) n) * H (r N) n)/(r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
        ∀ C : ℝ, C₀ ≤ C → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
            (amplificationInnerWeight (amplificationMultiplier B)) (H (r (s N))) (r (s N)) /
              ((B : ℝ)*amplificationMultiplier B) := by
  let A : ℕ → ℕ → ℂ := fun N n => star (movingBinLabel J k z N n) * H N n
  have hA : ∀ N n, ‖A N n‖ ≤ 2 := by
    intro N n
    dsimp only [A]
    rw [norm_mul,norm_star]
    have hg := norm_binLabel_le_one (fun i => primeBin (N : ℝ) J (k i)) z hz n
    exact (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hH N n)
  obtain ⟨s,hs,W,hW,hl⟩ := exists_arithmetic_amplification_profile_along A (by norm_num) hA r hr hmean
  obtain ⟨d,hd,hdB⟩ := smooth_amplified_profile_lower hFord hSD hM hMP W (by rwa [hW])
  let δ : ℝ := d*‖β‖/2
  have hδ : 0 < δ := div_pos (mul_pos hd (norm_pos_iff.mpr hβ)) (by norm_num)
  refine ⟨s,hs,δ^2/2,div_pos (sq_pos_of_pos hδ) (by norm_num),?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hCb⟩ := hdB L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hC
  filter_upwards [hCb C hC amplificationMultiplier amplificationMultiplier_valid,
    amplificationMultiplier_valid,eventually_gt_atTop 1] with B hBW hTB hB
  apply binLabel_energy_of_amplified_limit J hJ k hk z hz H (r ∘ s) (hr.comp hs) hB hTB.1 L τ C hδ
    (w := W.correlation (amplificationPeriod B)
      (smoothResidueAmplification B L τ C (amplificationMultiplier B)))
  · rw [hW] at hBW
    dsimp only [δ]
    linarith
  · exact hl B L τ C (amplificationMultiplier B)

end JointDickman

end OAI
end

theorem solution.{u_1} : type_of% @OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd_oai.{u_1} := @OAI.JointDickman.nonzero_binLabel_correlation_along_forces_energy_jd_oai.{u_1}
