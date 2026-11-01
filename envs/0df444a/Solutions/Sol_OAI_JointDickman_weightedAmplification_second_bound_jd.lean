-- Prove2me | solution 1 for OAI.JointDickman.weightedAmplification_second_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:58:45.584774+00:00
-- url     : https://prove2.me/submissions/9d6a3a22-8151-45f9-a1e9-8af351953d1e

import Mathlib
import Definitions.Def_OAIQ083J003

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

theorem bernoulliSubsetMass_complement_formula {α : Type*} [DecidableEq α]
    {P S : Finset α} (q : α → ℝ) (hS : S ⊆ P)
    (hq : ∀ p ∈ P, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      (∏ p ∈ P, (1 - q p)) * ∏ p ∈ S, (q p / (1 - q p)) := by
  have hne : (∏ p ∈ S, (1 - q p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => hq p (hS hp))
  rw [Finset.prod_div_distrib]
  have hsplit := Finset.prod_sdiff hS (f := fun p => 1 - q p)
  rw [← hsplit]
  unfold bernoulliSubsetMass
  field_simp

/-- Products of distinct prime sets remember their set of factors. -/
theorem primeProduct_injective {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {S T : Finset ℕ} (hS : S ⊆ P) (hT : T ⊆ P)
    (heq : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have hSF := Nat.primeFactors_prod (fun p hp => hP p (hS hp))
  have hTF := Nat.primeFactors_prod (fun p hp => hP p (hT hp))
  rw [← hSF, ← hTF, heq]

theorem primeProductMass_at_product {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    primeProductMass P z (∏ p ∈ S, p) =
      bernoulliSubsetMass P (fun p => z / p) S := by
  classical
  unfold primeProductMass
  rw [Finset.sum_eq_single S]
  · simp
  · intro T hT hTS
    have hne : (∏ p ∈ T, p) ≠ ∏ p ∈ S, p :=
      fun heq => hTS (primeProduct_injective hP (Finset.mem_powerset.mp hT) hS heq)
    simp [hne]
  · intro hn
    exact False.elim (hn (Finset.mem_powerset.mpr hS))

/-- Exact `ν_z` mass, factored into the all-absent probability and the
local odds ratios. -/
theorem primeProductMass_exact {P S : Finset ℕ} (z : ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P)
    (hz : ∀ p ∈ P, 1 - z / (p : ℝ) ≠ 0) :
    primeProductMass P z (∏ p ∈ S, p) =
      (∏ p ∈ P, (1 - z / (p : ℝ))) *
        ∏ p ∈ S, ((z / (p : ℝ)) / (1 - z / (p : ℝ))) := by
  rw [primeProductMass_at_product z hP hS]
  exact bernoulliSubsetMass_complement_formula _ hS hz

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

/-- Probability `1/2` at each member of a fixed site gives the uniform
fair-split mass, including the empty site. -/
theorem bernoulliSubsetMass_half {α : Type*} [DecidableEq α]
    {S T : Finset α} (hT : T ⊆ S) :
    bernoulliSubsetMass S (fun _ => (1 / 2 : ℝ)) T = (1 / 2 : ℝ) ^ S.card := by
  unfold bernoulliSubsetMass
  simp only [Finset.prod_const]
  norm_num only [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add, add_comm T.card, Finset.card_sdiff_add_card_eq_card hT]

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

theorem bernoulliBitMass_sum (q : ℝ) : ∑ b, bernoulliBitMass q b = 1 := by
  simp [bernoulliBitMass]

theorem bernoulliBitMass_nonneg {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) (b : Bool) :
    0 ≤ bernoulliBitMass q b := by
  cases b <;> simp only [bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  · exact sub_nonneg.mpr hq.2
  · exact hq.1

/-- Changing a Bernoulli success probability has exactly this `L¹` cost. -/
theorem bernoulliBitMass_l1 (q r : ℝ) :
    (∑ b, |bernoulliBitMass q b - bernoulliBitMass r b|) = 2 * |q - r| := by
  simp only [Fintype.sum_bool, bernoulliBitMass, Bool.false_eq_true, ↓reduceIte]
  rw [show 1 - q - (1 - r) = -(q - r) by ring, abs_neg]
  ring

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

/-- Independent Bernoulli subset laws are Lipschitz in their probabilities. -/
theorem bernoulliSubsetMass_l1_perturb {α : Type*} [DecidableEq α]
    (P : Finset α) (q r : α → ℝ)
    (hq : ∀ i ∈ P, 0 ≤ q i ∧ q i ≤ 1) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) :
    (∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S|) ≤
      2 * ∑ i ∈ P, |q i - r i| := by
  classical
  have h := finiteProductMass_l1_le
    (fun (i : P) => bernoulliBitMass (q i.val))
    (fun (i : P) => bernoulliBitMass (r i.val))
    (fun i b => bernoulliBitMass_nonneg (hq i.val i.property) b)
    (fun i b => bernoulliBitMass_nonneg (hr i.val i.property) b)
    (fun i => bernoulliBitMass_sum (q i.val)) (fun i => bernoulliBitMass_sum (r i.val))
  rw [← (subsetHitEquiv P).sum_comp
    (fun x => |finiteProductMass (fun (i : P) => bernoulliBitMass (q i.val)) x -
      finiteProductMass (fun (i : P) => bernoulliBitMass (r i.val)) x|)] at h
  simp_rw [bernoulliSubsetMass_eq_product, bernoulliBitMass_l1] at h
  have hl : (∑ S : P.powerset, |bernoulliSubsetMass P q S.val - bernoulliSubsetMass P r S.val|) =
      ∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S| :=
    Finset.sum_coe_sort P.powerset (fun S => |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S|)
  rw [hl, show (∑ i : P, 2 * |q i.val - r i.val|) = ∑ i ∈ P, 2 * |q i - r i| from
    Finset.sum_coe_sort P (fun i => 2 * |q i - r i|), ← Finset.mul_sum] at h
  exact h

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

theorem amplificationExponent_gt_one : 1 < amplificationExponent := by
  have h := Real.log_two_gt_d9
  unfold amplificationExponent
  linarith

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

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

/-- The amplification loss `B/R^α`, with `R=B/(1000 log B)`, vanishes for
every `α>1`. This is the exact expression before introducing `R`. -/
theorem amplification_log_loss_tendsto_zero {α : ℝ} (hα : 1 < α) :
    Tendsto (fun B : ℝ => B * (1000 * Real.log B) ^ α / B ^ α)
      atTop (𝓝 0) := by
  have h := (log_power_div_power_tendsto_zero α (sub_pos.mpr hα)).const_mul
    ((1000 : ℝ) ^ α)
  have heq : (fun B : ℝ => (1000 : ℝ) ^ α * ((Real.log B) ^ α / B ^ (α - 1)))
      =ᶠ[atTop] (fun B => B * (1000 * Real.log B) ^ α / B ^ α) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
    have hB0 : 0 < B := lt_trans zero_lt_one hB
    have hpow : B ^ α ≠ 0 := (Real.rpow_pos_of_pos hB0 α).ne'
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_nonneg hB.le),
      Real.rpow_sub hB0, Real.rpow_one]
    field_simp
  simpa only [mul_zero] using h.congr' heq

theorem amplification_log_loss :
    Tendsto (fun B : ℝ => B * (1000 * Real.log B) ^ amplificationExponent /
      B ^ amplificationExponent) atTop (𝓝 0) :=
  amplification_log_loss_tendsto_zero amplificationExponent_gt_one

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

theorem coefficientScale_eventually_le : ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ B := by
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1, eventually_gt_atTop 1] with B hR hB
  have hp : auxiliaryRatio B ^ (1 / 2 : ℝ) ≤ auxiliaryRatio B := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 / 2 : ℝ) ≤ 1))
  calc
    coefficientScale B ≤ Real.log (auxiliaryCutoff B) * auxiliaryRatio B :=
      mul_le_mul_of_nonneg_left hp (Real.log_natCast_nonneg _)
    _ = B := by rw [mul_comm, auxiliaryRatio_mul_log hB]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveSingleDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form Euler product at the roughness cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem roughSieveTheta_bounds (P p : ℕ) :
    0 ≤ roughSieveTheta P p ∧ roughSieveTheta P p ≤ 1 := by
  unfold roughSieveTheta
  split_ifs <;> norm_num

theorem roughSieveRate_bounds (P p : ℕ) (hp : p.Prime) :
    0 ≤ roughSieveRate P p ∧ roughSieveRate P p ≤ 1 / (p : ℝ) ∧
      roughSieveRate P p ≤ 1 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hθ := roughSieveTheta_bounds P p
  have hle : roughSieveRate P p ≤ 1 / (p : ℝ) := by
    unfold roughSieveRate
    exact div_le_div_of_nonneg_right (by linarith) hp0.le
  exact ⟨div_nonneg (by linarith) hp0.le, hle,
    hle.trans ((div_le_one hp0).mpr hp1)⟩

theorem roughSieveRate_sum {P Z : ℕ} (hPZ : P ≤ Z) :
    (∑ p ∈ Nat.primesLE Z, roughSieveRate P p) = (1 / 2 : ℝ) *
      ((∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)) + (∑ p ∈ Nat.primesLE P, 1 / (p : ℝ))) := by
  classical
  have hfilter : (Nat.primesLE Z).filter (fun p => p ≤ P) = Nat.primesLE P := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hp⟩, hle⟩
      exact ⟨hle, hp⟩
    · rintro ⟨hle, hp⟩
      exact ⟨⟨hle.trans hPZ, hp⟩, hle⟩
  have heq (p : ℕ) : roughSieveRate P p = (1 / 2 : ℝ) * (1 / (p : ℝ)) +
      (1 / 2 : ℝ) * (if p ≤ P then 1 / (p : ℝ) else 0) := by
    unfold roughSieveRate roughSieveTheta
    split_ifs <;> ring
  simp_rw [heq]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_filter, hfilter]
  ring

theorem roughSieveRate_removed_le (P Z : ℕ) :
    (∑ p ∈ Nat.primesLE Z, roughSieveRate P p) ≤
      (∑ p ∈ sievePrimes Z, roughSieveRate P p) + 6 := by
  classical
  let S := (Nat.primesLE Z).filter (fun p => ¬6 ≤ p)
  have hcard : S.card ≤ 6 := by
    apply le_trans (card_le_card (show S ⊆ range 6 from fun p hp =>
      mem_range.mpr (Nat.lt_of_not_ge (mem_filter.mp hp).2)))
    simp
  have hsum : (∑ p ∈ S, roughSieveRate P p) ≤ 6 := by
    calc
      _ ≤ ∑ _p ∈ S, (1 : ℝ) := sum_le_sum (fun p hp =>
        (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
      _ = S.card := by simp
      _ ≤ 6 := by exact_mod_cast hcard
  have heq := sum_filter_add_sum_filter_not (Nat.primesLE Z) (fun p => 6 ≤ p)
    (roughSieveRate P)
  change (∑ p ∈ sievePrimes Z, roughSieveRate P p) + (∑ p ∈ S, roughSieveRate P p) = _ at heq
  linarith

/-- The square of the one-form density has exactly the required two
logarithms in its denominator; bounded primes have already been removed. -/
theorem roughSieveDensity_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ P Z : ℕ, 2 ≤ P → P ≤ Z →
      roughSieveDensity P Z ^ 2 * Real.log P * Real.log Z ≤ C := by
  obtain ⟨M, A, hA, hMertens⟩ := hM
  let K := M - A / Real.log 2
  have hlow (N : ℕ) (hN : 2 ≤ N) :
      Real.log (Real.log N) + K ≤ ∑ p ∈ Nat.primesLE N, 1 / (p : ℝ) := by
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h := (abs_le.mp (hMertens N hN2)).1
    rw [Nat.floor_natCast, ← primesLE_eq_filter] at h
    have hdiv := div_le_div_of_nonneg_left hA (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (Real.log_le_log (by norm_num) hN2)
    dsimp [K]
    linarith
  refine ⟨Real.exp (12 - 2 * K), Real.exp_pos _, ?_⟩
  intro P Z hP hPZ
  have hZ : 2 ≤ Z := hP.trans hPZ
  have hlP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlZ : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
  let S := ∑ p ∈ sievePrimes Z, roughSieveRate P p
  have hS : (1 / 2 : ℝ) * (Real.log (Real.log P) + Real.log (Real.log Z)) + K - 6 ≤ S := by
    have hrem := roughSieveRate_removed_le P Z
    rw [roughSieveRate_sum hPZ] at hrem
    dsimp [S]
    linarith [hlow P hP, hlow Z hZ]
  have hd0 : 0 ≤ roughSieveDensity P Z := prod_nonneg (fun p hp =>
    sub_nonneg.mpr (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
  have hd : roughSieveDensity P Z ≤ Real.exp (-S) := by
    calc
      _ ≤ ∏ p ∈ sievePrimes Z, Real.exp (-roughSieveRate P p) := Finset.prod_le_prod
        (fun p hp => sub_nonneg.mpr
          (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)
        (fun p _ => Real.one_sub_le_exp_neg _)
      _ = Real.exp (-S) := by rw [← Real.exp_sum, sum_neg_distrib]
  calc
    _ ≤ Real.exp (-S) ^ 2 * Real.log P * Real.log Z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hd0 hd 2) hlP.le) hlZ.le
    _ = Real.exp (-2 * S + Real.log (Real.log P) + Real.log (Real.log Z)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hlP, Real.exp_log hlZ]
      have he : Real.exp (-S) ^ 2 = Real.exp (-2 * S) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [he]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cancellation of the coefficient scale in the sieve density -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientScale_sq_eq {B : ℕ} (hB : 1 < B) :
    coefficientScale B ^ 2 = (B : ℝ) * Real.log (auxiliaryCutoff B) := by
  have hR := auxiliaryRatio_pos hB
  have hpow : (auxiliaryRatio B ^ (1 / 2 : ℝ)) ^ 2 = auxiliaryRatio B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
  rw [coefficientScale, mul_pow, hpow]
  have hmul := auxiliaryRatio_mul_log hB
  nlinarith

theorem roughSieveDensity_nonneg (P Z : ℕ) : 0 ≤ roughSieveDensity P Z :=
  prod_nonneg (fun p hp => sub_nonneg.mpr
    (roughSieveRate_bounds P p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2).2.2)

theorem coefficient_sieve_density_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z →
      δ * B ≤ Real.log Z →
      coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z ≤ C := by
  obtain ⟨K, hK, hbound⟩ := roughSieveDensity_log_bound hM
  refine ⟨Real.sqrt (K / δ), Real.sqrt_pos.mpr (div_pos hK hδ), ?_⟩
  intro B Z hB hPZ hlog
  have hP : 2 ≤ auxiliaryCutoff B := by
    exact one_lt_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  have hb := hbound (auxiliaryCutoff B) Z hP hPZ
  have hδmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (sq_nonneg (roughSieveDensity (auxiliaryCutoff B) Z))
      (Real.log_natCast_nonneg (auxiliaryCutoff B)))
  have hsq : (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 2 ≤ K / δ := by
    apply (le_div_iff₀ hδ).mpr
    rw [mul_pow, coefficientScale_sq_eq hB]
    nlinarith
  apply (sq_le_sq₀ (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _))
    (Real.sqrt_nonneg _)).mp
  rwa [Real.sq_sqrt (div_pos hK hδ).le]

theorem sieveCutoff_eventually {c : ℝ} (hc : 0 < c) :
    ∀ᶠ B : ℕ in atTop, 2 ≤ sieveCutoff c B ∧ auxiliaryCutoff B ≤ sieveCutoff c B ∧
      (c / 2) * B ≤ Real.log (sieveCutoff c B) ∧
      (sieveCutoff c B : ℝ) ≤ Real.exp (c * B) := by
  have hlarge : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.exp ((c / 2) * B) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : 0 < c / 2))).eventually_ge_atTop 2
  have hpoly : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ 1000 ≤ Real.exp ((c / 2) * B) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1000 (by linarith : 0 < c / 2)).def
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h] with B hB
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) 1000),
      abs_of_pos (Real.exp_pos _), one_mul] using hB
  filter_upwards [hlarge, hpoly] with B hlargeB hpolyB
  have hfloor : Real.exp ((c / 2) * B) ≤ (sieveCutoff c B : ℝ) := by
    have heq : Real.exp (c * B) = Real.exp ((c / 2) * B) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have h := Nat.lt_floor_add_one (Real.exp (c * B))
    change Real.exp (c * B) < (sieveCutoff c B : ℝ) + 1 at h
    rw [heq] at h
    nlinarith
  refine ⟨?_, ?_, ?_, Nat.floor_le (Real.exp_pos _).le⟩
  · exact_mod_cast hlargeB.trans hfloor
  · have h := hpolyB.trans hfloor
    exact_mod_cast h
  · have h := Real.log_le_log (Real.exp_pos ((c / 2) * B)) hfloor
    simpa only [Real.log_exp] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionCutoffScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed sieve cutoff used for the addition-product small-ball bound -/

namespace JointDickman

open Filter
open scoped Topology

theorem additionSieveCutoff_eventually :
    ∀ᶠ Y : ℝ in atTop, 0 < Y ∧ 2 ≤ additionSieveCutoff Y ∧
      Y / 200 ≤ Real.log (additionSieveCutoff Y) ∧
      (additionSieveCutoff Y : ℝ) ≤ Real.exp (Y / 100) ∧
      (2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y) * Y ≤ Real.exp (Y / 2) := by
  have hexp : ∀ᶠ Y : ℝ in atTop, 2 ≤ Real.exp (Y / 200) := by
    apply (Real.tendsto_exp_atTop.comp ?_).eventually_ge_atTop 2
    exact tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 200)
  have hlim : Tendsto (fun Y : ℝ => 4 * (Y / Real.exp ((12 / 25 : ℝ) * Y))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0 : ℝ) < 12 / 25)).tendsto_div_nhds_zero
    simpa only [pow_one, mul_zero] using h.const_mul 4
  filter_upwards [hexp, hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with Y he hs hY
  have hfloor : Real.exp (Y / 200) ≤ (additionSieveCutoff Y : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (Y / 100))
    change Real.exp (Y / 100) < (additionSieveCutoff Y : ℝ) + 1 at hh
    have heq : Real.exp (Y / 100) = Real.exp (Y / 200)^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq] at hh
    nlinarith only [hh, he]
  have hlog : Y / 200 ≤ Real.log (additionSieveCutoff Y) := by
    have hh := Real.log_le_log (Real.exp_pos (Y / 200)) hfloor
    simpa only [Real.log_exp] using hh
  have hZupper : (additionSieveCutoff Y : ℝ) ≤ Real.exp (Y / 100) := Nat.floor_le (Real.exp_pos _).le
  have hZ0 : (0 : ℝ) ≤ additionSieveCutoff Y := Nat.cast_nonneg _
  have he1 : 1 ≤ Real.exp (Y / 100) := Real.one_le_exp_iff.mpr (by positivity)
  have hrem : 2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y ≤
      4 * Real.exp (Y / 50) := by
    calc
      _ ≤ 2 * (2 * Real.exp (Y / 100)) * Real.exp (Y / 100) := by gcongr; linarith only [hZupper, he1]
      _ = _ := by rw [show Y / 50 = Y / 100 + Y / 100 by ring, Real.exp_add]; ring
  have hsmall : 4 * Y ≤ Real.exp ((12 / 25 : ℝ) * Y) := by
    apply (div_le_one (Real.exp_pos _)).mp
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨hY, ?_, hlog, hZupper, ?_⟩
  · exact_mod_cast he.trans hfloor
  · calc
      _ ≤ (4 * Real.exp (Y / 50)) * Y := mul_le_mul_of_nonneg_right hrem hY.le
      _ = (4 * Y) * Real.exp (Y / 50) := by ring
      _ ≤ Real.exp ((12 / 25 : ℝ) * Y) * Real.exp (Y / 50) :=
        mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicNonnegative
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Periodic interval counts with a sparse error

For a nonnegative periodic weight, the error is bounded by its total mass
in one period. This retains the number of allowed residues in sieve errors.
-/

namespace JointDickman

open Finset

private theorem real_periodic_sum_div_mod {q : ℕ} (f : ZMod q → ℝ) (N : ℕ) :
    (∑ n ∈ range N, f n) =
      (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n := by
  have h := periodic_sum_div_mod (fun a => (f a : ℂ)) N
  exact_mod_cast h

/-- A prefix costs at most the mass of one complete period. -/
theorem nonnegative_periodic_prefix_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ) / q * ∑ n ∈ range q, f n| ≤
      ∑ n ∈ range q, f n := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hr : N % q < q := Nat.mod_lt N hq
  have hrR : ((N % q : ℕ) : ℝ) ≤ q := by exact_mod_cast hr.le
  have hfull : 0 ≤ ∑ n ∈ range q, f n := sum_nonneg (fun n _ => hf n)
  have hpart : 0 ≤ ∑ n ∈ range (N % q), f n := sum_nonneg (fun n _ => hf n)
  have hle : (∑ n ∈ range (N % q), f n) ≤ ∑ n ∈ range q, f n :=
    sum_le_sum_of_subset_of_nonneg (range_mono hr.le) (fun n _ _ => hf n)
  have hcoef : 0 ≤ ((N % q : ℕ) : ℝ) / q := by positivity
  have hcoef1 : ((N % q : ℕ) : ℝ) / q ≤ 1 := (div_le_one hqR).mpr hrR
  have hdecomp : (N : ℝ) = (N / q : ℕ) * (q : ℝ) + (N % q : ℕ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm : N = N / q * q + N % q)
  rw [real_periodic_sum_div_mod]
  have hid : (N / q : ℕ) * (∑ n ∈ range q, f n) + ∑ n ∈ range (N % q), f n -
      (N : ℝ) / q * ∑ n ∈ range q, f n =
      (∑ n ∈ range (N % q), f n) -
        ((N % q : ℕ) : ℝ) / q * ∑ n ∈ range q, f n := by
    rw [hdecomp]
    field_simp
    ring
  rw [hid, abs_le]
  constructor <;> nlinarith

/-- Two prefix errors give the interval error, uniformly in its location. -/
theorem nonnegative_periodic_interval_error {q : ℕ} (hq : 0 < q)
    (f : ZMod q → ℝ) (hf : ∀ a, 0 ≤ f a) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, f n) - ((b : ℝ) - a) / q * ∑ n ∈ range q, f n| ≤
      2 * ∑ n ∈ range q, f n := by
  have ha := nonnegative_periodic_prefix_error hq f hf a
  have hb := nonnegative_periodic_prefix_error hq f hf b
  rw [sum_Ico_eq_sub (fun n : ℕ => f (n : ZMod q)) hab]
  calc
    _ = |((∑ n ∈ range b, f n) - (b : ℝ) / q * ∑ n ∈ range q, f n) -
        ((∑ n ∈ range a, f n) - (a : ℝ) / q * ∑ n ∈ range q, f n)| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Chinese remainder counts for the sieve -/

namespace JointDickman

open Finset

/-- Uniform residue sums factor over any finite pairwise coprime family. -/
theorem crt_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (f : ∀ i, ZMod (m i) → ℝ) :
    (∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i))) =
      ∏ i, ∑ a : ZMod (m i), f i a := by
  classical
  let : NeZero (∏ i, m i) := ⟨prod_ne_zero_iff.mpr (fun i _ => (hm i).ne')⟩
  let e := ZMod.prodEquivPi m hcop
  have hsum : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∏ i, ∑ b : ZMod (m i), f i b := by
    rw [Fintype.sum_equiv e.toEquiv (fun a => ∏ i, f i (e a i))
      (fun b => ∏ i, f i (b i)) (fun _ => rfl)]
    exact (Fintype.prod_sum f).symm
  have hperiod : (∑ a : ZMod (∏ i, m i), ∏ i, f i (e a i)) =
      ∑ n ∈ range (∏ i, m i), ∏ i, f i (n : ZMod (m i)) := by
    have h := residue_sum_eq_range (fun a : ZMod (∏ i, m i) =>
      ((∏ i, f i (e a i) : ℝ) : ℂ))
    have heval (n : ℕ) : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) :=
      map_natCast e n
    simp only [heval, Pi.natCast_apply] at h
    exact_mod_cast h
  exact hperiod.symm.trans hsum

/-- The simultaneous prescribed-root count is exactly the product of the
local root counts, including an empty family of moduli. -/
theorem crt_root_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) :
    (∑ n ∈ range (∏ i, m i),
      if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  have hind (n : ℕ) : (∏ i, if (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) =
      if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  rw [crt_period_sum m hm hcop (fun i a => if a ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simp

/-- An interval intersection has at most two errors per simultaneous
residue class, independent of the modulus and the interval location. -/
theorem crt_root_interval_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i))) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ i, (n : ZMod (m i)) ∈ A i then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ i, ((A i).card : ℝ) / (m i)| ≤
        2 * ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun n : ZMod (∏ i, m i) => if ∀ i, e n i ∈ A i then (1 : ℝ) else 0
  have hF (n : ℕ) : F n = if ∀ i, (n : ZMod (m i)) ∈ A i then 1 else 0 := by
    have heval : e (n : ZMod (∏ i, m i)) = (n : ∀ i, ZMod (m i)) := map_natCast e n
    simp [F, heval]
  have hmass : (∑ n ∈ range (∏ i, m i), F n) = ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_root_period_count m hm hcop A
  have h := nonnegative_periodic_interval_error hM F
    (fun n => by dsimp [F]; split_ifs <;> norm_num) hab
  rw [hmass] at h
  simp_rw [hF] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [prod_div_distrib, Nat.cast_prod]
  ring

/-- Specialization to a finite set of distinct primes. -/
theorem prime_root_interval_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Ico a b, if ∀ p ∈ P, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ∏ p ∈ P, ((A p).card : ℝ) / p| ≤
        2 * ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_root_interval_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab
  simpa only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ) / p),
    P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)), Subtype.forall] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRemainders
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary bounds for the total sieve remainder

A crude fixed power of the level suffices: the manuscript allows a fixed
sieve cutoff sufficiently small compared with the counting scale.
-/

namespace JointDickman

open Finset

/-- Fixed exponential weights in the number of prime factors admit a
fixed polynomial bound in the product. -/
theorem prime_card_power_le_product_power (D : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime) (k : ℕ) :
    k ^ D.card ≤ (∏ p ∈ D, p) ^ k := by
  calc
    _ = ∏ _p ∈ D, k := by simp
    _ ≤ ∏ p ∈ D, p ^ k := prod_le_prod' (fun p hp =>
      k.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (hD p hp).two_le k))
    _ = _ := prod_pow D k id

/-- Distinct subsets give distinct squarefree products; summing their
fixed-factor-count weights below `N` costs at most `N^(k+1)+N^k`. -/
theorem sieve_level_power_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (k N : ℕ) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), k ^ D.card) ≤
      (N + 1) * N ^ k := by
  classical
  let S := P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N)
  have hinj : Set.InjOn (fun D : Finset ℕ => ∏ p ∈ D, p) (↑S : Set (Finset ℕ)) := by
    intro D hD E hE heq
    exact primeProduct_injective hP
      (mem_powerset.mp (mem_filter.mp hD).1)
      (mem_powerset.mp (mem_filter.mp hE).1) heq
  have hsub : S.image (fun D => ∏ p ∈ D, p) ⊆ range (N + 1) := by
    intro d hd
    obtain ⟨D, hD, rfl⟩ := mem_image.mp hd
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2)
  calc
    _ ≤ ∑ D ∈ S, (∏ p ∈ D, p) ^ k := by
      apply sum_le_sum
      intro D hD
      exact prime_card_power_le_product_power D
        (fun p hp => hP p (mem_powerset.mp (mem_filter.mp hD).1 hp)) k
    _ = ∑ d ∈ S.image (fun D => ∏ p ∈ D, p), d ^ k := (sum_image (f := fun d : ℕ => d ^ k) hinj).symm
    _ ≤ ∑ d ∈ range (N + 1), d ^ k := sum_le_sum_of_subset hsub
    _ ≤ ∑ _d ∈ range (N + 1), N ^ k := by
      apply sum_le_sum
      intro d hd
      exact Nat.pow_le_pow_left (Nat.le_of_lt_succ (mem_range.mp hd)) k
    _ = _ := by simp

/-- The same level bound with arbitrary local root counts bounded by `k`. -/
theorem sieve_level_root_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ → ℕ) (k N : ℕ) (hr : ∀ p ∈ P, r p ≤ k) :
    (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p) ≤ N), ∏ p ∈ D, r p) ≤
      (N + 1) * N ^ k := by
  apply le_trans _ (sieve_level_power_sum P hP k N)
  apply sum_le_sum
  intro D hD
  calc
    _ ≤ ∏ _p ∈ D, k := prod_le_prod' (fun p hp =>
      hr p (mem_powerset.mp (mem_filter.mp hD).1 hp))
    _ = _ := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Reducing local weights by random forbidding

The upper sieve is applied to deterministic forbidden congruences. Randomly
forbidding each form converts that bound to the product of its local weights,
without changing the remainder. The transfer below is exact on finite sets;
the deterministic upper-sieve estimate is a separate published input.
-/

namespace JointDickman

open Finset

private theorem avoidsSelected_eq_product {ι : Type*} [DecidableEq ι]
    (S E : Finset ι) : avoidsSelected S E = ∏ i ∈ S, if i ∈ E then (0 : ℝ) else 1 := by
  classical
  by_cases h : Disjoint S E
  · rw [avoidsSelected, ite_eq_left h]
    symm
    apply prod_eq_one
    intro i hi
    have hn : i ∉ E := fun he => Finset.disjoint_left.mp h hi he
    simp [hn]
  · rw [avoidsSelected, ite_eq_right h]
    symm
    obtain ⟨i, hi, he⟩ := Finset.not_disjoint_iff.mp h
    exact prod_eq_zero hi (by simp [he])

/-- Average survival is exactly the product of the retained local weights. -/
theorem bernoulliSubsetMass_avoids {ι : Type*} [DecidableEq ι]
    (P E : Finset ι) (hE : E ⊆ P) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S * avoidsSelected S E) =
      ∏ i ∈ E, θ i := by
  simp_rw [avoidsSelected_eq_product]
  rw [bernoulliSubsetMass_tilt]
  calc
    (∏ i ∈ P, (1 - (1 - θ i) + (1 - θ i) * if i ∈ E then (0 : ℝ) else 1)) =
        ∏ i ∈ P, if i ∈ E then θ i else 1 := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> ring
    _ = ∏ i ∈ E, θ i := by
      rw [← prod_subset hE]
      · apply prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        simp [hi]

/-- Exact finite expectation identity for a population of points. -/
theorem randomized_sifted_mass {ι X : Type*} [DecidableEq ι] [Fintype X]
    (P : Finset ι) (E : X → Finset ι) (hE : ∀ x, E x ⊆ P)
    (w : X → ℝ) (θ : ι → ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
      ∑ x, w x * avoidsSelected S (E x)) = ∑ x, w x * ∏ i ∈ E x, θ i := by
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  calc
    (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        (w x * avoidsSelected S (E x))) =
      w x * ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun i => 1 - θ i) S *
        avoidsSelected S (E x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring
    _ = _ := by rw [bernoulliSubsetMass_avoids P (E x) (hE x)]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_UpperSieveInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published finite-event upper sieve

Theorem 2.4 of Kevin Ford, *Sieve Methods Lecture Notes, Spring 2023*,
page 18, https://ford126.web.illinois.edu/sieve2023.pdf, in its general
probability-space formulation (Section 1.2). The sum of absolute remainders
is only over squarefree products at most the sifting bound. No arithmetic
progression estimate or application-specific weight bound is assumed here.
-/

namespace JointDickman

open Finset

/-- Deleting sieve primes also preserves the dimension condition. -/
theorem SieveDimension.subset {P S : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hd : SieveDimension P g κ A z) (hS : S ⊆ P)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    SieveDimension S g κ A z := by
  intro y v hy hyv hvz
  apply le_trans _ (hd y v hy hyv hvz)
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    exact mem_filter.mpr ⟨hS (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · intro p hp
    exact inv_nonneg.mpr (by linarith [(hg p (hS (mem_filter.mp hp).1)).2])
  · intro p hp _
    exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hp).1).2])).mpr
      (by linarith [(hg p (mem_filter.mp hp).1).1])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveDimension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sieve dimension from Mertens' estimate -/

namespace JointDickman

open Finset

/-- The possible prime at the lower endpoint costs at most `1 / log y`. -/
theorem closed_prime_interval_sum_le
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (P : Finset ℕ) (y v : ℝ),
      (∀ p ∈ P, p.Prime) → 2 ≤ y → y ≤ v →
      (∑ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v),
        1 / (p : ℝ)) ≤ Real.log (Real.log v / Real.log y) + K / Real.log y := by
  obtain ⟨C, hC, hbound⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + 1, by positivity, ?_⟩
  intro P y v hP hy hyv
  have hy0 : 0 ≤ y := by linarith
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlv : 0 < Real.log v := Real.log_pos (by linarith)
  have hlogle : Real.log y ≤ Real.log v := Real.log_le_log (by linarith) hyv
  have hnle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hln : Real.log y ≤ (⌊y⌋₊ : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < y by linarith), Nat.lt_floor_add_one y]
  have hnpos : (0 : ℝ) < ⌊y⌋₊ := hly.trans_le hln
  have hnot : ⌊y⌋₊ ∉ largePrimeSet v y := by
    intro hn
    exact (not_lt_of_ge hnle) (mem_filter.mp hn).2
  have hsub : P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v) ⊆
      insert ⌊y⌋₊ (largePrimeSet v y) := by
    intro p hp
    obtain ⟨hpP, hpy, hpv⟩ := mem_filter.mp hp
    by_cases hlt : y < (p : ℝ)
    · apply mem_insert_of_mem
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpv, hP p hpP⟩, hlt⟩
    · have heq : (p : ℝ) = y := le_antisymm (le_of_not_gt hlt) hpy
      apply mem_insert.mpr
      left
      rw [← heq, Nat.floor_natCast]
  calc
    _ ≤ ∑ p ∈ insert ⌊y⌋₊ (largePrimeSet v y), 1 / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = 1 / (⌊y⌋₊ : ℝ) + ∑ p ∈ largePrimeSet v y, 1 / (p : ℝ) := sum_insert hnot
    _ ≤ 1 / Real.log y +
        ((Real.log (Real.log v) - Real.log (Real.log y)) +
          (C / Real.log v + C / Real.log y)) := by
      apply add_le_add
      · exact one_div_le_one_div_of_le hly hln
      · linarith [(abs_le.mp (hbound y v hy hyv)).2]
    _ ≤ Real.log (Real.log v / Real.log y) + (2 * C + 1) / Real.log y := by
      rw [Real.log_div hlv.ne' hly.ne']
      have hd := div_le_div_of_nonneg_left hC hly hlogle
      simp only [add_div, mul_div_assoc]
      linarith

/-- A fixed number of forbidden classes per prime has bounded dimension.
The dimension `2*k` is deliberately sufficient, rather than optimal. -/
theorem sieveDimension_of_reciprocal_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (P : Finset ℕ) (g : ℕ → ℝ) (z : ℝ),
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      SieveDimension P g (2 * k) A z := by
  obtain ⟨K, hK, hbound⟩ := closed_prime_interval_sum_le hM
  refine ⟨2 * k * K, by positivity, ?_⟩
  intro P g z hP hg y v hy hyv _
  let S := P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v)
  have hsub : S ⊆ P := filter_subset _ _
  have hsum : (∑ p ∈ S, g p) ≤ k * ∑ p ∈ S, 1 / (p : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum (fun p hp => by simpa only [mul_one_div] using (hg p (hsub hp)).2.2)
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ S, g p) :=
      inverse_product_le_exp S g (fun p hp => ⟨(hg p (hsub hp)).1, (hg p (hsub hp)).2.1⟩)
    _ ≤ Real.exp (2 * k *
        (Real.log (Real.log v / Real.log y) + K / Real.log y)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hbound P y v hP hy hyv) hk.le]
    _ = (Real.log v / Real.log y) ^ (2 * k) *
        Real.exp ((2 * k * K) / Real.log y) := by
      have hp : 0 < Real.log v / Real.log y :=
        div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
      rw [Real.rpow_def_of_pos hp, ← Real.exp_add]
      congr 1
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedUpperSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing weights in the published upper sieve

Independent random forbidding derives the Euler factors for arbitrary
retained weights in `[0,1]`. The original remainder is unchanged, and the
constant stays uniform over all the retained weights.
-/

namespace JointDickman

open Finset

theorem ford_weighted_upper_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) → SieveDimension P g κ A z →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  classical
  obtain ⟨C, hC, hbound⟩ := hFord κ A hκ hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ hd
  let R := ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
    |sieveRemainder E w M g D|
  have hq : ∀ p ∈ P, 0 ≤ 1 - θ p ∧ 1 - θ p ≤ 1 := by
    intro p hp
    constructor <;> linarith [(hθ p hp).1, (hθ p hp).2]
  have hupper (S : Finset ℕ) (hS : S ⊆ P) :
      (∑ x, w x * avoidsSelected S (E x)) ≤
        C * M * (∏ p ∈ S, (1 - g p)) + R := by
    apply (hbound X S E w M z g hz hM hw (fun p hp => hP p (hS hp))
      (fun p hp => hg p (hS hp)) (hd.subset hS hg)).trans
    apply add_le_add le_rfl
    apply sum_le_sum_of_subset_of_nonneg
    · intro D hD
      obtain ⟨hDS, hDz⟩ := mem_filter.mp hD
      exact mem_filter.mpr ⟨mem_powerset.mpr ((mem_powerset.mp hDS).trans hS), hDz⟩
    · intro D _ _
      exact abs_nonneg _
  calc
    _ = ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        ∑ x, w x * avoidsSelected S (E x) :=
      (randomized_sifted_mass P E hE w θ).symm
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S *
        (C * M * (∏ p ∈ S, (1 - g p)) + R) := by
      apply sum_le_sum
      intro S hS
      exact mul_le_mul_of_nonneg_left (hupper S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq)
    _ = C * M * (∑ S ∈ P.powerset,
          bernoulliSubsetMass P (fun p => 1 - θ p) S * ∏ p ∈ S, (1 - g p)) +
        R * (∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 - θ p) S) := by
      simp_rw [mul_add, sum_add_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro S _ <;> ring
    _ = C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) + R := by
      rw [bernoulliSubsetMass_tilt, bernoulliSubsetMass_sum, mul_one]
      congr 2
      apply prod_congr rfl
      intro p _
      ring

/-- The ready-to-apply bound: only Ford and Mertens remain published inputs;
no abstract sieve dimension hypothesis remains. -/
theorem weighted_upper_sieve_from_published
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Type) [Fintype X]
      (P : Finset ℕ) (E : X → Finset ℕ) (w : X → ℝ) (M z : ℝ)
      (g θ : ℕ → ℝ), 2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → (∀ x, E x ⊆ P) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ)) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ x, w x * ∏ p ∈ E x, θ p) ≤
        C * M * (∏ p ∈ P, (1 - g p + g p * θ p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D| := by
  obtain ⟨A, hA, hdim⟩ := sieveDimension_of_reciprocal_bound hM hk
  obtain ⟨C, hC, hbound⟩ := ford_weighted_upper_sieve hFord
    (show 0 < 2 * k by positivity) hA
  refine ⟨C, hC, ?_⟩
  intro X _ P E w M z g θ hz hM hw hP hE hg hθ
  exact hbound X P E w M z g θ hz hM hw hP hE
    (fun p hp => ⟨(hg p hp).1, by linarith [(hg p hp).2.1]⟩) hθ
    (hdim P g z (fun p hp => (hP p hp).1) hg)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The interval sieve with its actual arithmetic remainder -/

namespace JointDickman

open Finset

/-- CRT evaluates the actual remainder used by the upper sieve. -/
theorem root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p)) {a b : ℕ} (hab : a ≤ b)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D| ≤
        2 * ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (n : Ico a b) : D ⊆ rootEvents P A n ↔
      ∀ p ∈ D, (n.val : ZMod p) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  have hid : sieveRemainder (fun n : Ico a b => rootEvents P A n) (fun _ => 1)
      ((b : ℝ) - a) (fun p => ((A p).card : ℝ) / p) D =
      (∑ n ∈ Ico a b, if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0) -
        ((b : ℝ) - a) * ∏ p ∈ D, ((A p).card : ℝ) / p := by
    unfold sieveRemainder sieveIntersection
    simp_rw [hcond]
    rw [(Ico a b).sum_coe_sort (fun n : ℕ =>
      if ∀ p ∈ D, (n : ZMod p) ∈ A p then (1 : ℝ) else 0)]
  rw [hid]
  exact prime_root_interval_error D (fun p hp => hP p (hD hp)) A hab

/-- Uniform weighted interval bound, derived from Ford and Mertens. -/
theorem weighted_interval_sieve (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b : ℕ) (z : ℝ), a ≤ b → 2 ≤ z →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, ((A p).card : ℝ) ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P A θ a b z hab hz hP hA hθ
  let E := fun n : Ico a b => rootEvents P A n
  let g := fun p => ((A p).card : ℝ) / p
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ k / (p : ℝ) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    dsimp [g]
    refine ⟨by positivity, ?_, div_le_div_of_nonneg_right (hA p hp) hp0.le⟩
    apply (div_le_iff₀ hp0).mpr
    linarith [(hP p hp).2.2, hA p hp]
  have h := hbound (Ico a b) P E (fun _ => 1) ((b : ℝ) - a) z g θ hz
    (sub_nonneg.mpr (by exact_mod_cast hab)) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)
    (fun n => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  dsimp only [E, g] at h
  rw [(Ico a b).sum_coe_sort (fun n : ℕ => ∏ p ∈ rootEvents P A n, θ p)] at h
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  exact root_sieve_remainder P (fun p hp => (hP p hp).1) A hab
    (mem_powerset.mp (mem_filter.mp hD).1)

/-- A completely explicit polynomial remainder suffices at a small fixed
power cutoff. All interval positions and reducing weights are uniform. -/
theorem weighted_interval_sieve_polynomial
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
      (θ : ℕ → ℝ) (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p ∈ rootEvents P A n, θ p) ≤
        C * ((b : ℝ) - a) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / p + ((A p).card : ℝ) / p * θ p)) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b Z hab hZ hP hA hθ
  have h := hbound P A θ a b Z hab (by exact_mod_cast hZ)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1,
      by exact_mod_cast (hP p hp).2.2⟩)
    (fun p hp => by exact_mod_cast hA p hp) hθ
  apply h.trans
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq]
  exact_mod_cast sieve_level_root_sum P (fun p hp => (hP p hp).1)
    (fun p => (A p).card) k Z hA

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThreeFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local upper bounds for b, c, and b+jc

At primes not dividing j the exact three-form mean is bounded by the cube
of the single-form mean. Degenerate primes cost at most `1 + 24/p`.
-/

namespace JointDickman

open Finset

theorem residueWeight_nonneg {α : Type*} (a x : α) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ residueWeight t a x := by
  classical
  unfold residueWeight
  split_ifs <;> positivity

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

theorem tiltedPrimeWeight_bounds (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedPrimeWeight Q s p ∧ tiltedPrimeWeight Q s p ≤ 1 := by
  unfold tiltedPrimeWeight
  split_ifs <;> constructor <;> nlinarith [Real.exp_pos s]

theorem tiltedSieveTheta_bounds (P : ℕ) (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) (p : ℕ) :
    0 ≤ tiltedSieveTheta P Q s p ∧ tiltedSieveTheta P Q s p ≤ 1 := by
  unfold tiltedSieveTheta
  split_ifs
  · norm_num
  · exact tiltedPrimeWeight_bounds Q hs p

theorem tilted_prime_product (S Q : Finset ℕ) (s : ℝ) :
    (∏ p ∈ S, tiltedPrimeWeight Q s p) =
      (1 / 2 : ℝ) ^ S.card * Real.exp (s * (S ∩ Q).card) := by
  classical
  have heq (p : ℕ) : tiltedPrimeWeight Q s p =
      (1 / 2 : ℝ) * (if p ∈ Q then Real.exp s else 1) := by
    by_cases hp : p ∈ Q <;> simp [tiltedPrimeWeight, hp]
  have hfilter : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
  simp_rw [heq]
  rw [prod_mul_distrib, prod_const, ← prod_filter, hfilter, prod_const, ← Real.exp_nat_mul]
  congr 2; ring

theorem tiltedCoefficientWeight_le_sieved (B Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) (n : ℕ) :
    tiltedCoefficientWeight B Q s n ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) := by
  classical
  have hnonneg : 0 ≤ coefficientScale B *
      ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
    mul_nonneg (coefficientScale_nonneg _) (prod_nonneg (fun p _ =>
      residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q hs p).1))
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE (auxiliaryCutoff B))
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) =
            if p ∣ n then tiltedPrimeWeight Q s p else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬p ≤ auxiliaryCutoff B := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, tiltedSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hprod : (∏ p ∈ n.primeFactors, tiltedPrimeWeight Q s p) ≤
          ∏ p ∈ (sievePrimes Z).filter (fun p => p ∣ n), tiltedPrimeWeight Q s p :=
        prod_le_prod_of_subset_of_le_one hsub
          (fun p _ => (tiltedPrimeWeight_bounds Q hs p).1)
          (fun p _ _ => (tiltedPrimeWeight_bounds Q hs p).2)
      have htprod := tilted_prime_product n.primeFactors Q s
      rw [htprod] at hprod
      have hbound := mul_le_mul_of_nonneg_left hprod (coefficientScale_nonneg B)
      simpa only [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight,
        ArithmeticFunction.coe_mk, ite_eq_left hd, squarefreeWeight, ite_eq_left hsq,
        hcard, primeDivisorCount, mul_assoc, prod_congr rfl heq, ← prod_filter] using hbound
    · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, squarefreeWeight, hd, hsq] using hnonneg
  · simpa [tiltedCoefficientWeight, coefficientWeight, roughSquarefreeWeight, hd] using hnonneg

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TiltedSieveDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler-product cost of an exponential prime-count tilt -/

namespace JointDickman

open Finset

theorem tilted_sieve_density_bound (P Z : ℕ) (Q : Finset ℕ) {s : ℝ}
    (hs : Real.exp s ≤ 2) :
    tiltedSieveDensity P Z Q s ≤ roughSieveDensity P Z *
      Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := by
  classical
  let S := sievePrimes Z
  let x := fun p => (1 - tiltedSieveTheta P Q s p) / (p : ℝ)
  let y := roughSieveRate P
  have hp (p : ℕ) (h : p ∈ S) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp h).1).2
  have hx (p : ℕ) (h : p ∈ S) : 0 ≤ x p ∧ x p ≤ 1 / 2 := by
    have htheta := tiltedSieveTheta_bounds P Q hs p
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    dsimp [x]
    constructor
    · exact div_nonneg (by linarith) hp0.le
    · apply (div_le_iff₀ hp0).mpr
      linarith
  have hy (p : ℕ) (h : p ∈ S) : 0 ≤ y p ∧ y p ≤ 1 / 2 := by
    have hb := roughSieveRate_bounds P p (hp p h)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    exact ⟨hb.1, hb.2.1.trans (one_div_le_one_div_of_le (by norm_num) hp2)⟩
  have hquad (f : ℕ → ℝ) (hf : ∀ p ∈ S, 0 ≤ f p ∧ f p ≤ 1 / (p : ℝ)) :
      ∑ p ∈ S, f p ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ p ∈ S, 1 / (p : ℝ) ^ 2 := by
        apply sum_le_sum
        intro p h
        simpa only [one_div_pow] using pow_le_pow_left₀ (hf p h).1 (hf p h).2 2
      _ ≤ 1 := by
        simpa using sum_reciprocal_square_tail S (by norm_num : (1 : ℕ) ≠ 0)
          (fun p h => (hp p h).one_lt)
  have hxq := hquad x (fun p h => ⟨(hx p h).1, by
    dsimp [x]
    exact div_le_div_of_nonneg_right (by linarith [(tiltedSieveTheta_bounds P Q hs p).1]) (Nat.cast_nonneg p)⟩)
  have hyq := hquad y (fun p h => ⟨(hy p h).1, (roughSieveRate_bounds P p (hp p h)).2.1⟩)
  have hxe := finite_log_product_error S x hx
  have hye := finite_log_product_error S y hy
  have hlin : (∑ p ∈ S, y p) - (∑ p ∈ S, x p) =
      ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q := by
    rw [← sum_sub_distrib]
    unfold tiltPrimeReciprocalMass
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro p h
    by_cases hP : p ≤ P
    · have hn : ¬P < p := by omega
      simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, hP, hn]
    · have hP' : P < p := by omega
      by_cases hQ : p ∈ Q <;>
        simp [x, y, roughSieveRate, roughSieveTheta, tiltedSieveTheta, tiltedPrimeWeight, hP, hP', hQ]
      ring
  have hlog : Real.log (∏ p ∈ S, (1 - x p)) ≤
      Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4 := by
    have hxe' := (abs_le.mp hxe).2
    have hye' := (abs_le.mp hye).1
    linarith
  have hxprod : 0 < ∏ p ∈ S, (1 - x p) :=
    prod_pos (fun p h => by linarith [(hx p h).2])
  have hyprod : 0 < ∏ p ∈ S, (1 - y p) :=
    prod_pos (fun p h => by linarith [(hy p h).2])
  calc
    _ = Real.exp (Real.log (∏ p ∈ S, (1 - x p))) := (Real.exp_log hxprod).symm
    _ ≤ Real.exp (Real.log (∏ p ∈ S, (1 - y p)) +
        ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass P Z Q + 4) := Real.exp_le_exp.mpr hlog
    _ = _ := by rw [add_assoc, Real.exp_add, Real.exp_log hyprod]; rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The single-form sieve, with the same actual tilted weights -/

namespace JointDickman

open Finset

theorem single_form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ) (u v Z : ℕ),
      u ≤ v → 2 ≤ Z → (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 ≤ p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico u v, ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p)) ≤
        C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) + 2 * (Z + 1 : ℝ) * Z := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve_polynomial hFord hM (by norm_num : 0 < (1 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ u v Z huv hZ hP hθ
  have hb := hbound P (fun _ => {0}) θ u v Z huv hZ
    (fun p hp => by simpa using hP p hp) (fun _ _ => by simp) hθ
  have heq (n : ℕ) : (∏ p ∈ rootEvents P (fun _ => {0}) n, θ p) =
      ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) := by
    simp only [rootEvents, prod_filter, mem_singleton, residueWeight]
    congr!
  simp_rw [heq] at hb
  have hfactor (p : ℕ) : 1 - 1 / (p : ℝ) + 1 / p * θ p = 1 - (1 - θ p) / p := by ring
  simpa only [card_singleton, Nat.cast_one, pow_one, hfactor] using hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The combined normalizer and sieve density for an addition product -/

namespace JointDickman

open Finset

theorem quarterOdds_bounds {p : ℕ} (hp : 2 ≤ p) : 0 ≤ quarterOdds p ∧ quarterOdds p ≤ 1 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hfrac : (1 / 4 : ℝ) / p ≤ 1 / 8 := by
    apply (div_le_iff₀ hp0).mpr
    linarith only [hp2]
  have hden : 0 < 1 - (1 / 4 : ℝ) / p := by linarith only [hfrac]
  exact ⟨div_nonneg (by norm_num) hden.le, (div_le_one hden).mpr (by linarith only [hfrac])⟩

theorem additionSieveTheta_bounds (P : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ additionSieveTheta P p ∧ additionSieveTheta P p ≤ 1 := by
  unfold additionSieveTheta
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact quarterOdds_bounds hp

theorem additionSieve_local_bound (P : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    (if P < p then 1 - (1 / 4 : ℝ) / p else 1) *
        (1 - (1 - additionSieveTheta P p) / p) ≤
      (1 - 1 / (p : ℝ)) * Real.exp (1 / (p : ℝ)^2) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith only [hp2]
  have hrec : 1 / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith only [hp2])
  have hbase : 0 ≤ 1 - 1 / (p : ℝ) := by linarith only [hrec]
  have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 / (p : ℝ)^2)) hbase
  by_cases hP : p ≤ P
  · simp only [additionSieveTheta, hP, ite_true, if_true, Nat.not_lt.mpr hP, ite_false, if_false, sub_zero]
    have hsq : 0 ≤ (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)^2) := mul_nonneg hbase (by positivity)
    nlinarith only [hexp, hsq]
  · have hden : 1 - (1 / 4 : ℝ) / p ≠ 0 := by
      have hh : (1 / 4 : ℝ) / p ≤ 1 / 8 := (div_le_iff₀ hp0).mpr (by linarith only [hp2])
      linarith only [hh]
    have heq : (1 - (1 / 4 : ℝ) / p) * (1 - (1 - quarterOdds p) / p) =
        (1 - 1 / (p : ℝ)) + (1 / 4 : ℝ) * (1 / (p : ℝ)^2) := by
      have hden' : -1 + (p : ℝ) * 4 ≠ 0 := by linarith only [hp2]
      unfold quarterOdds
      field_simp [hden']
      linear_combination (p : ℝ) * mul_inv_cancel₀ hden'
    simp only [additionSieveTheta, hP, ite_false, if_false, Nat.lt_of_not_ge hP, ite_true, if_true, heq]
    have hcoef : (1 / 4 : ℝ) * (1 / (p : ℝ)^2) ≤
        (1 - 1 / (p : ℝ)) * (1 / (p : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (by linarith only [hrec]) (by positivity)
    nlinarith only [hexp, hcoef]

theorem additionSieve_normalizer_bound (P Z : ℕ) :
    primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) * additionSieveDensity P Z ≤
      Real.exp 1 * ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) := by
  classical
  have hprime : ∀ p ∈ Nat.primesLE Z, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hbase : 0 ≤ ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
  calc
    _ = ∏ p ∈ Nat.primesLE Z,
        (if P < p then 1 - (1 / 4 : ℝ) / p else 1) *
          (1 - (1 - additionSieveTheta P p) / p) := by
      rw [primeNormalizer, prod_filter, additionSieveDensity, prod_mul_distrib]
    _ ≤ ∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ)) * Real.exp (1 / (p : ℝ)^2) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hθ := additionSieveTheta_bounds P (hprime p hp).two_le
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
        have hfrac : (1 - additionSieveTheta P p) / p ≤ 1 :=
          (div_le_one hp0).mpr (by linarith only [hθ.1, hp1])
        apply mul_nonneg _ (sub_nonneg.mpr hfrac)
        split_ifs
        · have hh : (1 / 4 : ℝ) / p ≤ 1 := (div_le_one hp0).mpr (by linarith only [hp1])
          exact sub_nonneg.mpr hh
        · exact zero_le_one
      · intro p hp
        exact additionSieve_local_bound P (hprime p hp).two_le
    _ = (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) *
        Real.exp (∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)^2) := by rw [prod_mul_distrib, Real.exp_sum]
    _ ≤ _ := by
      rw [mul_comm (Real.exp 1)]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hbase
      simpa using sum_reciprocal_square_tail (Nat.primesLE Z) (by norm_num : (1 : ℕ) ≠ 0)
        (fun p hp => (hprime p hp).one_lt)

theorem prime_roughness_product_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℕ, 2 ≤ Z →
      (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) * Real.log Z ≤ K := by
  obtain ⟨M, A, hA, hMertens⟩ := hM
  refine ⟨Real.exp (-M + A / Real.log 2), Real.exp_pos _, ?_⟩
  intro Z hZ
  have hZ2 : (2 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hlog : 0 < Real.log Z := Real.log_pos (by linarith only [hZ2])
  have hm := (abs_le.mp (hMertens Z hZ2)).1
  rw [Nat.floor_natCast, ← primesLE_eq_filter] at hm
  have herror := div_le_div_of_nonneg_left hA (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (Real.log_le_log (by norm_num) hZ2)
  have hp : (∏ p ∈ Nat.primesLE Z, (1 - 1 / (p : ℝ))) ≤
      Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
      exact sub_nonneg.mpr ((div_le_one hp0).mpr hp1)
    · intro p _
      exact Real.one_sub_le_exp_neg _
  calc
    _ ≤ Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ))) * Real.log Z :=
      mul_le_mul_of_nonneg_right hp hlog.le
    _ = Real.exp (-(∑ p ∈ Nat.primesLE Z, 1 / (p : ℝ)) + Real.log (Real.log Z)) := by
      rw [Real.exp_add, Real.exp_log hlog]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hm, herror])

theorem additionSieve_density_log_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ P Z : ℕ, 2 ≤ Z →
      primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) *
        additionSieveDensity P Z * Real.log Z ≤ K := by
  obtain ⟨K, hK, hb⟩ := prime_roughness_product_log_bound hM
  refine ⟨Real.exp 1 * K, mul_pos (Real.exp_pos _) hK, ?_⟩
  intro P Z hZ
  have hl : 0 ≤ Real.log Z := Real.log_natCast_nonneg Z
  have hh := mul_le_mul_of_nonneg_right (additionSieve_normalizer_bound P Z) hl
  have hh' := mul_le_mul_of_nonneg_left (hb Z hZ) (Real.exp_pos 1).le
  nlinarith only [hh, hh']

theorem additionSieveDensity_nonneg (P Z : ℕ) : 0 ≤ additionSieveDensity P Z := by
  apply prod_nonneg
  intro p hp
  have hθ := additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le
  exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith only [hθ.1, hp1]))

theorem quarterNormalizer_le_prefix {Q : Finset ℕ} {P Z : ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (hsub : (Nat.primesLE Z).filter (fun p => P < p) ⊆ Q) :
    primeNormalizer Q (1 / 4) ≤
      primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) := by
  apply prod_le_prod_of_subset_of_le_one hsub
  · intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).one_le
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith only [hp1]))
  · intro p hp _
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hf : (0 : ℝ) ≤ (1 / 4 : ℝ) / p := div_nonneg (by norm_num) hp0
    linarith only [hf]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sieve majorants for the actual quarter-density product law -/

namespace JointDickman

open Finset

theorem additionSieveWeight_nonneg (P Z n : ℕ) : 0 ≤ additionSieveWeight P Z n := by
  apply prod_nonneg
  intro p hp
  exact residueWeight_nonneg _ _ (additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le).1

theorem quarter_primeProductMass_at_product {Q S : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime) (hS : S ⊆ Q) :
    primeProductMass Q (1 / 4) (∏ p ∈ S, p) =
      primeNormalizer Q (1 / 4) * (∏ p ∈ S, quarterOdds p) / (∏ p ∈ S, p : ℕ) := by
  have hden : ∀ p ∈ Q, 1 - (1 / 4 : ℝ) / p ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hQ p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hh : (1 / 4 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith only [hp2])
    linarith only [hh]
  rw [primeProductMass_exact (1 / 4) hQ hS hden]
  have hfactor (p : ℕ) : ((1 / 4 : ℝ) / p) / (1 - (1 / 4 : ℝ) / p) = quarterOdds p / p := by
    unfold quarterOdds
    ring
  simp_rw [hfactor]
  rw [prod_div_distrib, ← Nat.cast_prod]
  unfold primeNormalizer
  ring

theorem quarter_product_weight_le_sieve {Q S : Finset ℕ} (P Z : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hS : S ⊆ Q) (hrough : ∀ p ∈ Q, P < p) :
    (∏ p ∈ S, quarterOdds p) ≤ additionSieveWeight P Z (∏ p ∈ S, p) := by
  classical
  let n := ∏ p ∈ S, p
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hQ p (hS hp)
  have hn : n ≠ 0 := prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  have hpf : n.primeFactors = S := Nat.primeFactors_prod hprime
  have heq (p : ℕ) (hp : p ∈ Nat.primesLE Z) :
      residueWeight (additionSieveTheta P p) 0 (n : ZMod p) =
        if p ∈ S then quarterOdds p else 1 := by
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hdiv : p ∣ n ↔ p ∈ S := by
      rw [← hpf, Nat.mem_primeFactors]
      simp only [hpp, hn, and_true, true_and, ne_eq, not_false_eq_true]
    by_cases hpS : p ∈ S
    · have hpP : ¬p ≤ P := Nat.not_le.mpr (hrough p (hS hpS))
      simp [residueWeight, ZMod.natCast_eq_zero_iff, hdiv, hpS, additionSieveTheta, hpP]
    · simp [residueWeight, ZMod.natCast_eq_zero_iff, hdiv, hpS]
  have hsubset : (Nat.primesLE Z).filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hprod := prod_le_prod_of_subset_of_le_one hsubset
    (fun p hp => (quarterOdds_bounds (hprime p hp).two_le).1)
    (fun p hp _ => (quarterOdds_bounds (hprime p hp).two_le).2)
  unfold additionSieveWeight
  change _ ≤ ∏ p ∈ Nat.primesLE Z, residueWeight (additionSieveTheta P p) 0 (n : ZMod p)
  rw [prod_congr rfl heq]
  rw [← prod_filter]
  exact hprod

theorem quarter_primeProductMass_le_sieve {Q : Finset ℕ} (P Z n : ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hrough : ∀ p ∈ Q, P < p) :
    primeProductMass Q (1 / 4) n ≤
      primeNormalizer Q (1 / 4) / n * additionSieveWeight P Z n := by
  classical
  by_cases hs : n ∈ Q.powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hS, rfl⟩ := mem_image.mp hs
    have hSQ := mem_powerset.mp hS
    rw [quarter_primeProductMass_at_product hQ hSQ]
    have hQ0 := (primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) ≤ 1)).1
    calc
      _ = (primeNormalizer Q (1 / 4) / (∏ p ∈ S, p : ℕ)) * (∏ p ∈ S, quarterOdds p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quarter_product_weight_le_sieve P Z hQ hSQ hrough)
        (div_nonneg hQ0 (Nat.cast_nonneg _))
  · rw [primeProductMass_eq_zero (1 / 4) n hs]
    exact mul_nonneg (div_nonneg
      (primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)).1
      (Nat.cast_nonneg n)) (additionSieveWeight_nonneg P Z n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionIntervalSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform interval bounds for an addition product -/

namespace JointDickman

open Finset

/-- The quarter-product probability on an interval is controlled by its
relative length and the explicit sieve remainder, uniformly in the upper
prime cutoff. -/
theorem addition_product_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P Z u v : ℕ) (Q : Finset ℕ) (X : ℝ),
      u ≤ v → 2 ≤ Z → 0 < X →
      (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, P < p) →
      (Nat.primesLE Z).filter (fun p => P < p) ⊆ Q →
      (∀ n ∈ Ico u v, X ≤ (n : ℝ)) →
      (∑ n ∈ Ico u v, primeProductMass Q (1 / 4) n) ≤
        K * (((v : ℝ) - u) / (X * Real.log Z)) + 2 * (Z + 1 : ℝ) * Z / X := by
  obtain ⟨C, hC, hsieve⟩ := single_form_interval_sieve hFord hM
  obtain ⟨D, hD, hdensity⟩ := additionSieve_density_log_bound hM
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro P Z u v Q X huv hZ hX hQ hrough hprefix hlow
  have hZ1 : (1 : ℝ) < Z := by exact_mod_cast (by omega : 1 < Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ1
  have hq := primeNormalizer_bounds Q hQ (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hlen : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hw := hsieve (Nat.primesLE Z) (additionSieveTheta P) u v Z huv hZ
    (fun p hp => ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1,
      (Nat.mem_primesLE.mp hp).2.two_le⟩)
    (fun p hp => additionSieveTheta_bounds P (Nat.mem_primesLE.mp hp).2.two_le)
  change (∑ n ∈ Ico u v, additionSieveWeight P Z n) ≤
    C * ((v : ℝ) - u) * additionSieveDensity P Z + 2 * (Z + 1 : ℝ) * Z at hw
  have hqD : primeNormalizer Q (1 / 4) * additionSieveDensity P Z ≤ D / Real.log Z := by
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ primeNormalizer ((Nat.primesLE Z).filter (fun p => P < p)) (1 / 4) *
          additionSieveDensity P Z * Real.log Z := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (quarterNormalizer_le_prefix hQ hprefix)
            (additionSieveDensity_nonneg P Z)) hlog.le
      _ ≤ D := hdensity P Z hZ
  have hsum : (∑ n ∈ Ico u v, primeProductMass Q (1 / 4) n) ≤
      (primeNormalizer Q (1 / 4) / X) * ∑ n ∈ Ico u v, additionSieveWeight P Z n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    apply (quarter_primeProductMass_le_sieve P Z n hQ hrough).trans
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hq.1 hX (hlow n hn)) (additionSieveWeight_nonneg P Z n)
  calc
    _ ≤ _ := hsum
    _ ≤ (primeNormalizer Q (1 / 4) / X) *
        (C * ((v : ℝ) - u) * additionSieveDensity P Z + 2 * (Z + 1 : ℝ) * Z) :=
      mul_le_mul_of_nonneg_left hw (div_nonneg hq.1 hX.le)
    _ = (C * ((v : ℝ) - u) * (primeNormalizer Q (1 / 4) * additionSieveDensity P Z) +
        primeNormalizer Q (1 / 4) * (2 * (Z + 1 : ℝ) * Z)) / X := by ring
    _ ≤ (C * ((v : ℝ) - u) * (D / Real.log Z) + 2 * (Z + 1 : ℝ) * Z) / X := by
      apply div_le_div_of_nonneg_right _ hX.le
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hqD (mul_nonneg hC.le hlen)
      · exact mul_le_of_le_one_left (by positivity) hq.2
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionSmallBall
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform small-ball bounds for the addition product -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Any logarithmic interval of bounded length above Y/2 carries O(1/Y)
quarter-product mass. The prime set may extend above or below the interval;
only its containing the fixed sieve range is needed. -/
theorem addition_product_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in atTop, ∀ (P : ℕ) (Q : Finset ℕ) (v : ℝ),
      Y / 2 ≤ v → (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, P < p) →
      (Nat.primesLE (additionSieveCutoff Y)).filter (fun p => P < p) ⊆ Q →
      (∑ n ∈ Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊, primeProductMass Q (1 / 4) n) ≤ K / Y := by
  obtain ⟨K, hK, hsieve⟩ := addition_product_interval_sieve hFord hM
  refine ⟨200 * K * (Real.exp H + 1) + 1, by positivity, ?_⟩
  filter_upwards [additionSieveCutoff_eventually] with Y hscale
  intro P Q v hv hQ hrough hprefix
  have hY : 0 < Y := hscale.1
  have hZ := hscale.2.1
  have hlog := hscale.2.2.1
  have hrem := hscale.2.2.2.2
  have hlog0 : 0 < Real.log (additionSieveCutoff Y) := (by positivity : 0 < Y / 200).trans_le hlog
  have hv0 : 0 ≤ v := (by positivity : 0 ≤ Y / 2).trans hv
  have hX : 0 < Real.exp v := Real.exp_pos v
  have hX1 : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv0
  have huv : ⌈Real.exp v⌉₊ ≤ ⌊Real.exp (v + H)⌋₊ + 1 := by
    apply Nat.ceil_le.mpr
    have hh : Real.exp v ≤ Real.exp (v + H) := Real.exp_le_exp.mpr (by linarith only [hH])
    have hf := Nat.lt_floor_add_one (Real.exp (v + H))
    exact hh.trans (by exact_mod_cast hf.le)
  have hlow : ∀ n ∈ Ico ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1), Real.exp v ≤ (n : ℝ) := by
    intro n hn
    exact (Nat.le_ceil (Real.exp v)).trans (by exact_mod_cast (mem_Ico.mp hn).1)
  have hbound := hsieve P (additionSieveCutoff Y) ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1)
    Q (Real.exp v) huv hZ hX hQ hrough hprefix hlow
  have hlen : ((⌊Real.exp (v + H)⌋₊ + 1 : ℕ) : ℝ) - ⌈Real.exp v⌉₊ ≤
      (Real.exp H + 1) * Real.exp v := by
    have hf := Nat.floor_le (Real.exp_pos (v + H)).le
    have hc := Nat.le_ceil (Real.exp v)
    rw [Real.exp_add] at hf
    push_cast
    rw [Real.exp_add]
    nlinarith only [hf, hc, hX1]
  have hfrac : (((⌊Real.exp (v + H)⌋₊ + 1 : ℕ) : ℝ) - ⌈Real.exp v⌉₊) /
      (Real.exp v * Real.log (additionSieveCutoff Y)) ≤ 200 * (Real.exp H + 1) / Y := by
    calc
      _ ≤ ((Real.exp H + 1) * Real.exp v) / (Real.exp v * Real.log (additionSieveCutoff Y)) :=
        div_le_div_of_nonneg_right hlen (mul_nonneg hX.le hlog0.le)
      _ = (Real.exp H + 1) / Real.log (additionSieveCutoff Y) := by field_simp
      _ ≤ _ := by
        apply (div_le_div_iff₀ hlog0 hY).mpr
        have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 200 * (Real.exp H + 1))
        nlinarith only [hh]
  have hrem' : 2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y / Real.exp v ≤ 1 / Y := by
    apply (div_le_div_iff₀ hX hY).mpr
    simpa only [one_mul] using hrem.trans (Real.exp_le_exp.mpr hv)
  have hI : Ico ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1) =
      Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊ := by
    ext n
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hI] at hbound
  calc
    _ ≤ _ := hbound
    _ ≤ K * (200 * (Real.exp H + 1) / Y) + 1 / Y :=
      add_le_add (mul_le_mul_of_nonneg_left hfrac hK.le) hrem'
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact splitting of independent prime choices into two ranges -/

namespace JointDickman

open Finset

theorem bernoulliSubsetMass_union {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q)
    (q : α → ℝ) :
    bernoulliSubsetMass (P ∪ Q) q (A ∪ D) =
      bernoulliSubsetMass P q A * bernoulliSubsetMass Q q D := by
  classical
  have had : Disjoint A D := hd.mono hA hD
  have hdiff : (P ∪ Q) \ (A ∪ D) = (P \ A) ∪ (Q \ D) := by
    ext p
    simp only [mem_sdiff, mem_union]
    have hAP := @hA p
    have hDQ := @hD p
    have hn : ¬(p ∈ P ∧ p ∈ Q) := fun h => disjoint_left.mp hd h.1 h.2
    tauto
  have hdd : Disjoint (P \ A) (Q \ D) := hd.mono sdiff_subset sdiff_subset
  unfold bernoulliSubsetMass
  rw [hdiff, prod_union had, prod_union hdd]
  ring

/-- Arbitrary tests factor exactly after splitting the prime range. -/
theorem bernoulliSubsetMass_partition_sum {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) q S * F S) =
      ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset,
        bernoulliSubsetMass P q A * bernoulliSubsetMass Q q D * F (A ∪ D) := by
  classical
  have he := (subsetPartitionEquiv P Q hd).symm.sum_comp
    (fun S : (P ∪ Q).powerset => bernoulliSubsetMass (P ∪ Q) q S.val * F S.val)
  rw [Fintype.sum_prod_type] at he
  calc
    _ = ∑ S : (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) q S.val * F S.val :=
      (sum_coe_sort _ _).symm
    _ = ∑ A : P.powerset, ∑ D : Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A.val ∪ D.val) * F (A.val ∪ D.val) := he.symm
    _ = ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A ∪ D) * F (A ∪ D) := by
      exact (sum_coe_sort P.powerset (fun A => ∑ D : Q.powerset,
        bernoulliSubsetMass (P ∪ Q) q (A ∪ D.val) * F (A ∪ D.val))).trans
        (sum_congr rfl (fun A _ => sum_coe_sort Q.powerset
          (fun D => bernoulliSubsetMass (P ∪ Q) q (A ∪ D) * F (A ∪ D))))
    _ = _ := by
      apply sum_congr rfl
      intro A hA
      apply sum_congr rfl
      intro D hD
      rw [bernoulliSubsetMass_union hd (mem_powerset.mp hA) (mem_powerset.mp hD)]

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

theorem fairRetentionBitMass_marginal (q : ℝ) (b : Bool) :
    (∑ hit, bernoulliBitMass q hit * fairRetentionBitMass hit b) = bernoulliBitMass (q / 2) b := by
  cases b <;> simp [fairRetentionBitMass, bernoulliBitMass] <;> ring

theorem fairRetentionMass_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (y : ι → Bool) :
    (∑ x, bernoulliSiteMass q x * fairRetentionMass x y) =
      bernoulliSiteMass (fun i => q i / 2) y := by
  classical
  simp only [bernoulliSiteMass, fairRetentionMass, finiteProductMass, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i hit => bernoulliBitMass (q i) hit *
    fairRetentionBitMass hit (y i))]
  simp_rw [fairRetentionBitMass_marginal]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThinningRanges
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factoring the remaining-set and second-coin law by prime range -/

namespace JointDickman

open Finset

theorem sum_powerset_partition {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, F S) = ∑ A ∈ P.powerset, ∑ D ∈ Q.powerset, F (A ∪ D) := by
  classical
  have he := (subsetPartitionEquiv P Q hd).symm.sum_comp (fun S : (P ∪ Q).powerset => F S.val)
  rw [Fintype.sum_prod_type] at he
  calc
    _ = ∑ S : (P ∪ Q).powerset, F S.val := (sum_coe_sort _ _).symm
    _ = ∑ A : P.powerset, ∑ D : Q.powerset, F (A.val ∪ D.val) := he.symm
    _ = _ := (sum_coe_sort P.powerset (fun A => ∑ D : Q.powerset, F (A ∪ D.val))).trans
      (sum_congr rfl (fun A _ => sum_coe_sort Q.powerset (fun D => F (A ∪ D))))

theorem subsetRetentionMass_union {α : Type*} [DecidableEq α]
    {P Q S R U V : Finset α} (hd : Disjoint P Q)
    (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) (hV : V ⊆ Q) :
    subsetRetentionMass (S ∪ R) (U ∪ V) = subsetRetentionMass S U * subsetRetentionMass R V := by
  classical
  have hu : U ∪ V ⊆ S ∪ R ↔ U ⊆ S ∧ V ⊆ R := by
    constructor
    · intro h
      constructor
      · intro p hp
        rcases mem_union.mp (h (mem_union_left V hp)) with hs | hr
        · exact hs
        · exact False.elim (disjoint_left.mp hd (hU hp) (hR hr))
      · intro p hp
        rcases mem_union.mp (h (mem_union_right U hp)) with hs | hr
        · exact False.elim (disjoint_left.mp hd (hS hs) (hV hp))
        · exact hr
    · rintro ⟨hu, hv⟩
      exact union_subset_union hu hv
  have hc := card_union_of_disjoint (hd.mono hS hR)
  by_cases hus : U ⊆ S <;> by_cases hvr : V ⊆ R <;>
    simp [subsetRetentionMass, hu, hus, hvr, hc, pow_add]

theorem jointRetentionMass_union {α : Type*} [DecidableEq α]
    {P Q S R U V : Finset α} (hd : Disjoint P Q)
    (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) (hV : V ⊆ Q) (q : α → ℝ) :
    jointRetentionMass (P ∪ Q) q (S ∪ R) (U ∪ V) =
      jointRetentionMass P q S U * jointRetentionMass Q q R V := by
  unfold jointRetentionMass
  rw [bernoulliSubsetMass_union hd hS hR, subsetRetentionMass_union hd hS hR hU hV]
  ring

/-- The joint law factors before imposing any event. This keeps the order
of high-prime exposure and low-prime averaging explicit. -/
theorem jointRetentionMass_partition {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (F : Finset α → Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
      jointRetentionMass (P ∪ Q) q S T * F S T) =
      ∑ S ∈ P.powerset, ∑ R ∈ Q.powerset, ∑ U ∈ P.powerset, ∑ V ∈ Q.powerset,
        jointRetentionMass P q S U * jointRetentionMass Q q R V * F (S ∪ R) (U ∪ V) := by
  rw [sum_powerset_partition P Q hd]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro R hR
  rw [sum_powerset_partition P Q hd]
  apply sum_congr rfl
  intro U hU
  apply sum_congr rfl
  intro V hV
  rw [jointRetentionMass_union hd (mem_powerset.mp hS) (mem_powerset.mp hR)
    (mem_powerset.mp hU) (mem_powerset.mp hV)]

open Classical in
/-- A lower bound on the number of exposed remaining primes bounds the
chance that none of their fair second coins adds a prime. -/
theorem remaining_high_no_addition_bound {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (k : ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if k ≤ (S.card : ℝ) then jointRetentionMass P q S ∅ else 0) ≤
      (1 / 2 : ℝ)^k := by
  have hpow {n : ℕ} (hn : k ≤ (n : ℝ)) : (1 / 2 : ℝ)^n ≤ (1 / 2 : ℝ)^k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hn
  calc
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * (1 / 2 : ℝ)^k := by
      apply sum_le_sum
      intro S hS
      have hm := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
      split_ifs with hs
      · unfold jointRetentionMass subsetRetentionMass
        simp only [empty_subset, ite_true, if_true]
        exact mul_le_mul_of_nonneg_left (hpow hs) hm
      · exact mul_nonneg hm (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_HighLowThinning
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging high second coins after the low addition product -/

namespace JointDickman

open Finset

theorem partition_union_inter_left {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q) :
    (A ∪ D) ∩ P = A := by
  ext p
  have ha := @hA p
  have hn : p ∈ D → p ∉ P := fun hp hpp => disjoint_left.mp hd hpp (hD hp)
  simp only [mem_inter, mem_union]
  tauto

theorem partition_union_inter_right {α : Type*} [DecidableEq α]
    {P Q A D : Finset α} (hd : Disjoint P Q) (hA : A ⊆ P) (hD : D ⊆ Q) :
    (A ∪ D) ∩ Q = D := by
  rw [union_comm]
  exact partition_union_inter_left hd.symm hD hA

open Classical in
/-- The high tail restriction and no high additions leave the low addition
law unchanged. In particular, this identity does not condition high second
coins on the low-ratio event. -/
theorem high_low_thinning_factor {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (q : α → ℝ) (k : ℝ) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, ∑ T ∈ (P ∪ Q).powerset,
      jointRetentionMass (P ∪ Q) q S T *
        (if k ≤ ((S ∩ Q).card : ℝ) ∧ T ∩ Q = ∅ then F (T ∩ P) else 0)) =
      highNoAdditionMass Q q k *
        (∑ U ∈ P.powerset, bernoulliSubsetMass P (fun p => q p / 2) U * F U) := by
  classical
  rw [jointRetentionMass_partition P Q hd]
  have hinner (S R U : Finset α) (hS : S ⊆ P) (hR : R ⊆ Q) (hU : U ⊆ P) :
      (∑ V ∈ Q.powerset, jointRetentionMass P q S U * jointRetentionMass Q q R V *
        (if k ≤ (((S ∪ R) ∩ Q).card : ℝ) ∧ (U ∪ V) ∩ Q = ∅ then F ((U ∪ V) ∩ P) else 0)) =
      jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U := by
    have heq (V : Finset α) (hV : V ∈ Q.powerset) :
        jointRetentionMass P q S U * jointRetentionMass Q q R V *
          (if k ≤ (((S ∪ R) ∩ Q).card : ℝ) ∧ (U ∪ V) ∩ Q = ∅ then F ((U ∪ V) ∩ P) else 0) =
        if V = ∅ then
          jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U
        else 0 := by
      rw [partition_union_inter_right hd hS hR,
        partition_union_inter_right hd hU (mem_powerset.mp hV),
        partition_union_inter_left hd hU (mem_powerset.mp hV)]
      by_cases hv : V = ∅ <;> by_cases hk : k ≤ (R.card : ℝ) <;> simp [hv, hk]
    rw [sum_congr rfl heq]
    simp only [sum_ite_eq', empty_mem_powerset, ite_true, if_true]
  calc
    _ = ∑ S ∈ P.powerset, ∑ R ∈ Q.powerset, ∑ U ∈ P.powerset,
        jointRetentionMass P q S U * (if k ≤ (R.card : ℝ) then jointRetentionMass Q q R ∅ else 0) * F U := by
      apply sum_congr rfl
      intro S hS
      apply sum_congr rfl
      intro R hR
      apply sum_congr rfl
      intro U hU
      exact hinner S R U (mem_powerset.mp hS) (mem_powerset.mp hR) (mem_powerset.mp hU)
    _ = highNoAdditionMass Q q k *
        (∑ S ∈ P.powerset, ∑ U ∈ P.powerset, jointRetentionMass P q S U * F U) := by
      unfold highNoAdditionMass
      rw [sum_comm]
      rw [sum_mul]
      apply sum_congr rfl
      intro R _
      simp only [mul_sum]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro U _
      ring
    _ = _ := by
      congr 1
      simpa only [jointRetentionMass, ← mul_sum, mul_assoc] using subsetRetentionMass_expectation P q F


open Classical in
/-- The coefficient's high primes are all kept. Low coefficient coins
retain their original independent fair law. -/
theorem fixed_high_retention_factor {α : Type*} [DecidableEq α]
    (P Q : Finset α) (hd : Disjoint P Q) (F : Finset α → ℝ) :
    (∑ S ∈ (P ∪ Q).powerset, bernoulliSubsetMass (P ∪ Q) (fun _ => (1 / 2 : ℝ)) S *
      (if S ∩ Q = Q then F (S ∩ P) else 0)) =
      (1 / 2 : ℝ)^Q.card * (∑ A ∈ P.powerset, bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A * F A) := by
  classical
  rw [bernoulliSubsetMass_partition_sum P Q hd]
  have hi (A : Finset α) (hA : A ⊆ P) :
      (∑ D ∈ Q.powerset,
        bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) D *
            (if (A ∪ D) ∩ Q = Q then F ((A ∪ D) ∩ P) else 0)) =
      (1 / 2 : ℝ)^Q.card * (bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A * F A) := by
    have he (D : Finset α) (hD : D ∈ Q.powerset) :
        bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) D *
            (if (A ∪ D) ∩ Q = Q then F ((A ∪ D) ∩ P) else 0) =
        if D = Q then bernoulliSubsetMass P (fun _ => (1 / 2 : ℝ)) A *
          bernoulliSubsetMass Q (fun _ => (1 / 2 : ℝ)) Q * F A else 0 := by
      rw [partition_union_inter_right hd hA (mem_powerset.mp hD),
        partition_union_inter_left hd hA (mem_powerset.mp hD)]
      split_ifs with h
      · rw [h]
      · exact mul_zero _
    rw [sum_congr rfl he]
    simp only [sum_ite_eq', mem_powerset.mpr (Subset.refl Q), ite_true, if_true,
      bernoulliSubsetMass_half (Subset.refl Q)]
    ring
  rw [sum_congr rfl (fun A hA => hi A (mem_powerset.mp hA)), mul_sum]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeRangeOperators
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The high-prime restrictions as finite averaging operators -/

namespace JointDickman

open Finset

theorem keptHighAverage_eq (P Q : Finset ℕ) (hd : Disjoint P Q) (F : Finset ℕ → ℝ) :
    keptHighAverage P Q F = (1 / 2 : ℝ)^Q.card * subsetAverage P (fun _ => 1 / 2) F :=
  fixed_high_retention_factor P Q hd F

theorem noHighAdditionAverage_eq (P Q : Finset ℕ) (hd : Disjoint P Q)
    (q : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → ℝ) :
    noHighAdditionAverage P Q q k F = highNoAdditionMass Q q k *
      subsetAverage P (fun p => q p / 2) F := high_low_thinning_factor P Q hd q k F

theorem subsetAverage_const_mul (P : Finset ℕ) (q : ℕ → ℝ) (c : ℝ) (F : Finset ℕ → ℝ) :
    subsetAverage P q (fun S => c * F S) = c * subsetAverage P q F := by
  unfold subsetAverage
  rw [mul_sum]
  apply sum_congr rfl
  intro S _
  ring

theorem subsetAverage_le_const (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (F : Finset ℕ → ℝ) (K : ℝ)
    (hF : ∀ S ⊆ P, F S ≤ K) : subsetAverage P q F ≤ K := by
  calc
    _ ≤ ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * K :=
      sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left (hF S (mem_powerset.mp hS))
        (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq))
    _ = K := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

theorem highNoAdditionMass_nonneg (Q : Finset ℕ) (q : ℕ → ℝ) (k : ℝ)
    (hq : ∀ p ∈ Q, 0 ≤ q p ∧ q p ≤ 1) : 0 ≤ highNoAdditionMass Q q k := by
  unfold highNoAdditionMass
  apply sum_nonneg
  intro S hS
  split_ifs
  · unfold jointRetentionMass subsetRetentionMass
    simp only [empty_subset, ite_true, if_true]
    exact mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq) (by positivity)
  · exact le_rfl

/-- Keeping both coefficients' high parts is averaged only after a uniform
bound for the two low coefficient choices has been established. -/
theorem keptHighAverage_pair_bound (P Q R S : Finset ℕ) (hPQ : Disjoint P Q)
    (hRS : Disjoint R S) (F : Finset ℕ → Finset ℕ → ℝ) (K : ℝ)
    (hF : ∀ A ⊆ P, ∀ D ⊆ R, F A D ≤ K) :
    keptHighAverage P Q (fun A => keptHighAverage R S (F A)) ≤
      (1 / 2 : ℝ)^Q.card * (1 / 2 : ℝ)^S.card * K := by
  rw [keptHighAverage_eq P Q hPQ]
  have hi (A : Finset ℕ) (hA : A ⊆ P) : keptHighAverage R S (F A) ≤ (1 / 2 : ℝ)^S.card * K := by
    rw [keptHighAverage_eq R S hRS]
    exact mul_le_mul_of_nonneg_left
      (subsetAverage_le_const R (fun _ => 1 / 2) (by intros; norm_num) (F A) K (hF A hA)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (subsetAverage_le_const P (fun _ => 1 / 2) (by intros; norm_num) _ _ hi)
    (show (0 : ℝ) ≤ (1 / 2 : ℝ)^Q.card by positivity)
  convert hh using 1 <;> first | rfl | ring

/-- The two remaining processes factor into the high no-change mass and
exactly their two independent low addition laws. -/
theorem noHighAdditionAverage_pair_eq (P Q : Finset ℕ) (hd : Disjoint P Q)
    (q r : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → Finset ℕ → ℝ) :
    noHighAdditionAverage P Q r k (fun V => noHighAdditionAverage P Q q k (fun U => F U V)) =
      highNoAdditionMass Q r k * highNoAdditionMass Q q k *
        subsetAverage P (fun p => r p / 2) (fun V => subsetAverage P (fun p => q p / 2) (fun U => F U V)) := by
  rw [noHighAdditionAverage_eq P Q hd]
  simp_rw [noHighAdditionAverage_eq P Q hd]
  rw [subsetAverage_const_mul]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ManuscriptAdditionProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's actual addition-prime process -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem additionPrimes_prime (B : ℕ) (Y : ℝ) : ∀ p ∈ additionPrimes B Y, p.Prime := by
  intro p hp
  exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2

theorem additionPrimes_rough (B : ℕ) (Y : ℝ) :
    ∀ p ∈ additionPrimes B Y, auxiliaryCutoff B < p := by
  intro p hp
  exact_mod_cast (mem_filter.mp hp).2

theorem additionPrimes_contains_cutoff {B : ℕ} {Y : ℝ} (hY : 0 ≤ Y) (hYB : Y ≤ 8 * B) :
    (Nat.primesLE (additionSieveCutoff Y)).filter (fun p => auxiliaryCutoff B < p) ⊆ additionPrimes B Y := by
  intro p hp
  obtain ⟨hpZ, hpP⟩ := mem_filter.mp hp
  have hscale : Y / 100 ≤ min Y (4 * B) := le_min (by linarith only [hY]) (by linarith only [hYB, hY])
  have hZ : (additionSieveCutoff Y : ℝ) ≤ Real.exp (min Y (4 * B)) :=
    (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr hscale)
  have hpp : (p : ℝ) ≤ Real.exp (min Y (4 * B)) :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hpZ).1 : (p : ℝ) ≤ additionSieveCutoff Y).trans hZ
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpp, (Nat.mem_primesLE.mp hpZ).2⟩, ?_⟩
  exact_mod_cast hpP

theorem manuscript_addition_interval_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y v : ℝ,
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → Y / 2 ≤ v →
      (∑ n ∈ Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊,
        primeProductMass (additionPrimes B Y) (1 / 4) n) ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := addition_product_small_ball hFord hM hH
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hbound
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlog.eventually_ge_atTop Y₀, hlog.eventually_ge_atTop 0] with B hb hb0
  intro Y v hY hYB hv
  exact hY₀ Y (hb.trans hY) (auxiliaryCutoff B) (additionPrimes B Y) v hv
    (additionPrimes_prime B Y) (additionPrimes_rough B Y)
    (additionPrimes_contains_cutoff (hb0.trans hY) hYB)

theorem additionLogIntervalMass_le_integer_interval (B : ℕ) (Y v H : ℝ) :
    additionLogIntervalMass B Y v H ≤
      ∑ n ∈ Icc ⌈Real.exp (max v (Y / 2))⌉₊ ⌊Real.exp (max v (Y / 2) + H)⌋₊,
        primeProductMass (additionPrimes B Y) (1 / 4) n := by
  classical
  rw [primeProductMass_sum_event]
  unfold additionLogIntervalMass
  apply sum_le_sum
  intro S hS
  have hSP := mem_powerset.mp hS
  have hn : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (additionPrimes_prime B Y p (hSP hp)).pos)
  have hw : 0 ≤ bernoulliSubsetMass (additionPrimes B Y) (fun p => (1 / 4 : ℝ) / p) S := by
    apply bernoulliSubsetMass_nonneg hSP
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (additionPrimes_prime B Y p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  by_cases hlog : v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧
      Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧ Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ)
  · have hlower : Real.exp (max v (Y / 2)) ≤ (∏ p ∈ S, p : ℕ) := by
      rw [← Real.exp_log hn]
      exact Real.exp_le_exp.mpr (max_le hlog.1 hlog.2.2)
    have hupper : (∏ p ∈ S, p : ℕ) ≤ Real.exp (max v (Y / 2) + H) := by
      rw [← Real.exp_log hn]
      exact Real.exp_le_exp.mpr (hlog.2.1.trans (add_le_add (le_max_left _ _) le_rfl))
    have hmem : (∏ p ∈ S, p) ∈ Icc ⌈Real.exp (max v (Y / 2))⌉₊
        ⌊Real.exp (max v (Y / 2) + H)⌋₊ :=
      mem_Icc.mpr ⟨Nat.ceil_le.mpr hlower, Nat.le_floor hupper⟩
    simp only [hlog, hmem, and_self, ite_true, if_true, le_refl]
  · simp only [hlog, ite_false, if_false]
    split_ifs <;> first | exact hw | exact le_rfl

/-- Manuscript Lemma `amp-small-ball`, for the actual independent
Bernoulli(1/(4p)) addition product and every translated interval. -/
theorem manuscript_addition_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y v : ℝ,
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B →
      additionLogIntervalMass B Y v H ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := manuscript_addition_interval_bound hFord hM hH
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro Y v hY hYB
  exact (additionLogIntervalMass_le_integer_interval B Y v H).trans
    (hb Y (max v (Y / 2)) hY hYB (le_max_right _ _))

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

theorem inverseSelectedPrimeOdds_le {P z : ℝ} (hP : 0 < P)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hcut : ∀ p ∈ S, P ≤ p) :
    (∏ p ∈ S, (1 - z / (p : ℝ))⁻¹) ≤ Real.exp (2 * (S.card : ℝ) / P) := by
  have hx (p : ℕ) (hp : p ∈ S) : 0 ≤ z / (p : ℝ) ∧ z / (p : ℝ) ≤ 1 / 2 := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hS p hp).pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    exact ⟨div_nonneg hz hp0.le, (div_le_iff₀ hp0).mpr (by linarith)⟩
  have hsum : (∑ p ∈ S, z / (p : ℝ)) ≤ (S.card : ℝ) / P := by
    calc
      _ ≤ ∑ _p ∈ S, 1 / P := sum_le_sum (fun p hp => by
        have hp0 : (0 : ℝ) < p := hP.trans_le (hcut p hp)
        exact (div_le_div_of_nonneg_right hz1 hp0.le).trans
          (one_div_le_one_div_of_le hP (hcut p hp)))
      _ = _ := by simp [div_eq_mul_inv]
  exact (inverse_product_le_exp S (fun p => z / (p : ℝ)) hx).trans
    (Real.exp_le_exp.mpr (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)))

theorem bernoulliSubsetMass_eq_uncorrected_odds {P S : Finset ℕ} (q : ℕ → ℝ)
    (hS : S ⊆ P) (hq : ∀ p ∈ S, 1 - q p ≠ 0) :
    bernoulliSubsetMass P q S =
      uncorrectedSubsetMass P q S * ∏ p ∈ S, (1 - q p)⁻¹ := by
  rw [uncorrectedSubsetMass_identity q hS, prod_inv_distrib, mul_assoc,
    mul_inv_cancel₀ (prod_ne_zero_iff.mpr hq), mul_one]

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

theorem primeNormalizer_coefficientScale_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      primeNormalizer (auxiliaryPrimes B) (1 / 2) ≤ C * coefficientScale B / B := by
  let C : ℝ := (4 : ℝ) ^ (-(1 / 2 : ℝ)) + 1
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  have ht := auxiliary_primeNormalizer_tendsto hM (z := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (4 : ℝ) ^ (-(1 / 2 : ℝ)) < C by
      dsimp [C] <;> linarith)), eventually_gt_atTop 1] with B hQ hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  apply (le_div_iff₀ hB0).mpr
  calc
    _ = (primeNormalizer (auxiliaryPrimes B) (1 / 2) * auxiliaryRatio B ^ (1 / 2 : ℝ)) *
        coefficientScale B := by rw [mul_right_comm, mul_assoc, coefficientScale_mul_sqrt_ratio hB]
    _ ≤ C * coefficientScale B :=
      mul_le_mul_of_nonneg_right hQ.le (coefficientScale_nonneg B)

theorem auxiliary_selected_odds_bound :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      (∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹) ≤ Real.exp 1 := by
  have ht : Tendsto (fun B : ℕ => (32 / (5 * Real.log 2)) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (32 / (5 * Real.log 2))
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hcut : ∀ p ∈ S, (auxiliaryCutoff B : ℝ) ≤ p := by
    intro p hp
    exact (mem_filter.mp (hS hp)).2.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ (16 / 5 : ℝ) * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  apply (inverseSelectedPrimeOdds_le hP (by norm_num) (by norm_num) S hprime hcut).trans
  apply Real.exp_le_exp.mpr
  calc
    2 * (S.card : ℝ) / auxiliaryCutoff B ≤
        2 * ((16 / 5 : ℝ) * B / Real.log 2) / auxiliaryCutoff B := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hP.le
    _ = (32 / (5 * Real.log 2)) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AuxiliaryLogarithms
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic scales for the regularity grid -/

namespace JointDickman

open Filter
open scoped Topology

theorem log_auxiliaryCutoff (B : ℕ) :
    Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
  simp [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DyadicTailSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the lower-tail Chernoff bounds over dyadic endpoints -/

namespace JointDickman

open Finset

theorem geometric_sum_under_cap (S : Finset ℕ) {r w : ℝ}
    (hr : 1 < r) (hw : 0 ≤ w) (hcap : ∀ i ∈ S, w * r ^ i ≤ 1) :
    (∑ i ∈ S, w * r ^ i) ≤ r / (r - 1) := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.max' hS
    have hm : m ∈ S := S.max'_mem hS
    have hsub : S ⊆ range (m + 1) := by
      intro i hi
      exact mem_range.mpr (Nat.lt_succ_of_le (S.le_max' i hi))
    have hsum : (∑ i ∈ range (m + 1), w * r ^ i) * (r - 1) = w * (r ^ (m + 1) - 1) := by
      rw [← mul_sum, mul_assoc, geom_sum_mul]
    have hlast := hcap m hm
    calc
      _ ≤ ∑ i ∈ range (m + 1), w * r ^ i := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ r / (r - 1) := by
        apply (le_div_iff₀ (sub_pos.mpr hr)).mpr
        rw [hsum, pow_succ]
        have h := mul_le_mul_of_nonneg_right hlast (by linarith : 0 ≤ r)
        nlinarith
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    simp only [he, sum_empty]
    positivity

theorem dyadic_power_sum_bound (S : Finset ℕ) {B Y a : ℝ}
    (hB : 0 < B) (hY : 0 ≤ Y) (ha : 0 < a)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ a) ≤
      (2 : ℝ) ^ a / ((2 : ℝ) ^ a - 1) := by
  have heq (i : ℕ) : (((2 : ℝ) ^ i * Y) / B) ^ a =
      (Y / B) ^ a * ((2 : ℝ) ^ a) ^ i := by
    rw [mul_div_assoc, Real.mul_rpow (by positivity) (div_nonneg hY hB.le),
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  simp_rw [heq]
  apply geometric_sum_under_cap S (Real.one_lt_rpow (by norm_num) ha) (Real.rpow_nonneg (div_nonneg hY hB.le) _)
  intro i hi
  rw [← heq]
  have hle : ((2 : ℝ) ^ i * Y) / B ≤ 1 := (div_le_one hB).mpr (hcap i hi)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ i * Y) / B) hle ha.le
  simpa only [Real.one_rpow] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ConditionalPrimeParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual remaining-prime parameters after a coefficient is selected -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem remainingPrimeParameter_mem_Icc (S : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold remainingPrimeParameter
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · refine ⟨div_nonneg (by norm_num) (by linarith), ?_⟩
    exact (div_le_one (by linarith : 0 < 2 * (p : ℝ) - 1)).mpr (by linarith)

theorem unselected_parameter_error {p : ℕ} (hp : 2 ≤ p) :
    |1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p| ≤ 1 / (p : ℝ)^2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : 0 < 2 * (p : ℝ) - 1 := by linarith
  have heq : 1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p =
      1 / (2 * (p : ℝ) * (2 * p - 1)) := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (p : ℝ)^2)
  nlinarith only [hp']

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionalAdditionProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Addition products after fixing the first coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem conditionalAdditionParameter_bounds (A : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    0 ≤ conditionalAdditionParameter A p ∧ conditionalAdditionParameter A p ≤ 1 := by
  obtain ⟨h0, h1⟩ := remainingPrimeParameter_mem_Icc A hp
  unfold conditionalAdditionParameter
  constructor <;> linarith only [h0, h1]

theorem conditionalAdditionParameter_error (A : Finset ℕ) {p : ℕ} (hp : 2 ≤ p) :
    |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p| ≤
      1 / (p : ℝ)^2 + if p ∈ A then 1 / (p : ℝ) else 0 := by
  classical
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
  by_cases ha : p ∈ A
  · simp only [conditionalAdditionParameter, remainingPrimeParameter, ha, ite_true, if_true, zero_div,
      zero_sub, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) / p)]
    have hd : (1 / 4 : ℝ) / p ≤ 1 / (p : ℝ) := div_le_div_of_nonneg_right (by norm_num) hpR.le
    linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]
  · have heq : conditionalAdditionParameter A p - (1 / 4 : ℝ) / p =
        (1 / (2 * (p : ℝ) - 1) - (1 / 2 : ℝ) / p) / 2 := by
      simp only [conditionalAdditionParameter, remainingPrimeParameter, ha, ite_false, if_false]
      ring
    rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have he := unselected_parameter_error hp
    simp only [ha, ite_false, if_false, add_zero]
    linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]

theorem selected_reciprocal_bound {B : ℕ} {A : Finset ℕ} {κ : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B)
    (hsize : (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B)) :
    (∑ p ∈ A, 1 / (p : ℝ)) ≤ (κ / Real.log 2) * (B : ℝ) / auxiliaryCutoff B := by
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ A, p.Prime := fun p hp => auxiliaryPrimes_prime B p (hA hp)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (A.card : ℝ) ≤ κ * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound A hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ A, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hsize
  calc
    _ ≤ ∑ _p ∈ A, 1 / (auxiliaryCutoff B : ℝ) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hP0 (mem_filter.mp (hA hp)).2.le)
    _ = (A.card : ℝ) / auxiliaryCutoff B := by simp [div_eq_mul_inv]
    _ ≤ (κ * B / Real.log 2) / auxiliaryCutoff B := div_le_div_of_nonneg_right hcard hP0.le
    _ = _ := by ring

theorem conditionalAdditionParameter_total_error {B : ℕ} {A P : Finset ℕ} {κ : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (hP : P ⊆ auxiliaryPrimes B)
    (hsize : (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B)) :
    (∑ p ∈ P, |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p|) ≤
      (1 + (κ / Real.log 2) * B) / auxiliaryCutoff B := by
  classical
  have hP0 : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (Nat.ne_of_gt (Nat.zero_lt_of_lt hB))
  have hsq := sum_reciprocal_square_tail P hP0 (fun p hp => by
    exact_mod_cast (mem_filter.mp (hP hp)).2)
  have hsum := sum_le_sum (fun p hp => conditionalAdditionParameter_error A
    (auxiliaryPrimes_prime B p (hP hp)).two_le)
  have hsub : P.filter (fun p => p ∈ A) ⊆ A := fun p hp => (mem_filter.mp hp).2
  have hsel : (∑ p ∈ P, if p ∈ A then 1 / (p : ℝ) else 0) ≤
      (κ / Real.log 2) * B / auxiliaryCutoff B := by
    rw [← sum_filter]
    exact (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
      (selected_reciprocal_bound hB hA hsize)
  rw [sum_add_distrib] at hsum
  calc
    _ ≤ (∑ p ∈ P, 1 / (p : ℝ)^2) + (∑ p ∈ P, if p ∈ A then 1 / (p : ℝ) else 0) := hsum
    _ ≤ 1 / (auxiliaryCutoff B : ℝ) + (κ / Real.log 2) * B / auxiliaryCutoff B :=
      add_le_add hsq hsel
    _ = _ := by ring

open Classical in
theorem bernoulliSubsetMass_event_perturb {α : Type*} [DecidableEq α]
    (P : Finset α) (q r : α → ℝ) (E : Finset α → Prop)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1) :
    (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) ≤
      (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P r S else 0) +
        2 * ∑ p ∈ P, |q p - r p| := by
  classical
  have hh : (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P q S else 0) -
      (∑ S ∈ P.powerset, if E S then bernoulliSubsetMass P r S else 0) ≤
        ∑ S ∈ P.powerset, |bernoulliSubsetMass P q S - bernoulliSubsetMass P r S| := by
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro S _
    split_ifs
    · exact le_abs_self _
    · simpa only [sub_self] using abs_nonneg (bernoulliSubsetMass P q S - bernoulliSubsetMass P r S)
  have hl := bernoulliSubsetMass_l1_perturb P q r hq hr
  linarith only [hh, hl]


theorem additionPrimes_subset_auxiliary (B : ℕ) (Y : ℝ) :
    additionPrimes B Y ⊆ auxiliaryPrimes B := by
  intro p hp
  obtain ⟨hpp, hrough⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨?_, (Nat.mem_primesLE.mp hpp).2⟩, hrough⟩
  exact (Nat.mem_primesLE.mp hpp).1.trans
    (Nat.floor_mono (Real.exp_le_exp.mpr (min_le_right Y (4 * (B : ℝ)))))

theorem conditionalAddition_error_small (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, 0 < (B : ℝ) ∧
      2 * ((1 + (κ / Real.log 2) * B) / auxiliaryCutoff B) ≤ 1 / (8 * B) := by
  have h1 := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul 16
  have h2 := ((polynomial_div_primeCutoff_tendsto_zero (k := 2) (by norm_num)).comp
    tendsto_natCast_atTop_atTop).const_mul (16 * (κ / Real.log 2))
  have ht : Tendsto (fun B : ℕ =>
      (16 * (B : ℝ) * (1 + (κ / Real.log 2) * B)) / auxiliaryCutoff B)
      atTop (𝓝 0) := by
    convert h1.add h2 using 1
    · ext B
      simp only [auxiliaryCutoff, Nat.cast_pow, pow_one, Function.comp_def]
      ring
    · simp only [mul_zero, add_zero]
  filter_upwards [ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hb hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  refine ⟨hB0, ?_⟩
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * B)).mpr
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- The small-ball estimate survives conditioning on any first coefficient
in the required fixed exponential range. The changed parameters and omitted
coefficient primes are accounted for explicitly. -/
theorem conditional_addition_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H κ : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A : Finset ℕ) (Y v : ℝ),
      A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B →
      conditionalAdditionLogIntervalMass B A Y v H ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := manuscript_addition_small_ball hFord hM hH
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  filter_upwards [hbound, conditionalAddition_error_small κ, hlog.eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hb he hlogB hB
  intro A Y v hA hsize hY hYB
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one (hlogB.trans hY)
  have hP := additionPrimes_subset_auxiliary B Y
  have hq : ∀ p ∈ additionPrimes B Y, 0 ≤ conditionalAdditionParameter A p ∧
      conditionalAdditionParameter A p ≤ 1 :=
    fun p hp => conditionalAdditionParameter_bounds A (additionPrimes_prime B Y p hp).two_le
  have hr : ∀ p ∈ additionPrimes B Y, 0 ≤ (1 / 4 : ℝ) / p ∧ (1 / 4 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (additionPrimes_prime B Y p hp).two_le
    refine ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hh := bernoulliSubsetMass_event_perturb (additionPrimes B Y)
    (conditionalAdditionParameter A) (fun p => (1 / 4 : ℝ) / p)
    (fun S => v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
      Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ)) hq hr
  have hh' : conditionalAdditionLogIntervalMass B A Y v H ≤ additionLogIntervalMass B Y v H +
      2 * ∑ p ∈ additionPrimes B Y, |conditionalAdditionParameter A p - (1 / 4 : ℝ) / p| := by
    simpa only [conditionalAdditionLogIntervalMass, additionLogIntervalMass, Nat.cast_prod] using hh
  have herr := conditionalAdditionParameter_total_error hB hA hP hsize
  have htail : 1 / (8 * (B : ℝ)) ≤ 1 / Y := one_div_le_one_div_of_le hY0 hYB
  have hmain := hb Y v hY hYB
  have herr2 := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)
  have hc : K / Y + 1 / Y = (K + 1) / Y := by ring
  rw [← hc]
  linarith only [hh', herr2, he.2, htail, hmain]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_AdditionRatioWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Solving the second ratio condition for either addition product -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem ratio_log_bounds {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T)
    (hlo : T * c ≤ a) (hhi : a ≤ 2 * (T * c)) :
    0 ≤ Real.log a - Real.log T - Real.log c ∧
      Real.log a - Real.log T - Real.log c ≤ Real.log 2 := by
  have hl := Real.log_le_log (mul_pos hT hc) hlo
  have hu := Real.log_le_log ha hhi
  rw [Real.log_mul hT.ne' hc.ne'] at hl
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_pos hT hc).ne',
    Real.log_mul hT.ne' hc.ne'] at hu
  constructor <;> linarith only [hl, hu]

theorem first_addition_log_window {a c T u v : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) (hu : 0 < u) (hv : 0 < v)
    (hlo : T * (c * v) ≤ a * u) (hhi : a * u ≤ 2 * (T * (c * v))) :
    let t := Real.log T + Real.log c + Real.log v - Real.log a
    t ≤ Real.log u ∧ Real.log u ≤ t + Real.log 2 := by
  obtain ⟨hl, hh⟩ := ratio_log_bounds (mul_pos ha hu) (mul_pos hc hv) hT hlo hhi
  rw [Real.log_mul ha.ne' hu.ne', Real.log_mul hc.ne' hv.ne'] at hl hh
  dsimp only
  constructor <;> linarith only [hl, hh]

/-- Uniformly in both retained coefficient products, an oriented second-ratio
event has conditional mass O(1/Y). -/
theorem first_addition_ratio_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (Y T a c : ℝ),
      A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → 0 < T → 0 < a → 0 < c →
      firstAdditionRatioMass B A D Y T a c ≤ K / Y := by
  classical
  obtain ⟨K, hK, hbound⟩ := conditional_addition_small_ball hFord hM
    (κ := κ) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro A D Y T a c hA hsize hY hYB hT ha hc
  have hmass (E : Finset ℕ) (hE : E ⊆ additionPrimes B Y) (F : Finset ℕ) :
      0 ≤ bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter F) E :=
    bernoulliSubsetMass_nonneg hE (fun p hp =>
      conditionalAdditionParameter_bounds F (additionPrimes_prime B Y p hp).two_le)
  have hp (E : Finset ℕ) (hE : E ⊆ additionPrimes B Y) : (0 : ℝ) < (∏ p ∈ E, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hpe => (additionPrimes_prime B Y p (hE hpe)).pos)
  unfold firstAdditionRatioMass
  calc
    _ ≤ ∑ V ∈ (additionPrimes B Y).powerset,
        bernoulliSubsetMass (additionPrimes B Y) (conditionalAdditionParameter D) V * (K / Y) := by
      apply sum_le_sum
      intro V hV
      apply mul_le_mul_of_nonneg_left _ (hmass V (mem_powerset.mp hV) D)
      let t := Real.log T + Real.log c + Real.log (∏ p ∈ V, p : ℕ) - Real.log a
      refine le_trans ?_ (hb A Y t hA hsize hY hYB)
      unfold conditionalAdditionLogIntervalMass
      apply sum_le_sum
      intro U hU
      have hU0 := hp U (mem_powerset.mp hU)
      have hV0 := hp V (mem_powerset.mp hV)
      split_ifs with he hwindow
      · exact le_rfl
      · obtain ⟨hl, hh⟩ := first_addition_log_window ha hc hT hU0 hV0 he.1 he.2.1
        exact False.elim (hwindow ⟨hl, hh, he.2.2⟩)
      · exact hmass U (mem_powerset.mp hU) A
      · exact le_rfl
    _ = K / Y := by rw [← sum_mul, bernoulliSubsetMass_sum, one_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationScaleSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The convergent scale sum in the amplification second moment -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem amplification_scale_sum (S : Finset ℕ) {B L : ℝ}
    (hB : 0 < B) (hL : 0 < L)
    (hcap : ∀ i ∈ S, (2 : ℝ)^i * L ≤ 8 * B) :
    (∑ i ∈ S, (((2 : ℝ)^i * L) / B)^amplificationExponent / ((2 : ℝ)^i * L)) ≤
      ((8 : ℝ)^(amplificationExponent - 1) *
        ((2 : ℝ)^(amplificationExponent - 1) /
          ((2 : ℝ)^(amplificationExponent - 1) - 1))) / B := by
  have ha : 0 < amplificationExponent - 1 := sub_pos.mpr amplificationExponent_gt_one
  have heq (i : ℕ) :
      (((2 : ℝ)^i * L) / B)^amplificationExponent / ((2 : ℝ)^i * L) =
      (8 : ℝ)^(amplificationExponent - 1) / B *
        (((2 : ℝ)^i * L) / (8 * B))^(amplificationExponent - 1) := by
    have hx : 0 < (2 : ℝ)^i * L := by positivity
    have hratio : ((2 : ℝ)^i * L) / B = 8 * (((2 : ℝ)^i * L) / (8 * B)) := by field_simp
    have hpow : (((2 : ℝ)^i * L) / B)^(amplificationExponent - 1) =
        (8 : ℝ)^(amplificationExponent - 1) *
          (((2 : ℝ)^i * L) / (8 * B))^(amplificationExponent - 1) := by
      rw [hratio, Real.mul_rpow (by norm_num) (by positivity)]
    calc
      _ = (((2 : ℝ)^i * L) / B)^(amplificationExponent - 1) / B := by
        rw [Real.rpow_sub (div_pos hx hB), Real.rpow_one]
        field_simp
      _ = _ := by rw [hpow]; ring
  simp_rw [heq]
  rw [← mul_sum]
  have hsum := dyadic_power_sum_bound S (mul_pos (by norm_num : (0 : ℝ) < 8) hB)
    hL.le ha hcap
  have hh := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0 : ℝ) ≤ (8 : ℝ)^(amplificationExponent - 1) / B)
  convert hh using 1 <;> first | rfl | ring

/-- The no-change contribution, including the outside factor B, tends to zero. -/
theorem amplification_no_change_tendsto :
    Tendsto (fun B : ℕ => (B : ℝ) * (auxiliaryRatio B)^(-amplificationExponent))
      atTop (𝓝 0) := by
  have ht := amplification_log_loss.comp tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryRatio, Real.rpow_neg (by positivity : (0 : ℝ) ≤ B / (1000 * Real.log B)),
    Real.div_rpow hB0.le (by positivity)]
  dsimp only [Function.comp_def]
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AmplificationPrimeRanges
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual low and high prime ranges used by the second split -/

namespace JointDickman

open Finset

theorem additionPrimes_eq_filter (B : ℕ) (Y : ℝ) :
    additionPrimes B Y = (auxiliaryPrimes B).filter (fun p : ℕ => Real.log p ≤ Y) := by
  classical
  ext p
  constructor
  · intro hp
    have haux := additionPrimes_subset_auxiliary B Y hp
    refine mem_filter.mpr ⟨haux, ?_⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (additionPrimes_prime B Y p hp).pos
    apply (Real.log_le_iff_le_exp hp0).mpr
    have hh := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mp hh |>.trans
      (Real.exp_le_exp.mpr (min_le_left _ _))
  · intro hp
    obtain ⟨haux, hlog⟩ := mem_filter.mp hp
    have hprime := auxiliaryPrimes_prime B p haux
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hu : (p : ℝ) ≤ Real.exp (4 * (B : ℝ)) := by
      exact (Nat.le_floor_iff (Real.exp_pos _).le).mp
        (Nat.mem_primesLE.mp (mem_filter.mp haux).1).1
    have hy : (p : ℝ) ≤ Real.exp Y := (Real.log_le_iff_le_exp hp0).mp hlog
    have hmin : (p : ℝ) ≤ Real.exp (min Y (4 * B)) := by
      rcases le_total Y (4 * (B : ℝ)) with h | h
      · simpa only [min_eq_left h] using hy
      · simpa only [min_eq_right h] using hu
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hmin, hprime⟩, (mem_filter.mp haux).2⟩

theorem additionPrimeRanges_disjoint (B : ℕ) (Y : ℝ) :
    Disjoint (additionPrimes B Y) (upperAdditionPrimes B Y) := disjoint_sdiff_self_right

theorem additionPrimeRanges_union (B : ℕ) (Y : ℝ) :
    additionPrimes B Y ∪ upperAdditionPrimes B Y = auxiliaryPrimes B :=
  union_sdiff_of_subset (additionPrimes_subset_auxiliary B Y)

theorem selected_upperAdditionPrimes {B : ℕ} {Y : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) : A ∩ upperAdditionPrimes B Y = highPrimePart Y A := by
  classical
  ext p
  simp only [upperAdditionPrimes, additionPrimes_eq_filter, mem_inter, mem_sdiff,
    mem_filter, highPrimePart]
  constructor
  · rintro ⟨ha, _, hn⟩
    exact ⟨ha, lt_of_not_ge (fun h => hn ⟨hA ha, h⟩)⟩
  · rintro ⟨ha, hh⟩
    exact ⟨ha, hA ha, fun h => not_le_of_gt hh h.2⟩

theorem selected_additionPrimeRanges_union {B : ℕ} {Y : ℝ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    (A ∩ additionPrimes B Y) ∪ (A ∩ upperAdditionPrimes B Y) = A := by
  rw [← inter_union_distrib_left, additionPrimeRanges_union, inter_eq_left.mpr hA]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_OrientedSplitBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One oriented change interval in the actual conditional split law -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem additionRatioTest_average (B : ℕ) (A D : Finset ℕ) (Y T a c : ℝ) :
    subsetAverage (additionPrimes B Y) (conditionalAdditionParameter D) (fun V =>
      subsetAverage (additionPrimes B Y) (conditionalAdditionParameter A)
        (fun U => additionRatioTest Y T a c U V)) = firstAdditionRatioMass B A D Y T a c := by
  classical
  unfold subsetAverage firstAdditionRatioMass additionRatioTest
  apply sum_congr rfl
  intro V _
  congr 1
  apply sum_congr rfl
  intro U _
  simp only [mul_ite, mul_one, mul_zero]

/-- The no-high-change probability and the low ratio probability multiply
in the exact conditional law. This statement retains the actual high masses. -/
theorem oriented_split_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (A D : Finset ℕ) (Y C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      0 < Y → Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → 0 < T →
      orientedSplitMass B A D Y C T ≤
        (1 / 2 : ℝ)^(A ∩ upperAdditionPrimes B Y).card *
        (1 / 2 : ℝ)^(D ∩ upperAdditionPrimes B Y).card *
        (highNoAdditionMass (upperAdditionPrimes B Y) (remainingPrimeParameter D)
          ((2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C) *
        highNoAdditionMass (upperAdditionPrimes B Y) (remainingPrimeParameter A)
          ((2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C) * (K / Y)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := first_addition_ratio_bound hFord hM κ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro A D Y C T hA hD hsize hY0 hY hYB hT
  let P := additionPrimes B Y
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  have hd : Disjoint P Q := additionPrimeRanges_disjoint B Y
  have hQA : ∀ p ∈ Q, 0 ≤ remainingPrimeParameter A p ∧ remainingPrimeParameter A p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc A (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hQD : ∀ p ∈ Q, 0 ≤ remainingPrimeParameter D p ∧ remainingPrimeParameter D p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc D (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hnonneg : 0 ≤ highNoAdditionMass Q (remainingPrimeParameter D) k *
      highNoAdditionMass Q (remainingPrimeParameter A) k :=
    mul_nonneg (highNoAdditionMass_nonneg Q _ k hQD) (highNoAdditionMass_nonneg Q _ k hQA)
  unfold orientedSplitMass
  apply keptHighAverage_pair_bound _ _ _ _ (hd.mono inter_subset_right inter_subset_right)
    (hd.mono inter_subset_right inter_subset_right)
  intro I hI J hJ
  have hIaux : I ∪ (A ∩ Q) ⊆ auxiliaryPrimes B :=
    union_subset (fun p hp => hA (mem_inter.mp (hI hp)).1) (fun p hp => hA (mem_inter.mp hp).1)
  have hJaux : J ∪ (D ∩ Q) ⊆ auxiliaryPrimes B :=
    union_subset (fun p hp => hD (mem_inter.mp (hJ hp)).1) (fun p hp => hD (mem_inter.mp hp).1)
  have ha : (0 : ℝ) < (∏ p ∈ I ∪ (A ∩ Q), p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hIaux hp)).pos)
  have hc : (0 : ℝ) < (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hJaux hp)).pos)
  rw [noHighAdditionAverage_pair_eq P Q hd]
  change highNoAdditionMass Q (remainingPrimeParameter D) k *
      highNoAdditionMass Q (remainingPrimeParameter A) k *
        subsetAverage P (conditionalAdditionParameter D) (fun V =>
          subsetAverage P (conditionalAdditionParameter A) (fun U =>
            additionRatioTest Y T (∏ p ∈ I ∪ (A ∩ Q), p : ℕ)
              (∏ p ∈ J ∪ (D ∩ Q), p : ℕ) U V)) ≤ _
  rw [additionRatioTest_average]
  exact mul_le_mul_of_nonneg_left
    (hb A D Y T _ _ hA hsize hY hYB hT ha hc) hnonneg

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_OrientedSplitExpansion
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditional oriented operator as one explicit finite event sum -/

namespace JointDickman

open Finset

private theorem ite_sum_zero_p1 {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
    (f : ι → ℝ) : (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]

open Classical in
theorem orientedSplitMass_expansion (B : ℕ) (A D : Finset ℕ) (Y C T : ℝ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    let P := additionPrimes B Y
    let H := upperAdditionPrimes B Y
    let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
    orientedSplitMass B A D Y C T =
      ∑ I ∈ A.powerset, ∑ J ∈ D.powerset,
      ∑ Q ∈ (auxiliaryPrimes B).powerset, ∑ V ∈ (auxiliaryPrimes B).powerset,
      ∑ R ∈ (auxiliaryPrimes B).powerset, ∑ U ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass A (fun _ => (1 / 2 : ℝ)) I *
        bernoulliSubsetMass D (fun _ => (1 / 2 : ℝ)) J *
        jointRetentionMass (auxiliaryPrimes B) (remainingPrimeParameter D) Q V *
        jointRetentionMass (auxiliaryPrimes B) (remainingPrimeParameter A) R U *
        (if (I ∩ (A ∩ H) = A ∩ H) ∧ (J ∩ (D ∩ H) = D ∩ H) ∧
            (k ≤ ((Q ∩ H).card : ℝ) ∧ V ∩ H = ∅) ∧ (k ≤ ((R ∩ H).card : ℝ) ∧ U ∩ H = ∅) then
          additionRatioTest Y T (∏ p ∈ (I ∩ (A ∩ P)) ∪ (A ∩ H), p : ℕ)
            (∏ p ∈ (J ∩ (D ∩ P)) ∪ (D ∩ H), p : ℕ) (U ∩ P) (V ∩ P) else 0) := by
  dsimp only
  unfold orientedSplitMass keptHighAverage noHighAdditionAverage
  dsimp only
  rw [selected_additionPrimeRanges_union hA, selected_additionPrimeRanges_union hD]
  simp only [additionPrimeRanges_union]
  simp only [ite_sum_zero_p1, mul_sum, mul_ite, mul_zero]
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro V _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro U _
  simp only [← ite_and]
  split_ifs <;> ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SingleCoefficientTilt
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential count moments for one actual coefficient -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_tilted_density_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      coefficientScale B * tiltedSieveDensity (auxiliaryCutoff B) Z Q s ≤
      M * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
  obtain ⟨C, hC, hbound⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨C * Real.exp 4, by positivity, ?_⟩
  intro B Z hB hPZ hlog Q s hs
  calc
    _ ≤ coefficientScale B * (roughSieveDensity (auxiliaryCutoff B) Z *
        Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q + 4)) :=
      mul_le_mul_of_nonneg_left (tilted_sieve_density_bound _ _ Q hs) (coefficientScale_nonneg B)
    _ = (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) *
        Real.exp 4 * Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) := by
      rw [Real.exp_add]; ring
    _ ≤ _ := by gcongr; exact hbound B Z hB hPZ hlog

theorem single_coefficient_exp_moment
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z u v : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z → u ≤ v →
      ∀ (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      (∑ n ∈ Ico u v, tiltedCoefficientWeight B Q s n) ≤
      C * ((v : ℝ) - u) * Real.exp (((Real.exp s - 1) / 2) *
        tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
      coefficientScale B * (2 * (Z + 1 : ℝ) * Z) := by
  obtain ⟨Cs, hCs, hsieve⟩ := single_form_interval_sieve hFord hM
  obtain ⟨M, hMpos, hnorm⟩ := single_tilted_density_normalization hM hδ
  refine ⟨Cs * M, mul_pos hCs hMpos, ?_⟩
  intro B Z u v hB hZ hPZ hlog huv Q s hs
  have hP : ∀ p ∈ sievePrimes Z, p.Prime ∧ p ≤ Z ∧ 2 ≤ p := by
    intro p hp
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    exact ⟨(Nat.mem_primesLE.mp hpZ).2, (Nat.mem_primesLE.mp hpZ).1, by omega⟩
  have hb := hsieve (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q s) u v Z huv hZ hP
    (fun p _ => tiltedSieveTheta_bounds _ Q hs p)
  have hlen : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hmain := mul_le_mul_of_nonneg_left (hnorm B Z hB hPZ hlog Q s hs)
    (mul_nonneg hCs.le hlen)
  calc
    _ ≤ ∑ n ∈ Ico u v, coefficientScale B *
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p) :=
      sum_le_sum (fun n _ => tiltedCoefficientWeight_le_sieved B Z Q hs n)
    _ = coefficientScale B * (∑ n ∈ Ico u v,
        ∏ p ∈ sievePrimes Z, residueWeight (tiltedSieveTheta (auxiliaryCutoff B) Q s p) 0 (n : ZMod p)) :=
      (mul_sum _ _ _).symm
    _ ≤ coefficientScale B * (Cs * ((v : ℝ) - u) *
        tiltedSieveDensity (auxiliaryCutoff B) Z Q s + 2 * (Z + 1 : ℝ) * Z) :=
      mul_le_mul_of_nonneg_left hb (coefficientScale_nonneg B)
    _ ≤ _ := by
      dsimp only [tiltedSieveDensity] at hmain ⊢
      nlinarith only [hmain]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleSieveRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A power saving in the one-coefficient sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem single_coefficient_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ H : ℝ, Real.exp (δ * B) ≤ H →
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤ H / (B : ℝ)^10 := by
  have hlim : Tendsto (fun B : ℕ => 4 * ((B : ℝ)^11 / Real.exp ((3 * δ / 4) * B)))
      atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 11 (by linarith : 0 < 3 * δ / 4)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    coefficientScale_eventually_le, sieveCutoff_eventually (by linarith : 0 < δ / 8),
    eventually_gt_atTop 0] with B hsmall hscale hcut hB
  intro H hH
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hF : 1 ≤ Real.exp ((δ / 8) * B) := Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) hB0.le)
  have hZ0 : (0 : ℝ) ≤ sieveCutoff (δ / 8) B := Nat.cast_nonneg _
  have hZplus : (sieveCutoff (δ / 8) B + 1 : ℝ) ≤ 2 * Real.exp ((δ / 8) * B) := by
    linarith only [hcut.2.2.2, hF]
  have hbound : singleCoefficientRemainder B (sieveCutoff (δ / 8) B) ≤
      4 * (B : ℝ) * Real.exp ((δ / 4) * B) := by
    calc
      _ ≤ (B : ℝ) * (2 * (2 * Real.exp ((δ / 8) * B)) * Real.exp ((δ / 8) * B)) := by
        unfold singleCoefficientRemainder
        apply mul_le_mul hscale _ (by positivity) hB0.le
        gcongr
        exact hcut.2.2.2
      _ = _ := by
        rw [show (δ / 4) * (B : ℝ) = (δ / 8) * B + (δ / 8) * B by ring, Real.exp_add]
        ring
  have hsmall' : 4 * (B : ℝ)^11 ≤ Real.exp ((3 * δ / 4) * B) := by
    apply (div_le_one (Real.exp_pos _)).mp
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have htotal : (4 * (B : ℝ) * Real.exp ((δ / 4) * B)) * (B : ℝ)^10 ≤ Real.exp (δ * B) := by
    calc
      _ = (4 * (B : ℝ)^11) * Real.exp ((δ / 4) * B) := by ring
      _ ≤ Real.exp ((3 * δ / 4) * B) * Real.exp ((δ / 4) * B) :=
        mul_le_mul_of_nonneg_right hsmall' (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (le_div_iff₀ (pow_pos hB0 10)).mpr
  exact ((mul_le_mul_of_nonneg_right hbound (pow_nonneg hB0.le 10)).trans htotal).trans hH

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SingleSieveMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-coefficient mean bound from the published upper sieve -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem single_coefficient_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ u v : ℕ, u ≤ v →
      Real.exp (δ * B) ≤ (v : ℝ) - u →
      (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) := by
  obtain ⟨C, hC, hbound⟩ := single_coefficient_exp_moment hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    single_coefficient_remainder_power hδ, eventually_gt_atTop 1] with B hcut hrem hB
  intro u v huv hlen
  have hb := hbound B (sieveCutoff (δ / 8) B) u v hB hcut.1 hcut.2.1
    (by linarith only [hcut.2.2.1]) huv ∅ 0 (by norm_num)
  have hm : (∑ n ∈ Ico u v, coefficientWeight B n) ≤ C * ((v : ℝ) - u) +
      singleCoefficientRemainder B (sieveCutoff (δ / 8) B) := by
    simpa [tiltedCoefficientWeight, singleCoefficientRemainder] using hb
  have hH : 0 ≤ (v : ℝ) - u := (Real.exp_pos _).le.trans hlen
  have hp : (1 : ℝ) ≤ (B : ℝ)^10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ B))
  have he := (hrem _ hlen).trans (div_le_self hH hp)
  nlinarith only [hm, he]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientDomination
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Manuscript equation (4): domination by the coefficient weight -/

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
/-- The actual prime-product probability is bounded by A₀(n)/(Bn),
uniformly over the full product range needed by the application. -/
theorem primeProductMass_coefficient_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ n : ℕ, 0 < n →
      (n : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) →
      primeProductMass (auxiliaryPrimes B) (1 / 2) n ≤
        C * coefficientWeight B n / ((B : ℝ) * n) := by
  obtain ⟨C, hC, hQ⟩ := primeNormalizer_coefficientScale_bound hM
  refine ⟨Real.exp 1 * C, mul_pos (Real.exp_pos _) hC, ?_⟩
  filter_upwards [hQ, auxiliary_selected_odds_bound, eventually_gt_atTop 1] with B hQB hodds hB
  intro n hn hsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 ≤ roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs <;> positivity
  by_cases hs : n ∈ (auxiliaryPrimes B).powerset.image (fun S => ∏ p ∈ S, p)
  · obtain ⟨S, hSP, hSn⟩ := mem_image.mp hs
    have hS : S ⊆ auxiliaryPrimes B := mem_powerset.mp hSP
    have hprime : ∀ p ∈ auxiliaryPrimes B, p.Prime := by
      intro p hp
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
    have hnonzero : ∀ p ∈ S, 1 - (1 / 2 : ℝ) / p ≠ 0 := by
      intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p (hS hp)).two_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hf : (1 / 2 : ℝ) / p < 1 := (div_lt_one hp0).mpr (by linarith)
      linarith
    have hmass : primeProductMass (auxiliaryPrimes B) (1 / 2) n =
        uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S *
          ∏ p ∈ S, (1 - (1 / 2 : ℝ) / p)⁻¹ := by
      rw [← hSn, primeProductMass_at_product (1 / 2) hprime hS,
        bernoulliSubsetMass_eq_uncorrected_odds _ hS hnonzero]
    have hnU : (n : ℝ) ≤ auxiliaryUpper B := by
      refine hsize.trans (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hunc : uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S =
        primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by
      rw [← uncorrectedPrimeProductMass_at_product (1 / 2) hprime hS, hSn]
      exact uncorrectedPrimeProductMass_harmonic hnU (1 / 2)
    have hunc0 : 0 ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S := by
      unfold uncorrectedSubsetMass
      apply mul_nonneg
      · apply prod_nonneg
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
        have hf : (1 / 2 : ℝ) / p ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        linarith
      · exact prod_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
    rw [hmass]
    calc
      _ ≤ uncorrectedSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) S * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (hodds S hS (by simpa only [hSn] using hsize)) hunc0
      _ = Real.exp 1 * primeNormalizer (auxiliaryPrimes B) (1 / 2) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n := by rw [hunc]; ring
      _ ≤ Real.exp 1 * (C * coefficientScale B / B) *
          roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1 / 2) n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQB (Real.exp_pos _).le) hr) hn0.le
      _ = _ := by unfold coefficientWeight; ring
  · rw [primeProductMass_eq_zero (1 / 2) n hs]
    exact div_nonneg (mul_nonneg (mul_pos (Real.exp_pos _) hC).le (coefficientWeight_nonneg B n))
      (mul_nonneg hB0.le hn0.le)

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

theorem coefficientDyadicBox_disjoint (T : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
  have hforward : ∀ k l : ℕ, k < l →
      Disjoint (coefficientDyadicBox T k) (coefficientDyadicBox T l) := by
    intro k l hlt
    apply disjoint_left.mpr
    intro ac hk hl
    have hkc := mem_Ico.mp (mem_product.mp hk).2
    have hlc := mem_Ico.mp (mem_product.mp hl).2
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hlt
    rw [pow_succ, mul_comm _ 2] at hpow
    omega
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hforward k l h
  · exact (hforward l k h).symm

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

/-- Every box in the cover is long enough for the sieve and remains
inside the coefficient range of the local prime-product law. -/
theorem coefficientDyadicBox_scales :
    ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ, (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      k ∈ Ico B (4 * B) →
      Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) ∧
        (4 * T * (2^k : ℕ) : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  have hexp : ∀ᶠ B : ℕ in atTop, (4 : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) :=
    (Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 10))).eventually_ge_atTop 4
  filter_upwards [hexp, eventually_gt_atTop 0] with B h4 hB
  intro T k hT hk
  have hk' := mem_Ico.mp hk
  have hklo : (B : ℝ) ≤ k := by exact_mod_cast hk'.1
  have hkhi : (k : ℝ) ≤ 4 * B := by exact_mod_cast hk'.2.le
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hlog0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.exp ((1 / 2 : ℝ) * B) ≤ ((2^k : ℕ) : ℝ) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hklo hlog0.le
    nlinarith only [hh, Real.log_two_gt_d9, hB0]
  have hhigh : ((2^k : ℕ) : ℝ) ≤ Real.exp ((14 / 5 : ℝ) * B) := by
    rw [nat_two_pow_exp]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hkhi hlog0.le
    nlinarith only [hh, Real.log_two_lt_d9, hB0]
  refine ⟨hlow, ?_⟩
  calc
    (4 * T * (2^k : ℕ) : ℝ) ≤
        Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((1 / 10 : ℝ) * B) * Real.exp ((14 / 5 : ℝ) * B) := by
      gcongr
    _ = Real.exp (3 * (B : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp ((16 / 5 : ℝ) * B) := Real.exp_le_exp.mpr (by linarith only [hB0])

theorem amplificationCoefficientPairs_size :
    ∀ᶠ B : ℕ in atTop, ∀ T a c : ℕ, 0 < T →
      (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (a, c) ∈ amplificationCoefficientPairs B T →
      (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) ∧
        (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
  classical
  filter_upwards [coefficientDyadicBox_scales] with B hs
  intro T a c hT hTsize hac
  obtain ⟨k, hk, hbox⟩ := mem_biUnion.mp (mem_filter.mp hac).1
  have hscale := (hs T k hTsize hk).2
  obtain ⟨ha, hc⟩ := mem_product.mp hbox
  have ha' : (a : ℝ) ≤ 4 * T * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp ha).2.le
  have hc' : (c : ℝ) ≤ 2 * (2^k : ℕ) := by exact_mod_cast (mem_Ico.mp hc).2.le
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  refine ⟨ha'.trans hscale, hc'.trans (le_trans ?_ hscale)⟩
  have hh := mul_le_mul_of_nonneg_right hT1 (by positivity : (0 : ℝ) ≤ (2^k : ℕ))
  nlinarith only [hh, show (0 : ℝ) ≤ (2^k : ℕ) by positivity]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientEventBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The size-and-ratio event has probability O(1/B) -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryHalfMass_pair_le {B a c : ℕ} {D : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hc : 0 < c) (hD : 0 ≤ D)
    (hma : primeProductMass (auxiliaryPrimes B) (1 / 2) a ≤
      D * coefficientWeight B a / ((B : ℝ) * a))
    (hmc : primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D * coefficientWeight B c / ((B : ℝ) * c)) :
    primeProductMass (auxiliaryPrimes B) (1 / 2) a *
      primeProductMass (auxiliaryPrimes B) (1 / 2) c ≤
      D^2 / ((B : ℝ)^2 * a * c) * (coefficientWeight B a * coefficientWeight B c) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    _ ≤ (D * coefficientWeight B a / ((B : ℝ) * a)) *
        (D * coefficientWeight B c / ((B : ℝ) * c)) :=
      mul_le_mul hma hmc (auxiliaryHalfMass_nonneg B c)
        (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B a)) (mul_nonneg hB0.le ha0.le))
    _ = _ := by field_simp

theorem coefficient_pair_box_mass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T k : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) → k ∈ Ico B (4 * B) →
      (∑ ac ∈ coefficientDyadicBox T k,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K / (B : ℝ)^2 := by
  obtain ⟨D, hD, hdom⟩ := primeProductMass_coefficient_domination hM
  obtain ⟨M, hM0, hmean⟩ := single_coefficient_mean_bound hFord hM (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨3 * D^2 * M^2, by positivity, ?_⟩
  filter_upwards [hdom, hmean, coefficientDyadicBox_scales, eventually_gt_atTop 0]
    with B hd hm hs hB
  intro T k hT hTsize hk
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let X := 2^k
  have hXnat : 0 < X := pow_pos (by norm_num) _
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hXnat
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hscale := hs T k hTsize hk
  have hlen : Real.exp ((1 / 2 : ℝ) * B) ≤ ((4 * T * X : ℕ) : ℝ) - (T * X : ℕ) := by
    push_cast
    nlinarith only [hscale.1, mul_le_mul_of_nonneg_right hT1 hX0.le]
  have hma := hm (T * X) (4 * T * X) (by nlinarith) hlen
  have hmc := hm X (2 * X) (by omega) (by push_cast; linarith only [hscale.1])
  have hcmean : 0 ≤ ∑ c ∈ Ico X (2 * X), coefficientWeight B c :=
    sum_nonneg fun c _ => coefficientWeight_nonneg B c
  have hprod := mul_le_mul hma hmc hcmean
    (mul_nonneg hM0.le (sub_nonneg.mpr (by exact_mod_cast (show T * X ≤ 4 * T * X by nlinarith))))
  have hpair : (∑ ac ∈ coefficientDyadicBox T k,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) := by
    unfold coefficientDyadicBox
    rw [sum_product]
    have hfactor : D^2 / ((B : ℝ)^2 * (T * X) * X) *
        (∑ a ∈ Ico (T * X) (4 * T * X), coefficientWeight B a) *
        (∑ c ∈ Ico X (2 * X), coefficientWeight B c) =
        ∑ a ∈ Ico (T * X) (4 * T * X), ∑ c ∈ Ico X (2 * X),
          D^2 / ((B : ℝ)^2 * (T * X) * X) * (coefficientWeight B a * coefficientWeight B c) := by
      simp only [mul_sum, sum_mul, mul_assoc]
      exact sum_comm
    rw [hfactor]
    apply sum_le_sum
    intro a ha
    apply sum_le_sum
    intro c hc
    have ha' := mem_Ico.mp ha
    have hc' := mem_Ico.mp hc
    have ha0 : 0 < a := lt_of_lt_of_le (Nat.mul_pos hT hXnat) ha'.1
    have hc0 : 0 < c := hXnat.trans_le hc'.1
    have hasize : (a : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) :=
      (by exact_mod_cast ha'.2.le : (a : ℝ) ≤ (4 * T * X : ℝ)).trans hscale.2
    have hcsize : (c : ℝ) ≤ Real.exp ((16 / 5 : ℝ) * B) := by
      have hh : (c : ℝ) ≤ 2 * X := by exact_mod_cast hc'.2.le
      exact hh.trans ((by nlinarith only [mul_le_mul_of_nonneg_right hT1 hX0.le] :
        (2 * X : ℝ) ≤ 4 * T * X).trans hscale.2)
    apply (auxiliaryHalfMass_pair_le hB ha0 hc0 hD.le (hd a ha0 hasize) (hd c hc0 hcsize)).trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (coefficientWeight_nonneg B a) (coefficientWeight_nonneg B c))
    apply div_le_div_of_nonneg_left (sq_nonneg D) (by positivity)
    have haR : (T * X : ℝ) ≤ a := by exact_mod_cast ha'.1
    have hcR : (X : ℝ) ≤ c := by exact_mod_cast hc'.1
    gcongr
  calc
    _ ≤ _ := hpair
    _ ≤ D^2 / ((B : ℝ)^2 * (T * X) * X) *
        ((M * (((4 * T * X : ℕ) : ℝ) - (T * X : ℕ))) *
          (M * (((2 * X : ℕ) : ℝ) - X))) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by
      push_cast
      field_simp
      ring

theorem coefficient_size_ratio_event_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ K := by
  obtain ⟨K, hK, hbound⟩ := coefficient_pair_box_mass_bound hFord hM
  refine ⟨4 * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hsum : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤
      ((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2) := by
    calc
      _ ≤ ∑ ac ∈ coefficientDyadicCover B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ac _ _ => mul_nonneg (auxiliaryHalfMass_nonneg B ac.1) (auxiliaryHalfMass_nonneg B ac.2))
      _ = ∑ k ∈ Ico B (4 * B), ∑ ac ∈ coefficientDyadicBox T k,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
        apply sum_biUnion
        intro k _ l _ hkl
        exact coefficientDyadicBox_disjoint T hkl
      _ ≤ ∑ _k ∈ Ico B (4 * B), K / (B : ℝ)^2 :=
        sum_le_sum fun k hk => hb T k hT hTsize hk
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hcard : ((Ico B (4 * B)).card : ℝ) ≤ 4 * B := by
    exact_mod_cast (show (Ico B (4 * B)).card ≤ 4 * B by rw [Nat.card_Ico]; omega)
  calc
    _ ≤ (B : ℝ) * (((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left hsum hB0.le
    _ ≤ (B : ℝ) * ((4 * B) * (K / (B : ℝ)^2)) := by gcongr
    _ = _ := by field_simp

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

/-- Given the first parts, the second fair split is exactly the independent
retention of coefficient primes and addition of remaining primes. -/
theorem second_split_reindex (A R : Finset ℕ) (hd : Disjoint A R)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ C ∈ (A ∪ R).powerset, subsetRetentionMass (A ∪ R) C * F C ((A ∪ R) \ C)) =
      ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
        subsetRetentionMass A I * subsetRetentionMass R U *
          F (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  rw [sum_powerset_partition A R hd]
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro U hU
  have hIA := mem_powerset.mp hI
  have hUR := mem_powerset.mp hU
  rw [subsetRetentionMass_union hd (Subset.refl A) (Subset.refl R) hIA hUR]
  have hdiff : (A ∪ R) \ (I ∪ U) = (A \ I) ∪ (R \ U) := by
    ext p
    have hi := @hIA p
    have hu := @hUR p
    have hn : ¬(p ∈ A ∧ p ∈ R) := fun h => disjoint_left.mp hd h.1 h.2
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hdiff]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SymmetricSplitLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- First fix the selected coefficient, then sample its actual conditional
remaining set, and finally split each of those two sets by independent fair coins. -/
theorem twoSplitSiteAverage_reindex (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, ∑ R ∈ P.powerset, fairSelectedRemainingMass P A R *
        ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
          subsetRetentionMass A I * subsetRetentionMass R U *
            F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  classical
  unfold twoSplitSiteAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  have hAP := mem_powerset.mp hA
  let H : Finset ℕ → ℝ := fun R => ∑ D ∈ P.powerset,
    subsetRetentionMass (A ∪ R) D * F A R D ((A ∪ R) \ D)
  have hpoint (S : Finset ℕ) :
      (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
        subsetRetentionMass S A * subsetRetentionMass S D * F A (S \ A) D (S \ D)) =
      bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S * subsetRetentionMass S A * H (S \ A) := by
    by_cases hAS : A ⊆ S
    · dsimp [H]
      rw [union_sdiff_of_subset hAS, mul_sum]
      apply sum_congr rfl
      intro D _
      ring
    · simp only [subsetRetentionMass, hAS, ite_false, if_false, mul_zero, zero_mul, sum_const_zero]
  simp_rw [hpoint]
  rw [first_split_reindex P A hAP H]
  apply sum_congr rfl
  intro R hR
  by_cases hd : Disjoint A R
  · have hARP : A ∪ R ⊆ P := union_subset hAP (mem_powerset.mp hR)
    dsimp [H]
    rw [subsetRetentionMass_sum_support hARP]
    rw [second_split_reindex A R hd]
  · simp only [fairSelectedRemainingMass, hd, ite_false, if_false, zero_mul]

/-- The conditional remaining-prime parameters enter by a proved finite
identity; the main two-split law is not assumed. -/
theorem twoSplitSiteAverage_conditional (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
        ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
          ∑ I ∈ A.powerset, ∑ U ∈ R.powerset,
            subsetRetentionMass A I * subsetRetentionMass R U *
              F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  rw [twoSplitSiteAverage_reindex]
  apply sum_congr rfl
  intro A hA
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  rw [fairSelectedRemainingMass_factor hP (mem_powerset.mp hA) (mem_powerset.mp hR)]
  ring

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

theorem twoSiteSplitMass_swap (P : Finset ℕ) (x : TwoSiteSplit P) :
    twoSiteSplitMass P x.swap = twoSiteSplitMass P x := by
  unfold twoSiteSplitMass TwoSiteSplit.swap
  ring

theorem subsetRetentionMass_nonneg (S T : Finset ℕ) : 0 ≤ subsetRetentionMass S T := by
  unfold subsetRetentionMass
  split_ifs <;> positivity

theorem twoSiteSplitMass_nonneg (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : TwoSiteSplit P) :
    0 ≤ twoSiteSplitMass P x := by
  have hq : ∀ p ∈ P, 0 ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  unfold twoSiteSplitMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.site₁.property) hq)
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.site₂.property) hq))
    (subsetRetentionMass_nonneg _ _)) (subsetRetentionMass_nonneg _ _))
    (subsetRetentionMass_nonneg _ _)) (subsetRetentionMass_nonneg _ _)

theorem twoSiteSplitProbability_swap (P : Finset ℕ) (E : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => E x.swap) = twoSiteSplitProbability P E := by
  classical
  unfold twoSiteSplitProbability
  have he := (twoSiteSwapEquiv P).sum_comp (fun x => if E x then twoSiteSplitMass P x else 0)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply sum_congr rfl
  intro x _
  change (if E x.swap then twoSiteSplitMass P x else 0) =
    if E x.swap then twoSiteSplitMass P x.swap else 0
  rw [twoSiteSplitMass_swap]

theorem bothAmplificationSplitsGood_swap (B L T : ℕ) (τ C : ℝ)
    (x : TwoSiteSplit (auxiliaryPrimes B)) :
    bothAmplificationSplitsGood B L T τ C x.swap ↔ bothAmplificationSplitsGood B L T τ C x := by
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_comm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteSplitSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the two-site configuration sum -/

namespace JointDickman

open Finset

theorem twoSiteSplit_sum (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, F x.site₁.val x.first₁.val x.second₁.val x.site₂.val x.first₂.val x.second₂.val) =
      ∑ S ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      ∑ T ∈ P.powerset, ∑ C ∈ P.powerset, ∑ E ∈ P.powerset, F S A D T C E := by
  classical
  have he := (twoSiteCoordinates P).symm.sum_comp
    (fun x => F x.site₁.val x.first₁.val x.second₁.val x.site₂.val x.first₂.val x.second₂.val)
  simp only [twoSiteCoordinates, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type] at he
  have h3 (G : Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
      (∑ A : P.powerset, ∑ D : P.powerset, ∑ E : P.powerset, G A.val D.val E.val) =
        ∑ A ∈ P.powerset, ∑ D ∈ P.powerset, ∑ E ∈ P.powerset, G A D E := by
    calc
      _ = ∑ A ∈ P.powerset, ∑ D : P.powerset, ∑ E : P.powerset, G A D.val E.val :=
        sum_coe_sort P.powerset (fun A => ∑ D : P.powerset, ∑ E : P.powerset, G A D.val E.val)
      _ = _ := by
        apply sum_congr rfl
        intro A _
        exact (sum_coe_sort P.powerset (fun D => ∑ E : P.powerset, G A D E.val)).trans
          (sum_congr rfl (fun D _ => sum_coe_sort P.powerset (fun E => G A D E)))
  calc
    _ = ∑ S : P.powerset, ∑ A : P.powerset, ∑ D : P.powerset,
        ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset,
          F S.val A.val D.val T.val C.val E.val := he.symm
    _ = ∑ S ∈ P.powerset, ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset, F S A D T.val C.val E.val :=
      h3 (fun S A D => ∑ T : P.powerset, ∑ C : P.powerset, ∑ E : P.powerset, F S A D T.val C.val E.val)
    _ = _ := by
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      exact h3 (F S A D)

/-- The two-site probability is the corresponding pair of one-site
expectations. The function sees each coefficient and remaining subset. -/
theorem twoSiteSplit_expectation (P : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ →
      Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
        x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val)) =
      twoSplitSiteAverage P (fun A R D Q => twoSplitSiteAverage P (fun C T E U => F A R D Q C T E U)) := by
  classical
  unfold twoSiteSplitMass
  rw [twoSiteSplit_sum P (fun S A D T C E =>
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
      bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
      subsetRetentionMass S A * subsetRetentionMass T C *
      subsetRetentionMass S D * subsetRetentionMass T E *
        F A (S \ A) D (S \ D) C (T \ C) E (T \ E))]
  unfold twoSplitSiteAverage
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro D _
  simp only [mul_sum]
  apply sum_congr rfl
  intro T _
  apply sum_congr rfl
  intro C _
  apply sum_congr rfl
  intro E _
  ring

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

theorem jointRemainingMass_nonneg {P R U : Finset ℕ} (A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hR : R ⊆ P) :
    0 ≤ jointRetentionMass P (remainingPrimeParameter A) R U :=
  mul_nonneg (bernoulliSubsetMass_nonneg hR (fun p hp =>
    remainingPrimeParameter_mem_Icc A (hP p hp).two_le)) (subsetRetentionMass_nonneg _ _)

theorem conditionalCoinAverage_mono {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ P, ∀ Q ⊆ P, ∀ U ⊆ P, ∀ V ⊆ P,
      F R Q I J U V ≤ G R Q I J U V) :
    conditionalCoinAverage P A D F ≤ conditionalCoinAverage P A D G := by
  unfold conditionalCoinAverage
  apply sum_le_sum
  intro I hI
  apply sum_le_sum
  intro J hJ
  apply sum_le_sum
  intro Q hQ
  apply sum_le_sum
  intro V hV
  apply sum_le_sum
  intro R hR
  apply sum_le_sum
  intro U hU
  apply mul_le_mul_of_nonneg_left
    (hFG I (mem_powerset.mp hI) J (mem_powerset.mp hJ) R (mem_powerset.mp hR)
      Q (mem_powerset.mp hQ) U (mem_powerset.mp hU) V (mem_powerset.mp hV))
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (bernoulliSubsetMass_nonneg (mem_powerset.mp hI) (by intros; norm_num))
    (bernoulliSubsetMass_nonneg (mem_powerset.mp hJ) (by intros; norm_num)))
    (jointRemainingMass_nonneg D hP (mem_powerset.mp hQ)))
    (jointRemainingMass_nonneg A hP (mem_powerset.mp hR))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DyadicChangeScales
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite dyadic decomposition by the largest changed prime -/

namespace JointDickman

open Finset

/-- One dyadic upper endpoint covers a fixed positive interval, with at
most a factor-two overshoot. -/
theorem dyadic_cover_endpoint {L X : ℝ} (hL : 0 < L) (hLX : L ≤ X) :
    ∃ N : ℕ, 0 < N ∧ X ≤ (2 : ℝ)^N * L ∧ (2 : ℝ)^N * L ≤ 2 * X := by
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hL).mpr hLX) (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · exact ((div_lt_iff₀ hL).mp hn').le
  · rw [pow_succ]
    have hh := (le_div_iff₀ hL).mp hn
    linarith only [hh]

/-- Every changed logarithm above the cutoff belongs to an actual dyadic
shell, including equality at an upper endpoint. -/
theorem dyadic_shell_cover {L x : ℝ} {N : ℕ} (_hL : 0 < L) (hx : L < x)
    (hcap : x ≤ (2 : ℝ)^N * L) :
    ∃ i ∈ Icc 1 N, ((2 : ℝ)^i * L) / 2 < x ∧ x ≤ (2 : ℝ)^i * L := by
  have hex : ∃ i : ℕ, x ≤ (2 : ℝ)^i * L := ⟨N, hcap⟩
  let i := Nat.find hex
  have hi : x ≤ (2 : ℝ)^i * L := Nat.find_spec hex
  have hiN : i ≤ N := Nat.find_min' hex hcap
  have hi0 : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz, pow_zero, one_mul] at hi
    linarith only [hx, hi]
  refine ⟨i, mem_Icc.mpr ⟨hi0, hiN⟩, ?_, hi⟩
  have hprev : ¬ x ≤ (2 : ℝ)^(i - 1) * L := Nat.find_min hex (by omega)
  have heq : ((2 : ℝ)^i * L) / 2 = (2 : ℝ)^(i - 1) * L := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi0)
    rw [hj]
    simp only [Nat.succ_sub_one, pow_succ]
    ring
  rw [heq]
  exact lt_of_not_ge hprev

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitChangeEvents
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Locating and orienting the largest changed prime -/

namespace JointDickman

open Finset

theorem twoSiteChangeSet_subset {P : Finset ℕ} (x : TwoSiteSplit P) : twoSiteChangeSet x ⊆ P := by
  intro p hp
  rcases mem_union.mp hp with h | h
  · rcases mem_symmDiff.mp h with h | h
    · exact mem_powerset.mp x.first₁.property h.1
    · exact mem_powerset.mp x.second₁.property h.1
  · rcases mem_symmDiff.mp h with h | h
    · exact mem_powerset.mp x.first₂.property h.1
    · exact mem_powerset.mp x.second₂.property h.1

theorem twoSiteChangeSet_eq_empty {P : Finset ℕ} (x : TwoSiteSplit P) :
    twoSiteChangeSet x = ∅ ↔ twoSiteNoChange x := by
  simp only [twoSiteChangeSet, union_eq_empty, symmDiff_eq_empty, twoSiteNoChange, Subtype.ext_iff]

theorem twoSiteChangeSet_swap {P : Finset ℕ} (x : TwoSiteSplit P) :
    twoSiteChangeSet x.swap = twoSiteChangeSet x := by
  simp only [twoSiteChangeSet, TwoSiteSplit.swap, symmDiff_comm]

theorem twoSiteNoHighChange_swap {P : Finset ℕ} (x : TwoSiteSplit P) (Y : ℝ) :
    twoSiteNoHighChange x.swap Y ↔ twoSiteNoHighChange x Y := by
  unfold twoSiteNoHighChange
  rw [twoSiteChangeSet_swap]

/-- At the largest changed prime, at least one orientation is an addition
at one of the two sites. -/
theorem twoSite_change_orientations {P : Finset ℕ} (x : TwoSiteSplit P) {p : ℕ} {Y : ℝ}
    (hp : p ∈ twoSiteChangeSet x) (hY : Y / 2 < Real.log p) :
    twoSiteAddition x Y false ∨ twoSiteAddition x Y true ∨
      twoSiteAddition x.swap Y false ∨ twoSiteAddition x.swap Y true := by
  rcases mem_union.mp hp with h | h
  · rcases mem_symmDiff.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨p, mem_sdiff.mpr h, hY⟩))
    · exact Or.inl ⟨p, mem_sdiff.mpr h, hY⟩
  · rcases mem_symmDiff.mp h with h | h
    · exact Or.inr (Or.inr (Or.inr ⟨p, mem_sdiff.mpr h, hY⟩))
    · exact Or.inr (Or.inl ⟨p, mem_sdiff.mpr h, hY⟩)

/-- Every nontrivial change belongs to a single covered dyadic interval;
the prime at its top gives one of the four addition orientations. -/
theorem largest_changed_prime_shell {B N : ℕ}
    (hB : 1 < B) (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B))
    (x : TwoSiteSplit (auxiliaryPrimes B)) (hx : ¬ twoSiteNoChange x) :
    ∃ i ∈ Icc 1 N, twoSiteNoHighChange x (primeTailEndpoint B i) ∧
      (twoSiteAddition x (primeTailEndpoint B i) false ∨ twoSiteAddition x (primeTailEndpoint B i) true ∨
        twoSiteAddition x.swap (primeTailEndpoint B i) false ∨ twoSiteAddition x.swap (primeTailEndpoint B i) true) := by
  classical
  have hne : (twoSiteChangeSet x).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    exact hx ((twoSiteChangeSet_eq_empty x).mp he)
  let p := (twoSiteChangeSet x).max' hne
  have hp : p ∈ twoSiteChangeSet x := max'_mem _ hne
  have hpP := twoSiteChangeSet_subset x hp
  have hprime := auxiliaryPrimes_prime B p hpP
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  have hL : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hlo : Real.log (auxiliaryCutoff B) < Real.log p :=
    Real.log_lt_log hP0 (mem_filter.mp hpP).2
  have hhi : Real.log p ≤ 4 * (B : ℝ) := by
    apply (Real.log_le_iff_le_exp hp0).mpr
    exact (Nat.le_floor_iff (Real.exp_pos _).le).mp (Nat.mem_primesLE.mp (mem_filter.mp hpP).1).1
  obtain ⟨i, hi, hilow, hiup⟩ := dyadic_shell_cover hL hlo (hhi.trans hcap)
  refine ⟨i, hi, ?_, twoSite_change_orientations x hp hilow⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (auxiliaryPrimes_prime B q (twoSiteChangeSet_subset x hq)).pos
  have hqp : q ≤ p := le_max' _ q hq
  exact (Real.log_le_log hq0 (by exact_mod_cast hqp)).trans hiup

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supports of retained and newly added prime subsets -/

namespace JointDickman

open Finset

theorem remainingSubsetMass_eq_zero {P A R : Finset ℕ} (hd : ¬ Disjoint A R) :
    bernoulliSubsetMass P (remainingPrimeParameter A) R = 0 := by
  classical
  obtain ⟨p, hpA, hpR⟩ := not_disjoint_iff.mp hd
  unfold bernoulliSubsetMass
  have hz : (∏ p ∈ R, remainingPrimeParameter A p) = 0 :=
    prod_eq_zero hpR (by simp only [remainingPrimeParameter, hpA, ite_true, if_true])
  rw [hz, zero_mul]

/-- No high coefficient changes force all old high coefficient primes to
be kept and prohibit any high additions. -/
theorem no_high_changes_retained_added {A R I U : Finset ℕ} {Y : ℝ}
    (hd : Disjoint A R) (hI : I ⊆ A) (hU : U ⊆ R)
    (hno : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) :
    highPrimePart Y I = highPrimePart Y A ∧ highPrimePart Y U = ∅ := by
  classical
  constructor
  · ext p
    simp only [highPrimePart, mem_filter]
    constructor
    · rintro ⟨hp, hy⟩
      exact ⟨hI hp, hy⟩
    · rintro ⟨hp, hy⟩
      refine ⟨?_, hy⟩
      by_contra hn
      have hnu : p ∉ U := fun hu => disjoint_left.mp hd hp (hU hu)
      have hm : p ∈ symmDiff A (I ∪ U) :=
        mem_symmDiff.mpr (Or.inl ⟨hp, by simpa only [mem_union, not_or] using And.intro hn hnu⟩)
      exact (not_le_of_gt hy) (hno p hm)
  · apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpu, hy⟩ := mem_filter.mp hp
    have hna : p ∉ A := fun ha => disjoint_left.mp hd ha (hU hpu)
    have hm : p ∈ symmDiff A (I ∪ U) :=
      mem_symmDiff.mpr (Or.inr ⟨mem_union_right I hpu, hna⟩)
    exact (not_le_of_gt hy) (hno p hm)

/-- A newly added prime in the top half of the shell forces the whole
addition product to have logarithm greater than Y/2. -/
theorem addition_product_log_large {P A I U : Finset ℕ} {Y : ℝ}
    (hP : ∀ p ∈ P, p.Prime) (hU : U ⊆ P)
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) (hI : I ⊆ A) :
    Y / 2 < Real.log (∏ p ∈ U, p : ℕ) := by
  obtain ⟨p, hp, hy⟩ := hadd
  obtain ⟨hpIU, hpA⟩ := mem_sdiff.mp hp
  have hpU : p ∈ U := (mem_union.mp hpIU).elim (fun h => False.elim (hpA (hI h))) id
  have hn : 0 < ∏ p ∈ U, p := prod_pos (fun q hq => (hP q (hU hq)).pos)
  have hle : p ≤ ∏ p ∈ U, p := Nat.le_of_dvd hn (dvd_prod_of_mem (fun p : ℕ => p) hpU)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p (hU hpU)).pos
  exact hy.trans_le (Real.log_le_log hp0 (by exact_mod_cast hle))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitProjectionSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projecting a native oriented split event to the low-prime test -/

namespace JointDickman

open Finset

theorem retained_high_projection {B : ℕ} {Y : ℝ} {A R I U : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B)
    (hd : Disjoint A R) (hI : I ⊆ A) (hU : U ⊆ R)
    (hno : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y) :
    I ∩ upperAdditionPrimes B Y = A ∩ upperAdditionPrimes B Y ∧
      U ∩ upperAdditionPrimes B Y = ∅ := by
  obtain ⟨hi, hu⟩ := no_high_changes_retained_added hd hI hU hno
  rw [selected_upperAdditionPrimes (hI.trans hA), selected_upperAdditionPrimes hA,
    selected_upperAdditionPrimes (hU.trans hR)]
  exact ⟨hi, hu⟩

theorem retained_low_high_union {B : ℕ} {Y : ℝ} {A I : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hI : I ⊆ A)
    (hhigh : I ∩ upperAdditionPrimes B Y = A ∩ upperAdditionPrimes B Y) :
    (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y) = I := by
  have hi : I ∩ (A ∩ additionPrimes B Y) = I ∩ additionPrimes B Y := by
    ext p
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hI h.1, h.2⟩⟩
  rw [hi, ← hhigh]
  exact selected_additionPrimeRanges_union (hI.trans hA)

theorem added_low_projection {B : ℕ} {Y : ℝ} {U : Finset ℕ}
    (hU : U ⊆ auxiliaryPrimes B) (hhigh : U ∩ upperAdditionPrimes B Y = ∅) :
    U ∩ additionPrimes B Y = U := by
  have hh := selected_additionPrimeRanges_union hU (Y := Y)
  rwa [hhigh, union_empty] at hh

/-- The native size-and-ratio event with an oriented changed prime implies
the precise low-addition test used in the conditional small-ball estimate. -/
theorem native_oriented_ratio_test {B T : ℕ} {Y : ℝ}
    {A D R Q I J U V : Finset ℕ}
    (hB : 0 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hR : R ⊆ auxiliaryPrimes B) (hQ : Q ⊆ auxiliaryPrimes B)
    (hAR : Disjoint A R) (hDQ : Disjoint D Q)
    (hI : I ⊆ A) (hJ : J ⊆ D) (hU : U ⊆ R) (hV : V ⊆ Q)
    (hnoA : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y)
    (hnoD : ∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y)
    (hpair : (∏ p ∈ I ∪ U, p, ∏ p ∈ J ∪ V, p) ∈ amplificationCoefficientPairs B T)
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) :
    additionRatioTest Y T
      (∏ p ∈ (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y), p : ℕ)
      (∏ p ∈ (J ∩ (D ∩ additionPrimes B Y)) ∪ (D ∩ upperAdditionPrimes B Y), p : ℕ)
      (U ∩ additionPrimes B Y) (V ∩ additionPrimes B Y) = 1 := by
  classical
  obtain ⟨hIA, hUhi⟩ := retained_high_projection hA hR hAR hI hU hnoA
  obtain ⟨hJD, hVhi⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
  rw [retained_low_high_union hA hI hIA, retained_low_high_union hD hJ hJD,
    added_low_projection (hU.trans hR) hUhi, added_low_projection (hV.trans hQ) hVhi]
  have hIU : Disjoint I U := hAR.mono hI hU
  have hJV : Disjoint J V := hDQ.mono hJ hV
  obtain ⟨_, _, hlo, hhi⟩ := (mem_amplificationCoefficientPairs hB).mp hpair
  have hlo' : (T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ)) ≤
      (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) := by
    rw [prod_union hIU, prod_union hJV] at hlo
    exact_mod_cast hlo
  have hhi' : (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) ≤
      2 * ((T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ))) := by
    rw [prod_union hIU, prod_union hJV] at hhi
    have hh : (∏ p ∈ I, p : ℕ) * (∏ p ∈ U, p : ℕ) <
        2 * (T : ℝ) * ((∏ p ∈ J, p : ℕ) * (∏ p ∈ V, p : ℕ)) := by exact_mod_cast hhi
    nlinarith only [hh]
  have hlarge := addition_product_log_large (auxiliaryPrimes_prime B) (hU.trans hR) hadd hI
  unfold additionRatioTest
  rw [ite_eq_left ⟨hlo', hhi', hlarge.le⟩]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NativeOrientedEvent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Domination of the actual oriented event by the conditional operator -/

namespace JointDickman
open Finset

/-- The native event forces all four high-prime restrictions and the exact
low-prime ratio test. Its two regular remaining sets supply the tail counts. -/
theorem nativeOrientedMass_le {B L T i : ℕ} {τ C : ℝ} {A D : Finset ℕ}
    (hB : 0 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    nativeOrientedMass B L T τ C (primeTailEndpoint B i) A D ≤
      orientedSplitMass B A D (primeTailEndpoint B i) C T := by
  classical
  rw [orientedSplitMass_expansion B A D (primeTailEndpoint B i) C T hA hD]
  change conditionalCoinAverage _ _ _ _ ≤ conditionalCoinAverage _ _ _ _
  apply conditionalCoinAverage_mono (auxiliaryPrimes_prime B)
  intro I hI J hJ R hR Q hQ U _ V _
  by_cases he : nativeOrientedEvent B L T τ C (primeTailEndpoint B i) A D R Q I J U V
  · have he' := he
    obtain ⟨hAR, hDQ, hU, hV, hRreg, hQreg, hnoA, hnoD, hpair, hadd⟩ := he
    obtain ⟨hi, hu⟩ := retained_high_projection hA hR hAR hI hU hnoA
    obtain ⟨hj, hv⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
    have hi' : I ∩ (A ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        A ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hI, hi]
    have hj' : J ∩ (D ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        D ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hJ, hj]
    have hr : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((R ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hR]
      exact hRreg.2 i
    have hq : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((Q ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hQ]
      exact hQreg.2 i
    have ht := native_oriented_ratio_test hB hA hD hR hQ hAR hDQ hI hJ hU hV
      hnoA hnoD hpair hadd
    simp only [he', hi', hj', hq, hv, hr, hu, and_self, ite_true, if_true, ht, le_refl]
  · simp only [ite_eq_right he]
    split_ifs
    · unfold additionRatioTest
      split_ifs <;> norm_num
    · exact le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalCoinSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restrict conditional averages to their actual probability support -/

namespace JointDickman
open Finset

theorem conditionalCoinAverage_le_on_support {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ P, ∀ Q ⊆ P, ∀ U ⊆ R, ∀ V ⊆ Q,
      Disjoint A R → Disjoint D Q → F R Q I J U V ≤ G R Q I J U V) :
    conditionalCoinAverage P A D F ≤ conditionalCoinAverage P A D G := by
  classical
  unfold conditionalCoinAverage
  apply sum_le_sum
  intro I hI
  apply sum_le_sum
  intro J hJ
  apply sum_le_sum
  intro Q hQ
  apply sum_le_sum
  intro V _
  apply sum_le_sum
  intro R hR
  apply sum_le_sum
  intro U _
  by_cases hAR : Disjoint A R
  · by_cases hDQ : Disjoint D Q
    · by_cases hU : U ⊆ R
      · by_cases hV : V ⊆ Q
        · apply mul_le_mul_of_nonneg_left
            (hFG I (mem_powerset.mp hI) J (mem_powerset.mp hJ) R (mem_powerset.mp hR)
              Q (mem_powerset.mp hQ) U hU V hV hAR hDQ)
          exact mul_nonneg (mul_nonneg (mul_nonneg
            (bernoulliSubsetMass_nonneg (mem_powerset.mp hI) (by intros; norm_num))
            (bernoulliSubsetMass_nonneg (mem_powerset.mp hJ) (by intros; norm_num)))
            (jointRemainingMass_nonneg D hP (mem_powerset.mp hQ)))
            (jointRemainingMass_nonneg A hP (mem_powerset.mp hR))
        · simp only [jointRetentionMass, subsetRetentionMass, hV, ite_false, if_false, mul_zero, zero_mul,
            le_refl]
      · simp only [jointRetentionMass, subsetRetentionMass, hU, ite_false, if_false, mul_zero, zero_mul,
          le_refl]
    · simp only [jointRetentionMass, remainingSubsetMass_eq_zero hDQ, zero_mul, mul_zero,
        le_refl]
  · simp only [jointRetentionMass, remainingSubsetMass_eq_zero hAR, zero_mul, mul_zero,
      le_refl]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitProbabilityBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite event bounds for the actual two-site split law -/

namespace JointDickman

open Finset

theorem twoSiteSplitProbability_or (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E F : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => E x ∨ F x) ≤
      twoSiteSplitProbability P E + twoSiteSplitProbability P F := by
  classical
  unfold twoSiteSplitProbability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  have hm := twoSiteSplitMass_nonneg P hP x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]
  all_goals linarith only [hm]

/-- A finite event cover costs the sum of the actual event probabilities. -/
theorem twoSiteSplitProbability_cover {ι : Type*} [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (I : Finset ι)
    (E N : TwoSiteSplit P → Prop) (F : ι → TwoSiteSplit P → Prop)
    (hcover : ∀ x, E x → N x ∨ ∃ i ∈ I, F i x) :
    twoSiteSplitProbability P E ≤ twoSiteSplitProbability P N +
      ∑ i ∈ I, twoSiteSplitProbability P (F i) := by
  classical
  unfold twoSiteSplitProbability
  rw [← sum_comm, ← sum_add_distrib]
  apply sum_le_sum
  intro x _
  have hm := twoSiteSplitMass_nonneg P hP x
  have hsum : 0 ≤ ∑ i ∈ I, if F i x then twoSiteSplitMass P x else 0 := by
    apply sum_nonneg
    intro i _
    split_ifs <;> first | exact hm | exact le_rfl
  have hn : 0 ≤ if N x then twoSiteSplitMass P x else 0 := by
    split_ifs <;> first | exact hm | exact le_rfl
  by_cases he : E x
  · simp only [he, ite_true, if_true]
    rcases hcover x he with hN | ⟨i, hi, hFi⟩
    · simp only [hN, ite_true, if_true]
      linarith only [hsum]
    · have hterm : twoSiteSplitMass P x ≤ ∑ j ∈ I, if F j x then twoSiteSplitMass P x else 0 := by
        have hh := single_le_sum (fun j (_hj : j ∈ I) => show 0 ≤ if F j x then twoSiteSplitMass P x else 0 by
          split_ifs <;> first | exact hm | exact le_rfl) hi
        simpa only [hFi, ite_true, if_true] using hh
      linarith only [hn, hterm]
  · simp only [he, ite_false, if_false]
    exact add_nonneg hn hsum


theorem twoSiteSplitProbability_four_or (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A B C D : TwoSiteSplit P → Prop) :
    twoSiteSplitProbability P (fun x => A x ∨ B x ∨ C x ∨ D x) ≤
      twoSiteSplitProbability P A + twoSiteSplitProbability P B +
        twoSiteSplitProbability P C + twoSiteSplitProbability P D := by
  calc
    _ ≤ twoSiteSplitProbability P A + twoSiteSplitProbability P (fun x => B x ∨ C x ∨ D x) :=
      twoSiteSplitProbability_or P hP A (fun x => B x ∨ C x ∨ D x)
    _ ≤ twoSiteSplitProbability P A +
        (twoSiteSplitProbability P B + twoSiteSplitProbability P (fun x => C x ∨ D x)) :=
      add_le_add le_rfl (twoSiteSplitProbability_or P hP B (fun x => C x ∨ D x))
    _ ≤ twoSiteSplitProbability P A +
        (twoSiteSplitProbability P B + (twoSiteSplitProbability P C + twoSiteSplitProbability P D)) :=
      add_le_add le_rfl (add_le_add le_rfl (twoSiteSplitProbability_or P hP C D))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SplitOrientationCover
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orienting the two-split event in its original symmetric law -/

namespace JointDickman

open Finset

/-- Orientation is performed before conditioning on the first coefficients.
Exchangeability accounts for the reverse direction with a factor of two. -/
theorem split_orientation_cover {B N : ℕ} (hB : 1 < B)
    (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B))
    (E : TwoSiteSplit (auxiliaryPrimes B) → Prop) (hE : ∀ x, E x.swap ↔ E x) :
    twoSiteSplitProbability (auxiliaryPrimes B) E ≤
      twoSiteSplitProbability (auxiliaryPrimes B) (fun x => E x ∧ twoSiteNoChange x) +
        2 * ∑ i ∈ Icc 1 N,
          (twoSiteSplitProbability (auxiliaryPrimes B) (splitOrientationEvent E (primeTailEndpoint B i) false) +
           twoSiteSplitProbability (auxiliaryPrimes B) (splitOrientationEvent E (primeTailEndpoint B i) true)) := by
  classical
  let G (i : ℕ) (b : Bool) := splitOrientationEvent E (primeTailEndpoint B i) b
  let F (i : ℕ) (x : TwoSiteSplit (auxiliaryPrimes B)) :=
    G i false x ∨ G i true x ∨ G i false x.swap ∨ G i true x.swap
  have hc : ∀ x, E x → (E x ∧ twoSiteNoChange x) ∨ ∃ i ∈ Icc 1 N, F i x := by
    intro x hx
    by_cases hn : twoSiteNoChange x
    · exact Or.inl ⟨hx, hn⟩
    · obtain ⟨i, hi, hh, ho⟩ := largest_changed_prime_shell hB hcap x hn
      refine Or.inr ⟨i, hi, ?_⟩
      have hxs := (hE x).mpr hx
      have hhs := (twoSiteNoHighChange_swap x (primeTailEndpoint B i)).mpr hh
      rcases ho with h | h | h | h
      · exact Or.inl ⟨hx, hh, h⟩
      · exact Or.inr (Or.inl ⟨hx, hh, h⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hxs, hhs, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hxs, hhs, h⟩))
  have hcover := twoSiteSplitProbability_cover (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (Icc 1 N) E (fun x => E x ∧ twoSiteNoChange x) F hc
  have hf (i : ℕ) : twoSiteSplitProbability (auxiliaryPrimes B) (F i) ≤
      2 * (twoSiteSplitProbability (auxiliaryPrimes B) (G i false) +
        twoSiteSplitProbability (auxiliaryPrimes B) (G i true)) := by
    have hh := twoSiteSplitProbability_four_or (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
      (G i false) (G i true) (fun x => G i false x.swap) (fun x => G i true x.swap)
    rw [twoSiteSplitProbability_swap, twoSiteSplitProbability_swap] at hh
    change twoSiteSplitProbability (auxiliaryPrimes B) (F i) ≤ _ at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring

  have hsum := sum_le_sum (fun i (_ : i ∈ Icc 1 N) => hf i)
  rw [← mul_sum] at hsum
  exact hcover.trans (add_le_add le_rfl hsum)

/-- The orientation bound for the actual simultaneous regular amplification events. -/
theorem amplification_orientation_cover {B N : ℕ} (L T : ℕ) (τ C : ℝ) (hB : 1 < B)
    (hcap : 4 * (B : ℝ) ≤ (2 : ℝ)^N * Real.log (auxiliaryCutoff B)) :
    twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) ≤
      twoSiteSplitProbability (auxiliaryPrimes B)
        (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) +
      2 * ∑ i ∈ Icc 1 N,
        (twoSiteSplitProbability (auxiliaryPrimes B)
          (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) +
         twoSiteSplitProbability (auxiliaryPrimes B)
          (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true)) :=
  split_orientation_cover hB hcap _ (bothAmplificationSplitsGood_swap B L T τ C)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalCoinReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Changing the order of the exact conditional finite averages -/

namespace JointDickman
open Finset

private theorem six_sum_reorder (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ I ∈ A.powerset, ∑ J ∈ D.powerset, ∑ Q ∈ P.powerset,
      ∑ V ∈ P.powerset, ∑ R ∈ P.powerset, ∑ U ∈ P.powerset, F R Q I J U V) =
    ∑ R ∈ P.powerset, ∑ I ∈ A.powerset, ∑ U ∈ P.powerset,
      ∑ Q ∈ P.powerset, ∑ J ∈ D.powerset, ∑ V ∈ P.powerset, F R Q I J U V := by
  conv_lhs => arg 2; ext I; arg 2; ext J; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext I; arg 2; ext J; rw [sum_comm]
  conv_lhs => arg 2; ext I; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext J; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext J; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext R; arg 2; ext I; arg 2; ext U; rw [sum_comm]

/-- Rewrite the common conditional average in site-first order, with
all retention sums over the common ambient prime set. -/
theorem conditionalCoinAverage_reindex (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    conditionalCoinAverage P A D F =
    ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
    ∑ I ∈ A.powerset, ∑ U ∈ P.powerset, subsetRetentionMass A I * subsetRetentionMass R U *
    (∑ Q ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter D) Q *
    ∑ J ∈ D.powerset, ∑ V ∈ P.powerset, subsetRetentionMass D J * subsetRetentionMass Q V *
      F R Q I J U V) := by
  unfold conditionalCoinAverage
  rw [six_sum_reorder]
  simp only [mul_sum]
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro V _
  rw [bernoulliHalf_eq_retention (mem_powerset.mp hI),
    bernoulliHalf_eq_retention (mem_powerset.mp hJ)]
  unfold jointRetentionMass
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteCoinLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full two-site law in the common conditional coin average -/

namespace JointDickman
open Finset

theorem twoSplitSiteAverage_coin (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    twoSplitSiteAverage P F =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
      ∑ R ∈ P.powerset, bernoulliSubsetMass P (remainingPrimeParameter A) R *
      ∑ I ∈ A.powerset, ∑ U ∈ P.powerset, subsetRetentionMass A I * subsetRetentionMass R U *
        F A R (I ∪ U) ((A \ I) ∪ (R \ U)) := by
  classical
  rw [twoSplitSiteAverage_conditional P hP]
  apply sum_congr rfl
  intro A _
  congr 1
  apply sum_congr rfl
  intro R hR
  congr 1
  apply sum_congr rfl
  intro I _
  apply sum_subset (powerset_mono.mpr (mem_powerset.mp hR))
  intro U _ hU
  have hn : ¬ U ⊆ R := fun h => hU (mem_powerset.mpr h)
  simp only [subsetRetentionMass, hn, ite_false, if_false, mul_zero, zero_mul]

/-- Exact disintegration by the two first coefficients, followed by the
conditional remaining-set and second-coin law. -/
theorem twoSiteSplit_coin_law (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ →
      Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
        x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val)) =
    ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => (1 / 2 : ℝ) / p) D *
      conditionalCoinAverage P A D (fun R Q I J U V =>
        F A R (I ∪ U) ((A \ I) ∪ (R \ U)) D Q (J ∪ V) ((D \ J) ∪ (Q \ V))) := by
  rw [twoSiteSplit_expectation, twoSplitSiteAverage_coin P hP]
  simp_rw [twoSplitSiteAverage_coin P hP, conditionalCoinAverage_reindex]
  simp only [mul_sum]
  apply sum_congr rfl
  intro A _
  conv_lhs => arg 2; ext R; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext R; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OrientedProbabilityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Applying the oriented conditional bound to the actual two-site event -/

namespace JointDickman
open Finset

open Classical in
theorem orientedTwoSplitTest_conditional_bound {B L T i : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 0 < B)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
      then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then
      orientedSplitMass B A D (primeTailEndpoint B i) C T else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg]
    apply le_trans (b := nativeOrientedMass B L T τ C (primeTailEndpoint B i) A D)
      ?_ (nativeOrientedMass_le hB hA hD)
    unfold nativeOrientedMass
    apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
    intro I _ J _ R _ Q _ U hU V hV hAR hDQ
    by_cases he : orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
    · have hn : nativeOrientedEvent B L T τ C (primeTailEndpoint B i) A D R Q I J U V :=
        ⟨hAR, hDQ, hU, hV, he.2.1, he.2.2.1, he.2.2.2.1,
          he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩
      simp only [he, hn, ite_true, if_true, le_refl]
    · simp only [he, ite_false, if_false]
      split_ifs <;> norm_num
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V) :=
      fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, if_false, mul_zero, sum_const_zero, le_refl]

open Classical in
/-- The first-recipient orientation probability is bounded by the first
coefficient average of the proved conditional operator. -/
theorem oriented_probability_bound {B L T i : ℕ} {τ C : ℝ} (hB : 0 < B) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) ≤
    ∑ A ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
      (if firstCoefficientGood B L T τ C A D then orientedSplitMass B A D (primeTailEndpoint B i) C T else 0) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if orientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false x
    · have ht : orientedTwoSplitTest B L T τ C (primeTailEndpoint B i)
          x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val := by
        refine ⟨⟨he.1.1.1, he.1.1.2.1, he.1.1.2.2.1⟩,
          he.1.1.2.2.2.1, he.1.1.2.2.2.2, ?_, ?_, he.1.2.1, he.2.2⟩
        · intro p hp
          exact he.2.1 p (mem_union_left _ hp)
        · intro p hp
          exact he.2.1 p (mem_union_right _ hp)
      simp only [he, F, ht, ite_true, if_true, mul_one, le_refl]
    · simp only [he, ite_false, if_false, F]
      split_ifs <;> simp only [mul_one, mul_zero]
      · exact hm
      · exact le_rfl
  apply hu.trans
  rw [twoSiteSplit_coin_law (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  apply sum_le_sum
  intro A hA
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro D hD
    exact mul_le_mul_of_nonneg_left
      (orientedTwoSplitTest_conditional_bound hB (mem_powerset.mp hA) (mem_powerset.mp hD))
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
        exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩))
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_HighCoinExponent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four high-prime factors after averaging the remaining subsets -/

namespace JointDickman

/-- The count cutoff's fourth power is exactly the required scale decay. -/
theorem high_coin_cutoff_identity {B Y C : ℝ} (hB : 0 < B) (hY : 0 < Y) :
    ((1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C))^4 =
      (2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add]
  congr 1
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hlog : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [hhalf, hlog]
  unfold amplificationExponent
  ring

theorem high_coin_four_factor_bound {B Y C x y : ℝ} {a d : ℕ}
    (hB : 0 < B) (hY : 0 < Y)
    (ha : (2 / 5 : ℝ) * Real.log (B / Y) - C ≤ (a : ℝ))
    (hd : (2 / 5 : ℝ) * Real.log (B / Y) - C ≤ (d : ℝ))
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxbound : x ≤ (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C))
    (hybound : y ≤ (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C)) :
    (1 / 2 : ℝ)^a * (1 / 2 : ℝ)^d * (x * y) ≤
      (2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent := by
  let q := (1 / 2 : ℝ)^((2 / 5 : ℝ) * Real.log (B / Y) - C)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hpa : (1 / 2 : ℝ)^a ≤ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha
  have hpd : (1 / 2 : ℝ)^d ≤ q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hd
  have h1 := mul_le_mul hpa hpd (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ)^d) hq
  have h2 := mul_le_mul hxbound hybound hy hq
  have hh := mul_le_mul h1 h2 (mul_nonneg hx hy) (mul_nonneg hq hq)
  calc
    _ ≤ q * q * (q * q) := hh
    _ = q^4 := by ring
    _ = _ := high_coin_cutoff_identity hB hY

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_RegularOrientedSplit
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regularity gain for one oriented change interval -/

namespace JointDickman

open Finset Filter
open scoped Topology

/-- The manuscript's conditional O_C((Y/B)^alpha/Y) estimate for a
recipient at one dyadic scale, in the actual remaining-prime law. -/
theorem regular_oriented_split_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (A D : Finset ℕ) (L i : ℕ) (τ C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      0 < primeTailEndpoint B i →
      Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i →
      primeTailEndpoint B i ≤ 8 * B → 0 < T →
      orientedSplitMass B A D (primeTailEndpoint B i) C T ≤
        K * (2 : ℝ)^(4 * C) * (primeTailEndpoint B i / B)^amplificationExponent /
          primeTailEndpoint B i := by
  obtain ⟨K, hK, hbound⟩ := oriented_split_bound hFord hM κ
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with B hb hB
  intro A D L i τ C T hA hD hsize hAr hDr hY hYL hYB hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let Y := primeTailEndpoint B i
  let Q := upperAdditionPrimes B Y
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Y) - C
  have ha : k ≤ ((A ∩ Q).card : ℝ) := by
    rw [selected_upperAdditionPrimes hA]
    exact hAr.2 i
  have hd : k ≤ ((D ∩ Q).card : ℝ) := by
    rw [selected_upperAdditionPrimes hD]
    exact hDr.2 i
  have hparam (S : Finset ℕ) : ∀ p ∈ Q,
      0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc S (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  have hx := highNoAdditionMass_nonneg Q (remainingPrimeParameter D) k (hparam D)
  have hy := highNoAdditionMass_nonneg Q (remainingPrimeParameter A) k (hparam A)
  have hxb := remaining_high_no_addition_bound Q (remainingPrimeParameter D) k (hparam D)
  have hyb := remaining_high_no_addition_bound Q (remainingPrimeParameter A) k (hparam A)
  have hfour := high_coin_four_factor_bound hB0 hY ha hd hx hy hxb hyb
  have hraw := hb A D Y C T hA hD hsize hY hYL hYB hT
  have hmul := mul_le_mul_of_nonneg_right hfour (div_nonneg hK.le hY.le)
  calc
    _ ≤ (1 / 2 : ℝ)^(A ∩ Q).card * (1 / 2 : ℝ)^(D ∩ Q).card *
        (highNoAdditionMass Q (remainingPrimeParameter D) k *
          highNoAdditionMass Q (remainingPrimeParameter A) k) * (K / Y) := by
      convert hraw using 1 <;> first | rfl | ring
    _ ≤ ((2 : ℝ)^(4 * C) * (Y / B)^amplificationExponent) * (K / Y) := hmul
    _ = _ := by ring


/-- All dyadic change intervals together cost O_C(1/B), uniformly in the
first coefficient sets satisfying the stated regularity conditions. -/
theorem regular_oriented_scale_sum
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (A D : Finset ℕ) (L : ℕ) (S : Finset ℕ) (τ C T : ℝ),
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp (κ * B) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      (∀ i ∈ S, primeTailEndpoint B i ≤ 8 * B) → 0 < T →
      (∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) ≤ K * (2 : ℝ)^(4 * C) / B := by
  obtain ⟨K, hK, hbound⟩ := regular_oriented_split_bound hFord hM κ
  let G := (8 : ℝ)^(amplificationExponent - 1) *
    ((2 : ℝ)^(amplificationExponent - 1) / ((2 : ℝ)^(amplificationExponent - 1) - 1))
  have hpow : 1 < (2 : ℝ)^(amplificationExponent - 1) :=
    Real.one_lt_rpow (by norm_num) (sub_pos.mpr amplificationExponent_gt_one)
  have hG : 0 < G := by dsimp [G] <;> positivity
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K * G, mul_pos hK hG, ?_⟩
  filter_upwards [hbound, hlog.eventually_gt_atTop 0, eventually_gt_atTop 0] with B hb hL0 hB
  intro A D L S τ C T hA hD hsize hAr hDr hcap hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hY0 (i : ℕ) : 0 < primeTailEndpoint B i := mul_pos (by positivity) hL0
  have hYL (i : ℕ) : Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i := by
    exact le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hs := amplification_scale_sum S hB0 hL0 hcap
  change (∑ i ∈ S, (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i) ≤ G / B at hs
  calc
    _ ≤ ∑ i ∈ S, K * (2 : ℝ)^(4 * C) * (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i :=
      sum_le_sum (fun i hi => hb A D L i τ C T hA hD hsize hAr hDr (hY0 i) (hYL i) (hcap i hi) hT)
    _ = (K * (2 : ℝ)^(4 * C)) *
        ∑ i ∈ S, (primeTailEndpoint B i / B)^amplificationExponent / primeTailEndpoint B i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ (K * (2 : ℝ)^(4 * C)) * (G / B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NoChangeSplitBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The no-change part of the amplification second moment -/

namespace JointDickman

open Finset Filter
open scoped Topology

theorem highPrimePart_at_cutoff {B : ℕ} {A : Finset ℕ} (hB : 1 < B)
    (hA : A ⊆ auxiliaryPrimes B) : highPrimePart (Real.log (auxiliaryCutoff B)) A = A := by
  classical
  apply filter_eq_self.mpr
  intro p hp
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  exact Real.log_lt_log hP0 (mem_filter.mp (hA hp)).2

theorem regular_no_change_split_bound {B L : ℕ} {A D : Finset ℕ} {τ C : ℝ}
    (hB : 1 < B) (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hAr : RegularPrimeSet B L τ C A) (hDr : RegularPrimeSet B L τ C D) :
    noChangeSplitMass B A D C ≤ (2 : ℝ)^(4 * C) * (auxiliaryRatio B)^(-amplificationExponent) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hY0 : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
  have ha : k ≤ (A.card : ℝ) := by
    have hh := hAr.2 0
    simp only [primeTailEndpoint, pow_zero, one_mul] at hh
    change k ≤ (highPrimePart (Real.log (auxiliaryCutoff B)) A).card at hh
    rwa [highPrimePart_at_cutoff hB hA] at hh
  have hd : k ≤ (D.card : ℝ) := by
    have hh := hDr.2 0
    simp only [primeTailEndpoint, pow_zero, one_mul] at hh
    change k ≤ (highPrimePart (Real.log (auxiliaryCutoff B)) D).card at hh
    rwa [highPrimePart_at_cutoff hB hD] at hh
  have hparam (S : Finset ℕ) : ∀ p ∈ auxiliaryPrimes B,
      0 ≤ remainingPrimeParameter S p ∧ remainingPrimeParameter S p ≤ 1 :=
    fun p hp => remainingPrimeParameter_mem_Icc S (auxiliaryPrimes_prime B p hp).two_le
  have hh := high_coin_four_factor_bound hB0 hY0 ha hd
    (highNoAdditionMass_nonneg _ _ k (hparam D))
    (highNoAdditionMass_nonneg _ _ k (hparam A))
    (remaining_high_no_addition_bound _ _ k (hparam D))
    (remaining_high_no_addition_bound _ _ k (hparam A))
  have heq : Real.log (auxiliaryCutoff B) / (B : ℝ) = (auxiliaryRatio B)⁻¹ := by
    rw [log_auxiliaryCutoff, auxiliaryRatio, inv_div]
  rw [heq, ← Real.rpow_neg_eq_inv_rpow] at hh
  exact hh

/-- Uniform vanishing after the extra factor B needed in the second moment. -/
theorem regular_no_change_vanishing (L : ℕ) (τ C : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℕ in atTop, ∀ A D : Finset ℕ,
      A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      (B : ℝ) * noChangeSplitMass B A D C ≤ ε := by
  intro ε hε
  have ht := amplification_no_change_tendsto.const_mul ((2 : ℝ)^(4 * C))
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (eventually_le_nhds hε), eventually_gt_atTop 1] with B hb hB
  intro A D hA hD hAr hDr
  have hh := mul_le_mul_of_nonneg_left (regular_no_change_split_bound hB hA hD hAr hDr)
    (Nat.cast_nonneg B)
  calc
    _ ≤ (2 : ℝ)^(4 * C) * ((B : ℝ) * (auxiliaryRatio B)^(-amplificationExponent)) := by
      convert hh using 1 <;> first | rfl | ring
    _ ≤ ε := hb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NoChangeCoinOperator
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact no-change operator on conditional second coins -/

namespace JointDickman
open Finset

theorem keptHighAverage_empty (P : Finset ℕ) (F : Finset ℕ → ℝ) :
    keptHighAverage ∅ P F = (1 / 2 : ℝ)^P.card * F ∅ := by
  rw [keptHighAverage_eq ∅ P (disjoint_empty_left P)]
  simp [subsetAverage, bernoulliSubsetMass]

theorem noHighAdditionAverage_empty (P : Finset ℕ) (q : ℕ → ℝ) (k : ℝ) (F : Finset ℕ → ℝ) :
    noHighAdditionAverage ∅ P q k F = highNoAdditionMass P q k * F ∅ := by
  rw [noHighAdditionAverage_eq ∅ P (disjoint_empty_left P)]
  simp [subsetAverage, bernoulliSubsetMass]

theorem noChangeCoinOperator_eq (P A D : Finset ℕ) (k : ℝ) :
    noChangeCoinOperator P A D k = (1 / 2 : ℝ)^A.card * (1 / 2 : ℝ)^D.card *
      (highNoAdditionMass P (remainingPrimeParameter D) k *
        highNoAdditionMass P (remainingPrimeParameter A) k) := by
  simp only [noChangeCoinOperator, keptHighAverage_empty, noHighAdditionAverage_empty, mul_one]
  ring

private theorem ite_sum_zero_p0 {ι : Type*} (s : Finset ι) (p : Prop) [Decidable p]
    (f : ι → ℝ) : (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, if p then f i else 0 := by
  by_cases hp : p <;> simp [hp]

open Classical in
theorem noChangeCoinOperator_expansion (P A D : Finset ℕ) (k : ℝ) :
    noChangeCoinOperator P A D k = conditionalCoinAverage P A D (fun R Q I J U V =>
      if I = A ∧ J = D ∧ (k ≤ (Q.card : ℝ) ∧ V = ∅) ∧ (k ≤ (R.card : ℝ) ∧ U = ∅)
      then 1 else 0) := by
  unfold noChangeCoinOperator keptHighAverage noHighAdditionAverage conditionalCoinAverage
  simp only [empty_union, ite_sum_zero_p0, mul_sum, mul_ite, mul_zero, mul_one]
  apply sum_congr rfl
  intro I hI
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro Q hQ
  apply sum_congr rfl
  intro V hV
  apply sum_congr rfl
  intro R hR
  apply sum_congr rfl
  intro U hU
  rw [inter_eq_left.mpr (mem_powerset.mp hI), inter_eq_left.mpr (mem_powerset.mp hJ),
    inter_eq_left.mpr (mem_powerset.mp hQ), inter_eq_left.mpr (mem_powerset.mp hV),
    inter_eq_left.mpr (mem_powerset.mp hR), inter_eq_left.mpr (mem_powerset.mp hU)]
  simp only [← ite_and]
  split_ifs <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NoChangeConditional
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The no-change event in the exact conditional law -/

namespace JointDickman
open Finset

theorem unchanged_split_parts {A R I U : Finset ℕ} (hd : Disjoint A R)
    (hU : U ⊆ R) (he : I ∪ U = A) : I = A ∧ U = ∅ := by
  have huA : U ⊆ A := by rw [← he]; exact subset_union_right
  have hu : U = ∅ := eq_empty_iff_forall_notMem.mpr (fun p hp =>
    disjoint_left.mp hd (huA hp) (hU hp))
  exact ⟨by simpa only [hu, union_empty] using he, hu⟩

theorem regular_card_at_cutoff {B L : ℕ} {τ C : ℝ} {R : Finset ℕ}
    (hB : 1 < B) (hR : R ⊆ auxiliaryPrimes B) (hr : RegularPrimeSet B L τ C R) :
    (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C ≤ (R.card : ℝ) := by
  have hh := hr.2 0
  simp only [primeTailEndpoint, pow_zero, one_mul] at hh
  change _ ≤ ((highPrimePart (Real.log (auxiliaryCutoff B)) R).card : ℝ) at hh
  rwa [highPrimePart_at_cutoff hB hR] at hh

open Classical in
theorem noChangeTwoSplitTest_conditional_bound {B L T : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 1 < B)
    :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V) then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then noChangeSplitMass B A D C else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg]
    let k := (2 / 5 : ℝ) * Real.log ((B : ℝ) / Real.log (auxiliaryCutoff B)) - C
    have hn : noChangeSplitMass B A D C = noChangeCoinOperator (auxiliaryPrimes B) A D k :=
      (noChangeCoinOperator_eq _ _ _ _).symm
    rw [hn, noChangeCoinOperator_expansion]
    apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
    intro I _ J _ R hR Q hQ U hU V hV hAR hDQ
    by_cases he : noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V)
    · obtain ⟨hi, hu⟩ := unchanged_split_parts hAR hU he.2.2.2.1
      obtain ⟨hj, hv⟩ := unchanged_split_parts hDQ hV he.2.2.2.2
      have hr := regular_card_at_cutoff hB hR he.2.1
      have hq := regular_card_at_cutoff hB hQ he.2.2.1
      rw [ite_eq_left he]
      change k ≤ (R.card : ℝ) at hr
      change k ≤ (Q.card : ℝ) at hq
      simp only [hi, hj, hu, hv, hr, hq, and_self, ite_true, if_true, le_refl]
    · simp only [he, ite_false, if_false]
      split_ifs <;> norm_num
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ noChangeTwoSplitTest B L T τ C A R (I ∪ U) D Q (J ∪ V) := fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, if_false, mul_zero, sum_const_zero, le_refl]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_FirstCoefficientAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging conditional estimates over the first coefficient event -/

namespace JointDickman
open Finset

theorem auxiliaryHalfSubsetMass_nonneg {B : ℕ} {A : Finset ℕ} (hA : A ⊆ auxiliaryPrimes B) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A := by
  apply bernoulliSubsetMass_nonneg hA
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

open Classical in
theorem firstCoefficientAverage_le {B L T : ℕ} {τ C K : ℝ}
    (hK : 0 ≤ K) (F : Finset ℕ → Finset ℕ → ℝ)
    (hF : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D → F A D ≤ K) :
    firstCoefficientAverage B L T τ C F ≤ K *
      ∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 := by
  rw [primeProductPair_sum_event]
  simp only [mul_sum]
  unfold firstCoefficientAverage
  apply sum_le_sum
  intro A hA
  rw [mul_sum]
  apply sum_le_sum
  intro D hD
  have ha := auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hA)
  have hd := auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hD)
  by_cases hg : firstCoefficientGood B L T τ C A D
  · have hm := hg.1
    simp only [hg, hm, ite_true, if_true]
    calc
      _ ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
          (bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D * K) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (hF A (mem_powerset.mp hA) D (mem_powerset.mp hD) hg) hd) ha
      _ = _ := by ring
  · simp only [hg, ite_false, if_false, mul_zero]
    split_ifs
    · exact mul_nonneg hK (mul_nonneg ha hd)
    · simp only [mul_zero, le_refl]

open Classical in
theorem firstCoefficientAverage_sum (B L T : ℕ) (τ C : ℝ) (S : Finset ℕ)
    (F : ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ i ∈ S, firstCoefficientAverage B L T τ C (F i)) =
      firstCoefficientAverage B L T τ C (fun A D => ∑ i ∈ S, F i A D) := by
  unfold firstCoefficientAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  simp only [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  simp only [← mul_sum]
  congr 1
  by_cases hg : firstCoefficientGood B L T τ C A D <;> simp [hg]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NoChangeProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the actual no-change event over its first coefficients -/

namespace JointDickman
open Finset

open Classical in
theorem no_change_probability_bound {B L T : ℕ} {τ C : ℝ} (hB : 1 < B) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤
    firstCoefficientAverage B L T τ C (fun A D => noChangeSplitMass B A D C) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if noChangeTwoSplitTest B L T τ C A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x
    · have ht : noChangeTwoSplitTest B L T τ C
          x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val :=
        ⟨⟨he.1.1.1, he.1.1.2.1, he.1.1.2.2.1⟩,
          he.1.1.2.2.2.1, he.1.1.2.2.2.2,
          congrArg Subtype.val he.2.1.symm, congrArg Subtype.val he.2.2.symm⟩
      simp only [he, F, ht, and_self, ite_true, if_true, mul_one, le_refl]
    · simp only [he, ite_false, if_false, F]
      split_ifs <;> simp only [mul_one, mul_zero]
      · exact hm
      · exact le_rfl
  apply hu.trans
  rw [twoSiteSplit_coin_law (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  apply sum_le_sum
  intro A hA
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro D hD
    exact mul_le_mul_of_nonneg_left
      (noChangeTwoSplitTest_conditional_bound hB)
      (auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hD))
  · exact auxiliaryHalfSubsetMass_nonneg (mem_powerset.mp hA)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NoChangeMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated no-change contribution is O(B^{-2}) -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem no_change_probability_small
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ C : ℝ), ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      twoSiteSplitProbability (auxiliaryPrimes B)
        (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) ≤ K / (B : ℝ)^2 := by
  obtain ⟨M, hM0, hm⟩ := coefficient_size_ratio_event_bound hFord hM
  refine ⟨M, hM0, ?_⟩
  intro L τ C
  filter_upwards [hm, regular_no_change_vanishing L τ C 1 (by norm_num), eventually_gt_atTop 1]
    with B hmb hnb hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hp : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D → noChangeSplitMass B A D C ≤ 1 / B := by
    intro A hA D hD hg
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hnb A D hA hD hg.2.1 hg.2.2]
  have hmass : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ M / B := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hmb T hT hTsize]
  calc
    _ ≤ firstCoefficientAverage B L T τ C (fun A D => noChangeSplitMass B A D C) :=
      no_change_probability_bound hB
    _ ≤ (1 / (B : ℝ)) * ∑ ac ∈ amplificationCoefficientPairs B T,
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
      firstCoefficientAverage_le (by positivity) _ hp
    _ ≤ (1 / (B : ℝ)) * (M / B) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RetainedRatioTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Low-prime tests for either direction of a coefficient ratio -/

namespace JointDickman
open Finset

theorem retained_ratio_test {B : ℕ} {Y T : ℝ} {A D R Q I J U V : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hR : R ⊆ auxiliaryPrimes B) (hQ : Q ⊆ auxiliaryPrimes B)
    (hAR : Disjoint A R) (hDQ : Disjoint D Q)
    (hI : I ⊆ A) (hJ : J ⊆ D) (hU : U ⊆ R) (hV : V ⊆ Q)
    (hnoA : ∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ Y)
    (hnoD : ∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ Y)
    (hlo : T * (∏ p ∈ J ∪ V, p : ℕ) ≤ (∏ p ∈ I ∪ U, p : ℕ))
    (hhi : (∏ p ∈ I ∪ U, p : ℕ) ≤ 2 * (T * (∏ p ∈ J ∪ V, p : ℕ)))
    (hadd : ∃ p ∈ (I ∪ U) \ A, Y / 2 < Real.log p) :
    additionRatioTest Y T
      (∏ p ∈ (I ∩ (A ∩ additionPrimes B Y)) ∪ (A ∩ upperAdditionPrimes B Y), p : ℕ)
      (∏ p ∈ (J ∩ (D ∩ additionPrimes B Y)) ∪ (D ∩ upperAdditionPrimes B Y), p : ℕ)
      (U ∩ additionPrimes B Y) (V ∩ additionPrimes B Y) = 1 := by
  classical
  obtain ⟨hIA, hUhi⟩ := retained_high_projection hA hR hAR hI hU hnoA
  obtain ⟨hJD, hVhi⟩ := retained_high_projection hD hQ hDQ hJ hV hnoD
  rw [retained_low_high_union hA hI hIA, retained_low_high_union hD hJ hJD,
    added_low_projection (hU.trans hR) hUhi, added_low_projection (hV.trans hQ) hVhi]
  have hIU : Disjoint I U := hAR.mono hI hU
  have hJV : Disjoint J V := hDQ.mono hJ hV
  rw [prod_union hIU, prod_union hJV, Nat.cast_mul, Nat.cast_mul] at hlo hhi
  have hlarge := addition_product_log_large (auxiliaryPrimes_prime B) (hU.trans hR) hadd hI
  exact ite_eq_left ⟨hlo, hhi, hlarge.le⟩

theorem reciprocal_ratio_bounds {T a c : ℝ} (hT : 0 < T)
    (hlo : T * c ≤ a) (hhi : a ≤ 2 * (T * c)) :
    (1 / (2 * T)) * a ≤ c ∧ c ≤ 2 * ((1 / (2 * T)) * a) := by
  constructor
  · calc
      _ = a / (2 * T) := by ring
      _ ≤ c := (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hhi])
  · calc
      c ≤ a / T := (le_div_iff₀ hT).mpr (by nlinarith only [hlo])
      _ = _ := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ConditionalOrientedEvent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional oriented bounds for a specified native ratio event -/

namespace JointDickman
open Finset

open Classical in
theorem conditional_oriented_event_bound {B L i : ℕ} {τ C T : ℝ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (E : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Prop)
    (hE : ∀ I ⊆ A, ∀ J ⊆ D, ∀ R ⊆ auxiliaryPrimes B, ∀ Q ⊆ auxiliaryPrimes B,
      ∀ U ⊆ R, ∀ V ⊆ Q, Disjoint A R → Disjoint D Q → E R Q I J U V →
      RegularPrimeSet B L τ C R ∧ RegularPrimeSet B L τ C Q ∧
      (∀ p ∈ symmDiff A (I ∪ U), Real.log p ≤ primeTailEndpoint B i) ∧
      (∀ p ∈ symmDiff D (J ∪ V), Real.log p ≤ primeTailEndpoint B i) ∧
      T * (∏ p ∈ J ∪ V, p : ℕ) ≤ (∏ p ∈ I ∪ U, p : ℕ) ∧
      (∏ p ∈ I ∪ U, p : ℕ) ≤ 2 * (T * (∏ p ∈ J ∪ V, p : ℕ)) ∧
      ∃ p ∈ (I ∪ U) \ A, primeTailEndpoint B i / 2 < Real.log p) :
    conditionalCoinAverage (auxiliaryPrimes B) A D
      (fun R Q I J U V => if E R Q I J U V then 1 else 0) ≤
      orientedSplitMass B A D (primeTailEndpoint B i) C T := by
  rw [orientedSplitMass_expansion B A D (primeTailEndpoint B i) C T hA hD]
  change conditionalCoinAverage _ _ _ _ ≤ conditionalCoinAverage _ _ _ _
  apply conditionalCoinAverage_le_on_support (auxiliaryPrimes_prime B)
  intro I hI J hJ R hR Q hQ U hU V hV hAR hDQ
  by_cases he : E R Q I J U V
  · obtain ⟨hr, hq, hnA, hnD, hlo, hhi, hadd⟩ := hE I hI J hJ R hR Q hQ U hU V hV hAR hDQ he
    obtain ⟨hi, hu⟩ := retained_high_projection hA hR hAR hI hU hnA
    obtain ⟨hj, hv⟩ := retained_high_projection hD hQ hDQ hJ hV hnD
    have hi' : I ∩ (A ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        A ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hI, hi]
    have hj' : J ∩ (D ∩ upperAdditionPrimes B (primeTailEndpoint B i)) =
        D ∩ upperAdditionPrimes B (primeTailEndpoint B i) := by
      rw [← inter_assoc, inter_eq_left.mpr hJ, hj]
    have hr' : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((R ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hR]
      exact hr.2 i
    have hq' : (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C ≤
        ((Q ∩ upperAdditionPrimes B (primeTailEndpoint B i)).card : ℝ) := by
      rw [selected_upperAdditionPrimes hQ]
      exact hq.2 i
    have ht := retained_ratio_test hA hD hR hQ hAR hDQ hI hJ hU hV hnA hnD hlo hhi hadd
    simp only [he, hi', hj', hq', hv, hr', hu, and_self, ite_true, if_true, ht, le_refl]
  · simp only [he, ite_false, if_false]
    split_ifs
    · unfold additionRatioTest
      split_ifs <;> norm_num
    · exact le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ConditionalCoinSwap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exchanging the two sites in a conditional coin average -/

namespace JointDickman
open Finset

theorem conditionalCoinAverage_swap (P A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    conditionalCoinAverage P A D F =
      conditionalCoinAverage P D A (fun R Q I J U V => F Q R J I V U) := by
  unfold conditionalCoinAverage
  rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext R; arg 2; ext Q; rw [sum_comm]
  conv_lhs => arg 2; ext J; arg 2; ext I; arg 2; ext R; rw [sum_comm]
  apply sum_congr rfl
  intro J _
  apply sum_congr rfl
  intro I _
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro Q _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SecondOrientedProbability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The second-recipient orientation, with the reciprocal ratio window -/

namespace JointDickman
open Finset

open Classical in
theorem secondOrientedTwoSplitTest_conditional_bound {B L T i : ℕ} {τ C : ℝ}
    {A D : Finset ℕ} (hB : 0 < B) (hT : 0 < T)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    conditionalCoinAverage (auxiliaryPrimes B) A D (fun R Q I J U V =>
      if secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V)
      then 1 else 0) ≤
    if firstCoefficientGood B L T τ C A D then
      orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T)) else 0 := by
  by_cases hg : firstCoefficientGood B L T τ C A D
  · rw [ite_eq_left hg, conditionalCoinAverage_swap]
    apply conditional_oriented_event_bound (L := L) (τ := τ) hD hA
    intro I _ J _ R _ Q _ U _ V _ _ _ he
    obtain ⟨_, hQreg, hRreg, hnA, hnD, hpair, hadd⟩ := he
    obtain ⟨_, _, hlo, hhi⟩ := (mem_amplificationCoefficientPairs hB).mp hpair
    have hlo' : (T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ) ≤ (∏ p ∈ J ∪ V, p : ℕ) := by
      exact_mod_cast hlo
    have hhi' : (∏ p ∈ J ∪ V, p : ℕ) ≤ 2 * ((T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ)) := by
      have hh : (∏ p ∈ J ∪ V, p : ℕ) < 2 * (T : ℝ) * (∏ p ∈ I ∪ U, p : ℕ) := by
        exact_mod_cast hhi
      nlinarith only [hh]
    have ht0 : (0 : ℝ) < T := by exact_mod_cast hT
    obtain ⟨hrlo, hrhi⟩ := reciprocal_ratio_bounds ht0 hlo' hhi'
    exact ⟨hRreg, hQreg, hnD, hnA, hrlo, hrhi, hadd⟩
  · have hf (R Q I J U V : Finset ℕ) :
        ¬ secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R (I ∪ U) D Q (J ∪ V) :=
      fun h => hg h.1
    simp only [conditionalCoinAverage, hg, hf, ite_false, if_false, mul_zero, sum_const_zero, le_refl]

open Classical in
/-- The second-recipient orientation probability is bounded by the first
coefficient average of the proved conditional operator. -/
theorem second_oriented_probability_bound {B L T i : ℕ} {τ C : ℝ} (hB : 0 < B) (hT : 0 < T) :
    twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true) ≤
    ∑ A ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) A *
    ∑ D ∈ (auxiliaryPrimes B).powerset, bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1 / 2 : ℝ) / p) D *
      (if firstCoefficientGood B L T τ C A D then orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T)) else 0) := by
  let F := fun A R E (_ : Finset ℕ) D Q H (_ : Finset ℕ) =>
    if secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i) A R E D Q H then (1 : ℝ) else 0
  have hu : twoSiteSplitProbability (auxiliaryPrimes B)
      (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true) ≤
      ∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
        F x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val (x.site₁.val \ x.second₁.val)
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val (x.site₂.val \ x.second₂.val) := by
    apply sum_le_sum
    intro x _
    have hm := twoSiteSplitMass_nonneg (auxiliaryPrimes B) (auxiliaryPrimes_prime B) x
    by_cases he : splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true x
    · have ht : secondOrientedTwoSplitTest B L T τ C (primeTailEndpoint B i)
          x.first₁.val (x.site₁.val \ x.first₁.val) x.second₁.val
          x.first₂.val (x.site₂.val \ x.first₂.val) x.second₂.val := by
        refine ⟨⟨he.1.1.1, he.1.1.2.1, he.1.1.2.2.1⟩,
          he.1.1.2.2.2.1, he.1.1.2.2.2.2, ?_, ?_, he.1.2.1, he.2.2⟩
        · intro p hp
          exact he.2.1 p (mem_union_left _ hp)
        · intro p hp
          exact he.2.1 p (mem_union_right _ hp)
      simp only [he, F, ht, ite_true, if_true, mul_one, le_refl]
    · simp only [he, ite_false, if_false, F]
      split_ifs <;> simp only [mul_one, mul_zero]
      · exact hm
      · exact le_rfl
  apply hu.trans
  rw [twoSiteSplit_coin_law (auxiliaryPrimes B) (auxiliaryPrimes_prime B)]
  apply sum_le_sum
  intro A hA
  apply mul_le_mul_of_nonneg_left
  · apply sum_le_sum
    intro D hD
    exact mul_le_mul_of_nonneg_left
      (secondOrientedTwoSplitTest_conditional_bound hB hT (mem_powerset.mp hA) (mem_powerset.mp hD))
      (bernoulliSubsetMass_nonneg (mem_powerset.mp hD) (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
        exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩))
  · apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_FirstOrientedMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first-recipient contribution to the amplification second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The first-recipient orientations, summed over all dyadic change scales,
have probability O_C(B^{-2}) in the actual two-site split law. -/
theorem first_oriented_probability_sum
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (L T : ℕ) (τ C : ℝ) (S : Finset ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ i ∈ S, primeTailEndpoint B i ≤ 8 * B) →
      (∑ i ∈ S, twoSiteSplitProbability (auxiliaryPrimes B)
        (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false)) ≤
      K * (2 : ℝ)^(4 * C) / (B : ℝ)^2 := by
  obtain ⟨K, hK, hk⟩ := regular_oriented_scale_sum hFord hM (16 / 5)
  obtain ⟨M, hM0, hm⟩ := coefficient_size_ratio_event_bound hFord hM
  refine ⟨K * M, mul_pos hK hM0, ?_⟩
  filter_upwards [hk, hm, amplificationCoefficientPairs_size, eventually_gt_atTop 0]
    with B hkb hmb hsize hB
  intro L T τ C S hT hTsize hcap
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D →
      (∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) ≤
        K * (2 : ℝ)^(4 * C) / B := by
    intro A hA D hD hg
    exact hkb A D L S τ C T hA hD (hsize T _ _ hT hTsize hg.1).1
      hg.2.1 hg.2.2 hcap hT0
  have hmass : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ M / B := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hmb T hT hTsize]
  have hkn : 0 ≤ K * (2 : ℝ)^(4 * C) / B := by positivity
  calc
    _ ≤ ∑ i ∈ S, firstCoefficientAverage B L T τ C
        (fun A D => orientedSplitMass B A D (primeTailEndpoint B i) C T) :=
      sum_le_sum (fun i _ => oriented_probability_bound hB)
    _ = firstCoefficientAverage B L T τ C
        (fun A D => ∑ i ∈ S, orientedSplitMass B A D (primeTailEndpoint B i) C T) :=
      firstCoefficientAverage_sum B L T τ C S _
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) *
        ∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
      firstCoefficientAverage_le hkn _ hpoint
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) * (M / B) := mul_le_mul_of_nonneg_left hmass hkn
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_OrientedMoments
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The first-recipient contribution to the amplification second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The second-recipient orientations, summed over all dyadic change scales,
have probability O_C(B^{-2}) in the actual two-site split law. -/
theorem second_oriented_probability_sum
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (L T : ℕ) (τ C : ℝ) (S : Finset ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ i ∈ S, primeTailEndpoint B i ≤ 8 * B) →
      (∑ i ∈ S, twoSiteSplitProbability (auxiliaryPrimes B)
        (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true)) ≤
      K * (2 : ℝ)^(4 * C) / (B : ℝ)^2 := by
  obtain ⟨K, hK, hk⟩ := regular_oriented_scale_sum hFord hM (16 / 5)
  obtain ⟨M, hM0, hm⟩ := coefficient_size_ratio_event_bound hFord hM
  refine ⟨K * M, mul_pos hK hM0, ?_⟩
  filter_upwards [hk, hm, amplificationCoefficientPairs_size, eventually_gt_atTop 0]
    with B hkb hmb hsize hB
  intro L T τ C S hT hTsize hcap
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hpoint : ∀ A ⊆ auxiliaryPrimes B, ∀ D ⊆ auxiliaryPrimes B,
      firstCoefficientGood B L T τ C A D →
      (∑ i ∈ S, orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T))) ≤
        K * (2 : ℝ)^(4 * C) / B := by
    intro A hA D hD hg
    exact hkb D A L S τ C (1 / (2 * T)) hD hA (hsize T _ _ hT hTsize hg.1).2
      hg.2.2 hg.2.1 hcap (by positivity)
  have hmass : (∑ ac ∈ amplificationCoefficientPairs B T,
      primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
        primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2) ≤ M / B := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [hmb T hT hTsize]
  have hkn : 0 ≤ K * (2 : ℝ)^(4 * C) / B := by positivity
  calc
    _ ≤ ∑ i ∈ S, firstCoefficientAverage B L T τ C
        (fun A D => orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T))) :=
      sum_le_sum (fun i _ => second_oriented_probability_bound hB hT)
    _ = firstCoefficientAverage B L T τ C
        (fun A D => ∑ i ∈ S, orientedSplitMass B D A (primeTailEndpoint B i) C (1 / (2 * T))) :=
      firstCoefficientAverage_sum B L T τ C S _
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) *
        ∑ ac ∈ amplificationCoefficientPairs B T,
          primeProductMass (auxiliaryPrimes B) (1 / 2) ac.1 *
            primeProductMass (auxiliaryPrimes B) (1 / 2) ac.2 :=
      firstCoefficientAverage_le hkn _ hpoint
    _ ≤ (K * (2 : ℝ)^(4 * C) / B) * (M / B) := mul_le_mul_of_nonneg_left hmass hkn
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationSecondMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The amplification second moment in the independent-prime model -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Both actual fair splits are good with probability O(B^{-2}). The bound
uses the published upper sieve and prime reciprocal Mertens input. -/
theorem amplification_second_moment_probability
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) ≤
        K / (B : ℝ)^2 := by
  obtain ⟨K₁, hK₁, hf⟩ := first_oriented_probability_sum hFord hM
  obtain ⟨K₂, hK₂, hs⟩ := second_oriented_probability_sum hFord hM
  obtain ⟨K₀, hK₀, hn⟩ := no_change_probability_small hFord hM
  intro L τ C
  refine ⟨K₀ + 2 * (K₁ + K₂) * (2 : ℝ)^(4 * C), by positivity, ?_⟩
  filter_upwards [hf, hs, hn L τ C, auxiliaryRatio_tendsto.eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hfb hsb hnb hratio hB
  intro T hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hlog : 0 < Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hLB : Real.log (auxiliaryCutoff B) ≤ (B : ℝ) := by
    have hh : 1 ≤ (B : ℝ) / Real.log (auxiliaryCutoff B) := by
      simpa only [auxiliaryRatio, log_auxiliaryCutoff] using hratio
    have hh' := (le_div_iff₀ hlog).mp hh
    simpa only [one_mul] using hh'
  obtain ⟨N, _, hcap, hcap'⟩ := dyadic_cover_endpoint hlog
    (show Real.log (auxiliaryCutoff B) ≤ 4 * (B : ℝ) by linarith only [hLB, hB0])
  have hi : ∀ i ∈ Icc 1 N, primeTailEndpoint B i ≤ 8 * B := by
    intro i hi
    have hp : (2 : ℝ)^i ≤ (2 : ℝ)^N := pow_le_pow_right₀ (by norm_num) (mem_Icc.mp hi).2
    exact (mul_le_mul_of_nonneg_right hp hlog.le).trans (by linarith only [hcap'])
  have hfirst := hfb L T τ C (Icc 1 N) hT hTsize hi
  have hsecond := hsb L T τ C (Icc 1 N) hT hTsize hi
  have hno := hnb T hT hTsize
  calc
    _ ≤ twoSiteSplitProbability (auxiliaryPrimes B)
          (fun x => bothAmplificationSplitsGood B L T τ C x ∧ twoSiteNoChange x) +
        2 * ∑ i ∈ Icc 1 N,
          (twoSiteSplitProbability (auxiliaryPrimes B)
            (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) false) +
           twoSiteSplitProbability (auxiliaryPrimes B)
            (splitOrientationEvent (bothAmplificationSplitsGood B L T τ C) (primeTailEndpoint B i) true)) :=
      amplification_orientation_cover L T τ C hB hcap
    _ ≤ K₀ / (B : ℝ)^2 +
        2 * (K₁ * (2 : ℝ)^(4 * C) / (B : ℝ)^2 + K₂ * (2 : ℝ)^(4 * C) / (B : ℝ)^2) := by
      rw [sum_add_distrib]
      exact add_le_add hno (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TwoSiteSplitProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional products of the two independent fair splits -/

namespace JointDickman
open Finset

/-- Given the two sites, the two fair splits are independent. -/
theorem twoSiteSplit_product (P : Finset ℕ)
    (F G : Finset ℕ → Finset ℕ → Finset ℕ → Finset ℕ → ℝ) :
    (∑ x : TwoSiteSplit P, twoSiteSplitMass P x *
      F x.site₁.val x.site₂.val x.first₁.val x.first₂.val *
      G x.site₁.val x.site₂.val x.second₁.val x.second₂.val) =
    ∑ S ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
    ∑ T ∈ P.powerset, bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
      (sitePairSplitAverage P S T (F S T) * sitePairSplitAverage P S T (G S T)) := by
  unfold twoSiteSplitMass
  rw [twoSiteSplit_sum P (fun S A D T C E =>
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) S *
    bernoulliSubsetMass P (fun p => 1 / (p : ℝ)) T *
    subsetRetentionMass S A * subsetRetentionMass T C *
    subsetRetentionMass S D * subsetRetentionMass T E * F S T A C * G S T D E)]
  conv_rhs => arg 2; ext S; arg 2; arg 2; ext T; arg 2; rw [mul_comm]
  unfold sitePairSplitAverage
  simp only [sum_mul, mul_sum]
  apply sum_congr rfl
  intro S _
  conv_lhs => arg 2; ext A; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro C _
  apply sum_congr rfl
  intro D _
  apply sum_congr rfl
  intro E _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent-model amplification envelope and its second moment -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem independentAmplificationEnvelope_second_identity (B L T : ℕ) (τ C : ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
    ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
      (independentAmplificationEnvelope B L T τ C S R)^2) =
    (B : ℝ)^2 * twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) := by
  let F := fun S R A D => if amplificationSplitGood B L T τ C S R A D then (1 : ℝ) else 0
  have hp : (∑ x : TwoSiteSplit (auxiliaryPrimes B), twoSiteSplitMass (auxiliaryPrimes B) x *
      F x.site₁.val x.site₂.val x.first₁.val x.first₂.val *
      F x.site₁.val x.site₂.val x.second₁.val x.second₂.val) =
      twoSiteSplitProbability (auxiliaryPrimes B) (bothAmplificationSplitsGood B L T τ C) := by
    apply sum_congr rfl
    intro x _
    unfold F bothAmplificationSplitsGood
    by_cases h₁ : amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.first₁.val x.first₂.val <;>
    by_cases h₂ : amplificationSplitGood B L T τ C x.site₁.val x.site₂.val x.second₁.val x.second₂.val <;>
      simp only [h₁, h₂, and_self, and_false, false_and, ite_true, if_true, ite_false, if_false, mul_one, mul_zero]
  rw [← hp, twoSiteSplit_product]
  simp only [independentAmplificationEnvelope, mul_sum]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro R _
  dsimp only [F]
  ring

/-- The B-normalized fair-split envelope has a bounded second moment. -/
theorem independentAmplificationEnvelope_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        (independentAmplificationEnvelope B L T τ C S R)^2) ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := amplification_second_moment_probability hFord hM L τ C
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop 0] with B hB hB0
  intro T hT hTsize
  rw [independentAmplificationEnvelope_second_identity]
  have hz : (B : ℝ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt hB0))
  calc
    _ ≤ (B : ℝ)^2 * (K / (B : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (hB T hT hTsize) (sq_nonneg _)
    _ = K := by field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationPointBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bounds for the normalized fair-split envelope -/

namespace JointDickman
open Finset

theorem sitePairSplitAverage_mono (P S T : Finset ℕ) (F G : Finset ℕ → Finset ℕ → ℝ)
    (hFG : ∀ A ⊆ P, ∀ D ⊆ P, F A D ≤ G A D) :
    sitePairSplitAverage P S T F ≤ sitePairSplitAverage P S T G := by
  apply sum_le_sum
  intro A hA
  apply sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (hFG A (mem_powerset.mp hA) D (mem_powerset.mp hD))
    (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))

open Classical in
theorem independentAmplificationEnvelope_nonneg (B L T : ℕ) (τ C : ℝ) (S R : Finset ℕ) :
    0 ≤ independentAmplificationEnvelope B L T τ C S R := by
  unfold independentAmplificationEnvelope sitePairSplitAverage
  apply mul_nonneg (Nat.cast_nonneg _)
  apply sum_nonneg
  intro A _
  apply sum_nonneg
  intro D _
  apply mul_nonneg (mul_nonneg (subsetRetentionMass_nonneg _ _) (subsetRetentionMass_nonneg _ _))
  dsimp only
  split_ifs <;> norm_num

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

open Classical in
theorem independentWeightedAmplification_le_envelope (B L T : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (hw : ∀ a c, w a c ≤ 1)
    (hsupp : ∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0)
    (S R : Finset ℕ) :
    independentWeightedAmplification B L τ C w S R ≤ independentAmplificationEnvelope B L T τ C S R := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
  apply sitePairSplitAverage_mono
  intro A _ D _
  unfold amplificationSplitGood
  by_cases hr : RegularPrimeSet B L τ C A ∧ RegularPrimeSet B L τ C D ∧
      RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
  · by_cases hp : (∏ p ∈ A, p, ∏ p ∈ D, p) ∈ amplificationCoefficientPairs B T
    · simp only [hr, hp, true_and, ite_true, if_true]
      exact hw _ _
    · simp only [hr, hp, false_and, and_self, ite_true, if_true, ite_false, if_false, hsupp _ _ hp, le_refl]
  · simp only [hr, and_false, ite_false, if_false, le_refl]

theorem weightedAmplification_second_bound_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (T : ℕ) (w : ℕ → ℕ → ℝ), 0 < T → (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
      (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
      (∀ a c, (a, c) ∉ amplificationCoefficientPairs B T → w a c = 0) →
      (∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) S *
      ∑ R ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) R *
        (independentWeightedAmplification B L τ C w S R)^2) ≤ K := by
  intro L τ C
  obtain ⟨K, hK, hb⟩ := independentAmplificationEnvelope_second_bound hFord hM L τ C
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb] with B hB
  intro T w hT hTsize hw hsupp
  apply le_trans _ (hB T hT hTsize)
  apply sum_le_sum
  intro S hS
  have hnonneg (A : Finset ℕ) (hA : A ⊆ auxiliaryPrimes B) :
      0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1 / (p : ℝ)) A := by
    apply bernoulliSubsetMass_nonneg hA
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).one_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).pos
    exact ⟨by positivity, (div_le_one hp0).mpr hp1⟩
  apply mul_le_mul_of_nonneg_left _ (hnonneg S (mem_powerset.mp hS))
  apply sum_le_sum
  intro R hR
  apply mul_le_mul_of_nonneg_left _ (hnonneg R (mem_powerset.mp hR))
  have hx := independentWeightedAmplification_nonneg B L τ C w (fun a c => (hw a c).1) S R
  have hy := independentAmplificationEnvelope_nonneg B L T τ C S R
  exact (sq_le_sq₀ hx hy).mpr
    (independentWeightedAmplification_le_envelope B L T τ C w (fun a c => (hw a c).2) hsupp S R)

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.weightedAmplification_second_bound_jd_oai := @OAI.JointDickman.weightedAmplification_second_bound_jd_oai
