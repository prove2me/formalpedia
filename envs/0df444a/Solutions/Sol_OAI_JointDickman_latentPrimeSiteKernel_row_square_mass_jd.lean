-- Prove2me | solution 1 for OAI.JointDickman.latentPrimeSiteKernel_row_square_mass_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:14:05.473234+00:00
-- url     : https://prove2.me/submissions/1d41a3db-712e-44ce-8fd0-9479d11db892

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_tiltedCandidatePairCount_bound_jd

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

theorem primeProductMass_eq_zero {P : Finset ℕ} (z : ℝ) (n : ℕ)
    (hn : n ∉ P.powerset.image (fun S => ∏ p ∈ S, p)) :
    primeProductMass P z n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro S hS
  have hne : (∏ p ∈ S, p) ≠ n := fun heq =>
    hn (Finset.mem_image.mpr ⟨S, hS, heq⟩)
  simp [hne]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RootSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent selection of form roots, including repeated roots -/

namespace JointDickman

open Finset

/-- The chance that a residue survives independent choices of forbidden
forms is the product of the retained weights of all forms vanishing there. -/
theorem bernoulli_root_survival {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (root : ι → α) (θ : ι → ℝ) (x : α) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (if x ∈ S.image root then 0 else 1)) =
      ∏ i ∈ I.filter (fun i => root i = x), θ i := by
  classical
  let E := I.filter (fun i => root i = x)
  have hid (S : Finset ι) (hS : S ⊆ I) :
      avoidsSelected S E = if x ∈ S.image root then 0 else 1 := by
    have hiff : Disjoint S E ↔ x ∉ S.image root := by
      constructor
      · intro h hx
        obtain ⟨i, hiS, hi⟩ := mem_image.mp hx
        exact disjoint_left.mp h hiS (mem_filter.mpr ⟨hS hiS, hi⟩)
      · intro h
        apply disjoint_left.mpr
        intro i hiS hiE
        exact h (mem_image.mpr ⟨i, hiS, (mem_filter.mp hiE).2⟩)
    unfold avoidsSelected
    by_cases hx : x ∈ S.image root
    · have hn : ¬ Disjoint S E := fun h => (hiff.mp h) hx
      simp [hn, hx]
    · simp [hiff.mpr hx, hx]
  have h := bernoulliSubsetMass_avoids I E (filter_subset _ _) θ
  apply Eq.trans _ h
  apply sum_congr rfl
  intro S hS
  rw [hid S (mem_powerset.mp hS)]

/-- Uniform survival mass for a deterministic root set. -/
theorem root_survival_mean {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 0 < Fintype.card α) (T : Finset α) :
    (∑ x : α, (if x ∈ T then (0 : ℝ) else 1)) / Fintype.card α =
      1 - (T.card : ℝ) / Fintype.card α := by
  have hx (x : α) : (if x ∈ T then (0 : ℝ) else 1) =
      1 - (if x ∈ T then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  simp_rw [hx]
  rw [sum_sub_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one,
    sum_ite_mem, sum_const]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  simp [sub_div, hcard]

/-- Averaging the local sieve density gives exactly the uniform residue
average of the original form weights, even when some roots coincide. -/
theorem bernoulli_root_density {ι α : Type*} [DecidableEq ι]
    [Fintype α] [DecidableEq α] (hα : 0 < Fintype.card α)
    (I : Finset ι) (root : ι → α) (θ : ι → ℝ) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (1 - ((S.image root).card : ℝ) / Fintype.card α)) =
      (∑ x : α, ∏ i ∈ I.filter (fun i => root i = x), θ i) / Fintype.card α := by
  simp_rw [← root_survival_mean hα, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  exact bernoulli_root_survival I root θ x

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ProductComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RandomRootSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently randomized root sets

Averaging the uniform deterministic bound preserves its remainder and
factors its main term. The root sets at a prime may contain coincident
roots of several forms; only their union and its cardinality matter.
-/

namespace JointDickman

open Finset

/-- Exact expectation of a product under the finite product law. -/
theorem finiteProductMass_product_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ F : ∀ i, Ω i → ℝ) :
    (∑ ω, finiteProductMass μ ω * ∏ i, F i (ω i)) =
      ∏ i, ∑ x, μ i x * F i x := by
  simp_rw [finiteProductMass, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => μ i x * F i x)).symm

/-- Arbitrary independent choices of at most `k` roots per prime satisfy
the interval upper bound, with one uniform polynomial remainder. -/
theorem randomized_root_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (Ω : P → Type) [∀ p, Fintype (Ω p)]
      (μ : ∀ p, Ω p → ℝ) (A : ∀ p : P, Ω p → Finset (ZMod p.val))
      (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p x, 0 ≤ μ p x) → (∀ p, ∑ x, μ p x = 1) →
      (∀ p x, (A p x).card ≤ k) →
      (∑ n ∈ Ico a b, ∏ p : P, ∑ x, μ p x *
        (if (n : ZMod p.val) ∈ A p x then 0 else 1)) ≤
      C * ((b : ℝ) - a) * (∏ p : P, ∑ x, μ p x *
        (1 - ((A p x).card : ℝ) / p.val)) +
      2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_interval_sieve_polynomial hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P Ω _ μ A a b Z hab hZ hP hμ hμ1 hA
  let roots (ω : ∀ p, Ω p) (q : ℕ) : Finset (ZMod q) :=
    if hq : q ∈ P then A ⟨q, hq⟩ (ω ⟨q, hq⟩) else ∅
  have hroot (ω : ∀ p, Ω p) (p : P) : roots ω p.val = A p (ω p) := by
    simp [roots, p.property]
  have hprod (ω : ∀ p, Ω p) (n : ℕ) :
      (∏ p ∈ rootEvents P (roots ω) n, (0 : ℝ)) =
        ∏ p : P, if (n : ZMod p.val) ∈ A p (ω p) then 0 else 1 := by
    calc
      _ = ∏ p ∈ P, if (n : ZMod p) ∈ roots ω p then (0 : ℝ) else 1 := by
        simp only [rootEvents, prod_filter]
      _ = ∏ p : P, if (n : ZMod p.val) ∈ roots ω p.val then (0 : ℝ) else 1 :=
        (P.prod_coe_sort (fun p : ℕ => if (n : ZMod p) ∈ roots ω p then (0 : ℝ) else 1)).symm
      _ = _ := by simp_rw [hroot]
  have hpoint (ω : ∀ p, Ω p) :
      (∑ n ∈ Ico a b, ∏ p : P,
        if (n : ZMod p.val) ∈ A p (ω p) then (0 : ℝ) else 1) ≤
        C * ((b : ℝ) - a) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val)) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
    have h := hbound P (roots ω) (fun _ => 0) a b Z hab hZ hP
      (fun p hp => by simpa [roots, hp] using hA ⟨p, hp⟩ (ω ⟨p, hp⟩))
      (by intros; norm_num)
    simp_rw [hprod] at h
    simpa only [mul_zero, add_zero,
      ← P.prod_coe_sort (fun p : ℕ => 1 - ((roots ω p).card : ℝ) / p), hroot] using h
  calc
    _ = ∑ ω, finiteProductMass μ ω * (∑ n ∈ Ico a b, ∏ p : P,
        if (n : ZMod p.val) ∈ A p (ω p) then (0 : ℝ) else 1) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      exact (finiteProductMass_product_expectation μ
        (fun p x => if (n : ZMod p.val) ∈ A p x then 0 else 1)).symm
    _ ≤ ∑ ω, finiteProductMass μ ω *
        (C * ((b : ℝ) - a) * (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val)) +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (finiteProductMass_nonneg μ hμ ω)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib]
      have hfirst : (∑ ω, finiteProductMass μ ω *
          (C * ((b : ℝ) - a) * ∏ p : P, (1 - ((A p (ω p)).card : ℝ) / p.val))) =
          C * ((b : ℝ) - a) * ∏ p : P, ∑ x, μ p x *
            (1 - ((A p x).card : ℝ) / p.val) := by
        rw [← finiteProductMass_product_expectation, mul_sum]
        apply sum_congr rfl
        intro ω _
        ring
      rw [hfirst, ← sum_mul, finiteProductMass_sum μ hμ1, one_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AffineLocalFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact local means for the three forms b, c, b+jc -/

namespace JointDickman

open Finset

open Classical in
theorem sum_two_residueWeights {α : Type*} [Fintype α] (t u : ℝ) (a b : α)
    (hab : a ≠ b) :
    ∑ x : α, residueWeight t a x * residueWeight u b x =
      (Fintype.card α : ℝ) - 2 + t + u := by
  have heq (x : α) : residueWeight t a x * residueWeight u b x =
      1 + (if x = a then t - 1 else 0) + (if x = b then u - 1 else 0) := by
    by_cases ha : x = a <;> by_cases hb : x = b
    · exact False.elim (hab (ha.symm.trans hb))
    all_goals simp [residueWeight, ha, hb, hab, Ne.symm hab]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true, if_true]
  ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ThreeFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem residueWeight_le_one {α : Type*} (a x : α) {t : ℝ} (ht : t ≤ 1) :
    residueWeight t a x ≤ 1 := by
  classical
  unfold residueWeight
  split_ifs <;> linarith

theorem one_le_cube_singular_factor {x d : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    1 ≤ (1 - d * x) ^ 3 * (1 + 24 * x) := by
  have hdx : 0 ≤ d * x := mul_nonneg hd hx
  have hdxle : d * x ≤ x := mul_le_of_le_one_left hx hd1
  have hcube : (1 / 8 : ℝ) ≤ (1 - d * x) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - d * x by linarith) 3
    norm_num at h
    exact h
  have hbernoulli : 1 - 3 * x ≤ (1 - d * x) ^ 3 := by
    have hprod := mul_nonneg (sq_nonneg (d * x)) (show 0 ≤ 3 - d * x by linarith)
    nlinarith
  have hextra := mul_le_mul_of_nonneg_left hcube (show 0 ≤ 24 * x by positivity)
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_ThreeFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-form rectangle sieve with its singular factor -/

namespace JointDickman

open Finset

theorem real_residue_sum_eq_range {p : ℕ} [NeZero p] (f : ZMod p → ℝ) :
    (∑ r : ZMod p, f r) = ∑ n ∈ range p, f n := by
  have h := residue_sum_eq_range (fun r => (f r : ℂ))
  exact_mod_cast h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_CoefficientSieveMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncating the prime conditions majorizes the actual coefficients -/

namespace JointDickman

open Finset

theorem sievedCoefficientWeight_nonneg (P Z n : ℕ) : 0 ≤ sievedCoefficientWeight P Z n :=
  prod_nonneg (fun p _ => residueWeight_nonneg _ _ (roughSieveTheta_bounds P p).1)

theorem roughSquarefreeWeight_le_sieved (P Z n : ℕ) :
    roughSquarefreeWeight (Nat.primesLE P) (1 / 2) n ≤ sievedCoefficientWeight P Z n := by
  classical
  by_cases hd : Disjoint n.primeFactors (Nat.primesLE P)
  · by_cases hsq : Squarefree n
    · have hcard : ArithmeticFunction.cardFactors n = n.primeFactors.card := by
        calc
          _ = ArithmeticFunction.cardFactors (∏ p ∈ n.primeFactors, p) :=
            congrArg ArithmeticFunction.cardFactors (Nat.prod_primeFactors_of_squarefree hsq).symm
          _ = _ := primeProduct_cardFactors _ (fun p hp => Nat.prime_of_mem_primeFactors hp)
      have heq (p : ℕ) (hp : p ∈ sievePrimes Z) :
          residueWeight (roughSieveTheta P p) 0 (n : ZMod p) =
            if p ∣ n then (1 / 2 : ℝ) else 1 := by
        have hpprime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
        by_cases hpn : p ∣ n
        · have hpP : ¬ p ≤ P := by
            intro h
            exact disjoint_left.mp hd (hpprime.mem_primeFactors hpn hsq.ne_zero)
              (Nat.mem_primesLE.mpr ⟨h, hpprime⟩)
          simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn, roughSieveTheta, hpP]
        · simp [residueWeight, ZMod.natCast_eq_zero_iff, hpn]
      have hsub : (sievePrimes Z).filter (fun p => p ∣ n) ⊆ n.primeFactors := by
        intro p hp
        have hmem := mem_filter.mp hp
        exact (Nat.mem_primesLE.mp (mem_filter.mp hmem.1).1).2.mem_primeFactors hmem.2 hsq.ne_zero
      have hsieve : sievedCoefficientWeight P Z n =
          (1 / 2 : ℝ) ^ ((sievePrimes Z).filter (fun p => p ∣ n)).card := by
        unfold sievedCoefficientWeight
        simp_rw [prod_congr rfl heq, ← prod_filter]
        simp
      rw [roughSquarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hd,
        squarefreeWeight, ArithmeticFunction.coe_mk, ite_eq_left hsq, hcard, hsieve]
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (card_le_card hsub)
    · simpa [roughSquarefreeWeight, squarefreeWeight, hd, hsq] using sievedCoefficientWeight_nonneg P Z n
  · simpa [roughSquarefreeWeight, hd] using sievedCoefficientWeight_nonneg P Z n

theorem coefficientWeight_le_sieved (B Z n : ℕ) :
    coefficientWeight B n ≤ coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n :=
  mul_le_mul_of_nonneg_left (roughSquarefreeWeight_le_sieved _ _ _) (coefficientScale_nonneg B)

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

theorem finiteExpectation_sum {J : Type*} [Fintype J] (w : Ω → ℝ) (f : J → Ω → ℝ) :
    finiteExpectation w (fun x => ∑ j, f j x) = ∑ j, finiteExpectation w (f j) := by
  simp only [finiteExpectation, mul_sum]
  exact sum_comm

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateRootKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_IntervalRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorption of the two-root interval sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_interval_remainder_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ L : ℝ, Real.exp (δ * B) ≤ L →
      coefficientScale B ^ 2 *
        (2 * (sieveCutoff (δ / 8) B + 1 : ℝ) * (sieveCutoff (δ / 8) B : ℝ) ^ 2) ≤ L := by
  have hlim : Tendsto (fun B : ℕ => 4 * ((B : ℝ) ^ 2 /
      Real.exp ((5 * δ / 8) * B))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 2 (by linarith : 0 < 5 * δ / 8)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 4
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    coefficientScale_eventually_le, sieveCutoff_eventually (by linarith : 0 < δ / 8)]
    with B hsmall hscale hcut
  intro L hL
  have hF : 1 ≤ Real.exp ((δ / 8) * B) := by
    have hZ1 : (1 : ℝ) ≤ sieveCutoff (δ / 8) B := by exact_mod_cast (show 1 ≤ sieveCutoff (δ / 8) B by omega)
    exact hZ1.trans hcut.2.2.2
  have hZ0 : (0 : ℝ) ≤ sieveCutoff (δ / 8) B := Nat.cast_nonneg _
  have hZF : (sieveCutoff (δ / 8) B : ℝ) + 1 ≤ 2 * Real.exp ((δ / 8) * B) := by linarith [hcut.2.2.2]
  have heq : Real.exp ((δ / 8) * B) ^ 3 * Real.exp ((5 * δ / 8) * B) = Real.exp (δ * B) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (B : ℝ) ^ 2 * (2 * (2 * Real.exp ((δ / 8) * B)) * Real.exp ((δ / 8) * B) ^ 2) := by
      apply mul_le_mul (pow_le_pow_left₀ (coefficientScale_nonneg B) hscale 2)
      · gcongr
        exact hcut.2.2.2
      · positivity
      · positivity
    _ = (4 * ((B : ℝ) ^ 2 / Real.exp ((5 * δ / 8) * B))) * Real.exp (δ * B) := by
      rw [← heq]
      field_simp
      ring
    _ ≤ 1 * Real.exp (δ * B) := mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ ≤ L := by simpa only [one_mul] using hL

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FormIntervalSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval sieve for individually weighted forms

Roots may coincide. The Euler factor is the exact residue average of all
local form weights, rather than a product that assumes distinct roots.
-/

namespace JointDickman

open Finset

/-- Independently weighting each form gives the precise local residue
factor, uniformly even when some roots coincide. -/
theorem form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (root : ∀ p : P, Fin k → ZMod p.val) (θ : P → Fin k → ℝ)
      (a b Z : ℕ), a ≤ b → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ n ∈ Ico a b, ∏ p : P, formRootWeight (root p) (θ p) (n : ZMod p.val)) ≤
      C * ((b : ℝ) - a) *
        (∏ p : P, (∑ r ∈ range p.val,
          formRootWeight (root p) (θ p) (r : ZMod p.val)) / p.val) +
        2 * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := randomized_root_interval_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P root θ a b Z hab hZ hP hθ
  let I : Finset (Fin k) := univ
  let Ω := {S : Finset (Fin k) // S ∈ I.powerset}
  let μ (p : P) (S : Ω) := bernoulliSubsetMass I (fun i => 1 - θ p i) S.val
  let A (p : P) (S : Ω) := S.val.image (root p)
  have hμ (p : P) (S : Ω) : 0 ≤ μ p S :=
    bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) (by
      intro i _
      constructor <;> linarith [(hθ p i).1, (hθ p i).2])
  have hμ1 (p : P) : ∑ S : Ω, μ p S = 1 := by
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S)]
    exact bernoulliSubsetMass_sum I _
  have hA (p : P) (S : Ω) : (A p S).card ≤ k := by
    calc
      _ ≤ S.val.card := card_image_le
      _ ≤ I.card := card_le_card (mem_powerset.mp S.property)
      _ = k := by simp [I]
  have hpoint (p : P) (n : ℕ) :
      (∑ S : Ω, μ p S * (if (n : ZMod p.val) ∈ A p S then 0 else 1)) =
        formRootWeight (root p) (θ p) (n : ZMod p.val) := by
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (if (n : ZMod p.val) ∈ S.val.image (root p) then 0 else 1)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (if (n : ZMod p.val) ∈ S.image (root p) then 0 else 1))]
    exact bernoulli_root_survival I (root p) (θ p) n
  have hdensity (p : P) :
      (∑ S : Ω, μ p S * (1 - ((A p S).card : ℝ) / p.val)) =
        (∑ r ∈ range p.val, formRootWeight (root p) (θ p) (r : ZMod p.val)) / p.val := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    have h := bernoulli_root_density (show 0 < Fintype.card (ZMod p.val) by
      rw [ZMod.card]; exact (hP p.val p.property).1.pos) I (root p) (θ p)
    simp only [ZMod.card] at h
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (1 - ((S.val.image (root p)).card : ℝ) / p.val)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (1 - ((S.image (root p)).card : ℝ) / p.val)), h]
    congr 1
    have hp := residue_sum_eq_range (fun r : ZMod p.val =>
      (formRootWeight (root p) (θ p) r : ℂ))
    exact_mod_cast hp
  have h := hbound P (fun _ => Ω) μ A a b Z hab hZ hP hμ hμ1 hA
  simpa only [hpoint, hdensity] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TwoFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two distinct affine roots and their weighted interval bound -/

namespace JointDickman

open Finset

theorem sum_two_residueWeights_bound {p : ℕ} [NeZero p]
    (t : ℝ) (a b : ZMod p) (hab : a ≠ b) :
    (∑ x : ZMod p, residueWeight t a x * residueWeight t b x) / p ≤
      (1 - (1 - t) / p) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  rw [sum_two_residueWeights t t a b hab, ZMod.card]
  have heq : (1 - (1 - t) / (p : ℝ)) ^ 2 - ((p : ℝ) - 2 + t + t) / p =
      ((1 - t) / p) ^ 2 := by field_simp <;> ring
  nlinarith [sq_nonneg ((1 - t) / (p : ℝ))]

theorem affine_residue_root {p : ℕ} [Fact p.Prime] (b j x : ZMod p) (hj : j ≠ 0) :
    b + j * x = 0 ↔ x = -b / j := by
  rw [eq_div_iff hj]
  constructor <;> intro h <;> linear_combination h

open Classical in
theorem formRootWeight_two {p : ℕ} (a b x : ZMod p) (t : ℝ) :
    formRootWeight ![a, b] (fun _ => t) x = residueWeight t a x * residueWeight t b x := by
  unfold formRootWeight
  rw [prod_filter, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, residueWeight]
  apply congrArg₂ (fun u v : ℝ => u * v)
  · exact @ite_cond_congr ℝ (a = x) (x = a) _ (Classical.propDecidable (x = a)) t 1 (propext eq_comm)
  · exact @ite_cond_congr ℝ (b = x) (x = b) _ (Classical.propDecidable (x = b)) t 1 (propext eq_comm)

theorem two_form_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (θ : ℕ → ℝ) (j b u v Z : ℕ),
      u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p ∧ ¬ p ∣ j ∧ ¬ p ∣ b) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) + j * n)) ≤
        C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := form_interval_sieve hFord hM (by norm_num : 0 < (2 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P θ j b u v Z huv hZ hP hθ
  classical
  let : ∀ p : P, Fact p.val.Prime := fun p => ⟨(hP p.val p.property).1⟩
  let root : (p : P) → Fin 2 → ZMod p.val := fun p => ![0, -(b : ZMod p.val) / (j : ZMod p.val)]
  let t : P → Fin 2 → ℝ := fun p _ => θ p.val
  have hroot (p : P) : (0 : ZMod p.val) ≠ -(b : ZMod p.val) / (j : ZMod p.val) := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have hb : (b : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.2
    have hj : (j : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.1
    exact (div_ne_zero (neg_ne_zero.mpr hb) hj).symm
  have heq (p : P) (x : ZMod p.val) : formRootWeight (root p) (t p) x =
      residueWeight (θ p.val) 0 x * residueWeight (θ p.val) 0 ((b : ZMod p.val) + j * x) := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have hj : (j : ZMod p.val) ≠ 0 := by simpa only [ne_eq, ZMod.natCast_eq_zero_iff] using (hP p.val p.property).2.2.2.1
    change formRootWeight ![0, -(b : ZMod p.val) / (j : ZMod p.val)] (fun _ => θ p.val) x = _
    rw [formRootWeight_two]
    congr 1
    by_cases hx : x = -(b : ZMod p.val) / (j : ZMod p.val)
    · simp [residueWeight, affine_residue_root _ _ _ hj, hx]
    · simp [residueWeight, affine_residue_root _ _ _ hj, hx]
  have hmean (p : P) : (∑ x ∈ range p.val, formRootWeight (root p) (t p) (x : ZMod p.val)) / p.val ≤
      (1 - (1 - θ p.val) / p.val) ^ 2 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    have h := sum_two_residueWeights_bound (θ p.val) (0 : ZMod p.val)
      (-(b : ZMod p.val) / (j : ZMod p.val)) (hroot p)
    rw [real_residue_sum_eq_range] at h
    have hpoint (x : ZMod p.val) : formRootWeight (root p) (t p) x =
        residueWeight (θ p.val) 0 x * residueWeight (θ p.val) (-(b : ZMod p.val) / (j : ZMod p.val)) x := by
      exact formRootWeight_two _ _ _ _
    simpa only [hpoint] using h
  have hh := hbound P root t u v Z huv hZ
    (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, (hP p hp).2.2.1⟩)
    (fun p _ => hθ p.val p.property)
  simp_rw [heq] at hh
  have hprod : (∏ p : P, (∑ x ∈ range p.val, formRootWeight (root p) (t p) (x : ZMod p.val)) / p.val) ≤
      (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 := by
    calc
      _ ≤ ∏ p : P, (1 - (1 - θ p.val) / p.val) ^ 2 := Finset.prod_le_prod
        (fun p _ => div_nonneg (sum_nonneg (fun x _ => by
          rw [heq]
          exact mul_nonneg (residueWeight_nonneg _ _ (hθ p.val p.property).1)
            (residueWeight_nonneg _ _ (hθ p.val p.property).1))) (Nat.cast_nonneg _))
        (fun p _ => hmean p)
      _ = _ := by rw [prod_pow, P.prod_coe_sort (fun p : ℕ => (1 - (1 - θ p) / p))]
  have hweight (n : ℕ) : (∏ p : P, residueWeight (θ p.val) 0 (n : ZMod p.val) *
      residueWeight (θ p.val) 0 ((b : ZMod p.val) + j * n)) =
      ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) * residueWeight (θ p) 0 ((b : ZMod p) + j * n) :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (θ p) 0 (n : ZMod p) *
      residueWeight (θ p) 0 ((b : ZMod p) + j * n))
  simp_rw [hweight] at hh
  simp_rw [heq] at hprod
  refine hh.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast huv)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DeletedPrimeFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cost of deleting exceptional primes from a two-form sieve -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem inverse_square_le_singular {p : ℕ} (hp : p.Prime) {d : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    ((1 - d / p)⁻¹) ^ 2 ≤ 1 + 24 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hs0 : 0 < 1 - d / (p : ℝ) := by
    have : d / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hs1 : 1 - d / (p : ℝ) ≤ 1 := sub_le_self _ (div_nonneg hd hp0.le)
  have hcube : 1 ≤ (1 - d / (p : ℝ)) ^ 3 * (1 + 24 / (p : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul] using
      one_le_cube_singular_factor (by positivity : (0 : ℝ) ≤ 1 / p) hx hd hd1
  have hsquare : (1 - d / (p : ℝ)) ^ 3 ≤ (1 - d / (p : ℝ)) ^ 2 := by
    exact pow_le_pow_of_le_one hs0.le hs1 (by norm_num)
  have hsq : 1 ≤ (1 - d / (p : ℝ)) ^ 2 * (1 + 24 / (p : ℝ)) :=
    hcube.trans (mul_le_mul_of_nonneg_right hsquare (by positivity))
  rw [inv_pow]
  exact (inv_le_iff_one_le_mul₀ (sq_pos_of_pos hs0)).mpr (by simpa only [mul_comm] using hsq)

open Classical in
theorem delete_two_prime_sets (P : Finset ℕ) (a b : ℕ → Prop) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 < f p ∧ f p ≤ 1) :
    (∏ p ∈ P.filter (fun p => ¬a p ∧ ¬b p), f p) ^ 2 ≤
      (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter a, (f p)⁻¹) ^ 2 *
        (∏ p ∈ P.filter b, (f p)⁻¹) ^ 2 := by
  rw [← prod_pow, prod_filter]
  have hlocal (p : ℕ) (hp : p ∈ P) :
      (if ¬a p ∧ ¬b p then f p ^ 2 else 1) ≤
        f p ^ 2 * (if a p then (f p)⁻¹ ^ 2 else 1) * (if b p then (f p)⁻¹ ^ 2 else 1) := by
    have heq : f p ^ 2 * (f p)⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (hf p hp).1.ne', one_pow]
    have hinv : 1 ≤ (f p)⁻¹ ^ 2 := one_le_pow₀ ((one_le_inv₀ (hf p hp).1).mpr (hf p hp).2)
    by_cases ha : a p <;> by_cases hb : b p <;>
      simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_self, and_false,
        false_and, ite_true, if_true, ite_false, if_false, mul_one, heq, one_mul] <;>
      first | exact hinv | exact le_rfl
  calc
    _ ≤ ∏ p ∈ P, f p ^ 2 * (if a p then (f p)⁻¹ ^ 2 else 1) *
        (if b p then (f p)⁻¹ ^ 2 else 1) := by
      apply Finset.prod_le_prod
      · intro p _
        split_ifs <;> positivity
      · exact hlocal
    _ = _ := by
      simp only [prod_mul_distrib, ← prod_pow, ← prod_filter]

open Classical in
theorem deleted_divisor_factor_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ → ℝ) (hd : ∀ p ∈ P, 0 ≤ d p ∧ d p ≤ 1) {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P.filter (fun p => p ∣ j), (1 - d p / p)⁻¹) ^ 2 ≤ singularFactor 24 j := by
  rw [← prod_pow]
  calc
    _ ≤ ∏ p ∈ P.filter (fun p => p ∣ j), (1 + 24 / (p : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
      intro p hp
      exact inverse_square_le_singular (hP p (mem_filter.mp hp).1)
        (hd p (mem_filter.mp hp).1).1 (hd p (mem_filter.mp hp).1).2
    _ ≤ _ := by
      apply prod_le_prod_of_subset_of_one_le
      · intro p hp
        exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
      · intros; positivity
      · intro p _ _
        exact le_add_of_nonneg_right (by positivity)

/-- Prime divisors above B^1000 have uniformly negligible reciprocal mass
on every fixed logarithmic size range. -/
theorem large_divisor_inverse_square_bound (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ (b : ℕ) (S : Finset ℕ), b ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ * B) → S ⊆ b.primeFactors →
      (∀ p ∈ S, auxiliaryCutoff B ≤ p) →
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) ^ 2 ≤ Real.exp 1 := by
  have hlim : Tendsto (fun B : ℕ => (4 * κ / Real.log 2) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have h := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (4 * κ / Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using h
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro b S hb hbsize hS hcut
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast pow_pos (Nat.zero_lt_of_lt hB) 1000
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
  have hprod : (∏ p ∈ S, p) ∣ b :=
    (prod_dvd_prod_of_subset _ _ id hS).trans (Nat.prod_primeFactors_dvd b)
  have hcard : (S.card : ℝ) * Real.log 2 ≤ κ * B := by
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hle : (∏ p ∈ S, p : ℕ) ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hprod
    have hp0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    have hle' : (∏ p ∈ S, p : ℕ) ≤ (b : ℝ) := by exact_mod_cast hle
    have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
    exact (Real.log_le_log hp0 hle').trans
      (by simpa only [Real.log_exp] using Real.log_le_log hbpos hbsize)
  have hinv := inverseSelectedPrimeOdds_le hP0 (by norm_num : (0 : ℝ) ≤ 1)
    le_rfl S hprime (fun p hp => by exact_mod_cast hcut p hp)
  have hs0 : 0 ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    have hinvp : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    exact inv_nonneg.mpr (by linarith)
  calc
    _ ≤ (Real.exp (2 * (S.card : ℝ) / auxiliaryCutoff B)) ^ 2 := pow_le_pow_left₀ hs0 hinv 2
    _ = Real.exp (4 * (S.card : ℝ) / auxiliaryCutoff B) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcard' := (le_div_iff₀ hlog2).mpr hcard
      have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard' (by norm_num : (0 : ℝ) ≤ 4)) hP0.le
      apply h.trans
      calc
        _ = (4 * κ / Real.log 2) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
        _ ≤ 1 := hsmall

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_GoodPrimeDensity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euler product after removing primes dividing j and b -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem good_sieve_density_bound (κ : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ Z j b : ℕ, j ≠ 0 → b ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ * B) → Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∏ p ∈ goodSievePrimes Z j b, (1 - roughSieveRate (auxiliaryCutoff B) p)) ^ 2 ≤
        roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1 := by
  classical
  filter_upwards [large_divisor_inverse_square_bound κ] with B hlarge
  intro Z j b hj hb hbsize hbrough
  let P := sievePrimes Z
  let d := fun p => 1 - roughSieveTheta (auxiliaryCutoff B) p
  let f := fun p => 1 - roughSieveRate (auxiliaryCutoff B) p
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have hd (p : ℕ) (_hp : p ∈ P) : 0 ≤ d p ∧ d p ≤ 1 := by
    have h := roughSieveTheta_bounds (auxiliaryCutoff B) p
    dsimp [d]
    constructor <;> linarith
  have hf (p : ℕ) (hp : p ∈ P) : 0 < f p ∧ f p ≤ 1 := by
    have h := roughSieveRate_bounds (auxiliaryCutoff B) p (hP p hp)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hinv : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    dsimp [f]
    constructor <;> linarith
  have hjfactor : (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 ≤ singularFactor 24 j :=
    deleted_divisor_factor_le P hP d hd hj
  let S := P.filter (fun p => p ∣ b)
  have hS : S ⊆ b.primeFactors := fun p hp =>
    (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hb
  have hcut (p : ℕ) (hp : p ∈ S) : auxiliaryCutoff B ≤ p := by
    by_contra h
    have hpP : p ∈ Nat.primesLE (auxiliaryCutoff B) :=
      Nat.mem_primesLE.mpr ⟨Nat.le_of_lt (Nat.lt_of_not_ge h), hP p (mem_filter.mp hp).1⟩
    exact disjoint_left.mp hbrough (hS hp) hpP
  have hinv := hlarge b S hb hbsize hS hcut
  have hbprod : (∏ p ∈ S, (f p)⁻¹) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ := by
    apply Finset.prod_le_prod
    · intro p hp
      exact inv_nonneg.mpr (hf p (mem_filter.mp hp).1).1.le
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p (mem_filter.mp hp).1).two_le
      have hinvp : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      apply (inv_le_inv₀ (hf p (mem_filter.mp hp).1).1 (by linarith : 0 < 1 - 1 / (p : ℝ))).mpr
      have h := (roughSieveRate_bounds (auxiliaryCutoff B) p (hP p (mem_filter.mp hp).1)).2.1
      dsimp [f]
      linarith
  have hbfactor : (∏ p ∈ S, (f p)⁻¹) ^ 2 ≤ Real.exp 1 :=
    (pow_le_pow_left₀ (prod_nonneg (fun p hp => inv_nonneg.mpr (hf p (mem_filter.mp hp).1).1.le)) hbprod 2).trans hinv
  have hdelete := delete_two_prime_sets P (fun p => p ∣ j) (fun p => p ∣ b) f hf
  have hpost : (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 *
      (∏ p ∈ S, (f p)⁻¹) ^ 2 ≤
      roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hjfactor (sq_nonneg _)
    · exact hbfactor
    · exact sq_nonneg _
    · exact mul_nonneg (sq_nonneg _) (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  have hdelete' : (∏ p ∈ goodSievePrimes Z j b, f p) ^ 2 ≤
      (∏ p ∈ P, f p) ^ 2 * (∏ p ∈ P.filter (fun p => p ∣ j), (f p)⁻¹) ^ 2 *
        (∏ p ∈ S, (f p)⁻¹) ^ 2 := by
    convert hdelete using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [goodSievePrimes, P, S] <;> congr!)
  exact hdelete'.trans hpost

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientPairMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual two-coefficient weight and its good-prime majorant -/

namespace JointDickman

open Finset

theorem coefficient_pair_le_good_primes (B Z b j n : ℕ) :
    coefficientWeight B n * coefficientWeight B (b + j * n) ≤ coefficientScale B ^ 2 *
      ∏ p ∈ goodSievePrimes Z j b, residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
        residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) + j * n) := by
  classical
  let f := fun p => residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 (n : ZMod p) *
    residueWeight (roughSieveTheta (auxiliaryCutoff B) p) 0 ((b : ZMod p) + j * n)
  have hf0 (p : ℕ) : 0 ≤ f p := mul_nonneg
    (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
    (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1)
  have hf1 (p : ℕ) : f p ≤ 1 := by
    have h := mul_le_mul (residueWeight_le_one (0 : ZMod p) n (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
      (residueWeight_le_one (0 : ZMod p) ((b : ZMod p) + j * n) (roughSieveTheta_bounds (auxiliaryCutoff B) p).2)
      (residueWeight_nonneg _ _ (roughSieveTheta_bounds (auxiliaryCutoff B) p).1) zero_le_one
    simpa only [mul_one] using h
  have hprod : (∏ p ∈ sievePrimes Z, f p) ≤ ∏ p ∈ goodSievePrimes Z j b, f p :=
    prod_le_prod_of_subset_of_le_one (filter_subset _ _) (fun p _ => hf0 p) (fun p _ _ => hf1 p)
  calc
    _ ≤ (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z n) *
        (coefficientScale B * sievedCoefficientWeight (auxiliaryCutoff B) Z (b + j * n)) :=
      mul_le_mul (coefficientWeight_le_sieved B Z n) (coefficientWeight_le_sieved B Z (b + j * n))
        (coefficientWeight_nonneg _ _) (mul_nonneg (coefficientScale_nonneg _) (sievedCoefficientWeight_nonneg _ _ _))
    _ = coefficientScale B ^ 2 * ∏ p ∈ sievePrimes Z, f p := by
      simp only [sievedCoefficientWeight, f, prod_mul_distrib, Nat.cast_add, Nat.cast_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientPairBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform fixed-coefficient two-form estimate (equation (6)) -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The fixed rough coefficient contributes only a bounded Euler factor;
all dependence on the nonzero positive slope is through the singular factor. -/
theorem coefficient_two_form_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ j b u v : ℕ,
      j ≠ 0 → b ≠ 0 → (b : ℝ) ≤ Real.exp (κ * B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      u ≤ v → Real.exp (δ * B) ≤ (v : ℝ) - u →
      (∑ n ∈ Ico u v, coefficientWeight B n * coefficientWeight B (b + j * n)) ≤
        C * ((v : ℝ) - u) * singularFactor 24 j := by
  classical
  obtain ⟨C, hC, hsieve⟩ := two_form_interval_sieve hFord hM
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM
    (by linarith : 0 < (δ / 8) / 2)
  refine ⟨C * M ^ 2 * Real.exp 1 + 1, by positivity, ?_⟩
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8),
    good_sieve_density_bound κ, coefficient_interval_remainder_small hδ,
    eventually_gt_atTop 1] with B hcut hgood herror hB
  intro j b u v hj hb hbsize hbrough huv hL
  let Z := sieveCutoff (δ / 8) B
  let P := goodSievePrimes Z j b
  let θ := roughSieveTheta (auxiliaryCutoff B)
  have hP (p : ℕ) (hp : p ∈ P) :
      p.Prime ∧ p ≤ Z ∧ 4 ≤ p ∧ ¬p ∣ j ∧ ¬p ∣ b := by
    obtain ⟨hpS, hpj, hpb⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hpS
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, by omega, hpj, hpb⟩
  have hs := hsieve P θ j b u v Z huv hcut.1 hP (fun p _ => roughSieveTheta_bounds _ p)
  have hg := hgood Z j b hj hb hbsize hbrough
  have hn := hnorm B Z hB hcut.2.1 hcut.2.2.1
  have hL0 : 0 ≤ (v : ℝ) - u := sub_nonneg.mpr (by exact_mod_cast huv)
  have hS0 : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  have hscaled : coefficientScale B ^ 2 * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 ≤
      M ^ 2 * singularFactor 24 j * Real.exp 1 := by
    calc
      _ ≤ coefficientScale B ^ 2 *
          (roughSieveDensity (auxiliaryCutoff B) Z ^ 2 * singularFactor 24 j * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hg (sq_nonneg _)
      _ = (coefficientScale B * roughSieveDensity (auxiliaryCutoff B) Z) ^ 2 *
          singularFactor 24 j * Real.exp 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (coefficientScale_nonneg B) (roughSieveDensity_nonneg _ _)) hn 2) hS0)
        (Real.exp_pos _).le
  have herr := herror ((v : ℝ) - u) hL
  calc
    _ ≤ ∑ n ∈ Ico u v, coefficientScale B ^ 2 *
        ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) + j * n) :=
      sum_le_sum (fun n _ => coefficient_pair_le_good_primes B Z b j n)
    _ = coefficientScale B ^ 2 * (∑ n ∈ Ico u v,
        ∏ p ∈ P, residueWeight (θ p) 0 (n : ZMod p) *
          residueWeight (θ p) 0 ((b : ZMod p) + j * n)) := by rw [mul_sum]
    _ ≤ coefficientScale B ^ 2 *
        (C * ((v : ℝ) - u) * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2 +
          2 * (Z + 1 : ℝ) * (Z : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ ≤ C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1) + ((v : ℝ) - u) := by
      rw [mul_add]
      apply add_le_add (b := C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1)) ?_ herr
      calc
        _ = C * ((v : ℝ) - u) * (coefficientScale B ^ 2 * (∏ p ∈ P, (1 - (1 - θ p) / p)) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (mul_nonneg hC.le hL0)
    _ ≤ C * ((v : ℝ) - u) * (M ^ 2 * singularFactor 24 j * Real.exp 1) +
        ((v : ℝ) - u) * singularFactor 24 j :=
      add_le_add le_rfl (le_mul_of_one_le_right hL0 (singularFactor_one_le (by norm_num) j))
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_TwoFormHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.JointDickman.coefficientWeight_zero _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic form of the fixed-endpoint coefficient bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem two_form_harmonic_box
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ c ∈ Ico q (4*q),
        (coefficientWeight B c*coefficientWeight B (b+j*c))/(b+j*c : ℕ)) ≤
          K/(T : ℝ)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := coefficient_two_form_bound hFord hM hδ κ
  refine ⟨3*K,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T q j b hT hq hTb hj hbsize hbrough
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hqr : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq0 : 0 < q := by exact_mod_cast hqr
  have hb : b ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.mul_pos hT hq0) hTb)
  have hlen : Real.exp (δ*B) ≤ (4*q : ℕ)-(q : ℝ) := by
    push_cast
    linarith
  have hsum := hB j b q (4*q) hj hb hbsize hbrough (by omega) hlen
  have hden0 : (0 : ℝ) < (T : ℝ)*q := mul_pos hTr hqr
  calc
    _ ≤ (∑ c ∈ Ico q (4*q), coefficientWeight B c*coefficientWeight B (b+j*c))/((T : ℝ)*q) := by
      rw [sum_div]
      apply sum_le_sum
      intro c _
      have hden : (T : ℝ)*q ≤ (b+j*c : ℕ) := by
        exact_mod_cast hTb.trans (Nat.le_add_right b (j*c))
      exact div_le_div_of_nonneg_left
        (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _)) hden0 hden
    _ ≤ (K*((4*q : ℕ)-(q : ℝ))*singularFactor 24 j)/((T : ℝ)*q) :=
      div_le_div_of_nonneg_right hsum hden0.le
    _ = _ := by
      push_cast
      field_simp
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointCoefficientMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The half-prime coefficient mass at a fixed first endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- After averaging the second endpoint, each fixed first coefficient
costs O(Sigma(j)/(B T)); its fair-split prefactor later supplies B. -/
theorem endpointCoefficientMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) (κ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T q j b : ℕ,
      0 < T → Real.exp (δ*B) ≤ (q : ℝ) → T*q ≤ b → j ≠ 0 →
      (b : ℝ) ≤ Real.exp (κ*B) →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      endpointCoefficientMass B b j q ≤ K/((B : ℝ)*T)*singularFactor 24 j := by
  obtain ⟨K,hK,harmonic⟩ := two_form_harmonic_box hFord hM hδ κ
  obtain ⟨D,hD,hdom⟩ := primeProductMass_coefficient_domination hM
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [harmonic,hdom,eventually_gt_atTop 0] with B hB hmass hB0
  intro T q j b hT hq hTb hj hbsize hbrough
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hqr : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hq
  have hq0 : 0 < q := by exact_mod_cast hqr
  have hb : 0 < b := lt_of_lt_of_le (Nat.mul_pos hT hq0) hTb
  have hs := hB T q j b hT hq hTb hj hbsize hbrough
  have hpoint (c : ℕ) : (if (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) then
      primeProductMass (auxiliaryPrimes B) (1/2) (b+j*c)*coefficientWeight B c else 0) ≤
      D/(B : ℝ)*(coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) := by
    split_ifs with ha
    · have hh := mul_le_mul_of_nonneg_right (hmass (b+j*c)
        (lt_of_lt_of_le hb (Nat.le_add_right _ _)) ha) (coefficientWeight_nonneg B c)
      convert hh using 1 <;> first | rfl | ring
    · exact mul_nonneg (div_nonneg hD.le hBr.le)
        (div_nonneg (mul_nonneg (coefficientWeight_nonneg B c) (coefficientWeight_nonneg B (b+j*c)))
          (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ c ∈ Ico q (4*q), D/(B : ℝ)*
        (coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) :=
      sum_le_sum (fun c _ => hpoint c)
    _ = D/(B : ℝ)*(∑ c ∈ Ico q (4*q),
        coefficientWeight B c*coefficientWeight B (b+j*c)/(b+j*c : ℕ)) := (mul_sum _ _ _).symm
    _ ≤ D/(B : ℝ)*(K/(T : ℝ)*singularFactor 24 j) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hD.le hBr.le)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EndpointCoefficientTest
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pushing the second endpoint's fair split onto its coefficient -/

namespace JointDickman
open Finset

theorem endpointCoefficientTest_nonneg (B b j q a : ℕ) :
    0 ≤ endpointCoefficientTest B b j q a := by
  apply sum_nonneg
  intro c _
  split_ifs
  · exact coefficientWeight_nonneg B c
  · rfl

theorem endpointCoefficientTest_ge {B b j q a c : ℕ}
    (hc : c ∈ Ico q (4*q)) (ha : a = b+j*c)
    (hsize : (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)) :
    coefficientWeight B c ≤ endpointCoefficientTest B b j q a := by
  classical
  calc
    _ = (if a = b+j*c ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)
        then coefficientWeight B c else 0) := by rw [ite_eq_left ⟨ha,hsize⟩]
    _ ≤ _ := single_le_sum (f := fun d => if a = b+j*d ∧ (a : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) then coefficientWeight B d else 0) (fun d _ => by split_ifs; exact coefficientWeight_nonneg B d; rfl) hc

/-- This identity uses the exact prime-product pushforward, so no local
limit or independence beyond the already constructed endpoint law is assumed. -/
theorem endpointCoefficientTest_mean (B b j q : ℕ) :
    (∑ A ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
        endpointCoefficientTest B b j q (∏ p ∈ A, p)) =
      endpointCoefficientMass B b j q := by
  classical
  unfold endpointCoefficientTest endpointCoefficientMass
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  by_cases hs : (b+j*c : ℕ) ≤ Real.exp ((16/5 : ℝ)*B)
  · simp only [hs,ite_true, if_true]
    unfold primeProductMass
    rw [sum_mul]
    apply sum_congr rfl
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b+j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_true, if_true]
    · simp only [ha,false_and,ite_false, if_false,mul_zero,zero_mul]
  · rw [ite_eq_right hs]
    apply sum_eq_zero
    intro A _
    by_cases ha : (∏ p ∈ A, p) = b+j*c
    · rw [ha]
      simp only [eq_self,true_and,hs,ite_false, if_false,mul_zero]
    · simp only [ha,false_and,ite_false, if_false,mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointRowScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A coefficient box chosen from the fixed endpoint alone -/

namespace JointDickman
open Finset

/-- One box, determined solely by the first coefficient, contains every
possible quotient in its support window. -/
theorem endpointRowScale_window {B T b c : ℕ} (hB : 2 ≤ B) (hT : 0 < T)
    (hc : 0 < c) (hlog : (B : ℝ) ≤ Real.log c)
    (hlo : T*c ≤ b) (hhi : b ≤ 2*T*c) :
    Real.exp ((1/2 : ℝ)*B) ≤ (endpointRowScale T b : ℝ) ∧
      c ∈ Ico (endpointRowScale T b) (4*endpointRowScale T b) ∧
      T*endpointRowScale T b ≤ b := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hlo' : (T : ℝ)*c ≤ b := by exact_mod_cast hlo
  have hhi' : (b : ℝ) ≤ 2*T*c := by exact_mod_cast hhi
  have hqc : endpointRowScale T b ≤ c := by
    apply Nat.ceil_le.mpr
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2*T)).mpr (by nlinarith)
  have hbq : (b : ℝ) ≤ (endpointRowScale T b : ℝ)*(2*T) := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2*T)).mp (Nat.le_ceil _)
  have hcq : (c : ℝ) ≤ 2*(endpointRowScale T b : ℝ) := by nlinarith
  have hq0 : (0 : ℝ) < endpointRowScale T b := by nlinarith
  have hclt : c < 4*endpointRowScale T b := by exact_mod_cast (by nlinarith : (c : ℝ) < 4*(endpointRowScale T b : ℝ))
  have hexp : Real.exp (B : ℝ) ≤ c := (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hcr)
  have hB' : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have he2 : (2 : ℝ) ≤ Real.exp ((1/2 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((1/2 : ℝ)*B)
    linarith
  have he : Real.exp (B : ℝ) = Real.exp ((1/2 : ℝ)*B)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  refine ⟨?_,mem_Ico.mpr ⟨hqc,hclt⟩,(Nat.mul_le_mul_left T hqc).trans hlo⟩
  rw [he] at hexp
  nlinarith

/-- All possible endpoint coefficients are in the fixed range needed for
the previously proved prime-product domination. -/
theorem endpointCoefficientWindow_size {B T b : ℕ} (hB : 10 ≤ B)
    (hT : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hw : EndpointCoefficientWindow B T b) :
    (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  obtain ⟨c,hc,_,hcsize,_,hbc⟩ := hw
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hce : (c : ℝ) ≤ Real.exp (2*B) := by
    rw [← Real.exp_log hcr]
    exact Real.exp_le_exp.mpr hcsize
  have hB' : (10 : ℝ) ≤ B := by exact_mod_cast hB
  have he2 : (2 : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((1/10 : ℝ)*B)
    linarith
  calc
    (b : ℝ) ≤ 2*(T : ℝ)*c := by exact_mod_cast hbc
    _ ≤ Real.exp ((1/10 : ℝ)*B)*Real.exp ((1/10 : ℝ)*B)*Real.exp (2*B) := by
      exact mul_le_mul (mul_le_mul he2 hT (Nat.cast_nonneg T) (Real.exp_pos _).le)
        hce (Nat.cast_nonneg c) (by positivity)
    _ = Real.exp ((11/5 : ℝ)*B) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EndpointConditionalMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform mean at one independently averaged endpoint -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem supportedEndpointTest_nonneg (B T b j a : ℕ) :
    0 ≤ supportedEndpointTest B T b j a := by
  unfold supportedEndpointTest
  split_ifs
  · exact endpointCoefficientTest_nonneg _ _ _ _ _
  · rfl

theorem supportedEndpointTest_ge {B T b j a c : ℕ}
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (hc : 0 < c) (hlog : (B : ℝ) ≤ Real.log c) (hlog' : Real.log c ≤ 2*B)
    (hlo : T*c ≤ b) (hhi : b ≤ 2*T*c) (ha : a = b+j*c)
    (hasize : a ≤ 2*T*c) :
    coefficientWeight B c ≤ supportedEndpointTest B T b j a := by
  have hw : EndpointCoefficientWindow B T b := ⟨c,hc,hlog,hlog',hlo,hhi⟩
  have hwa : EndpointCoefficientWindow B T a :=
    ⟨c,hc,hlog,hlog',by omega,hasize⟩
  rw [supportedEndpointTest,ite_eq_left hw]
  exact endpointCoefficientTest_ge (endpointRowScale_window (by omega) hT hc hlog hlo hhi).2.1
    ha (endpointCoefficientWindow_size hB hTs hwa)

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

theorem candidateMeanWeight_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (hχ : ∀ e, 0 ≤ χ e) (e : BlockCandidateIndex M) :
    0 ≤ candidateMeanWeight B L τ C S χ e := by
  exact finiteExpectation_nonneg _ _ (independentPrimeSetMass_nonneg B)
    (fun R => candidateRootWeight_nonneg B L τ C S χ hχ e R.val)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateForwardMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward candidate mass and the vanishing independent-root error -/

namespace JointDickman
open Finset Filter PublishedInputs
open scoped Topology

/-- The forward entry is zero once its lag is outside the candidate support. -/
theorem latentCandidateKernel_forward_zero {B L T H M : ℕ} {τ C : ℝ}
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (i k : Fin M)
    (hik : i < k) (hlag : T ≤ k.val-i.val) :
    latentCandidateKernel B L T H M τ C S χ i k = 0 := by
  classical
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  apply sum_eq_zero
  intro A _
  apply sum_eq_zero
  intro D _
  have hn : ¬ BlockCandidateAdmissible B L T H τ C ((i,k),(A,D)) := by
    intro he
    have ht := he.2.2.1
    change k.val-i.val < T at ht
    omega
  exact ite_eq_right hn

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

theorem candidateSiteKernel_diag (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i i a b = 0 :=
  latentCandidateKernel_diag _ _ _ _ _ _ _ _ _ _

theorem candidateSiteKernel_symm (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i k a b =
      candidateSiteKernel B L T H M τ C χ k i b a := by
  by_cases h : i = k
  · subst k
    rw [candidateSiteKernel_diag,candidateSiteKernel_diag]
  · unfold candidateSiteKernel
    rw [latentCandidateKernel_symm]
    apply latentCandidateKernel_local <;> simp [h,Ne.symm h]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentContributionCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The five-weight bound for one latent representation -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem candidateMeanWeight_small
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ e, candidateMeanWeight B L τ C S χ e ≤ (B : ℝ)^(-(22/100 : ℝ)) := by
  let ε := (1-5*weightExponent τ-(22/100 : ℝ))/12
  have hm := (weight_margins_of_le_samplingTau hτsmall).2.2
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  have hexp : 5*(weightExponent τ+ε)+ε-1 ≤ -(22/100 : ℝ) := by
    dsimp [ε]
    linarith
  obtain ⟨K,hK,hroot⟩ := independentRootMean_bounded hM
  have hgrow := ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K
  filter_upwards [regular_weights_cap hL hτ hε,hroot,hgrow,eventually_gt_atTop 1]
    with B hcap hroot hgrow hB
  intro C M S χ hχ e
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  let Q := (B : ℝ)^(weightExponent τ+ε)
  have hQ : 0 ≤ Q := Real.rpow_nonneg (Nat.cast_nonneg B) _
  have hpair (n : ℕ) (R : Finset ℕ) :
      regularCoefficientWeight B L τ C n*regularResidueWeight B L τ C R ≤ Q*Q :=
    mul_le_mul ((hcap C).2 n) ((hcap C).1 R)
      (regularResidueWeight_nonneg B L τ C R) hQ
  let W := regularCoefficientWeight B L τ C (candidateLow e)*
      regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
      (regularCoefficientWeight B L τ C (candidateHigh e)*
        regularResidueWeight B L τ C (S e.1.2 \ e.2.2))*
      regularCoefficientWeight B L τ C (candidateQuotient e)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _)))
      (regularCoefficientWeight_nonneg _ _ _ _ _)
  have hcapW : W ≤ Q^5 := by
    have hh := mul_le_mul (mul_le_mul (hpair (candidateLow e) (S e.1.1 \ e.2.1))
      (hpair (candidateHigh e) (S e.1.2 \ e.2.2))
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) (regularResidueWeight_nonneg _ _ _ _ _))
      (mul_nonneg hQ hQ)) ((hcap C).2 (candidateQuotient e))
      (regularCoefficientWeight_nonneg _ _ _ _ _) (by positivity)
    convert hh using 1 <;> first | rfl | ring
  rw [candidateMeanWeight_eq]
  change W/(B : ℝ)*χ e*independentRootMean B L τ C ≤ _
  calc
    _ ≤ W/(B : ℝ)*independentRootMean B L τ C :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (div_nonneg hW hB0.le) (hχ e))
        (independentRootMean_nonneg _ _ _ _)
    _ ≤ (Q^5/(B : ℝ))*(B : ℝ)^ε :=
      mul_le_mul (div_le_div_of_nonneg_right hcapW hB0.le) ((hroot L τ C).trans hgrow)
        (independentRootMean_nonneg _ _ _ _) (by positivity)
    _ = (B : ℝ)^(5*(weightExponent τ+ε)+ε-1) := by
      have hp : (B : ℝ)^(5*(weightExponent τ+ε)+ε-1) =
          ((B : ℝ)^(weightExponent τ+ε))^5*(B : ℝ)^ε/(B : ℝ) := by
        calc
          _ = (B : ℝ)^((weightExponent τ+ε)*5+ε)/(B : ℝ) := by
            rw [Real.rpow_sub hB0,Real.rpow_one]
            congr 2
            ring
          _ = ((B : ℝ)^((weightExponent τ+ε)*5)*(B : ℝ)^ε)/(B : ℝ) := by
            rw [Real.rpow_add hB0]
          _ = _ := by
            rw [Real.rpow_mul hB0.le]
            norm_num
      rw [hp]
      dsimp [Q]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB.le) hexp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMultiplicity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Keeping representation multiplicity in the latent second moment -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentCandidateKernel_representation_sum (B L T H M : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ)
    (i k : Fin M) (hik : i < k) :
    latentCandidateKernel B L T H M τ C S χ i k =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i k (S i) (S k),
        candidateMeanWeight B L τ C S χ ((i,k),ab) := by
  rw [latentCandidateKernel_pair B L T H τ C S χ i k hik]
  simp only [candidatePairRepresentations,Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]

/-- The multiplicity factor must be averaged with a first representation;
replacing it by one would incorrectly discard collisions on an edge. -/
theorem latentCandidateKernel_square_multiplicity
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ) (S : Fin M → Finset ℕ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ i k : Fin M, i < k →
      (latentCandidateKernel B L T H M τ C S χ i k)^2 ≤
        (B : ℝ)^(-(22/100 : ℝ))*
          (candidatePairRepresentations B L T H τ C i k (S i) (S k)).card*
          latentCandidateKernel B L T H M τ C S χ i k := by
  filter_upwards [candidateMeanWeight_small hM hL hτ hτsmall] with B hcap
  intro C T H M S χ hχ i k hik
  have hnn := latentCandidateKernel_nonneg B L T H M τ C S χ (fun e => (hχ e).1) i k
  have hbound : latentCandidateKernel B L T H M τ C S χ i k ≤
      (B : ℝ)^(-(22/100 : ℝ))*
        (candidatePairRepresentations B L T H τ C i k (S i) (S k)).card := by
    rw [latentCandidateKernel_representation_sum B L T H M τ C S χ i k hik]
    calc
      _ ≤ ∑ _ab ∈ candidatePairRepresentations B L T H τ C i k (S i) (S k),
          (B : ℝ)^(-(22/100 : ℝ)) :=
        sum_le_sum (fun ab _ => hcap C M S χ (fun e => (hχ e).2) ((i,k),ab))
      _ = _ := by simp [mul_comm]
  nlinarith [mul_le_mul_of_nonneg_right hbound hnn]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedRemainderLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact measure obtained by weighting the first representation

After requiring a coefficient and weighting the remaining primes by one
half, the unforced indicators have probability 1/(2p-1). Regularity tests
remain inside the expectation and do not alter its normalization.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem required_prime_mass_factor {P A S : Finset ℕ}
    (hA : A ⊆ S) (_hS : S ⊆ P) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) S =
      (1/(∏ p ∈ A, p : ℕ))*
        bernoulliSubsetMass (P \ A) (fun p => 1/(p : ℝ)) (S \ A) := by
  have he : (P \ A) \ (S \ A) = P \ S := by
    ext p
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hp, ha⟩, hs⟩
      exact ⟨hp,fun h => hs ⟨h,ha⟩⟩
    · rintro ⟨hp,hs⟩
      exact ⟨⟨hp,fun h => hs (hA h)⟩,fun h => hs h.1⟩
  have hp : (∏ p ∈ A, 1/(p : ℝ)) = 1/(∏ p ∈ A, p : ℕ) := by
    simp only [one_div,prod_inv_distrib,Nat.cast_prod]
  unfold bernoulliSubsetMass
  rw [he,← prod_sdiff hA,← hp]
  ring

theorem half_weight_tilt (P R : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hR : R ⊆ P) :
    bernoulliSubsetMass P (fun p => 1/(p : ℝ)) R*(1/2 : ℝ)^R.card =
      primeNormalizer P (1/2)*
        bernoulliSubsetMass P (fun p => 1/(2*(p : ℝ)-1)) R := by
  have hs (p : ℕ) (hp : p ∈ P) :
      1/(p : ℝ)*(1/2) = (1-(1/2 : ℝ)/p)*(1/(2*(p : ℝ)-1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)*2-1 ≠ 0 := by linarith
    field_simp [hp0, hd]
  have hn (p : ℕ) (hp : p ∈ P) :
      1-1/(p : ℝ) = (1-(1/2 : ℝ)/p)*(1-1/(2*(p : ℝ)-1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)*2-1 ≠ 0 := by linarith
    field_simp [hp0, hd]
    ring
  have hsel : (∏ p ∈ R, 1/(p : ℝ)*(1/2)) =
      ∏ p ∈ R, (1-(1/2 : ℝ)/p)*(1/(2*(p : ℝ)-1)) :=
    prod_congr rfl (fun p hp => hs p (hR hp))
  have hnon : (∏ p ∈ P \ R, (1-1/(p : ℝ))) =
      ∏ p ∈ P \ R, (1-(1/2 : ℝ)/p)*(1-1/(2*(p : ℝ)-1)) :=
    prod_congr rfl (fun p hp => hn p (mem_sdiff.mp hp).1)
  unfold bernoulliSubsetMass primeNormalizer
  rw [← prod_sdiff hR (f := fun p : ℕ => 1-(1/2 : ℝ)/p)]
  rw [prod_mul_distrib,prod_const] at hsel
  rw [mul_right_comm, hsel,hnon,prod_mul_distrib,prod_mul_distrib]
  ring

theorem weighted_required_prime_mass {B : ℕ} {A S : Finset ℕ}
    (hA : A ⊆ S) (hS : S ⊆ auxiliaryPrimes B) :
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
        bernoulliSubsetMass (auxiliaryPrimes B \ A)
          (fun p => 1/(2*(p : ℝ)-1)) (S \ A) := by
  rw [required_prime_mass_factor hA hS]
  have hR : S \ A ⊆ auxiliaryPrimes B \ A := sdiff_subset_sdiff hS subset_rfl
  have ht := half_weight_tilt (auxiliaryPrimes B \ A) (S \ A)
    (fun p hp => auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1) hR
  unfold residueBaseWeight remainderTiltNormalizer
  calc
    _ = auxiliaryRatio B^(1/2 : ℝ)/(∏ p ∈ A, p : ℕ)*
        (bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(p : ℝ)) (S \ A)*
          (1/2 : ℝ)^(S \ A).card) := by ring
    _ = _ := by rw [ht]; ring

/-- An arbitrary regularity or multiplicity test stays inside the new law. -/
theorem weighted_remainder_change_of_measure {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (F : Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A)*F (S \ A) else 0) =
      remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)*
        ∑ R ∈ (auxiliaryPrimes B \ A).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ A)
            (fun p => 1/(2*(p : ℝ)-1)) R*F R := by
  rw [← sum_filter,mul_sum]
  apply sum_bij (fun S _ => S \ A)
  · intro S hS
    exact mem_powerset.mpr (sdiff_subset_sdiff
      (mem_powerset.mp (mem_filter.mp hS).1) subset_rfl)
  · intro S hS T hT he
    have hs := sdiff_union_of_subset (mem_filter.mp hS).2
    have ht := sdiff_union_of_subset (mem_filter.mp hT).2
    rw [he] at hs
    exact hs.symm.trans ht
  · intro R hR
    have hr := mem_powerset.mp hR
    refine ⟨A ∪ R,mem_filter.mpr ⟨mem_powerset.mpr
      (union_subset hA (hr.trans sdiff_subset)),subset_union_left⟩,?_⟩
    ext p
    have hp : p ∈ R → p ∉ A := fun h => (mem_sdiff.mp (hr h)).2
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  · intro S hS
    rw [weighted_required_prime_mass (mem_filter.mp hS).2
      (mem_powerset.mp (mem_filter.mp hS).1)]
    ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RemainderNormalization
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalization of the first-representation measure -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem remainderTiltNormalizer_nonneg (B : ℕ) (A : Finset ℕ) :
    0 ≤ remainderTiltNormalizer B A := by
  apply mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _)
  apply prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedEndpointPair
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-endpoint law after selecting a first representation -/

namespace JointDickman
open Finset Classical

theorem weighted_endpoint_change_of_measure {B : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (F : Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        residueBaseWeight B (S \ A)*F S else 0) =
      remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)*
        ∑ R ∈ (auxiliaryPrimes B \ A).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ A)
            (fun p => 1/(2*(p : ℝ)-1)) R*F (A ∪ R) := by
  have hh := weighted_remainder_change_of_measure hA (fun R => F (A ∪ R))
  rw [← hh]
  apply sum_congr rfl
  intro S _
  split_ifs with hs
  · rw [union_sdiff_of_subset hs]
  · rfl

/-- Exact factorization of the first-representation measure at both
endpoints. The test may depend jointly on both reconstructed site types. -/
theorem weighted_endpoint_pair_change_of_measure {B : ℕ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*F S R else 0) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ))*
        ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
          ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U*
            bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V*
            F (A ∪ U) (D ∪ V) := by
  let G (S : Finset ℕ) := ∑ R ∈ (auxiliaryPrimes B).powerset, if D ⊆ R then
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
      residueBaseWeight B (R \ D)*F S R else 0
  have hfirst : (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*F S R else 0) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, if A ⊆ S then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          residueBaseWeight B (S \ A)*G S else 0 := by
    apply sum_congr rfl
    intro S _
    by_cases hs : A ⊆ S
    · rw [ite_eq_left hs]
      dsimp [G]
      rw [mul_sum]
      apply sum_congr rfl
      intro R _
      by_cases hr : D ⊆ R <;> simp only [hs,hr,and_self,true_and,ite_true, if_true,ite_false, if_false,mul_zero]
      ring
    · simp only [hs,false_and,ite_false, if_false,sum_const_zero]
  rw [hfirst,weighted_endpoint_change_of_measure hA G]
  have hsecond (S : Finset ℕ) : G S =
      remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)*
        ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
          bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V*
            F S (D ∪ V) := weighted_endpoint_change_of_measure hD (F S)
  simp_rw [hsecond,mul_sum]
  apply sum_congr rfl
  intro U _
  apply sum_congr rfl
  intro V _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularPairChangeOfMeasure
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact first-representation mass with both regularity tests -/

namespace JointDickman
open Finset Classical

/-- The forced coefficient and tilted normalization together give exactly
the half-prime subset law, scaled by B. -/
theorem coefficient_tilt_mass {B : ℕ} (hB : 1 < B) {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) :
    coefficientWeight B (∏ p ∈ A, p)*(remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)) =
      (B : ℝ)*bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A := by
  rw [coefficientWeight_primeProduct hA]
  have hR := auxiliaryRatio_pos hB
  have hs : (auxiliaryRatio B)^(1/2 : ℝ)*(auxiliaryRatio B)^(1/2 : ℝ) = auxiliaryRatio B := by
    rw [← Real.rpow_add hR]
    norm_num
  have hp : (1/2 : ℝ)^A.card/(∏ p ∈ A, p : ℕ) = ∏ p ∈ A, (1/2 : ℝ)/p := by
    rw [prod_div_distrib,prod_const,Nat.cast_prod]
  unfold residueBaseWeight remainderTiltNormalizer bernoulliSubsetMass primeNormalizer
  calc
    _ = (auxiliaryRatio B^(1/2 : ℝ)*auxiliaryRatio B^(1/2 : ℝ))*
        Real.log (auxiliaryCutoff B)*((1/2 : ℝ)^A.card/(∏ p ∈ A, p : ℕ))*
        ∏ p ∈ auxiliaryPrimes B \ A, (1-(1/2 : ℝ)/p) := by ring
    _ = _ := by rw [hs,auxiliaryRatio_mul_log hB,hp]; ring

/-- Regularity is kept inside the changed probability measure. In
particular, this identity makes no division by a regularity probability. -/
theorem regular_pair_change_of_measure {B L : ℕ} {τ C : ℝ} {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      if A ⊆ S ∧ D ⊆ R then
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R
      else 0) =
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ))*
      regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D
        (fun V => F (A ∪ U) (D ∪ V))) := by
  let G := fun S R => if RegularPrimeSet B L τ C (S \ A) ∧ RegularPrimeSet B L τ C (R \ D)
    then F S R else 0
  have hpoint (S R : Finset ℕ) :
      regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R =
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*G S R := by
    dsimp only [G]
    unfold regularResidueWeight
    split_ifs <;> simp_all
  have hpoint2 (S R : Finset ℕ) :
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        regularResidueWeight B L τ C (S \ A)*regularResidueWeight B L τ C (R \ D)*F S R =
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
        residueBaseWeight B (S \ A)*residueBaseWeight B (R \ D)*G S R := by
    have hh := congrArg (fun x =>
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*x) (hpoint S R)
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  simp_rw [hpoint2]
  rw [weighted_endpoint_pair_change_of_measure hA hD G]
  congr 1
  unfold regularTiltAverage
  apply sum_congr rfl
  intro U hU
  have hu : (A ∪ U) \ A = U := by
    ext p
    have hh : p ∈ U → p ∉ A := fun hp => (mem_sdiff.mp (mem_powerset.mp hU hp)).2
    simp only [mem_sdiff,mem_union]
    tauto
  have hpoint' (V : Finset ℕ) (hV : V ∈ (auxiliaryPrimes B \ D).powerset) :
      G (A ∪ U) (D ∪ V) = if RegularPrimeSet B L τ C U then
        if RegularPrimeSet B L τ C V then F (A ∪ U) (D ∪ V) else 0 else 0 := by
    have hv : (D ∪ V) \ D = V := by
      ext p
      have hh : p ∈ V → p ∉ D := fun hp => (mem_sdiff.mp (mem_powerset.mp hV hp)).2
      simp only [mem_sdiff,mem_union]
      tauto
    simp only [G,hu,hv]
    split_ifs <;> simp_all
  by_cases hr : RegularPrimeSet B L τ C U
  · simp only [hr,ite_true, if_true]
    rw [mul_sum]
    apply sum_congr rfl
    intro V hV
    rw [hpoint' V hV,ite_eq_left hr]
    ring
  · rw [ite_eq_right hr,mul_zero]
    apply sum_eq_zero
    intro V hV
    rw [hpoint' V hV,ite_eq_right hr,mul_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CandidateCoefficientFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the deterministic and remainder factors of a candidate -/

namespace JointDickman
open Finset Classical

theorem candidateCoefficientFactor_nonneg {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) (hχ : 0 ≤ χ e) :
    0 ≤ candidateCoefficientFactor B L τ C χ e := by
  unfold candidateCoefficientFactor
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _)
      (regularCoefficientWeight_nonneg _ _ _ _ _))
    (regularCoefficientWeight_nonneg _ _ _ _ _)) (Nat.cast_nonneg B)) hχ)
    (independentRootMean_nonneg _ _ _ _)

theorem candidateMeanWeight_factor {M : ℕ} (B L : ℕ) (τ C : ℝ)
    (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ) (e : BlockCandidateIndex M) :
    candidateMeanWeight B L τ C S χ e =
      candidateCoefficientFactor B L τ C χ e*
        regularResidueWeight B L τ C (S e.1.1 \ e.2.1)*
        regularResidueWeight B L τ C (S e.1.2 \ e.2.2) := by
  rw [candidateMeanWeight_eq]
  unfold candidateCoefficientFactor
  ring

theorem candidateCoefficientFactor_zero_left {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C A) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  unfold candidateCoefficientFactor candidateLow
  rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hA,ite_eq_right hr]
  simp

theorem candidateCoefficientFactor_zero_right {B L M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) {A D : Finset ℕ}
    (hD : D ⊆ auxiliaryPrimes B) (hr : ¬ RegularPrimeSet B L τ C D) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D)) = 0 := by
  have hz : regularCoefficientWeight B L τ C (candidateHigh ((i,t),(A,D))) = 0 := by
    change regularCoefficientWeight B L τ C (∏ p ∈ D, p) = 0
    rw [regularCoefficientWeight,coefficientPrimeSet_primeProduct hD,ite_eq_right hr]
  simp only [candidateCoefficientFactor,hz,mul_zero,zero_div,zero_mul]


/-- The local site kernel is a sum of deterministic factors times the two
regular remainder weights. -/
theorem candidateSiteKernel_factor_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t) (S R : Finset ℕ) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R,
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
          regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2) := by
  unfold candidateSiteKernel
  rw [latentCandidateKernel_representation_sum B L T H M τ C _ χ i t hit]
  have hne : i ≠ t := ne_of_lt hit
  simp only [Function.update_of_ne hne,Function.update_self]
  apply sum_congr rfl
  intro ab _
  rw [candidateMeanWeight_factor]
  simp only [Function.update_of_ne hne,Function.update_self]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstRepresentationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the kernel by a first coefficient pair -/

namespace JointDickman
open Finset Classical

/-- The unrestricted pair sum is exact: the coefficient and remainder
weights themselves impose the four endpoint regularity conditions. -/
theorem candidateSiteKernel_unrestricted_sum {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (S R : Finset ℕ) (hS : S ⊆ auxiliaryPrimes B) (hR : R ⊆ auxiliaryPrimes B) :
    candidateSiteKernel B L T H M τ C χ i t S R =
      ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
        if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
          candidateCoefficientFactor B L τ C χ ((i,t),ab)*
            regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
        else 0 := by
  rw [candidateSiteKernel_factor_sum χ i t hit S R]
  let J := (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset
  have hsub : candidatePairRepresentations B L T H τ C i t S R ⊆ J := by
    intro ab hab
    obtain ⟨ha,hd⟩ := mem_product.mp (mem_filter.mp hab).1
    exact mem_product.mpr ⟨mem_powerset.mpr ((mem_endpointSplits.mp ha).1.trans hS),
      mem_powerset.mpr ((mem_endpointSplits.mp hd).1.trans hR)⟩
  let w := fun ab : Finset ℕ × Finset ℕ =>
    if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
      candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
    else 0
  calc
    _ = ∑ ab ∈ candidatePairRepresentations B L T H τ C i t S R, w ab := by
      apply sum_congr rfl
      intro ab hab
      obtain ⟨hp,he⟩ := mem_filter.mp hab
      obtain ⟨ha,hd⟩ := mem_product.mp hp
      exact (ite_eq_left ⟨he,(mem_endpointSplits.mp ha).1,(mem_endpointSplits.mp hd).1⟩).symm
    _ = ∑ ab ∈ J, w ab := by
      apply sum_subset hsub
      intro ab hab hnot
      dsimp only [w]
      split_ifs with hc
      · have hpair := mem_product.mp hab
        have hA := mem_powerset.mp hpair.1
        have hD := mem_powerset.mp hpair.2
        by_cases ha : RegularPrimeSet B L τ C ab.1
        · by_cases hd : RegularPrimeSet B L τ C ab.2
          · by_cases hs : RegularPrimeSet B L τ C (S \ ab.1)
            · by_cases hr : RegularPrimeSet B L τ C (R \ ab.2)
              · exact False.elim (hnot (mem_filter.mpr ⟨mem_product.mpr
                  ⟨mem_endpointSplits.mpr ⟨hc.2.1,ha,hs⟩,
                   mem_endpointSplits.mpr ⟨hc.2.2,hd,hr⟩⟩,hc.1⟩))
              · simp only [regularResidueWeight,hr,ite_false, if_false,mul_zero]
            · simp only [regularResidueWeight,hs,ite_false, if_false,mul_zero,zero_mul]
          · rw [candidateCoefficientFactor_zero_right χ i t hD hd]
            simp
        · rw [candidateCoefficientFactor_zero_left χ i t hA ha]
          simp
      · rfl

/-- Averaging after fixing the first pair produces exactly its tilted
remainder law. The test can be the actual representation count. -/
theorem candidateSiteKernel_weighted_expectation {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hit : i < t)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
        candidateSiteKernel B L T H M τ C χ i t S R) =
    ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
      if BlockCandidateAdmissible B L T H τ C ((i,t),ab) then
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
        (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ))*
        regularTiltAverage B L τ C ab.1 (fun U => regularTiltAverage B L τ C ab.2
          (fun V => F (ab.1 ∪ U) (ab.2 ∪ V))) else 0 := by
  let J := (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset
  let W := fun (ab : Finset ℕ × Finset ℕ) (S R : Finset ℕ) =>
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
    bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
      if BlockCandidateAdmissible B L T H τ C ((i,t),ab) ∧ ab.1 ⊆ S ∧ ab.2 ⊆ R then
        candidateCoefficientFactor B L τ C χ ((i,t),ab)*
        regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)
      else 0
  have hexpand : (∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R*
        candidateSiteKernel B L T H M τ C χ i t S R) =
      ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        ∑ ab ∈ J, W ab S R := by
    apply sum_congr rfl
    intro S hS
    apply sum_congr rfl
    intro R hR
    rw [candidateSiteKernel_unrestricted_sum χ i t hit S R (mem_powerset.mp hS) (mem_powerset.mp hR),mul_sum]
  rw [hexpand]
  calc
    _ = ∑ ab ∈ J, ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
        W ab S R := by
      simp_rw [sum_comm (s := (auxiliaryPrimes B).powerset) (t := J)]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      have hp := mem_product.mp hab
      have hA := mem_powerset.mp hp.1
      have hD := mem_powerset.mp hp.2
      by_cases he : BlockCandidateAdmissible B L T H τ C ((i,t),ab)
      · rw [ite_eq_left he]
        have hpoint (S R : Finset ℕ) : W ab S R =
            candidateCoefficientFactor B L τ C χ ((i,t),ab)*
              (if ab.1 ⊆ S ∧ ab.2 ⊆ R then
                bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
                bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*
                regularResidueWeight B L τ C (S \ ab.1)*regularResidueWeight B L τ C (R \ ab.2)*F S R
              else 0) := by
          dsimp only [W]
          simp only [he,true_and]
          split_ifs <;> ring
        simp_rw [hpoint,← mul_sum]
        rw [regular_pair_change_of_measure hA hD F]
        ring
      · simp only [W,he,false_and,ite_false, if_false,mul_zero,sum_const_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstPairMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The remaining mass of first coefficient pairs -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Domination of one first pair after its remainder laws are normalized. -/
theorem candidateFirstPairMass_term_le {B L T H M : ℕ} {τ C : ℝ}
    (hB : 10 ≤ B) (hT : 0 < T) (hTs : (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B))
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (A D : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (he : BlockCandidateAdmissible B L T H τ C ((i,t),(A,D))) (hχ : χ ((i,t),(A,D)) ≤ 1) :
    candidateCoefficientFactor B L τ C χ ((i,t),(A,D))*
      (remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ))*
      (remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)) ≤
    (B : ℝ)*independentRootMean B L τ C*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) D*
      supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ D, p) := by
  let e : BlockCandidateIndex M := ((i,t),(A,D))
  let QA := remainderTiltNormalizer B A/(∏ p ∈ A, p : ℕ)
  let QD := remainderTiltNormalizer B D/(∏ p ∈ D, p : ℕ)
  have hQA : 0 ≤ QA := div_nonneg (remainderTiltNormalizer_nonneg B A) (Nat.cast_nonneg _)
  have hQD : 0 ≤ QD := div_nonneg (remainderTiltNormalizer_nonneg B D) (Nat.cast_nonneg _)
  have hroot : 0 ≤ independentRootMean B L τ C/(B : ℝ) :=
    div_nonneg (independentRootMean_nonneg _ _ _ _) (Nat.cast_nonneg B)
  obtain ⟨_,_,_,hc,hrel,_,_,_,_,_,hclo,hchi,hblo,hbhi,_,hahi⟩ := he
  have htest := (regularCoefficientWeight_le B L τ C (candidateQuotient e)).trans
    (supportedEndpointTest_ge hB hT hTs hc hclo hchi hblo hbhi hrel hahi)
  let W := independentRootMean B L τ C/(B : ℝ)*
    (regularCoefficientWeight B L τ C (∏ p ∈ A, p)*QA)*
    (regularCoefficientWeight B L τ C (∏ p ∈ D, p)*QD)
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg hroot
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQA))
    (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQD)
  have hbase : W ≤ independentRootMean B L τ C/(B : ℝ)*
      (coefficientWeight B (∏ p ∈ A, p)*QA)*(coefficientWeight B (∏ p ∈ D, p)*QD) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (regularCoefficientWeight_le _ _ _ _ _) hQA) hroot)
      (mul_le_mul_of_nonneg_right (regularCoefficientWeight_le _ _ _ _ _) hQD)
      (mul_nonneg (regularCoefficientWeight_nonneg _ _ _ _ _) hQD)
      (mul_nonneg hroot (mul_nonneg (coefficientWeight_nonneg _ _) hQA))
  calc
    _ = W*regularCoefficientWeight B L τ C (candidateQuotient e)*χ e := by
      dsimp only [W,QA,QD,e,candidateCoefficientFactor,candidateLow,candidateHigh]
      ring
    _ ≤ W*regularCoefficientWeight B L τ C (candidateQuotient e) :=
      mul_le_of_le_one_right (mul_nonneg hW (regularCoefficientWeight_nonneg _ _ _ _ _)) hχ
    _ ≤ (independentRootMean B L τ C/(B : ℝ)*
          (coefficientWeight B (∏ p ∈ A, p)*QA)*(coefficientWeight B (∏ p ∈ D, p)*QD))*
        supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ D, p) := by
      exact mul_le_mul hbase htest (regularCoefficientWeight_nonneg _ _ _ _ _)
        (mul_nonneg (mul_nonneg hroot (mul_nonneg (coefficientWeight_nonneg _ _) hQA))
          (mul_nonneg (coefficientWeight_nonneg _ _) hQD))
    _ = _ := by
      dsimp only [QA,QD]
      rw [coefficient_tilt_mass (by omega) hA,coefficient_tilt_mass (by omega) hD]
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstPairMassBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform first-representation mass at a fixed lag -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem halfPrimeSubsetMass_nonneg {B : ℕ} {A : Finset ℕ}
    (hA : A ∈ (auxiliaryPrimes B).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp hA)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p hp).two_le
  exact ⟨div_nonneg (by norm_num) (by linarith),
    (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)⟩

/-- The coefficient test averaged under the exact half-prime law. -/
theorem supportedEndpointTest_half_mean_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (T b j : ℕ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      Disjoint b.primeFactors (Nat.primesLE (auxiliaryCutoff B)) →
      (∑ A ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p) A*
        supportedEndpointTest B T b j (∏ p ∈ A, p)) ≤
        K/((B : ℝ)*T)*singularFactor 24 j := by
  obtain ⟨K,hK,hbound⟩ := endpointCoefficientMass_bound hFord hM
    (show (0 : ℝ) < 1/2 by norm_num) (16/5)
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 10] with B hmass hB
  intro T b j hT hTs hj hbrough
  by_cases hw : EndpointCoefficientWindow B T b
  · obtain ⟨c,hc,hlog,_,hlo,hhi⟩ := hw
    have hscale := endpointRowScale_window (by omega) hT hc hlog hlo hhi
    have hsize := endpointCoefficientWindow_size hB hTs
      (show EndpointCoefficientWindow B T b from ⟨c,hc,hlog,by assumption,hlo,hhi⟩)
    simp only [supportedEndpointTest,show EndpointCoefficientWindow B T b from
      ⟨c,hc,hlog,by assumption,hlo,hhi⟩,ite_true, if_true,endpointCoefficientTest_mean]
    exact hmass T _ j b hT hscale.1 hscale.2.2 hj hsize hbrough
  · simp only [supportedEndpointTest,hw,ite_false, if_false,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))

/-- Summing all first pairs costs O(Sigma(j)/T). There is no dependence
on the number of representations or on the endpoint regularity cutoffs. -/
theorem candidateFirstPairMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, χ e ≤ 1) →
      ∀ (i t : Fin M), i < t →
        candidateFirstPairMass B L T H τ C χ i t ≤ K/(T : ℝ)*singularFactor 24 (t.val-i.val) := by
  obtain ⟨K,hK,hmass⟩ := supportedEndpointTest_half_mean_bound hFord hM
  obtain ⟨D,hD,hroot⟩ := independentRootMean_bounded hM
  refine ⟨D*K,by positivity,?_⟩
  filter_upwards [hmass,hroot,eventually_ge_atTop 10] with B hmass hroot hB
  intro L T H M τ C hT hTs χ hχ i t hit
  have hj : t.val-i.val ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hit)
  have hBr : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let μ := bernoulliSubsetMass (auxiliaryPrimes B) (fun p => (1/2 : ℝ)/p)
  have hμ (A : Finset ℕ) (hA : A ∈ (auxiliaryPrimes B).powerset) : 0 ≤ μ A := halfPrimeSubsetMass_nonneg hA
  have hs : 0 ≤ singularFactor 24 (t.val-i.val) :=
    zero_le_one.trans (singularFactor_one_le (by norm_num) _)
  have hfixed (A : Finset ℕ) (hA : A ∈ (auxiliaryPrimes B).powerset) :
      (∑ E ∈ (auxiliaryPrimes B).powerset, μ E*
        supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ E, p)) ≤
        K/((B : ℝ)*T)*singularFactor 24 (t.val-i.val) := by
    apply hmass T _ _ hT hTs hj
    rw [Nat.primeFactors_prod (fun p hp => auxiliaryPrimes_prime B p (mem_powerset.mp hA hp))]
    exact auxiliarySubset_disjoint_small (mem_powerset.mp hA)
  calc
    _ ≤ ∑ ab ∈ (auxiliaryPrimes B).powerset.product (auxiliaryPrimes B).powerset,
        (B : ℝ)*independentRootMean B L τ C*μ ab.1*μ ab.2*
          supportedEndpointTest B T (∏ p ∈ ab.1, p) (t.val-i.val) (∏ p ∈ ab.2, p) := by
      apply sum_le_sum
      intro ab hab
      have hp := mem_product.mp hab
      split_ifs with he
      · exact candidateFirstPairMass_term_le hB hT hTs χ i t ab.1 ab.2
          (mem_powerset.mp hp.1) (mem_powerset.mp hp.2) he (hχ _)
      · exact mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (independentRootMean_nonneg _ _ _ _))
          (hμ _ hp.1)) (hμ _ hp.2)) (supportedEndpointTest_nonneg _ _ _ _ _)
    _ = (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, μ A*
          ∑ E ∈ (auxiliaryPrimes B).powerset, μ E*
            supportedEndpointTest B T (∏ p ∈ A, p) (t.val-i.val) (∏ p ∈ E, p) := by
      rw [Finset.product_eq_sprod,sum_product]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro E _
      ring
    _ ≤ (B : ℝ)*independentRootMean B L τ C*
        ∑ A ∈ (auxiliaryPrimes B).powerset, μ A*
          (K/((B : ℝ)*T)*singularFactor 24 (t.val-i.val)) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Nat.cast_nonneg B) (independentRootMean_nonneg _ _ _ _))
      apply sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (hfixed A hA) (hμ A hA)
    _ = independentRootMean B L τ C*K/(T : ℝ)*singularFactor 24 (t.val-i.val) := by
      rw [← sum_mul,bernoulliSubsetMass_sum,one_mul]
      field_simp
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hroot L τ C) hK.le) hTr.le) hs

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateMultiplicity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Using the tilted multiplicity estimate after fixing a first pair -/

namespace JointDickman
open Finset Classical

/-- This is the exact point at which the previously proved tilted count
enters the square estimate. No regularity probability is divided out. -/
theorem candidateMultiplicityMoment_le_firstMass {B L T H M : ℕ} {τ C Q : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (hχ : ∀ e, 0 ≤ χ e)
    (i t : Fin M) (hit : i < t)
    (hcount : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ D ∈ (auxiliaryPrimes B).powerset,
      BlockCandidateAdmissible B L T H τ C ((i,t),(A,D)) →
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      tiltedCandidatePairCount B L T H τ C i t A D ≤ Q) :
    candidateMultiplicityMoment B L T H τ C χ i t ≤
      Q*candidateFirstPairMass B L T H τ C χ i t := by
  unfold candidateMultiplicityMoment
  rw [candidateSiteKernel_weighted_expectation χ i t hit]
  unfold candidateFirstPairMass
  rw [mul_sum]
  apply sum_le_sum
  intro ab hab
  have hp := mem_product.mp hab
  by_cases he : BlockCandidateAdmissible B L T H τ C ((i,t),ab)
  · simp only [he,ite_true, if_true]
    by_cases ha : RegularPrimeSet B L τ C ab.1
    · by_cases hd : RegularPrimeSet B L τ C ab.2
      · have hc := hcount ab.1 hp.1 ab.2 hp.2 he ha hd
        have hweight : 0 ≤ candidateCoefficientFactor B L τ C χ ((i,t),ab)*
            (remainderTiltNormalizer B ab.1/(∏ p ∈ ab.1, p : ℕ))*
            (remainderTiltNormalizer B ab.2/(∏ p ∈ ab.2, p : ℕ)) :=
          mul_nonneg (mul_nonneg (candidateCoefficientFactor_nonneg _ _ _ _ _ _ (hχ _))
            (div_nonneg (remainderTiltNormalizer_nonneg _ _) (Nat.cast_nonneg _)))
            (div_nonneg (remainderTiltNormalizer_nonneg _ _) (Nat.cast_nonneg _))
        exact (mul_le_mul_of_nonneg_left hc hweight).trans_eq (mul_comm _ _)
      · rw [candidateCoefficientFactor_zero_right χ i t (mem_powerset.mp hp.2) hd]
        simp
    · rw [candidateCoefficientFactor_zero_left χ i t (mem_powerset.mp hp.1) ha]
      simp
  · simp only [he,ite_false, if_false,mul_zero,le_refl]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_CandidateSquareMoment
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated square of an actual latent edge -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem independentSubsetMass_nonneg {B : ℕ} {S : Finset ℕ}
    (hS : S ∈ (auxiliaryPrimes B).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S :=
  independentPrimeSetMass_nonneg B ⟨S,hS⟩

theorem candidateSquareMoment_le_multiplicity
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ)
      (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ (i t : Fin M), i < t →
        candidateSquareMoment B L T H τ C χ i t ≤
          (B : ℝ)^(-(22/100 : ℝ))*candidateMultiplicityMoment B L T H τ C χ i t := by
  filter_upwards [latentCandidateKernel_square_multiplicity hM hL hτ hτsmall] with B hB
  intro T H M C χ hχ i t hit
  have hpoint (S R : Finset ℕ) : (candidateSiteKernel B L T H M τ C χ i t S R)^2 ≤
      (B : ℝ)^(-(22/100 : ℝ))*(candidatePairRepresentations B L T H τ C i t S R).card*
        candidateSiteKernel B L T H M τ C χ i t S R := by
    have hh := hB C T H M (Function.update (fun _ => S) t R) χ hχ i t hit
    change (candidateSiteKernel B L T H M τ C χ i t S R)^2 ≤
      (B : ℝ)^(-(22/100 : ℝ))*
      (candidatePairRepresentations B L T H τ C i t
        ((Function.update (fun _ => S) t R) i) ((Function.update (fun _ => S) t R) t)).card*
      candidateSiteKernel B L T H M τ C χ i t S R at hh
    simpa only [Function.update_of_ne (ne_of_lt hit),Function.update_self] using hh
  unfold candidateSquareMoment candidateMultiplicityMoment
  rw [mul_sum]
  apply sum_le_sum
  intro S hS
  rw [mul_sum]
  apply sum_le_sum
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hpoint S R)
    (mul_nonneg (independentSubsetMass_nonneg hS) (independentSubsetMass_nonneg hR))
  convert hh using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentEdgeSquareBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated square bound for an admissible latent edge -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The full edge square has the manuscript's power saving. Both cited
inputs remain explicit; all representation and remainder steps are proved. -/
theorem candidateSquareMoment_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ (i t : Fin M), i < t → t.val-i.val ≤ auxiliaryCutoff B →
          ((t.val-i.val : ℕ) : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ ((t.val-i.val : ℕ) : ℝ) →
          candidateSquareMoment B L T H τ C χ i t ≤
            K/(T : ℝ)*(B : ℝ)^(-(21/100 : ℝ))*singularFactor 24 (t.val-i.val) := by
  obtain ⟨τ,hτ,hτcap,hτsampling,hcount⟩ := tiltedCandidatePairCount_bound_jd hFord hM hL hη hcap
  obtain ⟨K,hK,hfirst⟩ := candidateFirstPairMass_bound hFord hM
  refine ⟨τ,2*K,hτ,hτcap,hτsampling,by positivity,?_⟩
  filter_upwards [hcount,hfirst,candidateSquareMoment_le_multiplicity hM
    (show 1 ≤ L by omega) hτ.le hτsampling,eventually_ge_atTop 10]
    with B hcount hfirst hsquare hB
  intro T H M C hT hTs χ hχ i t hit hcut hjB hjlow
  have hTlarge : (T : ℝ) ≤ Real.exp B := hTs.trans (Real.exp_le_exp.mpr (by
    nlinarith [show (0 : ℝ) ≤ B from Nat.cast_nonneg B]))
  have hj : 0 < t.val-i.val := Nat.sub_pos_of_lt hit
  have hweighted := candidateMultiplicityMoment_le_firstMass χ (fun e => (hχ e).1) i t hit
    (Q := 2*(B : ℝ)^(8/1000 : ℝ)) (by
      intro A hA D hD he ha hd
      have hsizeA : (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
        obtain ⟨_,_,_,hc,_,_,_,_,_,_,hclo,hchi,hlo,hhi,_,_⟩ := he
        exact endpointCoefficientWindow_size hB hTs ⟨_,hc,hclo,hchi,hlo,hhi⟩
      have hsizeD : (∏ p ∈ D, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) := by
        obtain ⟨_,_,_,hc,_,_,_,_,_,_,hclo,hchi,_,_,hlo,hhi⟩ := he
        exact endpointCoefficientWindow_size hB hTs ⟨_,hc,hclo,hchi,hlo,hhi⟩
      exact hcount T H M C i t A D hTlarge (mem_powerset.mp hA) (mem_powerset.mp hD)
        ha hd hsizeA hsizeD hj hcut hjB hjlow)
  have hbpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpower : (B : ℝ)^(-(22/100 : ℝ))*(B : ℝ)^(8/1000 : ℝ) ≤
      (B : ℝ)^(-(21/100 : ℝ)) := by
    rw [← Real.rpow_add hbpos]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ B))
    norm_num
  have hbase : 0 ≤ 2*K/(T : ℝ)*singularFactor 24 (t.val-i.val) :=
    mul_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg T))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
  calc
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*candidateMultiplicityMoment B L T H τ C χ i t :=
      hsquare T H M C χ hχ i t hit
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*(2*(B : ℝ)^(8/1000 : ℝ)*candidateFirstPairMass B L T H τ C χ i t) :=
      mul_le_mul_of_nonneg_left hweighted (Real.rpow_nonneg hbpos.le _)
    _ ≤ (B : ℝ)^(-(22/100 : ℝ))*(2*(B : ℝ)^(8/1000 : ℝ)*
        (K/(T : ℝ)*singularFactor 24 (t.val-i.val))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hbpos.le _)
      exact mul_le_mul_of_nonneg_left (hfirst L T H M τ C hT hTs χ (fun e => (hχ e).2) i t hit)
        (by positivity)
    _ = (2*K/(T : ℝ)*singularFactor 24 (t.val-i.val))*
        ((B : ℝ)^(-(22/100 : ℝ))*(B : ℝ)^(8/1000 : ℝ)) := by ring
    _ ≤ (2*K/(T : ℝ)*singularFactor 24 (t.val-i.val))*(B : ℝ)^(-(21/100 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower hbase
    _ = _ := by ring

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

theorem candidateSiteKernel_zero_of_far {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i k : Fin M) (a b : Finset ℕ)
    (hfar : T ≤ Nat.dist i.val k.val) :
    candidateSiteKernel B L T H M τ C χ i k a b = 0 := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [Nat.dist_eq_sub_of_le hik.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hik hfar
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    rw [Nat.dist_eq_sub_of_le_right hki.le] at hfar
    exact latentCandidateKernel_forward_zero _ _ _ _ hki hfar

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentSquareSymmetry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Symmetry and lag support of the integrated edge square -/

namespace JointDickman
open Finset Classical

theorem candidateSquareMoment_symm (B L T H : ℕ) (τ C : ℝ) {M : ℕ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) :
    candidateSquareMoment B L T H τ C χ i t = candidateSquareMoment B L T H τ C χ t i := by
  unfold candidateSquareMoment
  rw [sum_comm]
  apply sum_congr rfl
  intro R _
  apply sum_congr rfl
  intro S _
  rw [candidateSiteKernel_symm]
  ring

theorem candidateSiteKernel_zero_of_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (S R : Finset ℕ)
    (hshort : Nat.dist i.val t.val ≤ H) :
    candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
  have hf (i t : Fin M) (hit : i < t) (S R : Finset ℕ)
      (hshort : t.val-i.val ≤ H) : candidateSiteKernel B L T H M τ C χ i t S R = 0 := by
    rw [candidateSiteKernel_factor_sum χ i t hit]
    apply sum_eq_zero
    intro ab hab
    have he := (mem_filter.mp hab).2
    have hlag := he.2.1
    change H < t.val-i.val at hlag
    omega
  rcases lt_trichotomy i t with hit | rfl | hti
  · apply hf i t hit S R
    simpa only [Nat.dist_eq_sub_of_le hit.le] using hshort
  · exact candidateSiteKernel_diag _ _ _ _ _ _ _ _ _ _ _
  · rw [candidateSiteKernel_symm]
    apply hf t i hti R S
    simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hshort

theorem candidateSquareMoment_diag (B L T H : ℕ) (τ C : ℝ) {M : ℕ}
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    candidateSquareMoment B L T H τ C χ i i = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_diag,zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

theorem candidateSquareMoment_zero_of_short {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hshort : Nat.dist i.val t.val ≤ H) :
    candidateSquareMoment B L T H τ C χ i t = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_zero_of_short χ i t _ _ hshort,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

theorem candidateSquareMoment_zero_of_far {B L T H M : ℕ} {τ C : ℝ}
    (χ : BlockCandidateIndex M → ℝ) (i t : Fin M) (hfar : T ≤ Nat.dist i.val t.val) :
    candidateSquareMoment B L T H τ C χ i t = 0 := by
  unfold candidateSquareMoment
  simp only [candidateSiteKernel_zero_of_far χ i t _ _ hfar,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,sum_const_zero]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentRowSquareBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated row-square estimate for the actual latent kernel -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Manuscript equation (24), before rewriting the finite expectations in
sampling notation. The short-lag cutoff supplies the separation needed by
the multiplicity sieve, and the singular factors sum uniformly over a row. -/
theorem candidateSquareMoment_row_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        T ≤ auxiliaryCutoff B → (T : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ H →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ i : Fin M, (∑ t : Fin M, candidateSquareMoment B L T H τ C χ i t) ≤
          K*(B : ℝ)^(-(21/100 : ℝ)) := by
  obtain ⟨τ,K,hτ,hτcap,hτsampling,hK,hbound⟩ := candidateSquareMoment_bound hFord hM hL hη hcap
  refine ⟨τ,2*Real.exp 24*K,hτ,hτcap,hτsampling,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro T H M C hT hTs hcut hT2 hH χ hχ i
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  let c := K/(T : ℝ)*(B : ℝ)^(-(21/100 : ℝ))
  have hc : 0 ≤ c := mul_nonneg (div_nonneg hK.le hTr.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpoint (t : Fin M) : candidateSquareMoment B L T H τ C χ i t ≤
      c*(if i ≠ t ∧ Nat.dist i.val t.val < T then singularFactor 24 (Nat.dist i.val t.val) else 0) := by
    by_cases heq : i = t
    · subst t
      simp only [candidateSquareMoment_diag,ne_eq,not_true_eq_false,false_and,ite_false, if_false,mul_zero,le_refl]
    by_cases hfar : T ≤ Nat.dist i.val t.val
    · rw [candidateSquareMoment_zero_of_far χ i t hfar,ite_eq_right (by omega),mul_zero]
    have hdist : Nat.dist i.val t.val < T := Nat.lt_of_not_ge hfar
    rw [ite_eq_left ⟨heq,hdist⟩]
    by_cases hshort : Nat.dist i.val t.val ≤ H
    · rw [candidateSquareMoment_zero_of_short χ i t hshort]
      exact mul_nonneg hc (zero_le_one.trans (singularFactor_one_le (by norm_num) _))
    have hjcut : Nat.dist i.val t.val ≤ auxiliaryCutoff B := hdist.le.trans hcut
    have hjB : (Nat.dist i.val t.val : ℝ) ≤ (B : ℝ)^2 :=
      (show (Nat.dist i.val t.val : ℝ) ≤ T by exact_mod_cast hdist.le).trans hT2
    have hjlow : η*(B : ℝ)^(32/100 : ℝ) ≤ (Nat.dist i.val t.val : ℝ) :=
      hH.trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hshort)))
    rcases lt_or_gt_of_ne heq with hit | hti
    · have hh := hB T H M C hT hTs χ hχ i t hit
      simpa only [Nat.dist_eq_sub_of_le hit.le] using hh
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjcut)
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjB)
        (by simpa only [Nat.dist_eq_sub_of_le hit.le] using hjlow)
    · rw [candidateSquareMoment_symm B L T H τ C χ i t]
      have hh := hB T H M C hT hTs χ hχ t i hti
      simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hh
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjcut)
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjB)
        (by simpa only [Nat.dist_eq_sub_of_le_right hti.le] using hjlow)
  calc
    _ ≤ ∑ t : Fin M, c*(if i ≠ t ∧ Nat.dist i.val t.val < T then
        singularFactor 24 (Nat.dist i.val t.val) else 0) := sum_le_sum (fun t _ => hpoint t)
    _ = c*∑ t : Fin M, if i ≠ t ∧ Nat.dist i.val t.val < T then
        singularFactor 24 (Nat.dist i.val t.val) else 0 := (mul_sum _ _ _).symm
    _ ≤ c*(2*Real.exp 24*T) := mul_le_mul_of_nonneg_left (distance_lag_singular_sum i T) hc
    _ = _ := by
      dsimp only [c]
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LatentRowSquareMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The integrated row estimate in the finite sampling notation -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem independentPrimePair_expectation (B : ℕ) (F : Finset ℕ → Finset ℕ → ℝ) :
    finiteExpectation (independentPrimeSetMass B) (fun S =>
      finiteExpectation (independentPrimeSetMass B) (fun R => F S.val R.val)) =
    ∑ S ∈ (auxiliaryPrimes B).powerset, ∑ R ∈ (auxiliaryPrimes B).powerset,
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
      bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R := by
  unfold finiteExpectation independentPrimeSetMass
  calc
    _ = ∑ S ∈ (auxiliaryPrimes B).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) S*
          ∑ R : (auxiliaryPrimes B).powerset,
            bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R.val*F S R.val :=
      sum_coe_sort _ _
    _ = _ := by
      apply sum_congr rfl
      intro S _
      rw [sum_coe_sort (auxiliaryPrimes B).powerset
        (fun R => bernoulliSubsetMass (auxiliaryPrimes B) (fun p => 1/(p : ℝ)) R*F S R),mul_sum]
      apply sum_congr rfl
      intro R _
      ring

theorem latentPrimeSiteKernel_row_square_eq (B L T H M : ℕ) (τ C : ℝ)
    (χ : BlockCandidateIndex M → ℝ) (i : Fin M) :
    siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
      (latentPrimeSiteKernel B L T H M τ C χ) i =
      ∑ t : Fin M, candidateSquareMoment B L T H τ C χ i t := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i,candidateSquareMoment_diag,zero_add]
  unfold siteRowSquareMass
  rw [finiteExpectation_sum]
  apply sum_congr rfl
  intro t _
  exact independentPrimePair_expectation B
    (fun S R => (candidateSiteKernel B L T H M τ C χ i t S R)^2)

/-- The actual latent kernel satisfies the integrated square-mass premise
used by the finite sampling theorem, with the manuscript exponent. -/
theorem latentPrimeSiteKernel_row_square_mass_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ K : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧ 0 < K ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        T ≤ auxiliaryCutoff B → (T : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ H →
        ∀ (χ : BlockCandidateIndex M → ℝ), (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ i : Fin M,
          siteRowSquareMass (fun _ : Fin M => independentPrimeSetMass B)
            (latentPrimeSiteKernel B L T H M τ C χ) i ≤ K*(B : ℝ)^(-(21/100 : ℝ)) := by
  obtain ⟨τ,K,hτ,hτcap,hτsampling,hK,hbound⟩ := candidateSquareMoment_row_bound hFord hM hL hη hcap
  refine ⟨τ,K,hτ,hτcap,hτsampling,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T H M C hT hTs hcut hT2 hH χ hχ i
  rw [latentPrimeSiteKernel_row_square_eq]
  exact hB T H M C hT hTs hcut hT2 hH χ hχ i

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.latentPrimeSiteKernel_row_square_mass_jd_oai := @OAI.JointDickman.latentPrimeSiteKernel_row_square_mass_jd_oai
