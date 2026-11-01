-- Prove2me | solution 1 for OAI.JointDickman.active_low_addition_class_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:02:46.848451+00:00
-- url     : https://prove2.me/submissions/444f966e-f247-4569-b802-2e6d566dfa79

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIntervalSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

/-- The Mertens remainder tends to its additive constant. -/
theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TwoFormLocalBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Two distinct affine roots and their weighted interval bound -/

namespace JointDickman

open Finset

theorem affine_residue_root {p : ℕ} [Fact p.Prime] (b j x : ZMod p) (hj : j ≠ 0) :
    b + j * x = 0 ↔ x = -b / j := by
  rw [eq_div_iff hj]
  constructor <;> intro h <;> linear_combination h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MixedTwoFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two-form sieve with a Rankin weight and a half weight -/

namespace JointDickman
open Finset Classical

theorem formRootWeight_two_mixed {p : ℕ} (a b x : ZMod p) (t u : ℝ) :
    formRootWeight ![a,b] ![t,u] x = residueWeight t a x*residueWeight u b x := by
  unfold formRootWeight
  rw [prod_filter,Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,residueWeight]
  apply congrArg₂ (fun v w : ℝ => v*w)
  · exact @ite_cond_congr ℝ (a = x) (x = a) _ (Classical.propDecidable (x = a)) t 1 (propext eq_comm)
  · exact @ite_cond_congr ℝ (b = x) (x = b) _ (Classical.propDecidable (x = b)) u 1 (propext eq_comm)

theorem mixed_two_root_mean {p : ℕ} [NeZero p] (a b : ZMod p) (hab : a ≠ b) (q : ℝ) :
    (∑ n ∈ range p, residueWeight q a (n : ZMod p)*residueWeight (1/2) b (n : ZMod p))/(p : ℝ) =
      1-(3/2-q)/(p : ℝ) := by
  rw [← real_residue_sum_eq_range (fun x : ZMod p => residueWeight q a x*residueWeight (1/2) b x),sum_two_residueWeights q (1/2) a b hab,ZMod.card]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

/-- Only the two weights needed by the numeric-addition argument are used.
The product is the exact local density for distinct roots. -/
theorem mixed_two_root_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ)
      (a b : (p : P) → ZMod p.val) (q : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) → (∀ p, a p ≠ b p) →
      (∑ n ∈ Ico u v, ∏ p : P,
        residueWeight q (a p) (n : ZMod p.val)*residueWeight (1/2) (b p) (n : ZMod p.val)) ≤
        K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := form_interval_sieve hFord hM (by norm_num : 0 < (2 : ℕ))
  refine ⟨K,hK,?_⟩
  intro P a b q u v Z hq hq1 huv hZ hP hab
  let root : (p : P) → Fin 2 → ZMod p.val := fun p => ![a p,b p]
  let θ : P → Fin 2 → ℝ := fun _ => ![q,1/2]
  have hθ (p : P) (i : Fin 2) : 0 ≤ θ p i ∧ θ p i ≤ 1 := by
    fin_cases i
    · exact ⟨hq,hq1⟩
    · norm_num [θ]
  have hh := hbound P root θ u v Z huv hZ hP hθ
  have hpoint (p : P) (x : ZMod p.val) : formRootWeight (root p) (θ p) x =
      residueWeight q (a p) x*residueWeight (1/2) (b p) x := formRootWeight_two_mixed _ _ _ _ _
  simp_rw [hpoint] at hh
  have hmean (p : P) :
      (∑ n ∈ range p.val, residueWeight q (a p) (n : ZMod p.val)*
        residueWeight (1/2) (b p) (n : ZMod p.val))/(p.val : ℝ) =
      1-(3/2-q)/(p.val : ℝ) := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    exact mixed_two_root_mean (a p) (b p) (hab p) q
  simp_rw [hmean] at hh
  rw [P.prod_coe_sort (fun p : ℕ => 1-(3/2-q)/(p : ℝ))] at hh
  exact hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MixedAffineSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both affine orientations of the numeric-addition sieve -/

namespace JointDickman
open Finset Classical

theorem affine_two_roots_ne {p : ℕ} [Fact p.Prime] (a b c d : ZMod p)
    (hb : b ≠ 0) (hd : d ≠ 0) (hdet : a*d-c*b ≠ 0) : -a/b ≠ -c/d := by
  intro h
  have he := (div_eq_div_iff hb hd).mp h
  apply hdet
  linear_combination -he

theorem residueWeight_affine {p : ℕ} [Fact p.Prime] (a b x : ZMod p)
    (hb : b ≠ 0) (q : ℝ) :
    residueWeight q 0 (a+b*x) = residueWeight q (-a/b) x := by
  have he := affine_residue_root a b x hb
  simp only [residueWeight,he]
  split_ifs <;> rfl

/-- Negative slopes are included, so the same statement applies when the
large numeric addition occurs at either endpoint. -/
theorem mixed_affine_interval_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (a b c d : ℤ) (q : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) →
      (∀ p ∈ P, (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧
        (a : ZMod p)*d-c*b ≠ 0) →
      (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n)) ≤
        K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2 := by
  obtain ⟨K,hK,hbound⟩ := mixed_two_root_interval_sieve hFord hM
  refine ⟨K,hK,?_⟩
  intro P a b c d q u v Z hq hq1 huv hZ hP hdet
  let : ∀ p : P, Fact p.val.Prime := fun p => ⟨(hP p.val p.property).1⟩
  let r₁ := fun p : P => -(a : ZMod p.val)/(b : ZMod p.val)
  let r₂ := fun p : P => -(c : ZMod p.val)/(d : ZMod p.val)
  have hr (p : P) : r₁ p ≠ r₂ p :=
    affine_two_roots_ne _ _ _ _ (hdet p.val p.property).1 (hdet p.val p.property).2.1
      (hdet p.val p.property).2.2
  have hh := hbound P r₁ r₂ q u v Z hq hq1 huv hZ hP hr
  have hterm (n : ℕ) : (∏ p : P,
      residueWeight q (r₁ p) (n : ZMod p.val)*residueWeight (1/2) (r₂ p) (n : ZMod p.val)) =
      ∏ p ∈ P, residueWeight q 0 ((a : ZMod p)+b*n)*
        residueWeight (1/2) 0 ((c : ZMod p)+d*n) := by
    rw [← P.prod_coe_sort]
    apply prod_congr rfl
    intro p _
    rw [residueWeight_affine _ _ _ (hdet p.val p.property).1,
      residueWeight_affine _ _ _ (hdet p.val p.property).2.1]
  simpa only [hterm] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MixedAffineHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic normalization for the numeric addition -/

namespace JointDickman
open Finset Classical

theorem mixed_affine_harmonic_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (a b c d : ℤ) (q W : ℝ) (u v Z : ℕ),
      0 ≤ q → q ≤ 1 → 0 < W → u ≤ v → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 4 ≤ p) →
      (∀ p ∈ P, (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧
        (a : ZMod p)*d-c*b ≠ 0) →
      (∀ n ∈ Ico u v, W ≤ (a : ℝ)+(b : ℝ)*n) →
      (∑ n ∈ Ico u v, (∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/
          ((a : ℝ)+(b : ℝ)*n)) ≤
        (K*((v : ℝ)-u)*(∏ p ∈ P, (1-(3/2-q)/(p : ℝ)))+2*(Z+1 : ℝ)*(Z : ℝ)^2)/W := by
  obtain ⟨K,hK,hbound⟩ := mixed_affine_interval_sieve hFord hM
  refine ⟨K,hK,?_⟩
  intro P a b c d q W u v Z hq hq1 hW huv hZ hP hdet hden
  have hh := hbound P a b c d q u v Z hq hq1 huv hZ hP hdet
  calc
    _ ≤ (∑ n ∈ Ico u v, ∏ p ∈ P,
        residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/W := by
      rw [sum_div]
      apply sum_le_sum
      intro n hn
      exact div_le_div_of_nonneg_left (prod_nonneg (fun p _ => mul_nonneg
        (residueWeight_nonneg _ _ hq) (residueWeight_nonneg _ _ (by norm_num)))) hW (hden n hn)
    _ ≤ _ := div_le_div_of_nonneg_right hh hW.le

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

theorem primePrefix_inter (B : ℕ) (g : ℝ) (S T : Finset ℕ) :
    primePrefix B g (S ∩ T) = S ∩ primePrefix B g T := by
  classical
  unfold primePrefix
  split_ifs
  · ext p
    simp only [mem_filter, mem_inter]
    tauto
  · rfl

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

theorem auxiliaryLogLength_tendsto : Tendsto auxiliaryLogLength atTop atTop :=
  Real.tendsto_log_atTop.comp auxiliaryRatio_tendsto

theorem log_auxiliaryCutoff (B : ℕ) :
    Real.log (auxiliaryCutoff B) = 1000 * Real.log B := by
  simp [auxiliaryCutoff, Nat.cast_pow, Real.log_pow]

theorem auxiliaryLogLength_eq {B : ℕ} (hB : 1 < B) :
    auxiliaryLogLength B = Real.log B - Real.log 1000 - Real.log (Real.log B) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength, auxiliaryRatio, Real.log_div hB0.ne' (mul_pos (by norm_num) hlog).ne',
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hlog.ne']
  ring

theorem logLogCutoff_div_log_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / Real.log B) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop)
  have hsmall := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hconst : Tendsto (fun B : ℕ => Real.log 1000 / Real.log B) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have h := hconst.add hsmall
  norm_num only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [log_auxiliaryCutoff, Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne', add_div]
  rfl

theorem auxiliaryLogLength_div_log_tendsto :
    Tendsto (fun B : ℕ => auxiliaryLogLength B / Real.log B) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub logLogCutoff_div_log_tendsto_zero
  norm_num only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : 0 < Real.log B := Real.log_pos (by exact_mod_cast hB)
  rw [auxiliaryLogLength_eq hB, log_auxiliaryCutoff,
    Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hl.ne']
  field_simp
  ring

theorem log_div_auxiliaryLogLength_tendsto :
    Tendsto (fun B : ℕ => Real.log B / auxiliaryLogLength B) atTop (𝓝 1) := by
  have h := auxiliaryLogLength_div_log_tendsto.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_div, inv_one] using h

theorem logLogCutoff_div_auxiliaryLogLength_tendsto_zero :
    Tendsto (fun B : ℕ => Real.log (Real.log (auxiliaryCutoff B)) / auxiliaryLogLength B) atTop (𝓝 0) := by
  have h := logLogCutoff_div_log_tendsto_zero.mul log_div_auxiliaryLogLength_tendsto
  norm_num only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with B hB
  have hl : Real.log B ≠ 0 := (Real.log_pos (by exact_mod_cast hB)).ne'
  field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularityPrimeSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens sums at the prefix scales used by regularity -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem auxiliaryCutoff_le_exp_rpow {c g : ℝ} (hc : 0 < c) (hg : 0 < g) :
    ∀ᶠ B : ℕ in atTop, (auxiliaryCutoff B : ℝ) ≤ Real.exp (c * (B : ℝ) ^ g) := by
  have hlim : Tendsto (fun B : ℕ => (1000 / c) * (Real.log B / (B : ℝ) ^ g)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((isLittleO_log_rpow_atTop hg).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul (1000 / c)
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hpow : 0 < (B : ℝ) ^ g := Real.rpow_pos_of_pos hB0 g
  have hsmall' : 1000 * Real.log B ≤ c * (B : ℝ) ^ g := by
    have hh : (1000 * Real.log B) / (c * (B : ℝ) ^ g) ≤ 1 := by
      convert hsmall using 1 <;> first | (with_reducible_and_instances rfl) | (field_simp)
    exact (div_le_one (mul_pos hc hpow)).mp hh
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast pow_pos (by omega : 0 < B) 1000
  calc
    _ = Real.exp (Real.log (auxiliaryCutoff B)) := (Real.exp_log hP).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [log_auxiliaryCutoff] using hsmall')

/-- Both interior prefixes and the full fixed exponential cutoff have
normalized reciprocal-prime mass g; the endpoint multiplier c contributes
only a bounded logarithm. -/
theorem regularity_prefix_prime_sum_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hg : 0 < g) :
    Tendsto (fun B : ℕ =>
      (∑ p ∈ largePrimeSet (Real.exp (c * (B : ℝ) ^ g)) (auxiliaryCutoff B), 1 / (p : ℝ)) /
        auxiliaryLogLength B) atTop (𝓝 g) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpow : Tendsto (fun B : ℕ => c * (B : ℝ) ^ g) atTop atTop :=
    ((tendsto_rpow_atTop hg).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have hupper := Real.tendsto_exp_atTop.comp hpow
  have hcut : Tendsto (fun B : ℕ => (auxiliaryCutoff B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto
  have herr : Tendsto (fun B : ℕ =>
      ((primeReciprocalSum (Real.exp (c * (B : ℝ) ^ g)) - Real.log (Real.log (Real.exp (c * (B : ℝ) ^ g)))) -
        (primeReciprocalSum (auxiliaryCutoff B) - Real.log (Real.log (auxiliaryCutoff B)))) /
          auxiliaryLogLength B) atTop (𝓝 0) :=
    ((hrem.comp hupper).sub (hrem.comp hcut)).div_atTop auxiliaryLogLength_tendsto
  have hconst : Tendsto (fun B : ℕ => Real.log c / auxiliaryLogLength B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryLogLength_tendsto
  have hmain := (hconst.add (log_div_auxiliaryLogLength_tendsto.const_mul g)).sub
    logLogCutoff_div_auxiliaryLogLength_tendsto_zero
  have h := herr.add hmain
  norm_num only [zero_add, mul_one, sub_zero] at h
  apply h.congr'
  filter_upwards [auxiliaryCutoff_le_exp_rpow hc hg, eventually_gt_atTop 1] with B hPY hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  rw [largePrimeSet_reciprocal_eq (Nat.cast_nonneg _) hPY, Real.log_exp,
    Real.log_mul hc.ne' (Real.rpow_pos_of_pos hB0 g).ne', Real.log_rpow hB0]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficient
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential prime-count tilts of the actual coefficient -/

namespace JointDickman

open Finset

theorem coefficient_prefix_count {B n : ℕ} (hn : n ≠ 0) (g : ℝ) :
    (primePrefix B g (coefficientPrimeSet B n)).card =
      primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n := by
  rw [coefficientPrimeSet_eq_inter hn, primePrefix_inter]
  rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularitySievePrimes
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the sieve's actual prefix prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem good_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P)
    (hU : 0 ≤ U) (hUZ : U ≤ Z) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet U P := by
  classical
  ext p
  constructor
  · intro hp
    exact (mem_filter.mp hp).2.2
  · intro hp
    obtain ⟨hpU, hpP⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hpZ : p ≤ Z := by
      have hpr : (p : ℝ) ≤ U := (Nat.le_floor_iff hU).mp hpU
      exact_mod_cast hpr.trans hUZ
    have hPp : P < p := by exact_mod_cast hpP
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩, ⟨hPp, hp⟩⟩

theorem full_prefix_sieve_set (P Z : ℕ) {U : ℝ} (hP : 6 ≤ P) (hZU : (Z : ℝ) ≤ U) :
    (sievePrimes Z).filter (fun p => P < p ∧ p ∈ largePrimeSet U P) = largePrimeSet Z P := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, hpP, _⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    apply mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Nat.floor_natCast] using hpZ
    · exact_mod_cast hpP
  · intro hp
    obtain ⟨hpZ, hpP⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hPp : P < p := by exact_mod_cast hpP
    have hpU : p ≤ ⌊U⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      ⟨hPp, mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, hpP⟩⟩⟩

theorem primePrefix_eq_largePrimeSet {B : ℕ} (hB : 1 ≤ B) {g : ℝ} (hg : g < 1) :
    primePrefix B g (auxiliaryPrimes B) =
      largePrimeSet (Real.exp ((B : ℝ) ^ g)) (auxiliaryCutoff B) := by
  classical
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpower : (B : ℝ) ^ g ≤ 4 * B := by
    have h := Real.rpow_le_rpow_of_exponent_le hB1 hg.le
    rw [Real.rpow_one] at h
    linarith
  have hupper : Real.exp ((B : ℝ) ^ g) ≤ auxiliaryUpper B := Real.exp_le_exp.mpr hpower
  rw [primePrefix, ite_eq_left hg]
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hplog⟩ := mem_filter.mp hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hpP
    obtain ⟨_, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) := by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hplog
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpX, hprime⟩, hpCut⟩
  · intro hp
    obtain ⟨hpU, hpCut⟩ := mem_filter.mp hp
    obtain ⟨hpU, hprime⟩ := Nat.mem_primesLE.mp hpU
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpX : (p : ℝ) ≤ Real.exp ((B : ℝ) ^ g) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mp hpU
    have hpUpper : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor (hpX.trans hupper)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpUpper, hprime⟩, hpCut⟩, ?_⟩
    simpa only [Real.log_exp] using Real.log_le_log hp0 hpX

theorem prefix_endpoint_le_sieveCutoff {c g : ℝ} (hc : 0 < c) (hg : g < 1) :
    ∀ᶠ B : ℕ in atTop, Real.exp ((B : ℝ) ^ g) ≤ sieveCutoff c B := by
  have hlim : Tendsto (fun B : ℕ => (B : ℝ) ^ g / B) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (power_div_power_tendsto_zero hg).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 2)),
    sieveCutoff_eventually hc, eventually_gt_atTop 0] with B hsmall hcut hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ g ≤ Real.log (sieveCutoff c B) := by
    have h := (div_le_iff₀ hB0).mp hsmall
    exact h.trans hcut.2.2.1
  have hZ : (0 : ℝ) < sieveCutoff c B := by exact_mod_cast (by omega : 0 < sieveCutoff c B)
  simpa only [Real.exp_log hZ] using Real.exp_le_exp.mpr hpow

/-- This is the actual reciprocal mass appearing in the tilted sieve,
including its finite cutoff, for every fixed regularity-grid point. -/
theorem tilt_prefix_mass_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c g : ℝ}
    (hc : 0 < c) (hc4 : c ≤ 4) (hg : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun B : ℕ =>
      tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        (primePrefix B g (auxiliaryPrimes B)) / auxiliaryLogLength B) atTop (𝓝 g) := by
  by_cases hglt : g < 1
  · have h := regularity_prefix_prime_sum_tendsto hM (by norm_num : (0 : ℝ) < 1) hg
    apply h.congr'
    filter_upwards [prefix_endpoint_le_sieveCutoff hc hglt,
      auxiliaryCutoff_tendsto.eventually_ge_atTop 6, eventually_ge_atTop 1] with B hX hP hB
    rw [one_mul, primePrefix_eq_largePrimeSet hB hglt]
    unfold tiltPrimeReciprocalMass
    rw [good_prefix_sieve_set _ _ hP (Real.exp_pos _).le hX]
  · have hg_eq : g = 1 := le_antisymm hg1 (le_of_not_gt hglt)
    subst g
    have h := regularity_prefix_prime_sum_tendsto hM hc (by norm_num : (0 : ℝ) < 1)
    apply h.congr'
    filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B hcut hP
    have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B := by
      refine hcut.2.2.2.trans (Real.exp_le_exp.mpr ?_)
      exact mul_le_mul_of_nonneg_right hc4 (Nat.cast_nonneg B)
    simp only [Real.rpow_one, primePrefix, lt_self_iff_false, ite_false, if_false]
    unfold tiltPrimeReciprocalMass auxiliaryPrimes
    rw [full_prefix_sieve_set _ _ hP hZU]
    simp only [largePrimeSet, Nat.floor_natCast, sieveCutoff]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MarkovRemainders
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of the Markov multipliers on sieve remainders -/

namespace JointDickman

open Filter
open scoped Topology

theorem auxiliaryLogLength_between :
    ∀ᶠ B : ℕ in atTop, 0 ≤ auxiliaryLogLength B ∧ auxiliaryLogLength B ≤ Real.log B := by
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [auxiliaryLogLength_tendsto.eventually_ge_atTop 0,
    hloglarge, eventually_gt_atTop 1] with B hℓ hlog hB
  refine ⟨hℓ, ?_⟩
  have hr : auxiliaryRatio B = (B : ℝ) / Real.log (auxiliaryCutoff B) := by
    rw [log_auxiliaryCutoff]
    rfl
  have hRB : auxiliaryRatio B ≤ B := by
    rw [hr]
    exact div_le_self (Nat.cast_nonneg _) hlog
  exact Real.log_le_log (auxiliaryRatio_pos hB) hRB

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeCountChernoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential bounds for counts in a selected prime subset -/

namespace JointDickman

open Finset

/-- The exact generating function for the count in Q. -/
theorem bernoulliSubsetMass_restricted_count_exp (P Q : Finset ℕ) (q : ℕ → ℝ) (s : ℝ) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) =
      ∏ p ∈ P ∩ Q, (1 - q p + q p * Real.exp s) := by
  classical
  have hv (S : Finset ℕ) : (∏ p ∈ S, if p ∈ Q then Real.exp s else 1) =
      Real.exp (s * (S ∩ Q).card) := by
    rw [← prod_filter, prod_const, ← Real.exp_nat_mul]
    have hf : S.filter (fun p => p ∈ Q) = S ∩ Q := by ext p; simp
    rw [hf]
    congr 1
    ring
  have h := bernoulliSubsetMass_tilt P q (fun p => if p ∈ Q then Real.exp s else 1)
  simp_rw [hv] at h
  rw [h]
  have heq (p : ℕ) : 1 - q p + q p * (if p ∈ Q then Real.exp s else 1) =
      if p ∈ Q then 1 - q p + q p * Real.exp s else 1 := by
    by_cases hp : p ∈ Q <;> simp [hp]
  simp_rw [heq]
  rw [← prod_filter]
  congr 1

theorem bernoulliSubsetMass_restricted_count_exp_bound (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  rw [bernoulliSubsetMass_restricted_count_exp]
  calc
    _ ≤ ∏ p ∈ P ∩ Q, Real.exp ((Real.exp s - 1) * q p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpP := (mem_inter.mp hp).1
        exact add_nonneg (sub_nonneg.mpr (hq p hpP).2)
          (mul_nonneg (hq p hpP).1 (Real.exp_pos _).le)
      · intro p _
        have h := Real.add_one_le_exp ((Real.exp s - 1) * q p)
        nlinarith
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

/-- Both upper and lower tails are covered by the signed threshold
`s*r ≤ s*count`; no asymptotic or distributional premise is hidden here. -/
theorem bernoulliSubsetMass_restricted_count_tail (P Q : Finset ℕ)
    (q : ℕ → ℝ) (s r : ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) :
    (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
      Real.exp (-s * r + (Real.exp s - 1) * ∑ p ∈ P ∩ Q, q p) := by
  classical
  have hmark : Real.exp (s * r) *
      (∑ S ∈ P.powerset, if s * r ≤ s * (S ∩ Q).card then bernoulliSubsetMass P q S else 0) ≤
        ∑ S ∈ P.powerset, bernoulliSubsetMass P q S * Real.exp (s * (S ∩ Q).card) := by
    rw [mul_sum]
    apply sum_le_sum
    intro S hS
    have hmass := bernoulliSubsetMass_nonneg (mem_powerset.mp hS) hq
    split_ifs with h
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) hmass
    · simpa only [mul_zero] using mul_nonneg hmass (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (hmark.trans (bernoulliSubsetMass_restricted_count_exp_bound P Q q s hq)) (Real.exp_pos (-s * r)).le
  have he : Real.exp (-s * r) * Real.exp (s * r) = 1 := by
    rw [← Real.exp_add]
    rw [show -s * r + s * r = 0 by ring, Real.exp_zero]
  simpa only [← mul_assoc, he, one_mul, ← Real.exp_add] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeIndicatorErrors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable prime-count estimates for the conditional indicator parameters -/

namespace JointDickman

open Finset

/-- Absolute errors in the inclusion probabilities control every restricted mean. -/
theorem restricted_indicator_mean_error (P Q : Finset ℕ) (q : ℕ → ℝ) {D : ℝ}
    (hD : (∑ p ∈ P, |q p - (1 / 2 : ℝ) / p|) ≤ D) :
    |(∑ p ∈ P ∩ Q, q p) - (1 / 2 : ℝ) * (∑ p ∈ P ∩ Q, 1 / (p : ℝ))| ≤ D := by
  calc
    _ = |∑ p ∈ P ∩ Q, (q p - (1 / 2 : ℝ) / p)| := by
      congr 1
      rw [sum_sub_distrib, mul_sum]
      congr 1
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ P ∩ Q, |q p - (1 / 2 : ℝ) / p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, |q p - (1 / 2 : ℝ) / p| :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left (fun _ _ _ => abs_nonneg _)
    _ ≤ D := hD

/-- At the full cutoff the sieve mass is just the actual prime reciprocal
mass, so the same Chernoff factors bound the indicator probabilities. -/
theorem full_cutoff_prime_mass (B : ℕ) (Q : Finset ℕ)
    (hP : 6 ≤ auxiliaryCutoff B) :
    tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff 4 B) Q =
      ∑ p ∈ auxiliaryPrimes B ∩ Q, 1 / (p : ℝ) := by
  classical
  have hset : (sievePrimes (sieveCutoff 4 B)).filter
      (fun p => auxiliaryCutoff B < p ∧ p ∈ Q) = auxiliaryPrimes B ∩ Q := by
    ext p
    simp only [mem_filter, mem_inter, sievePrimes, auxiliaryPrimes, auxiliaryUpper,
      sieveCutoff, largePrimeSet, mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨⟨hpZ, hp⟩, _hp6⟩, hpP, hpQ⟩
      exact ⟨⟨⟨hpZ, hp⟩, by exact_mod_cast hpP⟩, hpQ⟩
    · rintro ⟨⟨⟨hpZ, hp⟩, hpP⟩, hpQ⟩
      have hPp : auxiliaryCutoff B < p := by exact_mod_cast hpP
      exact ⟨⟨⟨hpZ, hp⟩, by omega⟩, hPp, hpQ⟩
  unfold tiltPrimeReciprocalMass
  rw [hset]

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

theorem remaining_parameter_total_error {P S : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) :
    (∑ p ∈ P, |remainingPrimeParameter S p - (1 / 2 : ℝ) / p|) ≤
      1 + ∑ p ∈ S, 1 / (p : ℝ) := by
  classical
  have hpoint (p : ℕ) (hp : p ∈ P) :
      |remainingPrimeParameter S p - (1 / 2 : ℝ) / p| ≤
        1 / (p : ℝ)^2 + if p ∈ S then 1 / (p : ℝ) else 0 := by
    by_cases hs : p ∈ S
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      simp only [remainingPrimeParameter, hs, ite_true, if_true, zero_sub, abs_neg,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) / p)]
      have hh : (1 / 2 : ℝ) / p ≤ 1 / (p : ℝ) :=
        div_le_div_of_nonneg_right (by norm_num) hp0.le
      linarith [show (0 : ℝ) ≤ 1 / (p : ℝ)^2 by positivity]
    · simpa only [remainingPrimeParameter, hs, ite_false, if_false, add_zero] using
        unselected_parameter_error (hP p hp).two_le
  have hsum := sum_le_sum hpoint
  have heq : P.filter (fun p => p ∈ S) = S := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsq : (∑ p ∈ P, 1 / (p : ℝ)^2) ≤ 1 := by
    simpa using sum_reciprocal_square_tail P (by norm_num : (1 : ℕ) ≠ 0) (fun p hp => (hP p hp).one_lt)
  rw [sum_add_distrib, ← sum_filter, heq] at hsum
  exact hsum.trans (add_le_add_left hsq _)

/-- Omitting a coefficient of fixed exponential size costs o(1) in total
reciprocal prime mass, uniformly in the coefficient. -/
theorem auxiliary_selected_reciprocal_sum_small {κ : ℝ} (_hκ : 0 < κ) :
    ∀ᶠ B : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ auxiliaryPrimes B →
      (∏ p ∈ S, p : ℕ) ≤ Real.exp (κ * B) → (∑ p ∈ S, 1 / (p : ℝ)) ≤ 1 := by
  have ht : Tendsto (fun B : ℕ => (κ / Real.log 2) *
      ((B : ℝ) / (auxiliaryCutoff B : ℝ))) atTop (𝓝 0) := by
    have hp := ((polynomial_div_primeCutoff_tendsto_zero (k := 1) (by norm_num)).comp
      tendsto_natCast_atTop_atTop).const_mul (κ / Real.log 2)
    simpa only [Function.comp_def, auxiliaryCutoff, Nat.cast_pow, pow_one, mul_zero] using hp
  filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 1] with B hsmall hB
  intro S hS hn
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (pow_pos (Nat.zero_lt_of_lt hB) 1000)
  have hprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Nat.mem_primesLE.mp (mem_filter.mp (hS hp)).1).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (S.card : ℝ) ≤ κ * B / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    refine (selectedPrime_card_log_bound S hprime).trans ?_
    have hn0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
      exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
    simpa only [Real.log_exp] using Real.log_le_log hn0 hn
  calc
    _ ≤ ∑ _p ∈ S, 1 / (auxiliaryCutoff B : ℝ) := sum_le_sum (fun p hp =>
      one_div_le_one_div_of_le hP0 (mem_filter.mp (hS hp)).2.le)
    _ = (S.card : ℝ) / auxiliaryCutoff B := by simp [div_eq_mul_inv]
    _ ≤ (κ * B / Real.log 2) / auxiliaryCutoff B := div_le_div_of_nonneg_right hcard hP0.le
    _ = (κ / Real.log 2) * ((B : ℝ) / (auxiliaryCutoff B : ℝ)) := by ring
    _ ≤ 1 := hsmall.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TiltedPrefixMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform prefix means after removing bounded prime products -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_reciprocal_mean_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {g : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) :
    Tendsto (fun B : ℕ => (∑ p ∈ primePrefix B g (auxiliaryPrimes B), 1/(p : ℝ))/
      auxiliaryLogLength B) atTop (𝓝 g) := by
  have h := tilt_prefix_mass_tendsto hM (by norm_num : (0 : ℝ) < 4) (by norm_num) hg hg1
  apply h.congr'
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop 6] with B hB
  rw [full_cutoff_prime_mass B _ hB]
  congr 2
  apply inter_eq_right.mpr
  unfold primePrefix
  split_ifs
  · exact filter_subset _ _
  · exact subset_rfl

theorem remaining_parameter_restricted_sum (P E Q : Finset ℕ) :
    (∑ p ∈ P ∩ Q, remainingPrimeParameter E p) =
      ∑ p ∈ (P \ E) ∩ Q, 1/(2*(p : ℝ)-1) := by
  calc
    _ = ∑ p ∈ (P \ E) ∩ Q, remainingPrimeParameter E p := by
      symm
      apply sum_subset
      · exact inter_subset_inter sdiff_subset subset_rfl
      · intro p hp hn
        have hpE : p ∈ E := by
          by_contra he
          exact hn (mem_inter.mpr ⟨mem_sdiff.mpr ⟨(mem_inter.mp hp).1,he⟩,(mem_inter.mp hp).2⟩)
        simp [remainingPrimeParameter,hpE]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      simp [remainingPrimeParameter,(mem_sdiff.mp (mem_inter.mp hp).1).2]

/-- A fixed exponential product removes only a bounded total parameter
error. The resulting normalized error tends to zero uniformly in that
product; this will be applied to the first coefficient and a fixed addition. -/
theorem tilted_prefix_mean_uniform
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ E : Finset ℕ, E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
      |(∑ p ∈ (auxiliaryPrimes B \ E) ∩ primePrefix B g (auxiliaryPrimes B),
          1/(2*(p : ℝ)-1))/auxiliaryLogLength B-g/2| ≤ ε := by
  let m := fun B : ℕ => ∑ p ∈ primePrefix B g (auxiliaryPrimes B), 1/(p : ℝ)
  have hm : Tendsto (fun B : ℕ => m B/auxiliaryLogLength B) atTop (𝓝 g) :=
    prefix_reciprocal_mean_tendsto hM hg hg1
  have herr : Tendsto (fun B : ℕ => 2/auxiliaryLogLength B+
      (1/2 : ℝ)*|m B/auxiliaryLogLength B-g|) atTop (𝓝 0) := by
    have h₂ : Tendsto (fun B : ℕ => (2 : ℝ)/auxiliaryLogLength B) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop auxiliaryLogLength_tendsto
    simpa using h₂.add (((hm.sub_const g).abs).const_mul (1/2 : ℝ))
  filter_upwards [auxiliary_selected_reciprocal_sum_small hκ,
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0,
    herr.eventually (Iio_mem_nhds hε)] with B hsmall hℓ heps
  intro E hE hprod
  have he := remaining_parameter_total_error (fun p hp => auxiliaryPrimes_prime B p hp) hE
  have he' := restricted_indicator_mean_error (D := 2) (auxiliaryPrimes B)
    (primePrefix B g (auxiliaryPrimes B)) (remainingPrimeParameter E)
    (he.trans (by linarith [hsmall E hE hprod]))
  rw [remaining_parameter_restricted_sum] at he'
  have hQ : auxiliaryPrimes B ∩ primePrefix B g (auxiliaryPrimes B) =
      primePrefix B g (auxiliaryPrimes B) := by
    apply inter_eq_right.mpr
    unfold primePrefix
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  rw [hQ] at he'
  let x := ∑ p ∈ (auxiliaryPrimes B \ E) ∩ primePrefix B g (auxiliaryPrimes B),
    1/(2*(p : ℝ)-1)
  have hdiv : |x/auxiliaryLogLength B-(1/2 : ℝ)*(m B/auxiliaryLogLength B)| ≤
      2/auxiliaryLogLength B := by
    rw [← mul_div_assoc,← sub_div,abs_div,abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right he' hℓ.le
  have htri := abs_sub_le (x/auxiliaryLogLength B) ((1/2 : ℝ)*(m B/auxiliaryLogLength B)) (g/2)
  have hmid : |(1/2 : ℝ)*(m B/auxiliaryLogLength B)-g/2| =
      (1/2 : ℝ)*|m B/auxiliaryLogLength B-g| := by
    rw [show (1/2 : ℝ)*(m B/auxiliaryLogLength B)-g/2 =
      (1/2 : ℝ)*(m B/auxiliaryLogLength B-g) by ring,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  rw [hmid] at htri
  dsimp only [x] at htri hdiv
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SievePrefixProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The numeric-addition sieve product after coefficient primes are deleted -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem prefix_reciprocal_removed_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g ε : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ E : Finset ℕ, E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
      (g-ε)*auxiliaryLogLength B ≤
        ∑ p ∈ primePrefix B g (auxiliaryPrimes B) \ E, 1/(p : ℝ) := by
  have hm := prefix_reciprocal_mean_tendsto hM hg hg1
  filter_upwards [hm.eventually (Ioi_mem_nhds (by linarith : g-ε/2 < g)),
    auxiliary_selected_reciprocal_sum_small hκ,
    auxiliaryLogLength_tendsto.eventually_ge_atTop (2/ε),
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hmean hEbound hlarge hℓ
  intro E hE hprod
  let Q := primePrefix B g (auxiliaryPrimes B)
  have hsum : (g-ε/2)*auxiliaryLogLength B ≤ ∑ p ∈ Q, 1/(p : ℝ) :=
    ((lt_div_iff₀ hℓ).mp hmean).le
  have herr : (∑ p ∈ Q ∩ E, 1/(p : ℝ)) ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)).trans (hEbound E hE hprod)
  have he := sum_sdiff (f := fun p : ℕ => 1/(p : ℝ)) (show Q ∩ E ⊆ Q from inter_subset_left)
  have hset : Q \ (Q ∩ E) = Q \ E := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hset] at he
  have hlarge' := (div_le_iff₀ hε).mp hlarge
  nlinarith

theorem numeric_sieve_prefix_product
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {κ g ε : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hg1 : g ≤ 1) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (E : Finset ℕ) (q : ℝ), E ⊆ auxiliaryPrimes B →
      (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) → 0 ≤ q → q ≤ 1 →
      (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ E, (1-(3/2-q)/(p : ℝ))) ≤
        Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B) := by
  filter_upwards [prefix_reciprocal_removed_lower hM hκ hg hg1 (half_pos hε),
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hsum hℓ
  intro E q hE hprod hq hq1
  let P := primePrefix B g (auxiliaryPrimes B) \ E
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    apply auxiliaryPrimes_prime B p
    have hQ : primePrefix B g (auxiliaryPrimes B) ⊆ auxiliaryPrimes B := by
      unfold primePrefix
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    exact hQ (mem_sdiff.mp hp).1
  have hprodexp : (∏ p ∈ P, (1-(3/2-q)/(p : ℝ))) ≤
      Real.exp (-(3/2-q)*(∑ p ∈ P, 1/(p : ℝ))) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp (-(3/2-q)/(p : ℝ)) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
          apply sub_nonneg.mpr
          exact (div_le_one (by linarith : (0 : ℝ) < p)).mpr (by linarith)
        · intro p _
          simpa only [neg_div,sub_eq_add_neg,add_comm] using
            Real.add_one_le_exp (-(3/2-q)/(p : ℝ))
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring
  refine hprodexp.trans (Real.exp_le_exp.mpr ?_)
  have hm := hsum E hE hprod
  have hc : 0 ≤ 3/2-q := by linarith
  have hh := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hc)
  have hεℓ := mul_nonneg hε.le hℓ.le
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_NumericPrefixHarmonic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic sieve at the actual large-addition prefix cutoff -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The prime cutoff and the Euler-product estimate are instantiated;
only the concrete progression geometry is left for an application. -/
theorem numeric_prefix_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (E : Finset ℕ) (a b c d : ℤ) (q W : ℝ) (u v : ℕ),
        E ⊆ auxiliaryPrimes B → (∏ p ∈ E, p : ℕ) ≤ Real.exp (κ*B) →
        0 ≤ q → q ≤ 1 → 0 < W → u ≤ v →
        (∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ E,
          (b : ZMod p) ≠ 0 ∧ (d : ZMod p) ≠ 0 ∧ (a : ZMod p)*d-c*b ≠ 0) →
        (∀ n ∈ Ico u v, W ≤ (a : ℝ)+(b : ℝ)*n) →
        (∑ n ∈ Ico u v, (∏ p ∈ primePrefix B g (auxiliaryPrimes B) \ E,
          residueWeight q 0 ((a : ZMod p)+b*n)*residueWeight (1/2) 0 ((c : ZMod p)+d*n))/
            ((a : ℝ)+(b : ℝ)*n)) ≤
          K*((v : ℝ)-u)/W*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
            2*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by
  obtain ⟨K,hK,hbound⟩ := mixed_affine_harmonic_sieve hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [numeric_sieve_prefix_product hM hκ hg hg1.le hε,
    eventually_ge_atTop 1, auxiliaryCutoff_tendsto.eventually_ge_atTop 4] with B hprod hB hcut
  intro E a b c d q W u v hE hEsize hq hq1 hW huv hdet hden
  let P := primePrefix B g (auxiliaryPrimes B) \ E
  let Z := numericAdditionSieveCutoff B g
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hZ : 2 ≤ Z := by
    apply Nat.le_floor
    change (2 : ℝ) ≤ Real.exp ((B : ℝ)^g)
    have hp : (1 : ℝ) ≤ (B : ℝ)^g := Real.one_le_rpow hB1 hg.le
    have he := Real.add_one_le_exp ((B : ℝ)^g)
    linarith
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ≤ Z ∧ 4 ≤ p := by
    have hpre := mem_sdiff.mp hp
    have hmemb : p ∈ (auxiliaryPrimes B).filter (fun p : ℕ => Real.log p ≤ (B : ℝ)^g) := by
      simpa only [primePrefix,ite_eq_left hg1] using hpre.1
    have hpA : p ∈ auxiliaryPrimes B := (mem_filter.mp hmemb).1
    have hprime := auxiliaryPrimes_prime B p hpA
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : Real.log p ≤ (B : ℝ)^g := (mem_filter.mp hmemb).2
    have hpZ : p ≤ Z := Nat.le_floor (by
      simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hlog)
    have hp4 : 4 ≤ p := by
      have hh := (mem_filter.mp hpA).2
      have hNat : auxiliaryCutoff B < p := by exact_mod_cast hh
      omega
    exact ⟨hprime,hpZ,hp4⟩
  have hh := hbound P a b c d q W u v Z hq hq1 hW huv hZ hP hdet hden
  have he := hprod E q hE hEsize hq hq1
  have hnon : 0 ≤ K*((v : ℝ)-u) := mul_nonneg hK.le (sub_nonneg.mpr (by exact_mod_cast huv))
  refine hh.trans ?_
  calc
    _ ≤ (K*((v : ℝ)-u)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+2*(Z+1 : ℝ)*(Z : ℝ)^2)/W :=
      div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left he hnon) le_rfl) hW.le
    _ = _ := by dsimp [Z] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionProgressionGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual progression of numeric additions -/

namespace JointDickman
open Finset Classical

/-- The determinant of the two progression forms is the fixed nonzero
opposite coefficient, with no dependence on the progression variable. -/
theorem addition_progression_determinant {e j b z₀ : ℕ} {c₀ : ℤ}
    (hbase : (e : ℤ)*z₀ = b+(j : ℤ)*c₀) :
    (z₀ : ℤ)*e-c₀*j = b := by linear_combination hbase

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AdditionSieveGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the actual coefficient primes in the addition sieve -/

namespace JointDickman
open Finset Classical

theorem additionExcludedPrimes_subset (B e b : ℕ) :
    additionExcludedPrimes B e b ⊆ auxiliaryPrimes B := inter_subset_right

theorem additionExcludedPrimes_product_le {B e b : ℕ} (he : 0 < e) (hb : 0 < b) :
    (∏ p ∈ additionExcludedPrimes B e b, p : ℕ) ≤ e*b := by
  apply Nat.le_of_dvd (Nat.mul_pos he hb)
  exact (prod_dvd_prod_of_subset _ _ id inter_subset_left).trans (Nat.prod_primeFactors_dvd (e*b))

theorem addition_progression_good_primes {B e j b z₀ : ℕ} {g : ℝ}
    (he : 0 < e) (hb : 0 < b) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B)
    {c : ℤ} (hbase : (e : ℤ)*z₀ = b+(j : ℤ)*c) :
    ∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
      (j : ZMod p) ≠ 0 ∧ (e : ZMod p) ≠ 0 ∧
        (z₀ : ZMod p)*e-(c : ZMod p)*j ≠ 0 := by
  intro p hp
  obtain ⟨hpQ,hpE⟩ := mem_sdiff.mp hp
  have hQ : primePrefix B g (auxiliaryPrimes B) ⊆ auxiliaryPrimes B := by
    unfold primePrefix
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hpP := hQ hpQ
  have hprime := auxiliaryPrimes_prime B p hpP
  have hbig : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp hpP).2
  have hn : ¬p ∣ e*b := by
    intro hd
    exact hpE (mem_inter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hprime,hd,(Nat.mul_pos he hb).ne'⟩,hpP⟩)
  have hne : ¬p ∣ e := fun hd => hn (dvd_mul_of_dvd_left hd b)
  have hnb : ¬p ∣ b := fun hd => hn (dvd_mul_of_dvd_right hd e)
  have hnj : ¬p ∣ j := Nat.not_dvd_of_pos_of_lt hj (lt_of_le_of_lt hcut hbig)
  have hdet := addition_progression_determinant hbase
  have hcast : (z₀ : ZMod p)*e-(c : ZMod p)*j = (b : ZMod p) := by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using congrArg (fun z : ℤ => (z : ZMod p)) hdet
  refine ⟨?_,?_,?_⟩
  · simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hnj
  · simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hne
  · rw [hcast]
    simpa only [ne_eq,ZMod.natCast_eq_zero_iff] using hnb

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionProgressionInterval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common interval for additions in a factor-four size window -/

namespace JointDickman
open Finset Classical

theorem additionInterval_order {W : ℝ} {j : ℕ} (hW : 0 ≤ W) :
    additionIntervalLower W j ≤ additionIntervalUpper W j := by
  have hh : W/(j : ℝ) ≤ 4*W/j := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    linarith
  exact (Nat.floor_mono hh).trans (Nat.le_succ _)

theorem additionInterval_contains {W : ℝ} {j z : ℕ} (hWz : W ≤ (z : ℝ))
    (hzW : (z : ℝ) ≤ 4*W) : z/j ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j) := by
  apply mem_Ico.mpr
  have hlo := Nat.floor_mono (div_le_div_of_nonneg_right hWz (Nat.cast_nonneg j))
  have hhi := Nat.floor_mono (div_le_div_of_nonneg_right hzW (Nat.cast_nonneg j))
  rw [Nat.floor_div_eq_div] at hlo hhi
  exact ⟨hlo,Nat.lt_succ_of_le hhi⟩

theorem additionInterval_denominator {W : ℝ} {j z₀ n : ℕ}
    (hj : 0 < j) (hW : 2*(j : ℝ) ≤ W)
    (hn : n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j)) :
    W/2 ≤ (z₀ : ℝ)+(j : ℝ)*n := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hf := Nat.lt_floor_add_one (W/(j : ℝ))
  change W/(j : ℝ) < (additionIntervalLower W j : ℝ)+1 at hf
  have hmul := (div_lt_iff₀ hjr).mp hf
  have hnr : (additionIntervalLower W j : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
  have hz₀ : (0 : ℝ) ≤ z₀ := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hnr hjr.le]

theorem additionInterval_length {W : ℝ} {j : ℕ} (hj : 0 < j) (hW : (j : ℝ) ≤ W) :
    (additionIntervalUpper W j : ℝ)-additionIntervalLower W j ≤ 5*W/j := by
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 ≤ W := hjr.le.trans hW
  have hf := Nat.floor_le (div_nonneg (by linarith : 0 ≤ 4*W) hjr.le)
  have hlo : (0 : ℝ) ≤ additionIntervalLower W j := Nat.cast_nonneg _
  have hfrac : (1 : ℝ) ≤ W/j := (le_div_iff₀ hjr).mpr (by simpa using hW)
  dsimp only [additionIntervalUpper]
  push_cast
  linarith [show 5*W/j = 4*W/j+W/j by ring]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicityRates
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The entropy and Poisson exponents in representation multiplicity -/

namespace JointDickman

/-- This identity is responsible for cancellation of the numeric sieve
and inclusion probability exponents. The conventions at zero agree. -/
theorem halfRankin_sub_halfPoisson (r : ℝ) :
    halfRankinExponent r-halfPoissonRate (1/2-r) = (1/2)*Real.binEntropy (2*r) := by
  have hlog : Real.log ((1/2 : ℝ)/r) = -Real.log (2*r) := by
    rw [show (1/2 : ℝ)/r = (2*r)⁻¹ by simp [mul_inv_rev,div_eq_mul_inv,mul_comm],Real.log_inv]
  unfold halfRankinExponent halfPoissonRate Real.binEntropy
  rw [hlog,show 2*((1/2 : ℝ)-r) = 1-2*r by ring]
  simp only [Real.log_inv]
  ring

/-- A clamped exponential parameter handles the endpoint u=0 without an
infinite tilt. The loss is at most the chosen positive clamp δ. -/
theorem halfPoisson_clamped_chernoff {u δ : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let t := -Real.log (2*max δ u)
    0 ≤ t ∧ t ≤ -Real.log (2*δ) ∧
      t*u+(Real.exp (-t)-1)/2 ≤ -halfPoissonRate u+δ := by
  dsimp only
  have hmax : 0 < max δ u := lt_of_lt_of_le hδ (le_max_left _ _)
  have hm1 : max δ u ≤ 1/2 := max_le hδ1 hu1
  have hlog : Real.log (2*max δ u) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hmono : Real.log (2*δ) ≤ Real.log (2*max δ u) :=
    Real.log_le_log (by positivity) (by nlinarith [le_max_left δ u])
  refine ⟨by linarith,by linarith,?_⟩
  rw [neg_neg,Real.exp_log (by positivity)]
  by_cases hdu : δ ≤ u
  · rw [max_eq_right hdu]
    unfold halfPoissonRate
    linarith
  · have huδ : u ≤ δ := le_of_not_ge hdu
    rw [max_eq_left huδ]
    by_cases hu0 : u = 0
    · subst u
      simp only [halfPoissonRate,zero_mul,mul_zero,sub_zero,add_zero]
      linarith
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hl : Real.log (2*u) ≤ Real.log (2*δ) := Real.log_le_log (by positivity) (by linarith)
      have hp := mul_le_mul_of_nonneg_left hl hu
      unfold halfPoissonRate
      nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NumericRankinExponent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The clamped Rankin exponent for numeric additions -/

namespace JointDickman

/-- The entropy exponent from the numeric sieve loses at most the clamp.
This includes both the zero-cardinality class and counts exceeding half the
prefix mean. -/
theorem clamped_numeric_rankin {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let r := min x (1/2)
    let q := max δ r
    q+x*Real.log ((1/2)/q) ≤ halfRankinExponent r+δ := by
  dsimp only
  by_cases hx1 : x ≤ 1/2
  · rw [min_eq_left hx1]
    by_cases hd : δ ≤ x
    · rw [max_eq_right hd]
      unfold halfRankinExponent
      nlinarith
    · rw [max_eq_left (le_of_not_ge hd)]
      by_cases hx0 : x = 0
      · subst x
        simp [halfRankinExponent]
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have hfrac : (1/2 : ℝ)/δ ≤ (1/2 : ℝ)/x :=
          div_le_div_of_nonneg_left (by norm_num) hxpos (le_of_not_ge hd)
        have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (1/2 : ℝ)/δ) hfrac
        have hm := mul_le_mul_of_nonneg_left hlog hx
        unfold halfRankinExponent
        nlinarith
  · rw [min_eq_right (le_of_not_ge hx1),max_eq_right hδ1]
    norm_num [halfRankinExponent]
    exact hδ.le

theorem halfRankinExponent_le_half {r : ℝ} (hr : 0 ≤ r) : halfRankinExponent r ≤ 1/2 := by
  by_cases hr0 : r = 0
  · simp [hr0,halfRankinExponent]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (1/2 : ℝ)/r)
    have hh := mul_le_mul_of_nonneg_left hlog hr
    have he : r*((1/2 : ℝ)/r-1) = 1/2-r := by field_simp
    rw [he] at hh
    unfold halfRankinExponent
    nlinarith

/-- The grid cutoff contributes at most 3Δ when g-γ=2Δ; the clamp
contributes at most gδ. -/
theorem numeric_rankin_exponent_bound {g γ τ x δ : ℝ}
    (hg : 0 ≤ g) (hγ : γ ≤ g) (hx : 0 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let r := min x (1/2);
    let q := max δ r;
    -(3/2-q)*γ+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2 ≤
      g*(halfRankinExponent r-1-weightBaseExponent)+
        (3/2)*(g-γ)+g*δ+τ*Real.log 2 := by
  dsimp only
  have hclamp := clamped_numeric_rankin hx hδ hδ1
  have hmul := mul_le_mul_of_nonneg_left hclamp hg
  have hq : 0 ≤ max δ (min x (1/2)) := hδ.le.trans (le_max_left _ _)
  have hgap : 0 ≤ (g-γ)*max δ (min x (1/2)) := mul_nonneg (sub_nonneg.mpr hγ) hq
  unfold weightBaseExponent
  nlinarith

/-- The prefactor cannot grow with an unbounded cardinality: above the
clipping threshold its Rankin contribution is exactly one. -/
theorem numeric_rankin_prefactor_bound {g τ ℓ : ℝ} {d : ℕ} {δ : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hℓ : 0 < ℓ) (hτ : τ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let q := max δ (min ((d : ℝ)/(g*ℓ)) (1/2))
    ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2) ≤ Real.exp (3*ℓ) := by
  dsimp only
  let x := (d : ℝ)/(g*ℓ)
  let q := max δ (min x (1/2))
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le
  have hq : 0 < q := hδ.trans_le (le_max_left _ _)
  have hr : 0 ≤ min x (1/2) := le_min hx (by norm_num)
  have hc := clamped_numeric_rankin hx hδ hδ1
  have hf := halfRankinExponent_le_half hr
  have hclamp : x*Real.log ((1/2 : ℝ)/q) ≤ 1 := by
    change q+x*Real.log ((1/2 : ℝ)/q) ≤ _ at hc
    linarith
  have hmul := mul_le_mul_of_nonneg_left hclamp (mul_pos hg hℓ).le
  have hxid : g*ℓ*x = (d : ℝ) := by dsimp only [x]; field_simp
  rw [← mul_assoc,hxid] at hmul
  have hd : (d : ℝ)*Real.log ((1/2 : ℝ)/q) ≤ ℓ := by
    have hgℓ := mul_le_mul_of_nonneg_right hg1 hℓ.le
    nlinarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hterm : (g/2+τ)*Real.log 2 ≤ 2 := by nlinarith
  have heq : ((1/2 : ℝ)/q)^d = Real.exp ((d : ℝ)*Real.log ((1/2 : ℝ)/q)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  change ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2) ≤ _
  rw [heq,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem halfRankinExponent_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1/2) :
    0 ≤ halfRankinExponent r := by
  by_cases hr0 : r = 0
  · simp [hr0,halfRankinExponent]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hfrac : (1 : ℝ) ≤ (1/2 : ℝ)/r := (le_div_iff₀ hrpos).mpr (by linarith)
    have hlog := Real.log_nonneg hfrac
    unfold halfRankinExponent
    positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NumericAdditionWeights
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dropping prime conditions in the numeric-addition sieve -/

namespace JointDickman
open Finset Classical

theorem prime_product_weight_le_residue_product (S P : Finset ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hS : ∀ p ∈ S, p.Prime) (hP : ∀ p ∈ P, p.Prime) :
    q^S.card ≤ ∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p) := by
  let n := ∏ r ∈ S, r
  have hn : n ≠ 0 := prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hpf : n.primeFactors = S := Nat.primeFactors_prod hS
  have hdiv (p : ℕ) (hp : p ∈ P) : p ∣ n ↔ p ∈ S := by
    rw [← hpf,Nat.mem_primeFactors]
    simp only [hP p hp,hn,and_true,true_and,ne_eq,not_false_eq_true]
  have he (p : ℕ) (hp : p ∈ P) : residueWeight q 0 (n : ZMod p) = if p ∈ S then q else 1 := by
    simp only [residueWeight,ZMod.natCast_eq_zero_iff,hdiv p hp]
  have hs : P.filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hh := prod_le_prod_of_subset_of_le_one hs (f := fun _ : ℕ => q)
    (fun _ _ => hq) (fun _ _ _ => hq1)
  change q^S.card ≤ ∏ p ∈ P, residueWeight q 0 (n : ZMod p)
  rw [prod_congr rfl he,← prod_filter]
  simpa only [prod_const] using hh

theorem prefix_count_weight_le_residue_product (n : ℕ) (Q P : Finset ℕ)
    (hn : n ≠ 0) (hPQ : P ⊆ Q) (hP : ∀ p ∈ P, p.Prime) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q^(n.primeFactors ∩ Q).card ≤ ∏ p ∈ P, residueWeight q 0 (n : ZMod p) := by
  let S := n.primeFactors ∩ Q
  have he (p : ℕ) (hp : p ∈ P) : residueWeight q 0 (n : ZMod p) = if p ∈ S then q else 1 := by
    have hd : p ∈ S ↔ p ∣ n := by
      simp only [S,mem_inter,Nat.mem_primeFactors,hP p hp,hn,hPQ hp,and_true,true_and,ne_eq,not_false_eq_true]
    simp only [residueWeight,ZMod.natCast_eq_zero_iff,hd]
  have hs : P.filter (fun p => p ∈ S) ⊆ S := fun p hp => (mem_filter.mp hp).2
  have hh := prod_le_prod_of_subset_of_le_one hs (f := fun _ : ℕ => q)
    (fun _ _ => hq) (fun _ _ _ => hq1)
  rw [prod_congr rfl he,← prod_filter]
  simpa only [prod_const,S] using hh

/-- Prefix regularity of the alternative quotient supplies its half-weight.
Deleting all other prime conditions increases the numeric sum. -/
theorem regular_numeric_addition_majorant {B L k n : ℕ} {τ C q : ℝ}
    (S P : Finset ℕ) (hn : n ≠ 0) (hk : k ∈ Icc 1 L)
    (hreg : RegularPrimeSet B L τ C (coefficientPrimeSet B n))
    (hP : P ⊆ primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B))
    (hS : ∀ p ∈ S, p.Prime) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    q^S.card ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
      ∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p)*residueWeight (1/2) 0 (n : ZMod p) := by
  let Q := primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B)
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    apply auxiliaryPrimes_prime B p
    have hsub : Q ⊆ auxiliaryPrimes B := by
      unfold Q primePrefix
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    exact hsub (hP hp)
  have hz := prime_product_weight_le_residue_product S P hq hq1 hS hPprime
  have hc := prefix_count_weight_le_residue_product n Q P hn hP hPprime (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
  have hncard : ((n.primeFactors ∩ Q).card : ℝ) ≤ (((k : ℝ)/L)/2+τ)*auxiliaryLogLength B := by
    have hh := (hreg.1 k hk).2
    rwa [coefficient_prefix_count hn] at hh
  have hweight : 1 ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
      (1/2 : ℝ)^(n.primeFactors ∩ Q).card := by
    have hp : (1/2 : ℝ)^(n.primeFactors ∩ Q).card =
        Real.exp (-((n.primeFactors ∩ Q).card : ℝ)*Real.log 2) := by
      rw [show -((n.primeFactors ∩ Q).card : ℝ)*Real.log 2 =
        ((n.primeFactors ∩ Q).card : ℝ)*(-Real.log 2) by ring,
        Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hp,← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)])
  calc
    _ ≤ q^S.card*(Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        (1/2 : ℝ)^(n.primeFactors ∩ Q).card) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight (pow_nonneg hq _)
    _ = Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        (q^S.card*(1/2 : ℝ)^(n.primeFactors ∩ Q).card) := by ring
    _ ≤ Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)*
        ((∏ p ∈ P, residueWeight q 0 ((∏ r ∈ S, r : ℕ) : ZMod p))*
          (∏ p ∈ P, residueWeight (1/2) 0 (n : ZMod p))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hz hc (by positivity) (prod_nonneg (fun _ _ => residueWeight_nonneg _ _ hq))
    _ = _ := by rw [prod_mul_distrib]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrefixOmissions
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Few omissions above the addition prefix

This is the deterministic first step in the weighted multiplicity estimate
of `moments.tex`: total and prefix regularity leave at most 4τℓ omissions
above a prefix containing every added prime.
-/

namespace JointDickman
open Finset Classical

theorem primePrefix_mono (B : ℕ) (g : ℝ) {A R : Finset ℕ} (h : A ⊆ R) :
    primePrefix B g A ⊆ primePrefix B g R := by
  unfold primePrefix
  split_ifs
  · exact filter_subset_filter _ h
  · exact h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NumericAdditionClass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing a class of actual numeric additions

A class fixes the retained coefficient, the opposite coefficient, the lag,
the number of added primes, and a factor-four product window.  The alternative
quotient remains regular.  Its weighted sum is reduced to one progression.
-/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem primePrefix_exponent_mono {B : ℕ} (hB : 1 ≤ B) {g h : ℝ}
    (hgh : g ≤ h) (P : Finset ℕ) : primePrefix B g P ⊆ primePrefix B h P := by
  by_cases hh : h < 1
  · have hg : g < 1 := hgh.trans_lt hh
    simp only [primePrefix,ite_eq_left hg,ite_eq_left hh]
    intro p hp
    obtain ⟨hp,hlog⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp,hlog.trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hB) hgh)⟩
  · simp only [primePrefix,ite_eq_right hh]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_NumericSieveError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Negligibility of the large-addition sieve remainder -/

namespace JointDickman
open Filter
open scoped Topology

/-- At separated powers, the explicit polynomial sieve remainder is
smaller than every fixed power of B, uniformly in the allowed lag. -/
theorem numeric_sieve_scaled_error_tendsto {g a : ℝ} (ha : 0 < a) (hga : g < a) (D : ℝ) :
    Tendsto (fun B : ℝ => 32*B^(D+2)*Real.exp (3*B^g-B^a)) atTop (𝓝 0) := by
  have hp := (power_div_power_tendsto_zero hga).const_mul 3
  have hl := (log_power_div_power_tendsto_zero 1 ha).const_mul (D+2)
  have hc := (power_div_power_tendsto_zero ha).const_mul (Real.log 32)
  have hq : Tendsto (fun B : ℝ =>
      3*(B^g/B^a)-1+(D+2)*(Real.log B/B^a)+Real.log 32/B^a) atTop (𝓝 (-1)) := by
    simpa only [Real.rpow_one,Real.rpow_zero,one_div,mul_zero,zero_sub,sub_zero,
      add_zero,mul_one,mul_inv_rev,div_eq_mul_inv,one_mul] using ((hp.sub_const 1).add hl).add hc
  have he := hq.neg_mul_atTop (by norm_num : (-1 : ℝ) < 0) (tendsto_rpow_atTop ha)
  have hlim := Real.tendsto_exp_atBot.comp he
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
  dsimp
  have hBa := (Real.rpow_pos_of_pos hB a).ne'
  have hident : (3*(B^g/B^a)-1+(D+2)*(Real.log B/B^a)+Real.log 32/B^a)*B^a =
      Real.log 32+(D+2)*Real.log B+(3*B^g-B^a) := by field_simp <;> ring
  rw [hident,Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 32)]
  simp only [Real.rpow_def_of_pos hB]
  congr 2
  congr 1
  ring

theorem numeric_sieve_remainder_small {g a : ℝ} (ha : 0 < a) (hga : g < a) (D : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (W : ℝ), 0 < j → (j : ℝ) ≤ (B : ℝ)^2 →
      Real.exp ((B : ℝ)^a)/4 ≤ W →
      4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W ≤
        (B : ℝ)^(-D)/(j : ℝ) := by
  have hlim := (numeric_sieve_scaled_error_tendsto ha hga D).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with B hsmall hB
  intro j W hj hjB hW
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hB)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 < W := (by positivity : 0 < Real.exp ((B : ℝ)^a)/4).trans_le hW
  let E := Real.exp ((B : ℝ)^g)
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (Real.rpow_nonneg hB0.le _)
  have hZ : (numericAdditionSieveCutoff B g : ℝ) ≤ E := Nat.floor_le (Real.exp_pos _).le
  have herr : 4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W ≤
      32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by
    calc
      _ ≤ (4*(2*E)*E^2)/(Real.exp ((B : ℝ)^a)/4) := by
        apply div_le_div₀ (by positivity) _ (by positivity) hW
        gcongr
        linarith only [hZ,hE1]
      _ = _ := by
        dsimp only [E]
        rw [Real.exp_sub,show (3 : ℝ)*(B : ℝ)^g = (B : ℝ)^g+2*(B : ℝ)^g by ring,
          Real.exp_add,show Real.exp (2*(B : ℝ)^g) = Real.exp ((B : ℝ)^g)^2 by
            simpa only [Nat.cast_ofNat] using Real.exp_nat_mul ((B : ℝ)^g) 2]
        ring
  have hpow : (B : ℝ)^(D+2) = (B : ℝ)^D*(B : ℝ)^2 := by
    rw [Real.rpow_add hB0,Real.rpow_two]
  have hepos : 0 ≤ 32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by positivity
  have hmul : (32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a))*(j : ℝ)*(B : ℝ)^D ≤ 1 := by
    calc
      _ ≤ (32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a))*(B : ℝ)^2*(B : ℝ)^D := by gcongr
      _ = 32*(B : ℝ)^(D+2)*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) := by rw [hpow]; ring
      _ ≤ 1 := hsmall
  have hmain : 32*Real.exp (3*(B : ℝ)^g-(B : ℝ)^a) ≤ (B : ℝ)^(-D)/(j : ℝ) := by
    rw [Real.rpow_neg hB0.le]
    apply (le_div_iff₀ hj0).mpr
    rw [inv_eq_one_div]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hB0 D)).mpr hmul
  exact herr.trans hmain

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicityChernoff
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative lower-tail exponent with a perturbed prefix mean -/

namespace JointDickman

/-- The only mean hypothesis is an explicit numerical lower bound. In the
application it comes from `tilted_prefix_mean_uniform`, which uses the
published reciprocal-prime Mertens input. -/
theorem multiplicity_chernoff_exponent {g ℓ ω m τ ε δ r : ℝ}
    (hg : 0 ≤ g) (hℓ : 0 ≤ ℓ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hr : 0 ≤ r) (hr1 : r ≤ 1/2)
    (hω : g*r*ℓ ≤ ω) (hm : (g/2-ε)*ℓ ≤ m) :
    let t := -Real.log (2*max δ (1/2-r))
    t*((g/2+τ)*ℓ-ω)+(Real.exp (-t)-1)*m ≤
      (-g*halfPoissonRate (1/2-r)+g*δ+(-Real.log (2*δ))*τ+ε)*ℓ := by
  let t := -Real.log (2*max δ (1/2-r))
  obtain ⟨ht,htop,hrate⟩ := halfPoisson_clamped_chernoff (u := 1/2-r) (by linarith)
    (by linarith) hδ hδ1
  change 0 ≤ t at ht
  change t ≤ -Real.log (2*δ) at htop
  change t*(1/2-r)+(Real.exp (-t)-1)/2 ≤ -halfPoissonRate (1/2-r)+δ at hrate
  have he0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hfirst : t*((g/2+τ)*ℓ-ω) ≤ t*(g*(1/2-r)*ℓ+τ*ℓ) := by
    apply mul_le_mul_of_nonneg_left _ ht
    nlinarith
  have hsecond : (Real.exp (-t)-1)*m ≤
      (Real.exp (-t)-1)*(g/2*ℓ)+ε*ℓ := by
    have hh := mul_le_mul_of_nonpos_left hm (sub_nonpos.mpr he1)
    have herr := mul_nonneg (mul_nonneg he0 hε) hℓ
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hrate (mul_nonneg hg hℓ)
  have hτbound := mul_le_mul_of_nonneg_right htop (mul_nonneg hτ hℓ)
  change t*((g/2+τ)*ℓ-ω)+(Real.exp (-t)-1)*m ≤ _
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RequiredSubsetTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prescribed inclusions with a remaining prefix-count restriction -/

namespace JointDickman
open Finset Classical

/-- Conditioning on prescribed independent inclusions leaves the other
parameters unchanged. The test remains inside the finite expectation. -/
theorem bernoulliSubsetMass_required_test (P A : Finset ℕ) (q : ℕ → ℝ)
    (hA : A ⊆ P) (F : Finset ℕ → ℝ) :
    (∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S*F S else 0) =
      (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset,
        bernoulliSubsetMass (P \ A) q R*F (A ∪ R) := by
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
    have has := (mem_filter.mp hS).2
    have he : (P \ A) \ (S \ A) = P \ S := by
      ext p
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hp,ha⟩,hs⟩
        exact ⟨hp,fun h => hs ⟨h,ha⟩⟩
      · rintro ⟨hp,hs⟩
        exact ⟨⟨hp,fun h => hs (has h)⟩,fun h => hs h.1⟩
    have hu : A ∪ (S \ A) = S := union_sdiff_of_subset has
    rw [hu]
    unfold bernoulliSubsetMass
    rw [he,← prod_sdiff has]
    ring

/-- Lower-tail Chernoff bound with the prescribed inclusions retained.
This is the finite estimate used for numeric additions in `moments.tex`. -/
theorem bernoulliSubsetMass_required_prefix_tail (P A Q : Finset ℕ) (q : ℕ → ℝ)
    (hA : A ⊆ P) (hAQ : A ⊆ Q) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    (∑ S ∈ P.powerset, if A ⊆ S ∧ ((S ∩ Q).card : ℝ) ≤ r then
      bernoulliSubsetMass P q S else 0) ≤
      (∏ p ∈ A, q p)*Real.exp (t*(r-A.card)+
        (Real.exp (-t)-1)*∑ p ∈ (P \ A) ∩ Q, q p) := by
  have he : (∑ S ∈ P.powerset, if A ⊆ S ∧ ((S ∩ Q).card : ℝ) ≤ r then
      bernoulliSubsetMass P q S else 0) =
      (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset,
        if ((R ∩ Q).card : ℝ) ≤ r-A.card then bernoulliSubsetMass (P \ A) q R else 0 := by
    calc
      _ = ∑ S ∈ P.powerset, if A ⊆ S then bernoulliSubsetMass P q S*
          (if ((S ∩ Q).card : ℝ) ≤ r then 1 else 0) else 0 := by
        apply sum_congr rfl
        intro S _
        split_ifs <;> simp_all
      _ = (∏ p ∈ A, q p)*∑ R ∈ (P \ A).powerset, bernoulliSubsetMass (P \ A) q R*
          (if (((A ∪ R) ∩ Q).card : ℝ) ≤ r then 1 else 0) :=
        bernoulliSubsetMass_required_test P A q hA _
      _ = _ := by
        congr 1
        apply sum_congr rfl
        intro R hR
        have hr := mem_powerset.mp hR
        have hd : Disjoint A (R ∩ Q) := by
          apply disjoint_left.mpr
          intro p hp hpR
          exact (mem_sdiff.mp (hr (mem_inter.mp hpR).1)).2 hp
        have hc : (((A ∪ R) ∩ Q).card : ℝ) = (A.card : ℝ)+(R ∩ Q).card := by
          rw [union_inter_distrib_right,inter_eq_left.mpr hAQ,card_union_of_disjoint hd,Nat.cast_add]
        rw [hc]
        have hh : (A.card : ℝ)+(R ∩ Q).card ≤ r ↔ ((R ∩ Q).card : ℝ) ≤ r-A.card := by
          constructor <;> intro hh <;> linarith
        simp only [hh,mul_ite,mul_one,mul_zero]
  rw [he]
  have htail := bernoulliSubsetMass_restricted_count_tail (P \ A) Q q (-t) (r-A.card)
    (fun p hp => hq p (mem_sdiff.mp hp).1)
  have hb : (∑ R ∈ (P \ A).powerset,
        if ((R ∩ Q).card : ℝ) ≤ r-A.card then bernoulliSubsetMass (P \ A) q R else 0) ≤
      Real.exp (t*(r-A.card)+(Real.exp (-t)-1)*∑ p ∈ (P \ A) ∩ Q, q p) := by
    refine le_trans ?_ (by simpa only [neg_neg] using htail)
    apply sum_le_sum
    intro R hR
    have hnon := bernoulliSubsetMass_nonneg (mem_powerset.mp hR)
      (fun p hp => hq p (mem_sdiff.mp hp).1)
    split_ifs with hc hs
    · exact le_rfl
    · exact False.elim (hs (mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr ht)))
    · exact hnon
    · exact le_rfl
  exact mul_le_mul_of_nonneg_left hb (prod_nonneg (fun p hp => (hq p (hA hp)).1))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TiltedAdditionTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Availability of a fixed addition under the tilted remainder law -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem tilted_required_product (Z : Finset ℕ) (hZ : ∀ p ∈ Z, p.Prime) :
    (∏ p ∈ Z, 1/(2*(p : ℝ)-1)) =
      ((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ))*
        ∏ p ∈ Z, (1-(1/2 : ℝ)/p)⁻¹ := by
  have he (p : ℕ) (hp : p ∈ Z) :
      1/(2*(p : ℝ)-1) = ((1/2 : ℝ)/(p : ℝ))*(1-(1/2 : ℝ)/p)⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hZ p hp).ne_zero
    field_simp [hp0]
  rw [prod_congr rfl he,prod_mul_distrib,prod_div_distrib,prod_const,Nat.cast_prod]

/-- The odds correction is uniformly bounded for every allowed numeric
addition; its squarefree product is in the actual coefficient range. -/
theorem tilted_required_product_bound :
    ∀ᶠ B : ℕ in atTop, ∀ Z : Finset ℕ, Z ⊆ auxiliaryPrimes B →
      (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      (∏ p ∈ Z, 1/(2*(p : ℝ)-1)) ≤
        Real.exp 1*((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ)) := by
  filter_upwards [auxiliary_selected_odds_bound] with B hB
  intro Z hZ hsize
  rw [tilted_required_product Z (fun p hp => auxiliaryPrimes_prime B p (hZ hp))]
  have hnon : 0 ≤ (1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ) := by positivity
  exact (mul_le_mul_of_nonneg_left (hB Z hZ hsize) hnon).trans_eq (mul_comm _ _)

/-- Regularity is retained inside the probability. No conditional
probability or reciprocal of a regularity event occurs. -/
theorem tilted_addition_regular_tail {B L k : ℕ} {τ C : ℝ}
    (A Z : Finset ℕ) (hZ : Z ⊆ auxiliaryPrimes B \ A)
    (hk : k ∈ Icc 1 L)
    (hprefix : Z ⊆ primePrefix B ((k : ℝ)/L) Z)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
      if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
      (∏ p ∈ Z, 1/(2*(p : ℝ)-1))*
        Real.exp (t*((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B-Z.card)+
          (Real.exp (-t)-1)*
            ∑ p ∈ ((auxiliaryPrimes B \ A) \ Z) ∩
              primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B), 1/(2*(p : ℝ)-1)) := by
  let P := auxiliaryPrimes B \ A
  let Q := primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B)
  let q := fun p : ℕ => 1/(2*(p : ℝ)-1)
  have hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
    exact ⟨div_nonneg (by norm_num) (by linarith),(div_le_one (by linarith)).mpr (by linarith)⟩
  have hZQ : Z ⊆ Q := hprefix.trans (primePrefix_mono B _ (hZ.trans sdiff_subset))
  refine le_trans ?_ (bernoulliSubsetMass_required_prefix_tail P Z Q q hZ hZQ hq ht
    ((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B))
  apply sum_le_sum
  intro R hR
  have hr := mem_powerset.mp hR
  have hnon := bernoulliSubsetMass_nonneg hr hq
  split_ifs with hgood hcount
  · exact le_rfl
  · exfalso
    apply hcount
    refine ⟨hgood.1,?_⟩
    have he : R ∩ Q = primePrefix B ((k : ℝ)/L) R := by
      dsimp [Q]
      rw [← primePrefix_inter,inter_eq_left.mpr (hr.trans sdiff_subset)]
    rw [he]
    exact (hgood.2.1 k hk).2
  · exact hnon
  · exact le_rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TiltedAdditionRate
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large-addition availability estimate from Mertens -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Both the inclusion cost and the lower-tail cost are present. The first
remainder's regularity is inside the probability, as in (27) of moments.tex. -/
theorem tilted_addition_rate_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {τ δ ε : ℝ} (hτ : 0 ≤ τ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (A Z : Finset ℕ),
      A ⊆ auxiliaryPrimes B → Z ⊆ auxiliaryPrimes B \ A →
      (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      (∏ p ∈ Z, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
      Z ⊆ primePrefix B ((k : ℝ)/L) Z →
      (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
        if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
        Real.exp 1*((1/2 : ℝ)^Z.card/(∏ p ∈ Z, p : ℕ))*
          Real.exp ((-((k : ℝ)/L)*halfPoissonRate
            (1/2-clippedAdditionDensity B ((k : ℝ)/L) Z)+((k : ℝ)/L)*δ+
              (-Real.log (2*δ))*τ+ε)*auxiliaryLogLength B) := by
  have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
  have hkL : k ≤ L := (mem_Icc.mp hk).2
  have hL : 0 < L := by omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hg : 0 < (k : ℝ)/L := div_pos (by exact_mod_cast (by omega : 0 < k)) hLr
  have hg1 : (k : ℝ)/L ≤ 1 := (div_le_one hLr).mpr (by exact_mod_cast hkL)
  filter_upwards [tilted_prefix_mean_uniform hM (by norm_num : (0 : ℝ) < 32/5) hg hg1 hε,
    tilted_required_product_bound, auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hmean hprod hℓ
  intro C A Z hA hZ hAsize hZsize hprefix
  have hZA : Disjoint A Z := disjoint_left.mpr (fun p hpA hpZ => (mem_sdiff.mp (hZ hpZ)).2 hpA)
  have hAZ : A ∪ Z ⊆ auxiliaryPrimes B := union_subset hA (hZ.trans sdiff_subset)
  have hAZsize : (∏ p ∈ A ∪ Z, p : ℕ) ≤ Real.exp ((32/5 : ℝ)*B) := by
    rw [prod_union hZA,Nat.cast_mul]
    calc
      _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) :=
        mul_le_mul hAsize hZsize (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hm := hmean (A ∪ Z) hAZ hAZsize
  have hs : (auxiliaryPrimes B \ A) \ Z = auxiliaryPrimes B \ (A ∪ Z) := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  let g : ℝ := (k : ℝ)/L
  let r := clippedAdditionDensity B g Z
  let m := ∑ p ∈ ((auxiliaryPrimes B \ A) \ Z) ∩ primePrefix B g (auxiliaryPrimes B),
    1/(2*(p : ℝ)-1)
  let t := -Real.log (2*max δ (1/2-r))
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hg.le hℓ.le)) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hω : g*r*auxiliaryLogLength B ≤ Z.card := by
    have hh : r ≤ (Z.card : ℝ)/(g*auxiliaryLogLength B) := min_le_left _ _
    have hh' := (le_div_iff₀ (mul_pos hg hℓ)).mp hh
    nlinarith
  have hm' : (g/2-ε)*auxiliaryLogLength B ≤ m := by
    have he : g/2-ε ≤ m/auxiliaryLogLength B := by
      dsimp only [m,g]
      rw [hs]
      linarith [(abs_le.mp hm).1]
    exact (le_div_iff₀ hℓ).mp he
  have ht : 0 ≤ t := (halfPoisson_clamped_chernoff (u := 1/2-r) (by linarith)
    (by linarith) hδ hδ1).1
  have hrate := multiplicity_chernoff_exponent hg.le hℓ.le hτ hε.le hδ hδ1 hr hr1 hω hm'
  have hprob := tilted_addition_regular_tail (τ := τ) (C := C) A Z hZ hk hprefix ht
  have hprod' := hprod Z (hZ.trans sdiff_subset) hZsize
  refine hprob.trans ?_
  exact mul_le_mul hprod' (Real.exp_le_exp.mpr hrate) (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le (by positivity))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAdditionAvailability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expected large additions with first-remainder regularity retained -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem tiltedRegularSubsetCount_eq_sum (B L : ℕ) (τ C : ℝ)
    (A : Finset ℕ) (F : Finset (Finset ℕ)) :
    tiltedRegularSubsetCount B L τ C A F =
      ∑ Z ∈ F, ∑ R ∈ (auxiliaryPrimes B \ A).powerset,
        if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0 := by
  unfold tiltedRegularSubsetCount
  rw [sum_comm]
  apply sum_congr rfl
  intro R _
  by_cases hR : RegularPrimeSet B L τ C R
  · simp only [hR,ite_true, if_true,and_true,card_eq_sum_ones,Nat.cast_sum,sum_filter]
    rw [mul_sum]
    apply sum_congr rfl
    intro Z _
    by_cases hZ : Z ⊆ R <;> simp [hZ]
  · simp [hR]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAdditionGeometry
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The negative-slope progression for a large low-endpoint addition -/

namespace JointDickman
open Finset Classical

theorem low_addition_equation_modEq {e j b z w c d : ℕ} (hej : e.Coprime j)
    (hz : e*z+j*c = b) (hw : e*w+j*d = b) : Nat.ModEq j z w := by
  have hez : (e*z)%j = b%j := by simpa [Nat.add_mod] using congrArg (fun n => n%j) hz
  have hew : (e*w)%j = b%j := by simpa [Nat.add_mod] using congrArg (fun n => n%j) hw
  exact Nat.ModEq.cancel_left_of_coprime hej.symm (hez.trans hew.symm)

theorem low_addition_equation_progression {e j b w d : ℕ} (hj : 0 < j) (hej : e.Coprime j)
    (hw : e*w+j*d = b) :
    ∃ (z₀ : ℕ) (c₀ : ℤ), z₀ < j ∧
      (e : ℤ)*z₀+(j : ℤ)*c₀ = b ∧
      ∀ (z c : ℕ), e*z+j*c = b →
        z = z₀+j*(z/j) ∧ (c : ℤ) = c₀-(e : ℤ)*((z/j : ℕ) : ℤ) := by
  let z₀ := w%j
  let c₀ : ℤ := (d : ℤ)+(e : ℤ)*((w/j : ℕ) : ℤ)
  have hwdecomp : w = z₀+j*(w/j) := (Nat.mod_add_div w j).symm
  have hwInt : (e : ℤ)*w+(j : ℤ)*d = b := by exact_mod_cast hw
  have hwdecInt : (w : ℤ) = z₀+(j : ℤ)*((w/j : ℕ) : ℤ) := by exact_mod_cast hwdecomp
  have hbase : (e : ℤ)*z₀+(j : ℤ)*c₀ = b := by
    dsimp only [c₀]
    simp only [Int.natCast_ediv] at hwdecInt ⊢
    linear_combination hwInt-(e : ℤ)*hwdecInt
  refine ⟨z₀,c₀,Nat.mod_lt _ hj,hbase,?_⟩
  intro z c hz
  have hmod : z%j = w%j := low_addition_equation_modEq hej hz hw
  have hzdec : z = z₀+j*(z/j) := by
    change z = w%j+j*(z/j)
    rw [← hmod]
    exact (Nat.mod_add_div z j).symm
  refine ⟨hzdec,?_⟩
  have hzInt : (e : ℤ)*z+(j : ℤ)*c = b := by exact_mod_cast hz
  have hzdecInt : (z : ℤ) = z₀+(j : ℤ)*((z/j : ℕ) : ℤ) := by exact_mod_cast hzdec
  apply mul_left_cancel₀ (show (j : ℤ) ≠ 0 by exact_mod_cast hj.ne')
  simp only [Int.natCast_ediv] at hzdecInt ⊢
  linear_combination hzInt-hbase-(e : ℤ)*hzdecInt

theorem low_addition_progression_good_primes {B e j b z₀ : ℕ} {g : ℝ}
    (he : 0 < e) (hb : 0 < b) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B)
    {c : ℤ} (hbase : (e : ℤ)*z₀+(j : ℤ)*c = b) :
    ∀ p ∈ primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b,
      (j : ZMod p) ≠ 0 ∧ (-(e : ℤ) : ZMod p) ≠ 0 ∧
        (z₀ : ZMod p)*(-(e : ℤ) : ZMod p)-(c : ZMod p)*j ≠ 0 := by
  have hbase' : (e : ℤ)*z₀ = b+(j : ℤ)*(-c) := by linarith
  intro p hp
  obtain ⟨hj,he,hd⟩ := addition_progression_good_primes he hb hj hcut hbase' p hp
  refine ⟨hj,?_,?_⟩
  · simpa only [Int.cast_neg,Int.cast_natCast,neg_ne_zero] using he
  · have hid : (z₀ : ZMod p)*(-(e : ℤ) : ZMod p)-(c : ZMod p)*j =
        -((z₀ : ZMod p)*e-((-c : ℤ) : ZMod p)*j) := by
      simp only [Int.cast_neg,Int.cast_natCast]
      ring
    rw [hid]
    exact neg_ne_zero.mpr hd

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_LowAdditionSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic sieve for the decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem lowAdditionProgressionWeight_nonneg {B e j b z₀ n : ℕ} {g q : ℝ} {c₀ : ℤ}
    (hq : 0 ≤ q) : 0 ≤ lowAdditionProgressionWeight B g e j b z₀ c₀ q n := by
  apply div_nonneg _ (by positivity)
  exact prod_nonneg (fun _ _ => mul_nonneg (residueWeight_nonneg _ _ hq)
    (residueWeight_nonneg _ _ (by norm_num)))

theorem low_addition_window_harmonic_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (e j b z₀ : ℕ) (c₀ : ℤ) (q W : ℝ),
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (e : ℤ)*z₀+(j : ℤ)*c₀ = b →
        0 ≤ q → q ≤ 1 → 2*(j : ℝ) ≤ W →
        (∑ n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j),
          lowAdditionProgressionWeight B g e j b z₀ c₀ q n) ≤
          K/(j : ℝ)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
            4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by
  obtain ⟨K,hK,hbound⟩ := numeric_prefix_harmonic_bound hFord hM hκ hg hg1 hε
  refine ⟨10*K,by positivity,?_⟩
  filter_upwards [hbound] with B hB
  intro e j b z₀ c₀ q W he hb hj hcut hsize hbase hq hq1 hW
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hW0 : 0 < W := by linarith
  have hWhalf : 0 < W/2 := half_pos hW0
  have huv := additionInterval_order (j := j) hW0.le
  have hlen := additionInterval_length hj (by linarith : (j : ℝ) ≤ W)
  have hprod : (∏ p ∈ additionExcludedPrimes B e b, p : ℕ) ≤ Real.exp (κ*B) :=
    (by exact_mod_cast additionExcludedPrimes_product_le (B := B) he hb :
      ((∏ p ∈ additionExcludedPrimes B e b, p : ℕ) : ℝ) ≤ (e*b : ℕ)).trans hsize
  have hh := hB (additionExcludedPrimes B e b) z₀ j c₀ (-e) q (W/2)
    (additionIntervalLower W j) (additionIntervalUpper W j)
    (additionExcludedPrimes_subset B e b) hprod hq hq1 hWhalf huv
    (fun p hp => by simpa only [Int.cast_neg,Int.cast_natCast] using
      low_addition_progression_good_primes (g := g) he hb hj hcut hbase p hp)
    (fun n hn => by simpa only [Int.cast_natCast] using additionInterval_denominator hj hW hn)
  have hcoef : K*((additionIntervalUpper W j : ℝ)-additionIntervalLower W j)/(W/2) ≤
      (10*K)/(j : ℝ) := by
    calc
      _ ≤ K*(5*W/j)/(W/2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlen hK.le) hWhalf.le
      _ = _ := by field_simp <;> ring
  have herr : 2*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/(W/2) =
      4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W := by ring
  rw [herr] at hh
  have hfinal := hh.trans (add_le_add (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le) le_rfl)
  simpa only [lowAdditionProgressionWeight,Int.cast_natCast,Int.cast_neg,neg_mul,sub_eq_add_neg] using hfinal

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowNumericAdditionClass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Squarefree low-endpoint additions on a decreasing quotient progression -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem mem_lowNumericAdditionClass {B L e j b d : ℕ} {τ C W : ℝ} {Z : Finset ℕ} :
    Z ∈ lowNumericAdditionClass B L τ C e j b d W ↔
      Z ⊆ auxiliaryPrimes B ∧ Z.card = d ∧
        W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
        ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p)+j*c = b ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
  simp only [lowNumericAdditionClass,mem_filter,mem_powerset]

/-- The progression parametrization is injective on the squarefree prime
products in a class.  The remaining quotient's regularity supplies exactly
one half-weight factor, before the numeric interval is enlarged. -/
theorem low_numeric_addition_class_progression_bound {B L k e j b d z₀ : ℕ}
    {τ C W g q : ℝ} {c₀ : ℤ}
    (hB : 1 ≤ B) (hk : k ∈ Icc 1 L) (hg : g ≤ (k : ℝ)/L)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hprogress : ∀ z c : ℕ, e*z+j*c = b →
      z = z₀+j*(z/j) ∧ (c : ℤ) = c₀-(e : ℤ)*((z/j : ℕ) : ℤ)) :
    (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
      (((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2))*
        ∑ n ∈ Ico (additionIntervalLower W j) (additionIntervalUpper W j),
          lowAdditionProgressionWeight B g e j b z₀ c₀ q n := by
  let A := lowNumericAdditionClass B L τ C e j b d W
  let f : Finset ℕ → ℕ := fun Z => (∏ p ∈ Z, p)/j
  let F := lowAdditionProgressionWeight B g e j b z₀ c₀ q
  let a := ((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2)
  have ha : 0 ≤ a := by dsimp [a] <;> positivity
  have hf (Z : Finset ℕ) (hZ : Z ∈ A) : f Z ∈
      Ico (additionIntervalLower W j) (additionIntervalUpper W j) := by
    obtain ⟨_,_,hlo,hhi,_⟩ := mem_lowNumericAdditionClass.mp hZ
    exact additionInterval_contains hlo hhi
  have hinj : Set.InjOn f (↑A : Set (Finset ℕ)) := by
    intro Z hZ V hV heq
    obtain ⟨hZ,_,_,_,c,_,hc,_⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨hV,_,_,_,a',_,ha',_⟩ := mem_lowNumericAdditionClass.mp hV
    have hz := (hprogress _ _ hc).1
    have hv := (hprogress _ _ ha').1
    apply primeProduct_injective (auxiliaryPrimes_prime B) hZ hV
    calc
      _ = z₀+j*f Z := hz
      _ = z₀+j*f V := by rw [heq]
      _ = _ := hv.symm
  have hpoint (Z : Finset ℕ) (hZ : Z ∈ A) :
      (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ) ≤ a*F (f Z) := by
    obtain ⟨hZ,hd,_,_,c,hc0,hc,hreg⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨hz,hcq⟩ := hprogress _ _ hc
    let P := primePrefix B g (auxiliaryPrimes B) \ additionExcludedPrimes B e b
    have hP : P ⊆ primePrefix B ((k : ℝ)/L) (auxiliaryPrimes B) :=
      sdiff_subset.trans (primePrefix_exponent_mono hB hg _)
    have hmajor := regular_numeric_addition_majorant Z P hc0.ne' hk hreg hP
      (fun p hp => auxiliaryPrimes_prime B p (hZ hp)) hq.le hq1
    rw [hd] at hmajor
    have hprod (p : ℕ) : ((∏ r ∈ Z, r : ℕ) : ZMod p) =
        (z₀ : ZMod p)+j*(f Z : ℕ) := by
      have ht := congrArg (fun n : ℕ => (n : ZMod p)) hz
      simpa only [Nat.cast_add,Nat.cast_mul] using ht
    have hquot (p : ℕ) : (c : ZMod p) = (c₀ : ZMod p)-e*(f Z : ℕ) := by
      have ht := congrArg (fun x : ℤ => (x : ZMod p)) hcq
      simpa only [Int.cast_sub,Int.cast_mul,Int.cast_natCast] using ht
    have hden : ((∏ p ∈ Z, p : ℕ) : ℝ) = (z₀ : ℝ)+(j : ℝ)*(f Z : ℕ) := by
      exact_mod_cast hz
    have heq : (1/2 : ℝ)^d = ((1/2 : ℝ)/q)^d*q^d := by
      rw [← mul_pow,div_mul_cancel₀ _ hq.ne']
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hmajor (show 0 ≤ ((1/2 : ℝ)/q)^d by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul (show 0 ≤ ((∏ p ∈ Z, p : ℕ) : ℝ) by positivity)
    refine hdiv.trans_eq ?_
    dsimp only [a,F,lowAdditionProgressionWeight]
    simp_rw [hprod,hquot]
    rw [hden]
    dsimp only [P]
    ring
  calc
    _ ≤ ∑ Z ∈ A, a*F (f Z) := sum_le_sum hpoint
    _ = a*∑ Z ∈ A, F (f Z) := (mul_sum _ _ _).symm
    _ = a*∑ n ∈ A.image f, F n := by rw [sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_le_sum_of_subset_of_nonneg (by
        intro n hn
        obtain ⟨Z,hZ,rfl⟩ := mem_image.mp hn
        exact hf Z hZ) (fun _ _ _ => lowAdditionProgressionWeight_nonneg hq.le)) ha

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowNumericAdditionBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform harmonic bound for a low-endpoint numeric-addition class -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- This is the numeric sum before choosing the Rankin parameter.  All
progression and squarefree-product hypotheses have been discharged for the
actual class.  Its only analytic inputs are the cited upper sieve and Mertens. -/
theorem low_numeric_addition_class_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {κ g ε : ℝ} (hκ : 0 < κ) (hg : 0 < g) (hg1 : g < 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (L k : ℕ) (τ C : ℝ) (e j b d : ℕ) (q W : ℝ),
        k ∈ Icc 1 L → g ≤ (k : ℝ)/L →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → 0 < q → q ≤ 1 → 2*(j : ℝ) ≤ W →
        (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
          (((1/2 : ℝ)/q)^d*Real.exp (((((k : ℝ)/L)/2+τ)*auxiliaryLogLength B)*Real.log 2))*
            (K/(j : ℝ)*Real.exp ((-(3/2-q)*g+ε)*auxiliaryLogLength B)+
              4*(numericAdditionSieveCutoff B g+1 : ℝ)*(numericAdditionSieveCutoff B g : ℝ)^2/W) := by
  obtain ⟨K,hK,hbound⟩ := low_addition_window_harmonic_bound hFord hM hκ hg hg1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with B hB hB1
  intro L k τ C e j b d q W hk hgk he hb hj hcut hej hsize hq hq1 hW
  by_cases hne : (lowNumericAdditionClass B L τ C e j b d W).Nonempty
  · obtain ⟨Z,hZ⟩ := hne
    obtain ⟨_,_,_,_,c,_,hc,_⟩ := mem_lowNumericAdditionClass.mp hZ
    obtain ⟨z₀,c₀,_,hbase,hprogress⟩ := low_addition_equation_progression hj hej hc
    have hsum := low_numeric_addition_class_progression_bound hB1 hk hgk hq hq1 hprogress
      (τ := τ) (C := C) (d := d) (W := W)
    refine hsum.trans (mul_le_mul_of_nonneg_left
      (hB e j b z₀ c₀ q W he hb hj hcut hsize hbase hq.le hq1 hW) ?_)
    positivity
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne,sum_empty]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hW0 : 0 < W := by linarith
    positivity

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowNumericAddition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The large low-endpoint numeric-addition harmonic estimate -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- Equation (28) of the manuscript, for a positive lag and the designated
large addition at its low endpoint.  The explicit sieve remainder has been
absorbed uniformly in the cardinality class. -/
theorem large_low_numeric_addition_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g κ Δ δ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hκ : 0 < κ) (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (τ C : ℝ) (e j b d : ℕ) (W : ℝ), 0 ≤ τ → τ ≤ 1 →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        2*(j : ℝ) ≤ W → Real.exp ((B : ℝ)^(g-Δ))/4 ≤ W →
        (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
          K/(j : ℝ)*Real.exp
            (largeAdditionExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  have hγ : 0 < g-2*Δ := by linarith
  have hγ1 : g-2*Δ < 1 := by linarith
  have ha : 0 < g-Δ := by linarith
  have hγa : g-2*Δ < g-Δ := by linarith
  obtain ⟨K,hK,hbound⟩ := low_numeric_addition_class_bound hFord hM hκ hγ hγ1 hε
  refine ⟨K+1,by positivity,?_⟩
  filter_upwards [hbound,numeric_sieve_remainder_small ha hγa 10,
    auxiliaryLogLength_tendsto.eventually_gt_atTop 0,
    auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB herr hℓ hℓB hB1
  intro τ C e j b d W hτ hτ1 he hb hj hcut hej hsize hjB hW hWlarge
  let ℓ := auxiliaryLogLength B
  let x := (d : ℝ)/(g*ℓ)
  let r := min x (1/2)
  let q := max δ r
  let A := largeAdditionExponent g Δ δ τ ε ℓ d
  let P := ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2)
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have hBr : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le
  have hr : 0 ≤ r := le_min hx (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hq : 0 < q := hδ.trans_le (le_max_left _ _)
  have hq1 : q ≤ 1/2 := max_le hδ1 hr1
  have hP : 0 ≤ P := by dsimp [P] <;> positivity
  have hPsmall : P ≤ Real.exp (3*ℓ) := numeric_rankin_prefactor_bound hg hg1 hℓ hτ1 hδ hδ1
  have hclass := hB L k τ C e j b d q W hk (by rw [hkg]; linarith)
    he hb hj hcut hej hsize hq (by linarith) hW
  rw [hkg] at hclass
  change (∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
    (1/2 : ℝ)^d/((∏ p ∈ Z, p : ℕ) : ℝ)) ≤
      P*(K/(j : ℝ)*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ)+_) at hclass
  have hmain : P*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ) ≤ Real.exp (A*ℓ) := by
    have hpow : ((1/2 : ℝ)/q)^d = Real.exp ((d : ℝ)*Real.log ((1/2 : ℝ)/q)) := by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
    have hxid : g*ℓ*x = (d : ℝ) := by dsimp only [x]; field_simp [hg.ne',show ℓ ≠ 0 from hℓ.ne']
    have hexp := numeric_rankin_exponent_bound (τ := τ) hg.le (by linarith : g-2*Δ ≤ g) hx hδ hδ1
    change -(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2 ≤ _ at hexp
    have hgδ := mul_le_mul_of_nonneg_right hg1 hδ.le
    have hcoef : -(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2+ε ≤ A := by
      dsimp only [A,largeAdditionExponent,r] at *
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hℓ.le
    dsimp only [P]
    rw [hpow,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hexact : (d : ℝ)*Real.log ((1/2)/q)+((g/2+τ)*ℓ)*Real.log 2+
        (-(3/2-q)*(g-2*Δ)+ε)*ℓ =
        (-(3/2-q)*(g-2*Δ)+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2+ε)*ℓ := by
      calc
        _ = (g*ℓ*x)*Real.log ((1/2)/q)+((g/2+τ)*ℓ)*Real.log 2+
          (-(3/2-q)*(g-2*Δ)+ε)*ℓ := by rw [hxid]
        _ = _ := by ring
    rwa [hexact]
  have hA : -2 ≤ A := by
    have hF := halfRankinExponent_nonneg hr hr1
    have hbase : weightBaseExponent ≤ 1/2 := by
      unfold weightBaseExponent
      have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    have hlog : 0 ≤ τ*Real.log 2 := mul_nonneg hτ (Real.log_nonneg (by norm_num))
    have hh : -2 ≤ g*(halfRankinExponent r-1-weightBaseExponent) := by
      have hp := mul_nonneg hg.le hF
      have hb' : g*weightBaseExponent ≤ g*(1/2) := mul_le_mul_of_nonneg_left hbase hg.le
      nlinarith
    dsimp only [A,largeAdditionExponent]
    change -2 ≤ g*(halfRankinExponent r-1-weightBaseExponent)+3*Δ+δ+τ*Real.log 2+ε
    linarith
  have hW0 : 0 < W := by linarith
  have herr' := herr j W hj hjB hWlarge
  have herrfinal : P*(4*(numericAdditionSieveCutoff B (g-2*Δ)+1 : ℝ)*
      (numericAdditionSieveCutoff B (g-2*Δ) : ℝ)^2/W) ≤ Real.exp (A*ℓ)/(j : ℝ) := by
    calc
      _ ≤ Real.exp (3*ℓ)*((B : ℝ)^(-(10 : ℝ))/(j : ℝ)) :=
        mul_le_mul hPsmall herr' (by positivity) (Real.exp_pos _).le
      _ = Real.exp (3*ℓ-10*Real.log B)/(j : ℝ) := by
        rw [Real.rpow_def_of_pos hBr,← mul_div_assoc,← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hjr.le
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hA hℓ.le
        have hupper : ℓ ≤ Real.log B := hℓB.2
        linarith
  refine hclass.trans ?_
  rw [mul_add]
  calc
    _ = K/(j : ℝ)*(P*Real.exp ((-(3/2-q)*(g-2*Δ)+ε)*ℓ))+
        P*(4*(numericAdditionSieveCutoff B (g-2*Δ)+1 : ℝ)*
          (numericAdditionSieveCutoff B (g-2*Δ) : ℝ)^2/W) := by ring
    _ ≤ K/(j : ℝ)*Real.exp (A*ℓ)+Real.exp (A*ℓ)/(j : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) herrfinal
    _ = _ := by dsimp only [A,ℓ] <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowAdditionAvailability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-remainder availability for the large low-endpoint addition -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The Poisson penalty in the first remainder and the numeric Rankin
exponent cancel to half the binary entropy, as in equations (27)--(29).
The expectation keeps the first remainder's full regularity condition. -/
theorem large_low_addition_availability_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g κ Δ δ τ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hκ : 0 < κ) (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ) (W : ℝ),
        A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e*b : ℕ) ≤ Real.exp (κ*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        2*(j : ℝ) ≤ W → Real.exp ((B : ℝ)^(g-Δ))/4 ≤ W →
        tiltedRegularSubsetCount B L τ C A
          (availableLowNumericAdditionClass B L k τ C A e j b d W) ≤
          K/(j : ℝ)*Real.exp
            (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  obtain ⟨K,hK,hnumeric⟩ := large_low_numeric_addition_bound hFord hM hk hkg hg hg1 hκ hΔ hgap hδ hδ1 hε
  refine ⟨Real.exp 1*K,by positivity,?_⟩
  filter_upwards [hnumeric,tilted_addition_rate_bound hM hk hτ hδ hδ1 hε] with B hn hp
  intro C A e j b d W hA hAsize he hb hj hcut hej hsize hjB hW hWlarge
  let ℓ := auxiliaryLogLength B
  let r := min ((d : ℝ)/(g*ℓ)) (1/2)
  let E := -g*halfPoissonRate (1/2-r)+g*δ+(-Real.log (2*δ))*τ+ε
  let F := availableLowNumericAdditionClass B L k τ C A e j b d W
  have hpoint (Z : Finset ℕ) (hZ : Z ∈ F) :
      (∑ R ∈ (auxiliaryPrimes B \ A).powerset,
        if Z ⊆ R ∧ RegularPrimeSet B L τ C R then
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) R else 0) ≤
        (Real.exp 1*Real.exp (E*ℓ))*((1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ)) := by
    obtain ⟨hZ,hsub,hprod,hpre⟩ := mem_filter.mp hZ
    have hd := (mem_lowNumericAdditionClass.mp hZ).2.1
    have hh := hp C A Z hA hsub hAsize hprod hpre
    rw [hkg] at hh
    simp only [clippedAdditionDensity,hd] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp only [E,r,ℓ] <;> ring)
  have hsub : F ⊆ lowNumericAdditionClass B L τ C e j b d W := filter_subset _ _
  have hsum : tiltedRegularSubsetCount B L τ C A F ≤
      (Real.exp 1*Real.exp (E*ℓ))*
        ∑ Z ∈ lowNumericAdditionClass B L τ C e j b d W,
          (1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ) := by
    rw [tiltedRegularSubsetCount_eq_sum]
    calc
      _ ≤ ∑ Z ∈ F, (Real.exp 1*Real.exp (E*ℓ))*((1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ)) :=
        sum_le_sum hpoint
      _ = (Real.exp 1*Real.exp (E*ℓ))*∑ Z ∈ F, (1/2 : ℝ)^d/(∏ p ∈ Z, p : ℕ) :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) (by positivity)
  have hnum := hn τ C e j b d W hτ hτ1 he hb hj hcut hej hsize hjB hW hWlarge
  refine hsum.trans ((mul_le_mul_of_nonneg_left hnum (by positivity)).trans_eq ?_)
  have heq : E+largeAdditionExponent g Δ δ τ ε ℓ d =
      largeAvailabilityExponent g Δ δ τ ε ℓ d := by
    have hh := halfRankin_sub_halfPoisson r
    dsimp only [E,largeAdditionExponent,largeAvailabilityExponent,r] at *
    nlinarith
  calc
    _ = (Real.exp 1*K)/(j : ℝ)*
        Real.exp ((E+largeAdditionExponent g Δ δ τ ε ℓ d)*ℓ) := by
      have hexp : Real.exp ((E+largeAdditionExponent g Δ δ τ ε ℓ d)*ℓ) =
          Real.exp (E*ℓ)*Real.exp (largeAdditionExponent g Δ δ τ ε ℓ d*ℓ) := by
        rw [add_mul,Real.exp_add]
      rw [hexp]
      ring
    _ = _ := by rw [heq]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_LargeAdditionWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A large-addition window contains many lag periods -/

namespace JointDickman
open Filter
open scoped Topology

theorem large_addition_window_lag {a : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (W : ℝ), (j : ℝ) ≤ (B : ℝ)^2 →
      Real.exp ((B : ℝ)^a)/4 ≤ W → 2*(j : ℝ) ≤ W := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/a) 1 (by norm_num : (0 : ℝ) < 1)).comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have ht' : Tendsto (fun B : ℕ => 8*(B : ℝ)^2*Real.exp (-((B : ℝ)^a))) atTop (𝓝 0) := by
    have hh := ht.const_mul 8
    norm_num only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    dsimp
    rw [← Real.rpow_mul hB0.le,show a*(2/a) = 2 by field_simp]
    simp only [Real.rpow_two,neg_one_mul]
    ring
  filter_upwards [ht'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hsmall
  intro j W hj hW
  have hh : 8*(B : ℝ)^2 ≤ Real.exp ((B : ℝ)^a) := by
    rw [Real.exp_neg,← div_eq_mul_inv] at hsmall
    exact (div_le_one (Real.exp_pos _)).mp hsmall
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowClass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Active low-addition classes at the actual coefficient ratio -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem active_low_addition_class_bound_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ τ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (C : ℝ) (A : Finset ℕ) (e j b d : ℕ),
        A ⊆ auxiliaryPrimes B → (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < e → 0 < b → 0 < j → j ≤ auxiliaryCutoff B → e.Coprime j →
        (e : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) → (j : ℝ) ≤ (B : ℝ)^2 →
        tiltedRegularSubsetCount B L τ C A (activeLowAdditionClass B L k τ C Δ A e j b d) ≤
          K/(j : ℝ)*Real.exp
            (largeAvailabilityExponent g Δ δ τ ε (auxiliaryLogLength B) d*auxiliaryLogLength B) := by
  obtain ⟨K,hK,hbound⟩ := large_low_addition_availability_bound hFord hM hk hkg hg hg1
    (by norm_num : (0 : ℝ) < 32/5) hΔ hgap hδ hδ1 hτ hτ1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,large_addition_window_lag (by linarith : 0 < g-Δ)] with B hB hwindow
  intro C A e j b d hA hAsize he hb hj hcut hej hesize hjB
  unfold activeLowAdditionClass
  split_ifs with hactive
  · have hbsize := hactive.1
    have hW := hactive.2
    rw [hkg] at hW
    have hsize : (e*b : ℕ) ≤ Real.exp ((32/5 : ℝ)*B) := by
      push_cast
      calc
        _ ≤ Real.exp ((16/5 : ℝ)*B)*Real.exp ((16/5 : ℝ)*B) :=
          mul_le_mul hesize hbsize (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact hB C A e j b d (highAdditionWindow e b) hA hAsize he hb hj hcut hej hsize hjB
      (hwindow j _ hjB hW) hW
  · simp only [tiltedRegularSubsetCount,filter_empty,card_empty,Nat.cast_zero,ite_self,mul_zero,sum_const_zero]
    exact mul_nonneg (div_nonneg hK.le (Nat.cast_nonneg _)) (Real.exp_pos _).le

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.active_low_addition_class_bound_jd_oai := @OAI.JointDickman.active_low_addition_class_bound_jd_oai
