-- Prove2me | solution 1 for OAI.JointDickman.weighted_candidate_coefficient_removal_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:21:11.170379+00:00
-- url     : https://prove2.me/submissions/13ccd868-da8d-4429-9635-29600484b4b1

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_UnionSelection
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent selection of finite forbidden sets -/

namespace JointDickman

open Finset

/-- Independent form choices work equally for finite sets of zeros, such
as lines in a residue plane. Intersections between the sets cause no loss. -/
theorem bernoulli_union_survival {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) (x : α) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (if x ∈ S.biUnion F then 0 else 1)) =
      ∏ i ∈ I.filter (fun i => x ∈ F i), θ i := by
  classical
  let E := I.filter (fun i => x ∈ F i)
  have hid (S : Finset ι) (hS : S ⊆ I) :
      avoidsSelected S E = if x ∈ S.biUnion F then 0 else 1 := by
    have hiff : Disjoint S E ↔ x ∉ S.biUnion F := by
      constructor
      · intro h hx
        obtain ⟨i, hiS, hi⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp h hiS (mem_filter.mpr ⟨hS hiS, hi⟩)
      · intro h
        apply disjoint_left.mpr
        intro i hiS hiE
        exact h (mem_biUnion.mpr ⟨i, hiS, (mem_filter.mp hiE).2⟩)
    unfold avoidsSelected
    by_cases hx : x ∈ S.biUnion F
    · have hn : ¬ Disjoint S E := fun h => (hiff.mp h) hx
      simp [hn, hx]
    · simp [hiff.mpr hx, hx]
  have h := bernoulliSubsetMass_avoids I E (filter_subset _ _) θ
  apply Eq.trans _ h
  apply sum_congr rfl
  intro S hS
  rw [hid S (mem_powerset.mp hS)]

/-- The mean density of the surviving residue set is the exact residue
average of all retained form weights. -/
theorem bernoulli_union_density {ι α : Type*} [DecidableEq ι]
    [Fintype α] [DecidableEq α] (hα : 0 < Fintype.card α)
    (I : Finset ι) (F : ι → Finset α) (θ : ι → ℝ) :
    (∑ S ∈ I.powerset, bernoulliSubsetMass I (fun i => 1 - θ i) S *
      (1 - ((S.biUnion F).card : ℝ) / Fintype.card α)) =
      (∑ x : α, ∏ i ∈ I.filter (fun i => x ∈ F i), θ i) / Fintype.card α := by
  simp_rw [← root_survival_mean hα, ← mul_div_assoc]
  rw [← sum_div]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  exact bernoulli_union_survival I F θ x

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RandomRootSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PeriodicRectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse errors for a periodic nonnegative weight in a rectangle -/

namespace JointDickman

open Finset

/-- The rectangle error retains the mass in a single residue square,
which is essential when only a few residue lines are allowed. -/
theorem nonnegative_periodic_rectangle_error {q : ℕ} (hq : 0 < q)
    (F : ZMod q → ZMod q → ℝ) (hF : ∀ r s, 0 ≤ F r s)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        (((b : ℝ) - a) * ((d : ℝ) - c) / (q : ℝ) ^ 2) *
          ∑ r ∈ range q, ∑ s ∈ range q, F r s| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / q + 2) *
        ∑ r ∈ range q, ∑ s ∈ range q, F r s := by
  let G := fun r : ZMod q => ∑ s ∈ range q, F r s
  let M := ∑ r ∈ range q, G r
  let L₁ : ℝ := (b : ℝ) - a
  let L₂ : ℝ := (d : ℝ) - c
  have hL₁ : 0 ≤ L₁ := sub_nonneg.mpr (by exact_mod_cast hab)
  have hL₂ : 0 ≤ L₂ := sub_nonneg.mpr (by exact_mod_cast hcd)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hG (r : ZMod q) : 0 ≤ G r := sum_nonneg (fun s _ => hF r s)
  have hmass : 0 ≤ M := sum_nonneg (fun r _ => hG r)
  have hrow (m : ℕ) := nonnegative_periodic_interval_error hq (F m) (hF m) hcd
  have houter := nonnegative_periodic_interval_error hq G hG hab
  change |(∑ m ∈ Ico a b, G m) - L₁ / q * M| ≤ 2 * M at houter
  have hsumG : (∑ m ∈ Ico a b, G m) ≤ (L₁ / q + 2) * M := by
    linarith [(abs_le.mp houter).2]
  have hsumrow : |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
      L₂ / q * ∑ m ∈ Ico a b, G m| ≤ 2 * ∑ m ∈ Ico a b, G m := by
    rw [mul_sum, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ m ∈ Ico a b, 2 * G m := by
        apply sum_le_sum
        intro m _
        exact hrow m
      _ = _ := (mul_sum _ _ _).symm
  have hscaled : |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| ≤
      L₂ / q * (2 * M) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hL₂ hq0.le)]
    exact mul_le_mul_of_nonneg_left houter (div_nonneg hL₂ hq0.le)
  change |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
    (L₁ * L₂ / (q : ℝ) ^ 2) * M| ≤ 2 * ((L₁ + L₂) / q + 2) * M
  calc
    _ = |((∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m) +
        L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(∑ m ∈ Ico a b, ∑ n ∈ Ico c d, F m n) -
        L₂ / q * ∑ m ∈ Ico a b, G m| +
        |L₂ / q * ((∑ m ∈ Ico a b, G m) - L₁ / q * M)| := abs_add_le _ _
    _ ≤ 2 * (∑ m ∈ Ico a b, G m) + L₂ / q * (2 * M) :=
      add_le_add hsumrow hscaled
    _ ≤ 2 * ((L₁ / q + 2) * M) + L₂ / q * (2 * M) := by linarith
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRectangleCRT
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chinese remainder counts in two variables -/

namespace JointDickman

open Finset

/-- Complete residue squares factor by two applications of the CRT. -/
theorem crt_rectangle_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (F : ∀ i, ZMod (m i) → ZMod (m i) → ℝ) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      ∏ i, F i (r : ZMod (m i)) (s : ZMod (m i))) =
      ∏ i, ∑ r : ZMod (m i), ∑ s : ZMod (m i), F i r s := by
  calc
    _ = ∑ r ∈ range (∏ i, m i), ∏ i, ∑ s : ZMod (m i), F i (r : ZMod (m i)) s := by
      apply sum_congr rfl
      intro r _
      exact crt_period_sum m hm hcop (fun i s => F i (r : ZMod (m i)) s)
    _ = _ := crt_period_sum m hm hcop (fun i r => ∑ s : ZMod (m i), F i r s)

/-- A family of prescribed residue-pair sets has exactly the product of
its local cardinalities in a complete square. -/
theorem crt_pair_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i))) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hind (r s : ℕ) :
      (∏ i, if ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  rw [crt_rectangle_period_sum m hm hcop (fun i r s => if (r, s) ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  rw [← Fintype.sum_prod_type (fun rs : ZMod (m i) × ZMod (m i) =>
    if rs ∈ A i then (1 : ℝ) else 0)]
  simp

/-- The two-dimensional CRT remainder retains the exact number of
prescribed residue pairs. -/
theorem crt_pair_rectangle_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i)))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) -
      (((b : ℝ) - a) * ((d : ℝ) - c) / (∏ i, (m i : ℝ)) ^ 2) *
        ∏ i, ((A i).card : ℝ)| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ i, (m i : ℝ)) + 2) *
        ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun r s : ZMod (∏ i, m i) => if ∀ i, (e r i, e s i) ∈ A i then (1 : ℝ) else 0
  have hF (r s : ℕ) : F r s =
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    have hr : e (r : ZMod (∏ i, m i)) = (r : ∀ i, ZMod (m i)) := map_natCast e r
    have hs : e (s : ZMod (∏ i, m i)) = (s : ∀ i, ZMod (m i)) := map_natCast e s
    simp [F, hr, hs]
  have hmass : (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i), F r s) =
      ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_pair_period_count m hm hcop A
  have h := nonnegative_periodic_rectangle_error hM F
    (fun r s => by dsimp [F]; split_ifs <;> norm_num) hab hcd
  rw [hmass] at h
  simpa only [hF, Nat.cast_prod] using h

/-- Prime-set specialization with the local densities already factored. -/
theorem prime_pair_rectangle_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ P, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ((d : ℝ) - c) *
        ∏ p ∈ P, ((A p).card : ℝ) / (p : ℝ) ^ 2| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ P, (p : ℝ)) + 2) *
        ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_pair_rectangle_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab hcd
  simp only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)),
    P.prod_coe_sort (fun p : ℕ => (p : ℝ)), Subtype.forall] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  rw [prod_div_distrib, ← prod_pow]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRectangle
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle sieve with an explicit arithmetic remainder -/

namespace JointDickman

open Finset

/-- Actual intersections in a rectangle have the CRT error. -/
theorem pair_root_sieve_remainder (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
          ∏ p ∈ D, ((A p).card : ℝ) := by
  classical
  have hcond (r s : ℕ) : D ⊆ pairRootEvents P A r s ↔
      ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p := by
    constructor
    · intro h p hp
      exact (mem_filter.mp (h hp)).2
    · intro h p hp
      exact mem_filter.mpr ⟨hD hp, h p hp⟩
  unfold sieveRemainder sieveIntersection
  simp_rw [hcond]
  rw [Fintype.sum_prod_type]
  have hout : (∑ r : Ico a b, ∑ s : Ico c d,
      if ∀ p ∈ D, ((r.val : ZMod p), (s.val : ZMod p)) ∈ A p then (1 : ℝ) else 0) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0 := by
    apply Eq.trans _ ((Ico a b).sum_coe_sort (fun r : ℕ =>
      ∑ s ∈ Ico c d, if ∀ p ∈ D, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0))
    apply sum_congr rfl
    intro r _
    exact (Ico c d).sum_coe_sort (fun s : ℕ =>
      if ∀ p ∈ D, ((r.val : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0)
  rw [hout]
  exact prime_pair_rectangle_error D (fun p hp => hP p (hD hp)) A hab hcd

/-- With at most `k*p` local residue pairs, the denominator in the CRT
error cancels. This includes unions of at most `k` affine lines. -/
theorem pair_root_sieve_remainder_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (k : ℕ)
    (hA : ∀ p ∈ P, (A p).card ≤ k * p)
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    {D : Finset ℕ} (hD : D ⊆ P) :
    |sieveRemainder
      (fun n : (Ico a b) × (Ico c d) => pairRootEvents P A n.1 n.2)
      (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c))
      (fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2) D| ≤
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * ∏ p ∈ D, (p : ℝ)) *
          (k : ℝ) ^ D.card := by
  have hprod : 0 < ∏ p ∈ D, (p : ℝ) := prod_pos (fun p hp => by
    exact_mod_cast (hP p (hD hp)).pos)
  have hL : 0 ≤ ((b : ℝ) - a) + ((d : ℝ) - c) := add_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hab)) (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hcount : (∏ p ∈ D, ((A p).card : ℝ)) ≤
      (k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ) := by
    calc
      _ ≤ ∏ p ∈ D, (k : ℝ) * p := Finset.prod_le_prod (by intros; positivity)
        (fun p hp => by exact_mod_cast hA p (hD hp))
      _ = _ := by rw [prod_mul_distrib]; simp
  apply (pair_root_sieve_remainder P hP A hab hcd hD).trans
  calc
    _ ≤ 2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ D, (p : ℝ)) + 2) *
        ((k : ℝ) ^ D.card * ∏ p ∈ D, (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by field_simp

private theorem sum_rectangle_subtype (a b c d : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ x : (Ico a b) × (Ico c d), F x.1 x.2) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, F r s := by
  rw [Fintype.sum_prod_type]
  have hin (r : Ico a b) : (∑ s : Ico c d, F r s) = ∑ s ∈ Ico c d, F r s :=
    (Ico c d).sum_coe_sort (fun s => F r s)
  simp_rw [hin]
  exact (Ico a b).sum_coe_sort (fun r => ∑ s ∈ Ico c d, F r s)

/-- The weighted rectangle sieve, with all intersection errors evaluated.
The only analytic assumptions are the cited Ford and Mertens inputs. -/
theorem weighted_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (A : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (θ : ℕ → ℝ)
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p ∈ P, (A p).card ≤ k * p) →
      (∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p ∈ P, (1 - ((A p).card : ℝ) / (p : ℝ) ^ 2 +
            ((A p).card : ℝ) / (p : ℝ) ^ 2 * θ p)) +
        2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_upper_sieve_from_published hFord hM
    (show (0 : ℝ) < k by exact_mod_cast hk)
  refine ⟨C, hC, ?_⟩
  intro P A θ a b c d Z hab hcd hZ hP hA hθ
  let E := fun x : (Ico a b) × (Ico c d) => pairRootEvents P A x.1 x.2
  let g := fun p => ((A p).card : ℝ) / (p : ℝ) ^ 2
  let L := ((b : ℝ) - a) + ((d : ℝ) - c)
  have hL : 0 ≤ L := add_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
    (sub_nonneg.mpr (by exact_mod_cast hcd))
  have hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 / 2 ∧ g p ≤ (k : ℝ) / p := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    have hcard : ((A p).card : ℝ) ≤ (k : ℝ) * p := by exact_mod_cast hA p hp
    have hkp : 2 * (k : ℝ) ≤ p := by exact_mod_cast (hP p hp).2.2
    have hsmall : g p ≤ (k : ℝ) / p := by
      calc
        _ ≤ ((k : ℝ) * p) / (p : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hcard (sq_nonneg _)
        _ = _ := by field_simp
    refine ⟨by dsimp [g] <;> positivity, ?_, hsmall⟩
    exact hsmall.trans ((div_le_iff₀ hp0).mpr (by linarith))
  have h := hbound ((Ico a b) × (Ico c d)) P E (fun _ => 1)
    (((b : ℝ) - a) * ((d : ℝ) - c)) Z g θ (by exact_mod_cast hZ)
    (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hab))
      (sub_nonneg.mpr (by exact_mod_cast hcd))) (by intros; norm_num)
    (fun p hp => ⟨(hP p hp).1, by exact_mod_cast (hP p hp).2.1⟩)
    (fun x => filter_subset _ _) hg hθ
  simp only [one_mul] at h
  have hleft : (∑ x : (Ico a b) × (Ico c d), ∏ p ∈ E x, θ p) =
      ∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p ∈ pairRootEvents P A r s, θ p :=
    sum_rectangle_subtype a b c d (fun r s => ∏ p ∈ pairRootEvents P A r s, θ p)
  rw [hleft] at h
  have heq : P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ (Z : ℝ)) =
      P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z) := by
    ext D
    simp only [mem_filter, Nat.cast_le]
  rw [heq] at h
  have hrem : (∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
      |sieveRemainder E (fun _ => 1) (((b : ℝ) - a) * ((d : ℝ) - c)) g D|) ≤
      2 * (L + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
    calc
      _ ≤ ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          2 * (L + 2 * Z) * (k : ℝ) ^ D.card := by
        apply sum_le_sum
        intro D hD
        have hDP := mem_powerset.mp (mem_filter.mp hD).1
        have hdZ : (∏ p ∈ D, (p : ℝ)) ≤ Z := by
          rw [← Nat.cast_prod]
          exact_mod_cast (mem_filter.mp hD).2
        apply (pair_root_sieve_remainder_le P (fun p hp => (hP p hp).1) A k hA hab hcd hDP).trans
        dsimp only [L]
        nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) D.card]
      _ = 2 * (L + 2 * Z) * ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ Z),
          (k : ℝ) ^ D.card := (mul_sum _ _ _).symm
      _ ≤ 2 * (L + 2 * Z) * ((Z + 1 : ℝ) * (Z : ℝ) ^ k) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast sieve_level_power_sum P (fun p hp => (hP p hp).1) k Z
      _ = _ := by ring
  apply h.trans
  dsimp only [g, L] at hrem ⊢
  simpa only [mul_assoc] using add_le_add le_rfl hrem

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RandomRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent random forbidden sets in residue planes -/

namespace JointDickman

open Finset

theorem randomized_pair_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (Ω : P → Type) [∀ p, Fintype (Ω p)]
      (μ : ∀ p, Ω p → ℝ) (A : ∀ p : P, Ω p → Finset (ZMod p.val × ZMod p.val))
      (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p x, 0 ≤ μ p x) → (∀ p, ∑ x, μ p x = 1) →
      (∀ p x, (A p x).card ≤ k * p.val) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P, ∑ x, μ p x *
        (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1)) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) * (∏ p : P, ∑ x, μ p x *
        (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2)) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := weighted_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P Ω _ μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  let R := 2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k
  let roots (ω : ∀ p, Ω p) (q : ℕ) : Finset (ZMod q × ZMod q) :=
    if hq : q ∈ P then A ⟨q, hq⟩ (ω ⟨q, hq⟩) else ∅
  have hroot (ω : ∀ p, Ω p) (p : P) : roots ω p.val = A p (ω p) := by
    simp [roots, p.property]
  have hprod (ω : ∀ p, Ω p) (r s : ℕ) :
      (∏ p ∈ pairRootEvents P (roots ω) r s, (0 : ℝ)) =
        ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then 0 else 1 := by
    calc
      _ = ∏ p ∈ P, if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1 := by
        simp only [pairRootEvents, prod_filter]
      _ = ∏ p : P, if ((r : ZMod p.val), (s : ZMod p.val)) ∈ roots ω p.val then (0 : ℝ) else 1 :=
        (P.prod_coe_sort (fun p : ℕ =>
          if ((r : ZMod p), (s : ZMod p)) ∈ roots ω p then (0 : ℝ) else 1)).symm
      _ = _ := by simp_rw [hroot]
  have hpoint (ω : ∀ p, Ω p) :
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) ≤
        C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R := by
    have h := hbound P (roots ω) (fun _ => 0) a b c d Z hab hcd hZ hP
      (fun p hp => by simpa [roots, hp] using hA ⟨p, hp⟩ (ω ⟨p, hp⟩))
      (by intros; norm_num)
    simp_rw [hprod] at h
    simpa only [mul_zero, add_zero,
      ← P.prod_coe_sort (fun p : ℕ => 1 - ((roots ω p).card : ℝ) / (p : ℝ) ^ 2), hroot] using h
  calc
    _ = ∑ ω, finiteProductMass μ ω *
        (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
          if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p (ω p) then (0 : ℝ) else 1) := by
      symm
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      exact (finiteProductMass_product_expectation μ
        (fun p x => if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p x then 0 else 1))
    _ ≤ ∑ ω, finiteProductMass μ ω *
        (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
          (∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2)) + R) := by
      apply sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hpoint ω) (finiteProductMass_nonneg μ hμ ω)
    _ = _ := by
      simp_rw [mul_add, sum_add_distrib]
      have hfirst : (∑ ω, finiteProductMass μ ω *
          (C * ((b : ℝ) - a) * ((d : ℝ) - c) *
            ∏ p : P, (1 - ((A p (ω p)).card : ℝ) / (p.val : ℝ) ^ 2))) =
          C * ((b : ℝ) - a) * ((d : ℝ) - c) * ∏ p : P, ∑ x, μ p x *
            (1 - ((A p x).card : ℝ) / (p.val : ℝ) ^ 2) := by
        rw [← finiteProductMass_product_expectation, mul_sum]
        apply sum_congr rfl
        intro ω _
        ring
      rw [hfirst, ← sum_mul, finiteProductMass_sum μ hμ1, one_mul]
      dsimp [R]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveAffineLines
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cardinality of a proper affine line over a prime residue field -/

namespace JointDickman

open Finset

/-- A proper affine line has at most `p` residue pairs. -/
theorem affineResidueLine_card_le {p : ℕ} (hp : p.Prime)
    (a b c : ZMod p) (hproper : a ≠ 0 ∨ b ≠ 0) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (affineResidueLine a b c).card ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  change (affineResidueLine a b c).card ≤ p
  rcases hproper with ha | hb
  · have hinj : Set.InjOn Prod.snd (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext _ hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : a * x.1 = a * y.1 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ ha heq
    calc
      _ = ((affineResidueLine a b c).image Prod.snd).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp
  · have hinj : Set.InjOn Prod.fst (↑(affineResidueLine a b c) : Set (ZMod p × ZMod p)) := by
      intro x hx y hy hxy
      apply Prod.ext hxy
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      rw [hxy] at hx'
      have heq : b * x.2 = b * y.2 := by linear_combination hx' - hy'
      exact mul_left_cancel₀ hb heq
    calc
      _ = ((affineResidueLine a b c).image Prod.fst).card := (card_image_iff.mpr hinj).symm
      _ ≤ (univ : Finset (ZMod p)).card := card_le_card (subset_univ _)
      _ = p := by simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_FormRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independently weighted forms in a rectangle -/

namespace JointDickman

open Finset

/-- The rectangular form-weight bound with exact residue averages. Each
zero set may be any set of at most `p` pairs, in particular a proper line. -/
theorem form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (F : ∀ p : P, Fin k → Finset (ZMod p.val × ZMod p.val))
      (θ : P → Fin k → ℝ) (a b c d Z : ℕ), a ≤ b → c ≤ d → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, (F p i).card ≤ p.val) → (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico a b, ∑ s ∈ Ico c d, ∏ p : P,
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) ≤
      C * ((b : ℝ) - a) * ((d : ℝ) - c) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2) +
      2 * (((b : ℝ) - a) + ((d : ℝ) - c) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  classical
  obtain ⟨C, hC, hbound⟩ := randomized_pair_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P F θ a b c d Z hab hcd hZ hP hF hθ
  let I : Finset (Fin k) := univ
  let Ω := {S : Finset (Fin k) // S ∈ I.powerset}
  let μ (p : P) (S : Ω) := bernoulliSubsetMass I (fun i => 1 - θ p i) S.val
  let A (p : P) (S : Ω) := S.val.biUnion (F p)
  have hμ (p : P) (S : Ω) : 0 ≤ μ p S :=
    bernoulliSubsetMass_nonneg (mem_powerset.mp S.property) (by
      intro i _
      constructor <;> linarith [(hθ p i).1, (hθ p i).2])
  have hμ1 (p : P) : ∑ S : Ω, μ p S = 1 := by
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S)]
    exact bernoulliSubsetMass_sum I _
  have hA (p : P) (S : Ω) : (A p S).card ≤ k * p.val := by
    calc
      _ ≤ ∑ i ∈ S.val, (F p i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ S.val, p.val := sum_le_sum (fun i _ => hF p i)
      _ = S.val.card * p.val := by simp
      _ ≤ I.card * p.val := Nat.mul_le_mul_right _ (card_le_card (mem_powerset.mp S.property))
      _ = _ := by simp [I]
  have hpoint (p : P) (r s : ℕ) :
      (∑ S : Ω, μ p S * (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ A p S then 0 else 1)) =
        formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val)) := by
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.val.biUnion (F p) then 0 else 1)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (if ((r : ZMod p.val), (s : ZMod p.val)) ∈ S.biUnion (F p) then 0 else 1))]
    exact bernoulli_union_survival I (F p) (θ p) _
  have hdensity (p : P) :
      (∑ S : Ω, μ p S * (1 - ((A p S).card : ℝ) / (p.val : ℝ) ^ 2)) =
        (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          formSetWeight (F p) (θ p) ((r : ZMod p.val), (s : ZMod p.val))) / (p.val : ℝ) ^ 2 := by
    let : NeZero p.val := ⟨(hP p.val p.property).1.ne_zero⟩
    have h := bernoulli_union_density
      (show 0 < Fintype.card (ZMod p.val × ZMod p.val) by
        simp only [Fintype.card_prod, ZMod.card]
        exact Nat.mul_pos (hP p.val p.property).1.pos (hP p.val p.property).1.pos) I (F p) (θ p)
    simp only [Fintype.card_prod, ZMod.card, ← pow_two, Nat.cast_pow] at h
    change (∑ S : Ω, bernoulliSubsetMass I (fun i => 1 - θ p i) S.val *
      (1 - ((S.val.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)) = _
    rw [I.powerset.sum_coe_sort (fun S => bernoulliSubsetMass I (fun i => 1 - θ p i) S *
      (1 - ((S.biUnion (F p)).card : ℝ) / (p.val : ℝ) ^ 2)), h]
    congr 1
    have hres (f : ZMod p.val → ℝ) : (∑ x, f x) = ∑ n ∈ range p.val, f n := by
      exact_mod_cast residue_sum_eq_range (fun x => (f x : ℂ))
    rw [Fintype.sum_prod_type]
    simp_rw [hres]
    rfl
  have h := hbound P (fun _ => Ω) μ A a b c d Z hab hcd hZ hP hμ hμ1 hA
  simpa only [hpoint, hdensity] using h

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_AffineRectangleSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The weighted affine-line rectangle sieve -/

namespace JointDickman

open Finset

/-- The manuscript's rectangle sieve for proper affine forms, with the
exact local mean and an explicit polynomial remainder. -/
theorem affine_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ)
      (a b c : ∀ p : P, Fin k → ZMod p.val) (θ : P → Fin k → ℝ)
      (u v w x Z : ℕ), u ≤ v → w ≤ x → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 2 * k ≤ p) →
      (∀ p i, a p i ≠ 0 ∨ b p i ≠ 0) →
      (∀ p i, 0 ≤ θ p i ∧ θ p i ≤ 1) →
      (∑ r ∈ Ico u v, ∑ s ∈ Ico w x, ∏ p : P,
        affineFormWeight (a p) (b p) (c p) (θ p) (r : ZMod p.val) (s : ZMod p.val)) ≤
      C * ((v : ℝ) - u) * ((x : ℝ) - w) *
        (∏ p : P, (∑ r ∈ range p.val, ∑ s ∈ range p.val,
          affineFormWeight (a p) (b p) (c p) (θ p)
            (r : ZMod p.val) (s : ZMod p.val)) / (p.val : ℝ) ^ 2) +
      2 * (((v : ℝ) - u) + ((x : ℝ) - w) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ k := by
  obtain ⟨C, hC, hbound⟩ := form_rectangle_sieve hFord hM hk
  refine ⟨C, hC, ?_⟩
  intro P a b c θ u v w x Z huv hwx hZ hP hproper hθ
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p.val p.property).1.ne_zero⟩
  let F := fun (p : P) (i : Fin k) => affineResidueLine (a p i) (b p i) (c p i)
  have hF (p : P) (i : Fin k) : (F p i).card ≤ p.val :=
    affineResidueLine_card_le (hP p.val p.property).1 _ _ _ (hproper p i)
  have heq (p : P) (r s : ZMod p.val) :
      formSetWeight (F p) (θ p) (r, s) = affineFormWeight (a p) (b p) (c p) (θ p) r s := by
    simp [formSetWeight, F, affineResidueLine, prod_filter, affineFormWeight]
  simpa only [heq] using hbound P F θ u v w x Z huv hwx hZ hP hF hθ

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
theorem sum_residueWeight {α : Type*} [Fintype α] (t : ℝ) (a : α) :
    ∑ x : α, residueWeight t a x = (Fintype.card α : ℝ) - 1 + t := by
  have heq (x : α) : residueWeight t a x = 1 + (if x = a then t - 1 else 0) := by
    by_cases h : x = a <;> simp [residueWeight, h]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true, if_true]
  ring

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteTripleExtension
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite extension of an arithmetic triple sum by zero -/

namespace JointDickman
open Finset

theorem finite_triple_sum_extend {α β : Type*} [DecidableEq α] [DecidableEq β]
    {A A' : Finset α} {C C' : Finset β} (hA : A ⊆ A') (hC : C ⊆ C')
    (f : β → α → α → ℝ)
    (hsupp : ∀ c b a, f c b a ≠ 0 → c ∈ C ∧ b ∈ A ∧ a ∈ A) :
    (∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f c b a) =
      ∑ c ∈ C', ∑ b ∈ A', ∑ a ∈ A', f c b a := by
  calc
    _ = ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_congr rfl
      intro b _
      apply sum_subset hA
      intro a _ ha
      by_contra h
      exact ha (hsupp c b a h).2.2
    _ = ∑ c ∈ C, ∑ b ∈ A', ∑ a ∈ A', f c b a := by
      apply sum_congr rfl
      intro c _
      apply sum_subset hA
      intro b _ hb
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hb (hsupp c b a h).2.1
    _ = _ := by
      apply sum_subset hC
      intro c _ hc
      apply sum_eq_zero
      intro b _
      apply sum_eq_zero
      intro a _
      by_contra h
      exact hc (hsupp c b a h).1

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SingularFactor
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

theorem real_residue_double_sum_eq_range {p : ℕ} [NeZero p]
    (f : ZMod p → ZMod p → ℝ) :
    (∑ r : ZMod p, ∑ s : ZMod p, f r s) =
      ∑ m ∈ range p, ∑ n ∈ range p, f m n := by
  rw [real_residue_sum_eq_range]
  apply sum_congr rfl
  intro m _
  exact real_residue_sum_eq_range _

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ChernoffParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative choices for the regularity Chernoff bounds -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem exists_prefix_tilt {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ τ ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
        -s * τ + (g / 2) * (Real.exp s - 1 - s) ≤ -s * τ / 2 ∧
        -s * τ + (g / 2) * (Real.exp (-s) - 1 + s) ≤ -s * τ / 2 := by
  let s := min τ (1 / 10 : ℝ)
  have hs : 0 < s := lt_min hτ (by norm_num)
  have hsτ : s ≤ τ := min_le_left _ _
  have hs1 : s ≤ 1 / 10 := min_le_right _ _
  have hp := Real.abs_exp_sub_one_sub_id_le (show |s| ≤ 1 by rw [abs_of_pos hs]; linarith)
  have hn := Real.abs_exp_sub_one_sub_id_le (show |-s| ≤ 1 by rw [abs_neg, abs_of_pos hs]; linarith)
  have hp0 : 0 ≤ Real.exp s - 1 - s := by linarith [Real.add_one_le_exp s]
  have hn0 : 0 ≤ Real.exp (-s) - 1 + s := by linarith [Real.add_one_le_exp (-s)]
  have hp2 := (abs_le.mp hp).2
  have hn2 := (abs_le.mp hn).2
  refine ⟨s, hs, hsτ, hs1, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (s - 1 / 10)]
  · calc
      Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 2 := by norm_num
  · intro g hg hg1
    have hst := mul_nonneg hs.le (sub_nonneg.mpr hsτ)
    constructor
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hp0
      nlinarith
    · have hmul := mul_nonneg (sub_nonneg.mpr hg1) hn0
      nlinarith

theorem tail_tilt_margin :
    0 < (1 / 2 : ℝ) * (1 - Real.exp (-(1 / 10 : ℝ))) - (2 / 5 : ℝ) * (1 / 10) := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le
    (show |-(1 / 10 : ℝ)| ≤ 1 by norm_num))).2
  norm_num at h ⊢
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RegularityTailPrimeSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform lower bound for reciprocal-prime tail masses -/

namespace JointDickman

open Finset

theorem regularity_tail_prime_sum_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ B X Y : ℝ, 0 < B → 2 ≤ X → c * B ≤ Real.log X → 1 ≤ Y →
      Real.log (B / Y) - K ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) := by
  obtain ⟨C, hC, hm⟩ := prime_interval_mertens_error hM
  refine ⟨2 * C + |Real.log c|, by positivity, ?_⟩
  intro B X Y hB hX hlog hY
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hEY : 2 ≤ Real.exp Y := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ _ := Real.exp_le_exp.mpr hY
  have hlogB : Real.log (c * B) = Real.log c + Real.log B :=
    Real.log_mul hc.ne' hB.ne'
  by_cases hYX : Real.exp Y ≤ X
  · have hlogXY : Y ≤ Real.log X := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos Y) hYX
    have hlogX1 : 1 ≤ Real.log X := hY.trans hlogXY
    have herr := hm (Real.exp Y) X hEY hYX
    rw [Real.log_exp] at herr
    have hCY : C / Y ≤ C := div_le_self hC hY
    have hCX : C / Real.log X ≤ C := div_le_self hC hlogX1
    have hcompare : Real.log c + Real.log B ≤ Real.log (Real.log X) := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) hlog
    rw [Real.log_div hB.ne' hY0.ne']
    have hlo := (abs_le.mp herr).1
    have habs := neg_abs_le (Real.log c)
    linarith
  · have hXY : X < Real.exp Y := lt_of_not_ge hYX
    have hlogXY : Real.log X < Y := by
      simpa only [Real.log_exp] using Real.log_lt_log hX0 hXY
    have hcompare : Real.log c + Real.log B ≤ Real.log Y := by
      rw [← hlogB]
      exact Real.log_le_log (mul_pos hc hB) (hlog.trans hlogXY.le)
    have hsum : 0 ≤ ∑ p ∈ largePrimeSet X (Real.exp Y), 1 / (p : ℝ) :=
      sum_nonneg (fun _ _ => by positivity)
    rw [Real.log_div hB.ne' hY0.ne']
    have habs := neg_abs_le (Real.log c)
    linarith

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

theorem tailSaving_pos : 0 < tailSaving := tail_tilt_margin

theorem tail_chernoff_factor_bound {B Y M K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (hM : Real.log (B / Y) - K ≤ M) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M) ≤
    Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
      Real.exp (-(1 / 10 : ℝ) * C) * (Y / B) ^ tailSaving := by
  have hexp : Real.exp (-(1 / 10 : ℝ)) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  have hm := mul_le_mul_of_nonpos_left hM (show (Real.exp (-(1 / 10 : ℝ)) - 1) / 2 ≤ 0 by linarith)
  have hlog : Real.log (Y / B) = -Real.log (B / Y) := by
    rw [Real.log_div hY.ne' hB.ne', Real.log_div hB.ne' hY.ne']
    ring
  rw [Real.rpow_def_of_pos (div_pos hY hB), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  unfold tailSaving
  nlinarith

/-- The dyadic union bound is uniform in the number of endpoints and in C. -/
theorem dyadic_tail_chernoff_sum (S : Finset ℕ) {B Y K C : ℝ}
    (hB : 0 < B) (hY : 0 < Y) (M : ℕ → ℝ)
    (hM : ∀ i ∈ S, Real.log (B / ((2 : ℝ) ^ i * Y)) - K ≤ M i)
    (hcap : ∀ i ∈ S, (2 : ℝ) ^ i * Y ≤ B) :
    (∑ i ∈ S, Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / ((2 : ℝ) ^ i * Y)) - C) +
      ((Real.exp (-(1 / 10 : ℝ)) - 1) / 2) * M i)) ≤
      (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))) * Real.exp (-(1 / 10 : ℝ) * C) := by
  calc
    _ ≤ ∑ i ∈ S, Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
        Real.exp (-(1 / 10 : ℝ) * C) * (((2 : ℝ) ^ i * Y) / B) ^ tailSaving :=
      sum_le_sum (fun i hi => tail_chernoff_factor_bound hB (by positivity) (hM i hi))
    _ = (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
        ∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving := by rw [mul_sum]
    _ ≤ _ := by
      have h : (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          (∑ i ∈ S, (((2 : ℝ) ^ i * Y) / B) ^ tailSaving) ≤
          (Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) * Real.exp (-(1 / 10 : ℝ) * C)) *
          ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1)) :=
        mul_le_mul_of_nonneg_left (dyadic_power_sum_bound S hB hY.le tailSaving_pos hcap) (by positivity)
      convert h using 1 <;> first | rfl | ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MixedThreeFormLocal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three-form local means with independently tilted weights -/

namespace JointDickman

open Finset

open Classical in
theorem three_affine_residue_sum_mixed {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) (t u v : ℝ) :
    (∑ b : ZMod p, ∑ c : ZMod p,
      residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) =
      u * ((p : ℝ) - 1 + t * v) + ((p : ℝ) - 1) * ((p : ℝ) - 2 + t + v) := by
  rw [sum_comm]
  have hinner (c : ZMod p) : (∑ b : ZMod p,
      residueWeight t 0 b * residueWeight u 0 c * residueWeight v 0 (b + j * c)) =
      if c = 0 then u * ((p : ℝ) - 1 + t * v) else (p : ℝ) - 2 + t + v := by
    by_cases hc : c = 0
    · subst c
      simp only [mul_zero, add_zero, residueWeight, ite_true, if_true]
      calc
        _ = u * ∑ b : ZMod p, residueWeight (t * v) 0 b := by
          rw [mul_sum]
          apply sum_congr rfl
          intro b _
          by_cases hb : b = 0 <;> simp [residueWeight, hb]
          ring
        _ = _ := by rw [sum_residueWeight, ZMod.card]
    · have hroot : (0 : ZMod p) ≠ -(j * c) := by
        intro h
        exact mul_ne_zero hj hc (neg_eq_zero.mp h.symm)
      have heq (b : ZMod p) : residueWeight v 0 (b + j * c) = residueWeight v (-(j * c)) b := by
        simp [residueWeight, add_eq_zero_iff_eq_neg]
      simp only [hc, residueWeight, ite_false, if_false, mul_one]
      change (∑ b : ZMod p, residueWeight t 0 b * residueWeight v 0 (b + j * c)) = _
      simp_rw [heq]
      simpa only [ZMod.card] using sum_two_residueWeights t v (0 : ZMod p) (-(j * c)) hroot
  simp_rw [hinner]
  have heq (c : ZMod p) :
      (if c = 0 then u * ((p : ℝ) - 1 + t * v) else (p : ℝ) - 2 + t + v) =
      ((p : ℝ) - 2 + t + v) +
        (if c = 0 then u * ((p : ℝ) - 1 + t * v) - ((p : ℝ) - 2 + t + v) else 0) := by
    by_cases hc : c = 0 <;> simp [hc]
  simp_rw [heq]
  simp only [sum_add_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_ite_eq', mem_univ, ite_true, if_true]
  ring

theorem mixedThreeFormMean_le_one {p : ℕ} [NeZero p]
    (j : ZMod p) {t u v : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    mixedThreeFormMean j t u v ≤ 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  apply (div_le_one (sq_pos_of_pos hp0)).mpr
  calc
    _ ≤ ∑ _b : ZMod p, ∑ _c : ZMod p, (1 : ℝ) := by
      apply sum_le_sum
      intro b _
      apply sum_le_sum
      intro c _
      have htu : residueWeight t 0 b * residueWeight u 0 c ≤ 1 := by
        simpa only [mul_one] using mul_le_mul (residueWeight_le_one _ _ ht1)
          (residueWeight_le_one _ _ hu1) (residueWeight_nonneg _ _ hu) zero_le_one
      simpa only [mul_one] using mul_le_mul htu (residueWeight_le_one _ _ hv1)
        (residueWeight_nonneg _ _ hv) zero_le_one
    _ = _ := by simp [pow_two]

theorem mixedThreeFormMean_nondegenerate {p : ℕ} [Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) {t u v : ℝ} (ht : t ≤ 1) (hu : u ≤ 1) (hv : v ≤ 1) :
    mixedThreeFormMean j t u v ≤
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hp0 : (0 : ℝ) < p := by linarith
  have heq : mixedThreeFormMean j t u v =
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) -
        (1 - t) * (1 - u) * (1 - v) * ((p : ℝ) - 1) / (p : ℝ) ^ 3 := by
    unfold mixedThreeFormMean
    rw [three_affine_residue_sum_mixed j hj]
    field_simp
    ring
  rw [heq]
  exact sub_le_self _ (by positivity)

theorem mixedThreeFormMean_bound {p : ℕ} [Fact p.Prime]
    (j : ZMod p) {t u v : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    mixedThreeFormMean j t u v ≤
      (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) *
        (if j = 0 then 1 + 24 / (p : ℝ) else 1) := by
  by_cases hj : j = 0
  · rw [ite_eq_left hj]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    have hc : 1 ≤ (1 - 1 / (p : ℝ)) ^ 3 * (1 + 24 / (p : ℝ)) := by
      simpa only [one_mul, div_eq_mul_inv] using
        one_le_cube_singular_factor (by positivity : (0 : ℝ) ≤ 1 / p) hx (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    have hmin : (1 - 1 / (p : ℝ)) ^ 3 ≤
        (1 - (1 - t) / p) * (1 - (1 - u) / p) * (1 - (1 - v) / p) := by
      have hbase : 0 ≤ 1 - 1 / (p : ℝ) := by linarith
      have ht' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - t) / p := by
        have := div_nonneg ht hp0.le
        linarith [sub_div 1 t (p : ℝ)]
      have hu' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - u) / p := by
        have := div_nonneg hu hp0.le
        linarith [sub_div 1 u (p : ℝ)]
      have hv' : 1 - 1 / (p : ℝ) ≤ 1 - (1 - v) / p := by
        have := div_nonneg hv hp0.le
        linarith [sub_div 1 v (p : ℝ)]
      calc
        _ = (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ)) := by ring
        _ ≤ _ := mul_le_mul (mul_le_mul ht' hu' hbase (hbase.trans ht')) hv' hbase
          (mul_nonneg (hbase.trans ht') (hbase.trans hu'))
    exact (mixedThreeFormMean_le_one j ht ht1 hu hu1 hv hv1).trans
      (hc.trans (mul_le_mul_of_nonneg_right hmin (by positivity)))
  · rw [ite_eq_right hj, mul_one]
    exact mixedThreeFormMean_nondegenerate j hj ht1 hu1 hv1

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_MixedThreeFormSieve
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rectangle sieve for three separately tilted coefficient weights -/

namespace JointDickman

open Finset

theorem mixedThreeFormLocalFactor_eq {p : ℕ} [NeZero p] (j : ℕ) (t u v : ℝ) :
    mixedThreeFormLocalFactor p j t u v = mixedThreeFormMean (j : ZMod p) t u v := by
  unfold mixedThreeFormLocalFactor mixedThreeFormMean
  rw [real_residue_double_sum_eq_range]

theorem mixedThreeFormLocalFactor_nonneg (p j : ℕ) {t u v : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ mixedThreeFormLocalFactor p j t u v := by
  unfold mixedThreeFormLocalFactor
  exact div_nonneg (sum_nonneg (fun _b _ => sum_nonneg (fun _c _ =>
    mul_nonneg (mul_nonneg (residueWeight_nonneg _ _ ht) (residueWeight_nonneg _ _ hu))
      (residueWeight_nonneg _ _ hv)))) (sq_nonneg _)

open Classical in
theorem mixed_three_form_local_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t u v : ℕ → ℝ) (ht : ∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1)
    (hu : ∀ p ∈ P, 0 ≤ u p ∧ u p ≤ 1) (hv : ∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1)
    {j : ℕ} (hj : j ≠ 0) :
    (∏ p ∈ P, mixedThreeFormLocalFactor p j (t p) (u p) (v p)) ≤
      (∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
        (∏ p ∈ P, (1 - (1 - v p) / p)) * singularFactor 24 j := by
  have hlocal (p : ℕ) (hp : p ∈ P) : mixedThreeFormLocalFactor p j (t p) (u p) (v p) ≤
      (1 - (1 - t p) / p) * (1 - (1 - u p) / p) * (1 - (1 - v p) / p) *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := by
    let : Fact p.Prime := ⟨hP p hp⟩
    rw [mixedThreeFormLocalFactor_eq]
    simpa only [ZMod.natCast_eq_zero_iff] using mixedThreeFormMean_bound (j : ZMod p)
      (ht p hp).1 (ht p hp).2 (hu p hp).1 (hu p hp).2 (hv p hp).1 (hv p hp).2
  have hs (f : ℕ → ℝ) (hf : ∀ p ∈ P, 0 ≤ f p) (p : ℕ) (hp : p ∈ P) :
      0 ≤ 1 - (1 - f p) / p := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [hf p hp]
  have hexcept : (∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1) ≤ singularFactor 24 j := by
    rw [← prod_filter]
    apply prod_le_prod_of_subset_of_one_le
    · intro p hp
      exact (hP p (mem_filter.mp hp).1).mem_primeFactors (mem_filter.mp hp).2 hj
    · intros; positivity
    · intro p _ _
      exact le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ ∏ p ∈ P, (1 - (1 - t p) / p) * (1 - (1 - u p) / p) * (1 - (1 - v p) / p) *
        (if p ∣ j then 1 + 24 / (p : ℝ) else 1) := Finset.prod_le_prod
      (fun p hp => mixedThreeFormLocalFactor_nonneg p j (ht p hp).1 (hu p hp).1 (hv p hp).1) hlocal
    _ = (∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
        (∏ p ∈ P, (1 - (1 - v p) / p)) * ∏ p ∈ P, if p ∣ j then 1 + 24 / (p : ℝ) else 1 := by
      simp only [prod_mul_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left hexcept
      (mul_nonneg (mul_nonneg (prod_nonneg (hs t (fun p hp => (ht p hp).1)))
        (prod_nonneg (hs u (fun p hp => (hu p hp).1))))
          (prod_nonneg (hs v (fun p hp => (hv p hp).1))))

theorem mixed_three_form_rectangle_sieve
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (t u v : ℕ → ℝ)
      (j l₁ r₁ l₂ r₂ Z : ℕ), j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ → 2 ≤ Z →
      (∀ p ∈ P, p.Prime ∧ p ≤ Z ∧ 6 ≤ p) →
      (∀ p ∈ P, 0 ≤ t p ∧ t p ≤ 1) →
      (∀ p ∈ P, 0 ≤ u p ∧ u p ≤ 1) →
      (∀ p ∈ P, 0 ≤ v p ∧ v p ≤ 1) →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂, mixedThreeFormSieveWeight P t u v j b c) ≤
        C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) *
          ((∏ p ∈ P, (1 - (1 - t p) / p)) * (∏ p ∈ P, (1 - (1 - u p) / p)) *
            (∏ p ∈ P, (1 - (1 - v p) / p))) * singularFactor 24 j +
          2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := affine_rectangle_sieve hFord hM (by norm_num : 0 < (3 : ℕ))
  refine ⟨C, hC, ?_⟩
  intro P t u v j l₁ r₁ l₂ r₂ Z hj hI hJ hZ hP ht hu hv
  classical
  let a : (p : P) → Fin 3 → ZMod p.val := fun _ => ![1, 0, 1]
  let b : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 1, j]
  let c : (p : P) → Fin 3 → ZMod p.val := fun _ => ![0, 0, 0]
  let θ : P → Fin 3 → ℝ := fun p => ![t p.val, u p.val, v p.val]
  have hproper (p : P) (i : Fin 3) : a p i ≠ 0 ∨ b p i ≠ 0 := by
    let : Fact p.val.Prime := ⟨(hP p.val p.property).1⟩
    fin_cases i <;> simp [a, b]
  have hθ (p : P) (i : Fin 3) : 0 ≤ θ p i ∧ θ p i ≤ 1 := by
    fin_cases i
    · exact ht p.val p.property
    · exact hu p.val p.property
    · exact hv p.val p.property
  have heq (p : P) (r s : ZMod p.val) :
      affineFormWeight (a p) (b p) (c p) (θ p) r s =
        residueWeight (t p.val) 0 r * residueWeight (u p.val) 0 s *
          residueWeight (v p.val) 0 (r + j * s) := by
    simp [affineFormWeight, a, b, c, θ, Fin.prod_univ_succ, residueWeight, mul_assoc]
    split_ifs <;> rfl
  have hh := hbound P a b c θ l₁ r₁ l₂ r₂ Z hI hJ hZ hP hproper hθ
  simp_rw [heq] at hh
  have hweight (r s : ℕ) : (∏ p : P, residueWeight (t p.val) 0 (r : ZMod p.val) *
      residueWeight (u p.val) 0 (s : ZMod p.val) *
        residueWeight (v p.val) 0 ((r : ZMod p.val) + j * s)) = mixedThreeFormSieveWeight P t u v j r s :=
    P.prod_coe_sort (fun p : ℕ => residueWeight (t p) 0 (r : ZMod p) *
      residueWeight (u p) 0 (s : ZMod p) * residueWeight (v p) 0 ((r : ZMod p) + j * s))
  simp_rw [hweight] at hh
  change _ ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) *
    (∏ p : P, mixedThreeFormLocalFactor p.val j (t p.val) (u p.val) (v p.val)) + _ at hh
  rw [P.prod_coe_sort (fun p : ℕ => mixedThreeFormLocalFactor p j (t p) (u p) (v p))] at hh
  refine hh.trans (add_le_add ?_ le_rfl)
  have hprod := mixed_three_form_local_product_bound P (fun p hp => (hP p hp).1) t u v ht hu hv hj
  have harea : 0 ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) :=
    mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast hI)))
      (sub_nonneg.mpr (by exact_mod_cast hJ))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod harea

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

theorem coefficient_prefix_count {B n : ℕ} (hn : n ≠ 0) (g : ℝ) :
    (primePrefix B g (coefficientPrimeSet B n)).card =
      primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) n := by
  rw [coefficientPrimeSet_eq_inter hn, primePrefix_inter]
  rfl

theorem coefficient_tail_count {B n : ℕ} (hn : n ≠ 0) (Y : ℝ) :
    ((coefficientPrimeSet B n).filter (fun p : ℕ => Y < Real.log p)).card =
      primeDivisorCount ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) n := by
  classical
  rw [coefficientPrimeSet_eq_inter hn]
  congr 1
  ext p
  simp only [mem_filter, mem_inter]
  tauto

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

theorem tiltedCoefficientWeight_nonneg (B : ℕ) (Q : Finset ℕ) (s : ℝ) (n : ℕ) :
    0 ≤ tiltedCoefficientWeight B Q s n :=
  mul_nonneg (coefficientWeight_nonneg _ _) (Real.exp_pos _).le

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

open Classical in
theorem tail_sieve_set (B Z : ℕ) {Y : ℝ} (hP : 6 ≤ auxiliaryCutoff B)
    (hZU : (Z : ℝ) ≤ auxiliaryUpper B) (hY : Real.log (auxiliaryCutoff B) ≤ Y) :
    (sievePrimes Z).filter (fun p => auxiliaryCutoff B < p ∧
      p ∈ (auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) =
        largePrimeSet Z (Real.exp Y) := by
  have hP0 : (0 : ℝ) < auxiliaryCutoff B := by exact_mod_cast (by omega : 0 < auxiliaryCutoff B)
  have hPY : (auxiliaryCutoff B : ℝ) ≤ Real.exp Y := by
    simpa only [Real.exp_log hP0] using Real.exp_le_exp.mpr hY
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, _hpP, hpQ⟩ := mem_filter.mp hp
    obtain ⟨hpZ, _⟩ := mem_filter.mp hpS
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hYp := (mem_filter.mp hpQ).2
    have hxp : Real.exp Y < (p : ℝ) := by
      simpa only [Real.exp_log hp0] using Real.exp_lt_exp.mpr hYp
    exact mem_filter.mpr ⟨by simpa only [Nat.floor_natCast] using Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, hxp⟩
  · intro hp
    obtain ⟨hpZ, hxp⟩ := mem_filter.mp hp
    rw [Nat.floor_natCast] at hpZ
    obtain ⟨hpZ, hprime⟩ := Nat.mem_primesLE.mp hpZ
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpP : auxiliaryCutoff B < p := by exact_mod_cast (hPY.trans_lt hxp)
    have hpU : p ≤ ⌊auxiliaryUpper B⌋₊ := Nat.le_floor ((by exact_mod_cast hpZ : (p : ℝ) ≤ Z).trans hZU)
    have hlog : Y < Real.log p := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos Y) hxp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpZ, hprime⟩, by omega⟩,
      hpP, mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, hprime⟩, by exact_mod_cast hpP⟩, hlog⟩⟩

theorem tilt_tail_mass_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ, Real.log (auxiliaryCutoff B) ≤ Y →
      Real.log ((B : ℝ) / Y) - K ≤ tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
        ((auxiliaryPrimes B).filter (fun p : ℕ => Y < Real.log p)) := by
  classical
  obtain ⟨K, hK, hbound⟩ := regularity_tail_prime_sum_lower hM (by linarith : 0 < c / 2)
  refine ⟨K, hK, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually hc, auxiliaryCutoff_tendsto.eventually_ge_atTop 6,
    hloglarge, eventually_gt_atTop 0] with B hcut hP hlog hB
  intro Y hY
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hZU : (sieveCutoff c B : ℝ) ≤ auxiliaryUpper B :=
    hcut.2.2.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc4 hB0.le))
  unfold tiltPrimeReciprocalMass
  rw [tail_sieve_set B _ hP hZU hY]
  exact hbound B (sieveCutoff c B) Y hB0 (by exact_mod_cast hcut.1) hcut.2.2.1 (hlog.trans hY)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityChernoffFactors
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chernoff factors with the actual truncated sieve prime sets -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem actual_prefix_chernoff_decay
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ c g : ℝ, 0 < c → c ≤ 4 → 0 < g → g ≤ 1 →
        Tendsto (fun B => prefixUpperFactor B c g τ s) atTop (𝓝 0) ∧
        Tendsto (fun B => prefixLowerFactor B c g τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, _hsτ, hs1, he, hen, hmargin⟩ := exists_prefix_tilt hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro c g hc hc4 hg hg1
  let m := fun B => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B) (primePrefix B g (auxiliaryPrimes B))
  have hm : Tendsto (fun B => m B / auxiliaryLogLength B) atTop (𝓝 g) :=
    tilt_prefix_mass_tendsto hM hc hc4 hg hg1
  have hpos : -s * (g / 2 + τ) + ((Real.exp s - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).1
    nlinarith [mul_pos hs hτ]
  have hneg : s * (g / 2 - τ) + ((Real.exp (-s) - 1) / 2) * g < 0 := by
    have h := (hmargin g hg.le hg1).2
    nlinarith [mul_pos hs hτ]
  have hℓ : ∀ᶠ B : ℕ in atTop, auxiliaryLogLength B ≠ 0 :=
    (auxiliaryLogLength_tendsto.eventually_gt_atTop 0).mono (fun _ h => ne_of_gt h)
  constructor
  · have hlim := (hm.const_mul ((Real.exp s - 1) / 2)).const_add (-s * (g / 2 + τ))
    have hprod := hlim.neg_mul_atTop hpos auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixUpperFactor, m]
    field_simp
  · have hlim := (hm.const_mul ((Real.exp (-s) - 1) / 2)).const_add (s * (g / 2 - τ))
    have hprod := hlim.neg_mul_atTop hneg auxiliaryLogLength_tendsto
    apply Real.tendsto_exp_atBot.comp (hprod.congr' ?_)
    filter_upwards [hℓ] with B hB
    dsimp [prefixLowerFactor, m]
    field_simp

theorem actual_tail_chernoff_sum
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ} (hc : 0 < c) (hc4 : c ≤ 4) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ B : ℕ in atTop, ∀ (S : Finset ℕ) (C : ℝ),
      (∀ i ∈ S, primeTailEndpoint B i ≤ B) →
      (∑ i ∈ S, tailChernoffFactor B i c C) ≤ D * Real.exp (-(1 / 10 : ℝ) * C) := by
  classical
  obtain ⟨K, _hK, hbound⟩ := tilt_tail_mass_lower hM hc hc4
  let D := Real.exp (K * ((1 - Real.exp (-(1 / 10 : ℝ))) / 2)) *
    ((2 : ℝ) ^ tailSaving / ((2 : ℝ) ^ tailSaving - 1))
  have hr : 1 < (2 : ℝ) ^ tailSaving := Real.one_lt_rpow (by norm_num) tailSaving_pos
  refine ⟨D, mul_pos (Real.exp_pos _) (div_pos (by positivity) (by linarith)), ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [hbound, hloglarge, eventually_gt_atTop 0] with B hB hlog hBpos
  intro S C hS
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hY0 : 0 < Real.log (auxiliaryCutoff B) := by linarith
  have hY (i : ℕ) : Real.log (auxiliaryCutoff B) ≤ primeTailEndpoint B i := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    exact le_mul_of_one_le_left hY0.le hp
  exact dyadic_tail_chernoff_sum S hB0 hY0
    (fun i => tiltPrimeReciprocalMass (auxiliaryCutoff B) (sieveCutoff c B)
      ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)))
    (fun i _ => hB (primeTailEndpoint B i) (hY i)) hS

theorem tail_endpoint_index_lt {B i : ℕ} (hlog : 1 ≤ Real.log (auxiliaryCutoff B))
    (hi : primeTailEndpoint B i < B) : i < B := by
  have hp : (i : ℝ) < (2 : ℝ) ^ i := by exact_mod_cast (show i < 2 ^ i from Nat.lt_two_pow_self)
  have hm : (2 : ℝ) ^ i ≤ primeTailEndpoint B i :=
    le_mul_of_one_le_right (by positivity) hlog
  exact_mod_cast hp.trans (hm.trans_lt hi)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RectangleRemainder
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the explicit rectangular sieve remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem rectangle_remainder_bound {L H E F Z : ℝ} (hE : 0 < E)
    (hEL : E ≤ L) (hEH : E ≤ H) (hZ1 : 1 ≤ Z) (hZF : Z ≤ F) (hFE : F ≤ E) :
    2 * (L + H + 2 * Z) * (Z + 1) * Z ^ 3 ≤ 16 * L * H * F ^ 4 / E := by
  have hL : 0 ≤ L := hE.le.trans hEL
  have hH : 0 ≤ H := hE.le.trans hEH
  have hZ : 0 ≤ Z := by linarith
  have hF : 0 ≤ F := hZ.trans hZF
  have hELH : E * L ≤ L * H := by nlinarith [mul_le_mul_of_nonneg_left hEH hL]
  have hEHL : E * H ≤ L * H := mul_le_mul_of_nonneg_right hEL hH
  have hEZ : E * Z ≤ L * H := mul_le_mul hEL ((hZF.trans hFE).trans hEH) hZ hL
  have hlength : L + H + 2 * Z ≤ 4 * L * H / E := by
    apply (le_div_iff₀ hE).mpr
    nlinarith
  have hZF2 : Z + 1 ≤ 2 * F := by linarith
  calc
    _ ≤ 2 * (4 * L * H / E) * (2 * F) * F ^ 3 := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SieveRemainderDecay
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial saving in the explicit rectangle remainder -/

namespace JointDickman

open Filter
open scoped Topology

theorem coefficient_rectangle_remainder_power {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ B : ℕ in atTop, ∀ L H : ℝ,
      Real.exp (δ * B) ≤ L → Real.exp (δ * B) ≤ H →
      coefficientScale B ^ 3 *
        (2 * (L + H + 2 * sieveCutoff (δ / 8) B) *
          (sieveCutoff (δ / 8) B + 1 : ℝ) * (sieveCutoff (δ / 8) B : ℝ) ^ 3) ≤ (L * H) / (B : ℝ) ^ 10 := by
  have hlim : Tendsto (fun B : ℕ => 16 * ((B : ℝ) ^ 13 /
      Real.exp ((δ / 2) * B))) atTop (𝓝 0) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 13 (by linarith : 0 < δ / 2)).tendsto_div_nhds_zero
    simpa only [Function.comp_def, mul_zero] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul 16
  have hsmall := hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, coefficientScale_eventually_le,
    sieveCutoff_eventually (by linarith : 0 < δ / 8), eventually_gt_atTop 0]
    with B hsmallB hscale hcut hBpos
  intro L H hL hH
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hF : Real.exp ((δ / 8) * B) ≤ Real.exp (δ * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hz1 : (1 : ℝ) ≤ sieveCutoff (δ / 8) B := by exact_mod_cast (by omega : 1 ≤ sieveCutoff (δ / 8) B)
  have hbound := rectangle_remainder_bound (Real.exp_pos _) hL hH hz1 hcut.2.2.2 hF
  have heq : Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B) =
      (Real.exp ((δ / 2) * B))⁻¹ := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_neg]
    congr 1
    ring
  have hLH : 0 ≤ L * H := mul_nonneg ((Real.exp_pos _).le.trans hL)
    ((Real.exp_pos _).le.trans hH)
  have hL0 : 0 ≤ L := (Real.exp_pos _).le.trans hL
  have hH0 : 0 ≤ H := (Real.exp_pos _).le.trans hH
  calc
    _ ≤ (B : ℝ) ^ 3 * (16 * L * H * Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) :=
      mul_le_mul (pow_le_pow_left₀ (coefficientScale_nonneg B) hscale 3) hbound
        (by positivity) (pow_nonneg hB0 _)
    _ = (16 * ((B : ℝ) ^ 3 / Real.exp ((δ / 2) * B))) * (L * H) := by
      calc
        _ = 16 * (B : ℝ) ^ 3 * (Real.exp ((δ / 8) * B) ^ 4 / Real.exp (δ * B)) * (L * H) := by ring
        _ = _ := by rw [heq]; ring
    _ ≤ (1 / (B : ℝ) ^ 10) * (L * H) := by
      apply mul_le_mul_of_nonneg_right ?_ hLH
      have hBp : (0 : ℝ) < B := by exact_mod_cast hBpos
      apply (le_div_iff₀ (pow_pos hBp 10)).mpr
      convert hsmallB using 1 <;> first | rfl | ring
    _ = _ := by ring

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

theorem prefix_markov_multiplier_bounds {B : ℕ} {g τ s : ℝ}
    (hB : 1 ≤ B) (hg : 0 ≤ g) (hg1 : g ≤ 1) (hτ : 0 ≤ τ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hℓ : 0 ≤ auxiliaryLogLength B) (hℓlog : auxiliaryLogLength B ≤ Real.log B) :
    Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B)) ≤ B ∧
    Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) ≤ B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB)
  have hexp : Real.exp (Real.log B) = B := Real.exp_log hB0
  constructor
  · have hexponent : -s * ((g / 2 + τ) * auxiliaryLogLength B) ≤ Real.log B := by
      have hm := mul_nonneg hs (mul_nonneg (by linarith : 0 ≤ g / 2 + τ) hℓ)
      nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp
  · have hscoeff : s * (g / 2 - τ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show g / 2 - τ ≤ 1 by linarith) hs
      nlinarith
    have h := mul_le_mul_of_nonneg_right hscoeff hℓ
    have hexponent : s * ((g / 2 - τ) * auxiliaryLogLength B) ≤ Real.log B := by nlinarith
    exact (Real.exp_le_exp.mpr hexponent).trans_eq hexp

theorem tail_markov_multiplier_bound {B Y C : ℝ} (hB : 1 ≤ B) (hY : 1 ≤ Y) (hC : 0 ≤ C) :
    Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C)) ≤ B := by
  have hB0 : 0 < B := by linarith
  have hY0 : 0 < Y := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hdiv : B / Y ≤ B := div_le_self hB0.le hY
  have hlogdiv := Real.log_le_log (div_pos hB0 hY0) hdiv
  have hexponent : (1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log (B / Y) - C) ≤ Real.log B := by linarith
  exact (Real.exp_le_exp.mpr hexponent).trans_eq (Real.exp_log hB0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularityUnionBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite union bound for every failure of the regularity cutoff -/

namespace JointDickman

open Finset

theorem prefixViolationMass_nonneg (B L : ℕ) (τ : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ prefixViolationMass B L τ S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem tailViolationMass_nonneg (B : ℕ) (C : ℝ) (S : Finset ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ tailViolationMass B C S w := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs <;> linarith

theorem regularity_failure_union_bound {B L : ℕ} {τ C w : ℝ} (S : Finset ℕ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) (hw : 0 ≤ w)
    (hbad : ¬RegularPrimeSet B L τ C S) :
    w ≤ prefixViolationMass B L τ S w + tailViolationMass B C S w := by
  classical
  have hpnon := prefixViolationMass_nonneg B L τ S hw
  have htnon := tailViolationMass_nonneg B C S hw
  unfold RegularPrimeSet at hbad
  rcases not_and_or.mp hbad with hprefix | htail
  · obtain ⟨i, hi⟩ := not_forall.mp hprefix
    obtain ⟨hi, hbad_i⟩ := Classical.not_imp.mp hi
    have hsingle :
        (if ((primePrefix B ((i : ℝ) / L) S).card : ℝ) <
            (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then w else 0) +
        (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
            ((primePrefix B ((i : ℝ) / L) S).card : ℝ) then w else 0) ≤ prefixViolationMass B L τ S w := by
      apply single_le_sum (fun j _ => ?_) hi
      split_ifs <;> linarith
    rcases not_and_or.mp hbad_i with hlo | hhi
    · rw [ite_eq_left (lt_of_not_ge hlo)] at hsingle
      split_ifs at hsingle <;> linarith
    · rw [ite_eq_left (lt_of_not_ge hhi)] at hsingle
      split_ifs at hsingle <;> linarith
  · obtain ⟨i, hi⟩ := not_forall.mp htail
    have hfail := lt_of_not_ge hi
    have hY : 0 < primeTailEndpoint B i := by
      unfold primeTailEndpoint
      positivity
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hYi : primeTailEndpoint B i < B := by
      by_contra h
      have hBY : (B : ℝ) ≤ primeTailEndpoint B i := le_of_not_gt h
      have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr hBY
      have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
      linarith
    have hiB : i ∈ range B := mem_range.mpr (tail_endpoint_index_lt hlog hYi)
    have hsingle :
        (if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
            (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0) ≤
          tailViolationMass B C S w := by
      apply single_le_sum (fun j _ => ?_) hiB
      split_ifs <;> linarith
    rw [ite_eq_left hfail] at hsingle
    linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_TiltedCoefficientTriple
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential moments of the actual three-coefficient mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem tilted_coefficient_triple_le_sieved (B Z j b c : ℕ)
    (Q₁ Q₂ Q₃ : Finset ℕ) {s₁ s₂ s₃ : ℝ}
    (h₁ : Real.exp s₁ ≤ 2) (h₂ : Real.exp s₂ ≤ 2) (h₃ : Real.exp s₃ ≤ 2) :
    tiltedCoefficientWeight B Q₁ s₁ b * tiltedCoefficientWeight B Q₂ s₂ c *
      tiltedCoefficientWeight B Q₃ s₃ (b + j * c) ≤
    coefficientScale B ^ 3 * mixedThreeFormSieveWeight (sievePrimes Z)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂)
      (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c := by
  have h := mul_le_mul
    (mul_le_mul (tiltedCoefficientWeight_le_sieved B Z Q₁ h₁ b)
      (tiltedCoefficientWeight_le_sieved B Z Q₂ h₂ c)
      (tiltedCoefficientWeight_nonneg B Q₂ s₂ c)
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₁ h₁ p).1))))
    (tiltedCoefficientWeight_le_sieved B Z Q₃ h₃ (b + j * c))
    (tiltedCoefficientWeight_nonneg B Q₃ s₃ (b + j * c))
    (mul_nonneg
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₁ h₁ p).1)))
      (mul_nonneg (coefficientScale_nonneg B) (prod_nonneg (fun p _ =>
        residueWeight_nonneg _ _ (tiltedSieveTheta_bounds _ Q₂ h₂ p).1))))
  apply h.trans_eq
  simp only [mixedThreeFormSieveWeight, Nat.cast_add, Nat.cast_mul, prod_mul_distrib]
  ring

theorem tilted_density_normalization
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ B Z : ℕ, 1 < B → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      ∀ (Q₁ Q₂ Q₃ : Finset ℕ) (s₁ s₂ s₃ : ℝ),
      Real.exp s₁ ≤ 2 → Real.exp s₂ ≤ 2 → Real.exp s₃ ≤ 2 →
      coefficientScale B ^ 3 * (tiltedSieveDensity (auxiliaryCutoff B) Z Q₁ s₁ *
        tiltedSieveDensity (auxiliaryCutoff B) Z Q₂ s₂ * tiltedSieveDensity (auxiliaryCutoff B) Z Q₃ s₃) ≤
      M * Real.exp (((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁ +
        ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂ +
        ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃) := by
  obtain ⟨M, hM0, hnorm⟩ := coefficient_sieve_density_bound hM hδ
  refine ⟨M ^ 3 * Real.exp 12, by positivity, ?_⟩
  intro B Z hB hPZ hlog Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  let ρ := roughSieveDensity (auxiliaryCutoff B) Z
  let l₁ := ((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁
  let l₂ := ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂
  let l₃ := ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃
  have hd (Q : Finset ℕ) {s : ℝ} (hs : Real.exp s ≤ 2) : 0 ≤ tiltedSieveDensity (auxiliaryCutoff B) Z Q s := by
    unfold tiltedSieveDensity
    apply prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    apply sub_nonneg.mpr
    apply (div_le_one hp0).mpr
    linarith [(tiltedSieveTheta_bounds (auxiliaryCutoff B) Q hs p).1]
  have hρ := roughSieveDensity_nonneg (auxiliaryCutoff B) Z
  have hb₁ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₁ h₁
  have hb₂ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₂ h₂
  have hb₃ := tilted_sieve_density_bound (auxiliaryCutoff B) Z Q₃ h₃
  have hprod : tiltedSieveDensity (auxiliaryCutoff B) Z Q₁ s₁ *
      tiltedSieveDensity (auxiliaryCutoff B) Z Q₂ s₂ * tiltedSieveDensity (auxiliaryCutoff B) Z Q₃ s₃ ≤
      (ρ * Real.exp (l₁ + 4)) * (ρ * Real.exp (l₂ + 4)) * (ρ * Real.exp (l₃ + 4)) :=
    mul_le_mul (mul_le_mul hb₁ hb₂ (hd Q₂ h₂) (mul_nonneg hρ (Real.exp_pos _).le)) hb₃
      (hd Q₃ h₃) (mul_nonneg (mul_nonneg hρ (Real.exp_pos _).le) (mul_nonneg hρ (Real.exp_pos _).le))
  have hn := pow_le_pow_left₀ (mul_nonneg (coefficientScale_nonneg B) hρ) (hnorm B Z hB hPZ hlog) 3
  calc
    _ ≤ coefficientScale B ^ 3 * ((ρ * Real.exp (l₁ + 4)) * (ρ * Real.exp (l₂ + 4)) * (ρ * Real.exp (l₃ + 4))) :=
      mul_le_mul_of_nonneg_left hprod (pow_nonneg (coefficientScale_nonneg B) _)
    _ = (coefficientScale B * ρ) ^ 3 * Real.exp (l₁ + l₂ + l₃ + 12) := by
      have h12 : Real.exp (12 : ℝ) = Real.exp (4 : ℝ) ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      simp only [Real.exp_add, h12]
      ring
    _ ≤ M ^ 3 * Real.exp (l₁ + l₂ + l₃ + 12) :=
      mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

theorem tilted_coefficient_three_form_with_remainder
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (Q₁ Q₂ Q₃ : Finset ℕ) (s₁ s₂ s₃ : ℝ),
      Real.exp s₁ ≤ 2 → Real.exp s₂ ≤ 2 → Real.exp s₃ ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        tiltedCoefficientWeight B Q₁ s₁ b * tiltedCoefficientWeight B Q₂ s₂ c *
          tiltedCoefficientWeight B Q₃ s₃ (b + j * c)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (((Real.exp s₁ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₁ +
          ((Real.exp s₂ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₂ +
          ((Real.exp s₃ - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q₃) +
        coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hsieve⟩ := mixed_three_form_rectangle_sieve hFord hM
  obtain ⟨M, hM0, hnorm⟩ := tilted_density_normalization hM hδ
  refine ⟨C * M, by positivity, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  have hP (p : ℕ) (hp : p ∈ sievePrimes Z) : p.Prime ∧ p ≤ Z ∧ 6 ≤ p := by
    obtain ⟨hpZ, hp6⟩ := mem_filter.mp hp
    obtain ⟨hpZ, hpp⟩ := Nat.mem_primesLE.mp hpZ
    exact ⟨hpp, hpZ, hp6⟩
  have hs := hsieve (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
    (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃)
    j l₁ r₁ l₂ r₂ Z hj hI hJ hZ hP (fun p _ => tiltedSieveTheta_bounds _ Q₁ h₁ p)
      (fun p _ => tiltedSieveTheta_bounds _ Q₂ h₂ p) (fun p _ => tiltedSieveTheta_bounds _ Q₃ h₃ p)
  have hn := hnorm B Z hB hPZ hlog Q₁ Q₂ Q₃ s₁ s₂ s₃ h₁ h₂ h₃
  have ha : 0 ≤ C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (sub_nonneg.mpr (by exact_mod_cast hI)))
      (sub_nonneg.mpr (by exact_mod_cast hJ)))
      (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
  calc
    _ ≤ ∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂, coefficientScale B ^ 3 *
        mixedThreeFormSieveWeight (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
          (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c :=
      sum_le_sum (fun b _ => sum_le_sum (fun c _ => tilted_coefficient_triple_le_sieved B Z j b c Q₁ Q₂ Q₃ h₁ h₂ h₃))
    _ = coefficientScale B ^ 3 * (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        mixedThreeFormSieveWeight (sievePrimes Z) (tiltedSieveTheta (auxiliaryCutoff B) Q₁ s₁)
          (tiltedSieveTheta (auxiliaryCutoff B) Q₂ s₂) (tiltedSieveTheta (auxiliaryCutoff B) Q₃ s₃) j b c) := by
      simp_rw [mul_sum]
    _ ≤ coefficientScale B ^ 3 * _ := mul_le_mul_of_nonneg_left hs (pow_nonneg (coefficientScale_nonneg B) _)
    _ ≤ _ := by
      rw [mul_add]
      apply add_le_add (b := C * M * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j * _) ?_ le_rfl
      have h := mul_le_mul_of_nonneg_left hn ha
      convert h using 1 <;> first | (with_reducible_and_instances rfl) | (unfold tiltedSieveDensity at * <;> ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCountTail
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Markov bounds for prime counts in the actual coefficient sums -/

namespace JointDickman

open Finset

theorem weighted_exp_markov {α : Type*} (S : Finset α) (w N : α → ℝ) (s r : ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) :
    (∑ x ∈ S, if s * r ≤ s * N x then w x else 0) ≤
      Real.exp (-s * r) * ∑ x ∈ S, w x * Real.exp (s * N x) := by
  classical
  rw [mul_sum]
  apply sum_le_sum
  intro x hx
  have hwx := hw x hx
  by_cases h : s * r ≤ s * N x
  · rw [ite_eq_left h]
    have he : 1 ≤ Real.exp (-s * r) * Real.exp (s * N x) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    have hh := mul_le_mul_of_nonneg_left he (hw x hx)
    nlinarith
  · rw [ite_eq_right h]
    positivity

open Filter
open scoped Topology

theorem coefficient_form_exp_moment
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (Q : Finset ℕ) (s : ℝ), Real.exp s ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        tripleCoefficientWeight B j b c * Real.exp (s * triplePrimeCount k Q j b c)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
        coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  obtain ⟨C, hC, hb⟩ := tilted_coefficient_three_form_with_remainder hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s hs
  have hzero : Real.exp (0 : ℝ) ≤ 2 := by norm_num
  fin_cases k
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q s 0 0 hs hzero hzero
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q 0 s 0 hzero hs hzero
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h
  · have h := hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ Q Q Q 0 0 s hzero hzero hs
    simpa [tiltedCoefficientWeight, tripleCoefficientWeight, triplePrimeCount,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem coefficient_form_count_tail
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B Z j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ Z → auxiliaryCutoff B ≤ Z → δ * B ≤ Real.log Z →
      j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (Q : Finset ℕ) (s r : ℝ), Real.exp s ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ c ∈ Ico l₂ r₂,
        if s * r ≤ s * triplePrimeCount k Q j b c then tripleCoefficientWeight B j b c else 0) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        Real.exp (-s * r + ((Real.exp s - 1) / 2) * tiltPrimeReciprocalMass (auxiliaryCutoff B) Z Q) +
        Real.exp (-s * r) * coefficientScale B ^ 3 *
          (2 * (((r₁ : ℝ) - l₁) + ((r₂ : ℝ) - l₂) + 2 * Z) * (Z + 1 : ℝ) * (Z : ℝ) ^ 3) := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_exp_moment hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s r hs
  have hm := weighted_exp_markov ((Ico l₁ r₁) ×ˢ (Ico l₂ r₂))
    (fun bc => tripleCoefficientWeight B j bc.1 bc.2)
    (fun bc => triplePrimeCount k Q j bc.1 bc.2) s r
    (fun bc _ => mul_nonneg (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _))
      (coefficientWeight_nonneg _ _))
  rw [sum_product, sum_product] at hm
  have hh := hm.trans (mul_le_mul_of_nonneg_left
    (hb B Z j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k Q s hs) (Real.exp_pos _).le)
  apply hh.trans_eq
  rw [Real.exp_add]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientCountIndicators
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing regularity violations with the signed count events -/

namespace JointDickman

open Finset

theorem tripleCoefficientWeight_nonneg (B j b c : ℕ) : 0 ≤ tripleCoefficientWeight B j b c :=
  mul_nonneg (mul_nonneg (coefficientWeight_nonneg _ _) (coefficientWeight_nonneg _ _)) (coefficientWeight_nonneg _ _)

theorem tripleCoefficientWeight_eq_zero {k : Fin 3} {B j b c : ℕ}
    (h : coefficientForm k j b c = 0) : tripleCoefficientWeight B j b c = 0 := by
  fin_cases k <;> simp [coefficientForm] at h <;> simp [tripleCoefficientWeight, h]

open Classical in
theorem prefix_upper_indicator_le {B j b c : ℕ} (k : Fin 3) (g τ s : ℝ) (hs : 0 < s) :
    (if (g / 2 + τ) * auxiliaryLogLength B <
      ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ)
      then tripleCoefficientWeight B j b c else 0) ≤
    (if s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
      s * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_prefix_count (B := B) hn g
    by_cases hbad : (g / 2 + τ) * auxiliaryLogLength B <
        ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ)
    · have hm : s * ((g / 2 + τ) * auxiliaryLogLength B) ≤
          s * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c := by
        change _ ≤ s * (primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonneg_left hbad.le hs.le
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

open Classical in
theorem prefix_lower_indicator_le {B j b c : ℕ} (k : Fin 3) (g τ s : ℝ) (hs : 0 < s) :
    (if ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ) <
      (g / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b c else 0) ≤
    (if (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
      (-s) * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_prefix_count (B := B) hn g
    by_cases hbad : ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b c))).card : ℝ) <
        (g / 2 - τ) * auxiliaryLogLength B
    · have hm : (-s) * ((g / 2 - τ) * auxiliaryLogLength B) ≤
          (-s) * triplePrimeCount k (primePrefix B g (auxiliaryPrimes B)) j b c := by
        change _ ≤ (-s) * (primeDivisorCount (primePrefix B g (auxiliaryPrimes B)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonpos_left hbad.le (by linarith)
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

open Classical in
theorem tail_indicator_le {B j b c i : ℕ} (k : Fin 3) (C : ℝ) :
    (if (((coefficientPrimeSet B (coefficientForm k j b c)).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
      then tripleCoefficientWeight B j b c else 0) ≤
    (if (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
      (-(1 / 10 : ℝ)) * triplePrimeCount k
        ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) j b c
      then tripleCoefficientWeight B j b c else 0) := by
  by_cases hn : coefficientForm k j b c = 0
  · simp only [tripleCoefficientWeight_eq_zero hn, ite_self, le_refl]
  · have hcount := coefficient_tail_count (B := B) hn (primeTailEndpoint B i)
    by_cases hbad : (((coefficientPrimeSet B (coefficientForm k j b c)).filter
        (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C
    · have hm : (-(1 / 10 : ℝ)) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C) ≤
          (-(1 / 10 : ℝ)) * triplePrimeCount k
            ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) j b c := by
        change _ ≤ (-(1 / 10 : ℝ)) * (primeDivisorCount
          ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (coefficientForm k j b c) : ℝ)
        rw [← hcount]
        exact mul_le_mul_of_nonpos_left hbad.le (by norm_num)
      simp only [ite_eq_left hbad, ite_eq_left hm, le_refl]
    · rw [ite_eq_right hbad]
      split_ifs
      · exact tripleCoefficientWeight_nonneg _ _ _ _
      · rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientViolationBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted bounds for individual prefix and tail violations -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientRectangleRemainder_nonneg (B Z l₁ r₁ l₂ r₂ : ℕ)
    (hI : l₁ ≤ r₁) (hJ : l₂ ≤ r₂) : 0 ≤ coefficientRectangleRemainder B Z l₁ r₁ l₂ r₂ := by
  have hI' : (0 : ℝ) ≤ (r₁ : ℝ) - l₁ := sub_nonneg.mpr (by exact_mod_cast hI)
  have hJ' : (0 : ℝ) ≤ (r₂ : ℝ) - l₂ := sub_nonneg.mpr (by exact_mod_cast hJ)
  unfold coefficientRectangleRemainder
  have hs := coefficientScale_nonneg B
  positivity

theorem coefficient_prefix_pair_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (g τ s : ℝ), 0 < s → Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        ((if ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ) <
          (g / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b d else 0) +
        (if (g / 2 + τ) * auxiliaryLogLength B <
          ((primePrefix B g (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ)
          then tripleCoefficientWeight B j b d else 0))) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        (prefixLowerFactor B (δ / 8) g τ s + prefixUpperFactor B (δ / 8) g τ s) +
      (Real.exp (s * ((g / 2 - τ) * auxiliaryLogLength B)) +
        Real.exp (-s * ((g / 2 + τ) * auxiliaryLogLength B))) *
          coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k g τ s hs he hen
  have hlo := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    (primePrefix B g (auxiliaryPrimes B)) (-s) ((g / 2 - τ) * auxiliaryLogLength B) hen
  have hup := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    (primePrefix B g (auxiliaryPrimes B)) s ((g / 2 + τ) * auxiliaryLogLength B) he
  have hlow := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => prefix_lower_indicator_le (B := B) (j := j) (b := b) (c := d) k g τ s hs))).trans hlo
  have hupp := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => prefix_upper_indicator_le (B := B) (j := j) (b := b) (c := d) k g τ s hs))).trans hup
  simp only [neg_neg, mul_assoc] at hlow hupp
  simp only [sum_add_distrib]
  have h := add_le_add hlow hupp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [prefixLowerFactor, prefixUpperFactor, coefficientRectangleRemainder, mul_assoc]
  ring

theorem coefficient_tail_violation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (i : ℕ) (C₀ : ℝ),
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        if (((coefficientPrimeSet B (coefficientForm k j b d)).filter
          (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
            (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
          then tripleCoefficientWeight B j b d else 0) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j * tailChernoffFactor B i (δ / 8) C₀ +
      Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)) *
        coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hb⟩ := coefficient_form_count_tail hFord hM (by linarith : 0 < δ / 16)
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k i C₀
  have hen : Real.exp (-(1 / 10 : ℝ)) ≤ 2 := by
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 2 := by norm_num
  have h := hb B (sieveCutoff (δ / 8) B) j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k
    ((auxiliaryPrimes B).filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)) (-(1 / 10 : ℝ))
    ((2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀) hen
  have hh := (sum_le_sum (fun b _ => sum_le_sum (fun d _ => tail_indicator_le (B := B) (j := j) (b := b) (c := d) k C₀))).trans h
  simpa only [tailChernoffFactor, coefficientRectangleRemainder, neg_neg, mul_assoc] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_PrefixViolationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual prefix failures on a fixed grid -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem prefixGridError_nonneg (B L : ℕ) (c τ s : ℝ) :
    0 ≤ prefixGridError B L c τ s := by
  apply sum_nonneg
  intro i _
  exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem prefixGridError_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 10 ∧ Real.exp s ≤ 2 ∧ Real.exp (-s) ≤ 2 ∧
      ∀ (L : ℕ) (c : ℝ), 0 < L → 0 < c → c ≤ 4 →
        Tendsto (fun B => prefixGridError B L c τ s) atTop (𝓝 0) := by
  obtain ⟨s, hs, hs1, he, hen, hdec⟩ := actual_prefix_chernoff_decay hM hτ
  refine ⟨s, hs, hs1, he, hen, ?_⟩
  intro L c hL hc hc4
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlim := tendsto_finsetSum (Icc 1 L) (f := fun (i : ℕ) B =>
    prefixLowerFactor B c ((i : ℝ) / L) τ s +
      prefixUpperFactor B c ((i : ℝ) / L) τ s) (a := fun _ => (0 : ℝ)) (fun i hi => by
        have hi' := mem_Icc.mp hi
        have hip : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
        have hil : (i : ℝ) ≤ L := by exact_mod_cast hi'.2
        have hh := hdec c ((i : ℝ) / L) hc hc4 (div_pos hip hL')
          ((div_le_one hL').mpr hil)
        simpa using hh.2.add hh.1)
  simpa only [prefixGridError, sum_const_zero] using hlim

/-- Finite summation of a common main factor and uniformly bounded remainders. -/
theorem sum_le_linear_remainder {ι : Type*} (S : Finset ι)
    (f t r : ι → ℝ) {A E R : ℝ} (hE : 0 ≤ E)
    (hf : ∀ i ∈ S, f i ≤ A * t i + r i * E)
    (hr : ∀ i ∈ S, r i ≤ R) :
    (∑ i ∈ S, f i) ≤ A * (∑ i ∈ S, t i) + (S.card : ℝ) * R * E := by
  calc
    _ ≤ ∑ i ∈ S, (A * t i + R * E) := sum_le_sum (fun i hi =>
      (hf i hi).trans (add_le_add_right (mul_le_mul_of_nonneg_right (hr i hi) hE) _))
    _ = _ := by simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] <;> ring

theorem coefficient_prefix_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      ∀ (k : Fin 3) (L : ℕ) (τ s : ℝ), 0 < L → 0 ≤ τ → 0 < s → s ≤ 1 →
      Real.exp s ≤ 2 → Real.exp (-s) ≤ 2 →
      0 ≤ auxiliaryLogLength B → auxiliaryLogLength B ≤ Real.log B →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        prefixGridError B L (δ / 8) τ s +
      2 * L * B * coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hbound⟩ := coefficient_prefix_pair_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k L τ s hL hτ hs hs1 he hen hℓ hℓlog
  let f := fun i b d =>
    ((if ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ) <
      (((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B then tripleCoefficientWeight B j b d else 0) +
    (if (((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B <
      ((primePrefix B ((i : ℝ) / L) (coefficientPrimeSet B (coefficientForm k j b d))).card : ℝ)
      then tripleCoefficientWeight B j b d else 0))
  have hswap : (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ Icc 1 L, f i b d) =
      ∑ i ∈ Icc 1 L, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d := by
    calc
      _ = ∑ b ∈ Ico l₁ r₁, ∑ i ∈ Icc 1 L, ∑ d ∈ Ico l₂ r₂, f i b d :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  change (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ Icc 1 L, f i b d) ≤ _
  rw [hswap]
  have hE := coefficientRectangleRemainder_nonneg B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ hI hJ
  have hsum := sum_le_linear_remainder (Icc 1 L)
    (fun i => ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d)
    (fun i => prefixLowerFactor B (δ / 8) ((i : ℝ) / L) τ s +
      prefixUpperFactor B (δ / 8) ((i : ℝ) / L) τ s)
    (fun i => Real.exp (s * ((((i : ℝ) / L) / 2 - τ) * auxiliaryLogLength B)) +
      Real.exp (-s * ((((i : ℝ) / L) / 2 + τ) * auxiliaryLogLength B)))
    (R := 2 * B) hE
    (fun i _ => hbound B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k ((i : ℝ) / L) τ s hs he hen)
    (fun i hi => by
      have hi' := mem_Icc.mp hi
      have hL' : (0 : ℝ) < L := by exact_mod_cast hL
      have hg : 0 ≤ (i : ℝ) / L := div_nonneg (Nat.cast_nonneg _) hL'.le
      have hg1 : (i : ℝ) / L ≤ 1 := (div_le_one hL').mpr (by exact_mod_cast hi'.2)
      have hh := prefix_markov_multiplier_bounds (by omega : 1 ≤ B) hg hg1 hτ hs.le hs1 hℓ hℓlog
      linarith)
  convert hsum using 1
  all_goals try with_reducible_and_instances rfl
  simp only [prefixGridError, Nat.card_Icc, Nat.add_sub_cancel]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_TailViolationSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic summation of the actual tail failures -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem tailViolationMass_eq_restricted {B : ℕ} {C : ℝ} (S : Finset ℕ) (w : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    tailViolationMass B C S w = ∑ i ∈ activeTailIndices B,
      if ((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C then w else 0 := by
  classical
  unfold tailViolationMass activeTailIndices
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : primeTailEndpoint B i < B
  · simp only [hi, ite_true, if_true]
  · have hY : 0 < primeTailEndpoint B i := by unfold primeTailEndpoint; positivity
    have hdiv : (B : ℝ) / primeTailEndpoint B i ≤ 1 := (div_le_one hY).mpr (le_of_not_gt hi)
    have hlog' := Real.log_nonpos (div_nonneg (Nat.cast_nonneg B) hY.le) hdiv
    have hcount : (0 : ℝ) ≤ (S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card :=
      Nat.cast_nonneg _
    have hnot : ¬((S.filter (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
        (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C := by linarith
    simp only [hi, hnot, ite_false, if_false]

theorem coefficient_tail_sum_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ B j l₁ r₁ l₂ r₂ : ℕ,
      1 < B → 2 ≤ sieveCutoff (δ / 8) B → auxiliaryCutoff B ≤ sieveCutoff (δ / 8) B →
      (δ / 16) * B ≤ Real.log (sieveCutoff (δ / 8) B) → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
      1 ≤ Real.log (auxiliaryCutoff B) → ∀ (k : Fin 3) (C₀ : ℝ), 0 ≤ C₀ →
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        tailViolationMass B C₀ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) ≤
      C * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
        (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C₀) +
      (B : ℝ)^2 * coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ := by
  classical
  obtain ⟨C, hC, hbound⟩ := coefficient_tail_violation_bound hFord hM hδ
  refine ⟨C, hC, ?_⟩
  intro B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ hlogP k C₀ hC₀
  let f := fun i b d =>
    if (((coefficientPrimeSet B (coefficientForm k j b d)).filter
      (fun p : ℕ => primeTailEndpoint B i < Real.log p)).card : ℝ) <
      (2 / 5 : ℝ) * Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀
      then tripleCoefficientWeight B j b d else 0
  have heq : (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
      tailViolationMass B C₀ (coefficientPrimeSet B (coefficientForm k j b d))
        (tripleCoefficientWeight B j b d)) =
      ∑ i ∈ activeTailIndices B, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d := by
    simp_rw [tailViolationMass_eq_restricted _ _ hC₀ hlogP]
    change (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ i ∈ activeTailIndices B, f i b d) = _
    calc
      _ = ∑ b ∈ Ico l₁ r₁, ∑ i ∈ activeTailIndices B, ∑ d ∈ Ico l₂ r₂, f i b d :=
        sum_congr rfl (fun _ _ => sum_comm)
      _ = _ := sum_comm
  rw [heq]
  have hE := coefficientRectangleRemainder_nonneg B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂ hI hJ
  have hsum := sum_le_linear_remainder (activeTailIndices B)
    (fun i => ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, f i b d)
    (fun i => tailChernoffFactor B i (δ / 8) C₀)
    (fun i => Real.exp ((1 / 10 : ℝ) * ((2 / 5 : ℝ) *
      Real.log ((B : ℝ) / primeTailEndpoint B i) - C₀)))
    (R := B) hE
    (fun i _ => hbound B j l₁ r₁ l₂ r₂ hB hZ hPZ hlog hj hI hJ k i C₀)
    (fun i _ => by
      apply tail_markov_multiplier_bound (by exact_mod_cast (by omega : 1 ≤ B)) _ hC₀
      have hp : (1 : ℝ) ≤ (2 : ℝ)^i := one_le_pow₀ (by norm_num)
      exact one_le_mul_of_one_le_of_one_le hp hlogP)
  apply hsum.trans
  apply add_le_add_right
  have hcard : ((activeTailIndices B).card : ℝ) ≤ B := by
    exact_mod_cast (calc (activeTailIndices B).card ≤ (range B).card := card_filter_le _ _
                        _ = B := card_range B)
  have hh := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg B)
  have hh' := mul_le_mul_of_nonneg_right hh hE
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing mass discarded by the coefficient regularity cutoff -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem regularityRemainder_nonneg (B L : ℕ) : 0 ≤ regularityRemainder B L := by
  unfold regularityRemainder
  positivity

theorem regularityRemainder_tendsto (L : ℕ) :
    Tendsto (fun B => regularityRemainder B L) atTop (𝓝 0) := by
  have h₉ : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (9 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have h₈ : Tendsto (fun B : ℕ => (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun B : ℕ => (2 * (L : ℝ)) / (B : ℝ)^9 + (1 : ℝ) / (B : ℝ)^8) atTop (𝓝 0) := by
    simpa using h₉.add h₈
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with B hB
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  unfold regularityRemainder
  field_simp [hB0]

theorem discardedCoefficientWeight_le (B L j b d : ℕ) (τ C : ℝ)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log (auxiliaryCutoff B)) :
    discardedCoefficientWeight B L j b d τ C ≤ ∑ k : Fin 3,
      (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) := by
  classical
  have hw := tripleCoefficientWeight_nonneg B j b d
  have hn (k : Fin 3) := add_nonneg
    (prefixViolationMass_nonneg B L τ (coefficientPrimeSet B (coefficientForm k j b d)) hw)
    (tailViolationMass_nonneg B C (coefficientPrimeSet B (coefficientForm k j b d)) hw)
  unfold discardedCoefficientWeight
  split_ifs with h
  · exact sum_nonneg (fun k _ => hn k)
  · obtain ⟨k, hk⟩ := not_forall.mp h
    exact (regularity_failure_union_bound _ hC hlog hw hk).trans
      (single_le_sum (fun i _ => hn i) (mem_univ k))

/-- The positive-slope rectangle form of manuscript (9). Its error sequence
is independent of the tail cutoff, slope, and rectangle location. -/
theorem coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (j l₁ r₁ l₂ r₂ : ℕ),
          0 ≤ C → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
          Real.exp (δ * B) ≤ (r₁ : ℝ) - l₁ → Real.exp (δ * B) ≤ (r₂ : ℝ) - l₂ →
          (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, discardedCoefficientWeight B L j b d τ C) ≤
            K * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j *
              (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨Cp, hCp, hp⟩ := coefficient_prefix_sum_bound hFord hM hδ
  obtain ⟨Ct, hCt, ht⟩ := coefficient_tail_sum_bound hFord hM hδ
  obtain ⟨D, hD, htail⟩ := actual_tail_chernoff_sum hM (by linarith : 0 < δ / 8)
    (by linarith : δ / 8 ≤ 4)
  let K₀ := Cp + Ct * D + 1
  have hK₀ : 0 < K₀ := by dsimp [K₀] <;> positivity
  refine ⟨3 * K₀, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨s, hs, hs1, he, hen, hprefix⟩ := prefixGridError_tendsto hM hτ
  let ε := fun B => prefixGridError B L (δ / 8) τ s + regularityRemainder B L
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (hprefix L (δ / 8) hL (by linarith) (by linarith)).add
      (regularityRemainder_tendsto L)
  refine ⟨ε, fun B => add_nonneg (prefixGridError_nonneg ..) (regularityRemainder_nonneg ..), hε, ?_⟩
  have hloglarge : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (auxiliaryCutoff B) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)).eventually_ge_atTop 1
  filter_upwards [sieveCutoff_eventually (by linarith : 0 < δ / 8), htail,
    auxiliaryLogLength_between, coefficient_rectangle_remainder_power hδ,
    hloglarge, eventually_gt_atTop 1] with B hcut htailB hℓ hrem hlog hB
  intro C j l₁ r₁ l₂ r₂ hC hj hI hJ hlen₁ hlen₂
  let A := ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j
  let E := coefficientRectangleRemainder B (sieveCutoff (δ / 8) B) l₁ r₁ l₂ r₂
  have hlen₁0 : 0 ≤ (r₁ : ℝ) - l₁ := (Real.exp_pos _).le.trans hlen₁
  have hlen₂0 : 0 ≤ (r₂ : ℝ) - l₂ := (Real.exp_pos _).le.trans hlen₂
  have hsig := singularFactor_one_le (by norm_num : (0 : ℝ) ≤ 24) j
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg hlen₁0 hlen₂0) (by linarith)
  have hCpA : 0 ≤ Cp * A := mul_nonneg hCp.le hA
  have hCtA : 0 ≤ Ct * A := mul_nonneg hCt.le hA
  have hremE : (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤ A * regularityRemainder B L := by
    have hE : E ≤ (((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂)) / (B : ℝ)^10 := hrem _ _ hlen₁ hlen₂
    have hprod : ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) ≤ A :=
      le_mul_of_one_le_right (mul_nonneg hlen₁0 hlen₂0) hsig
    have hdiv := div_le_div_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ (B : ℝ)^10)
    have hh := mul_le_mul_of_nonneg_left (hE.trans hdiv)
      (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) * B + (B : ℝ)^2)
    simpa only [regularityRemainder, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have htail' := htailB (activeTailIndices B) C (fun i hi => (mem_filter.mp hi).2.le)
  have hsingle (k : Fin 3) :
      (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d))) ≤
      K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
    have hpb := hp B j l₁ r₁ l₂ r₂ hB hcut.1 hcut.2.1
      (by linarith only [hcut.2.2.1]) hj hI hJ k L τ s hL hτ.le hs
        (by linarith only [hs1]) he hen hℓ.1 hℓ.2
    have htb := ht B j l₁ r₁ l₂ r₂ hB hcut.1 hcut.2.1
      (by linarith only [hcut.2.2.1]) hj hI hJ hlog k C hC
    have hsum := add_le_add hpb htb
    simp_rw [← sum_add_distrib] at hsum
    have htb' := mul_le_mul_of_nonneg_left htail' hCtA
    have hmain :
        Cp * A * prefixGridError B L (δ / 8) τ s +
        Ct * A * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C) +
        (2 * (L : ℝ) * B + (B : ℝ)^2) * E ≤
        Cp * A * prefixGridError B L (δ / 8) τ s +
        (Ct * D) * A * Real.exp (-(1 / 10 : ℝ) * C) + A * regularityRemainder B L := by
      nlinarith only [htb', hremE]
    have hCpK : Cp ≤ K₀ := by dsimp [K₀]; linarith only [mul_pos hCt hD]
    have hCtK : Ct * D ≤ K₀ := by dsimp [K₀]; linarith only [hCp]
    have h1K : 1 ≤ K₀ := by dsimp [K₀]; linarith only [hCp, mul_pos hCt hD]
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpK hA)
      (prefixGridError_nonneg B L (δ / 8) τ s)
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtK hA)
      (Real.exp_pos (-(1 / 10 : ℝ) * C)).le
    have h₃ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1K hA)
      (regularityRemainder_nonneg B L)
    have hfinal := add_le_add (add_le_add h₁ h₂) h₃
    calc
      _ ≤ Cp * A * prefixGridError B L (δ / 8) τ s +
          Ct * A * (∑ i ∈ activeTailIndices B, tailChernoffFactor B i (δ / 8) C) +
          (2 * (L : ℝ) * B + (B : ℝ)^2) * E := by
        convert hsum using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [A, E]
        ring
      _ ≤ _ := hmain
      _ ≤ K₀ * A * prefixGridError B L (δ / 8) τ s +
          K₀ * A * Real.exp (-(1 / 10 : ℝ) * C) + K₀ * A * regularityRemainder B L := by
        simpa only [one_mul] using hfinal
      _ = K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by dsimp only [ε] <;> ring
  calc
    _ ≤ ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ k : Fin 3,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) :=
      sum_le_sum (fun b _ => sum_le_sum (fun d _ => discardedCoefficientWeight_le B L j b d τ C hC hlog))
    _ = ∑ k : Fin 3, ∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂,
        (prefixViolationMass B L τ (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d) +
        tailViolationMass B C (coefficientPrimeSet B (coefficientForm k j b d))
          (tripleCoefficientWeight B j b d)) := by
      rw [show (∑ b ∈ Ico l₁ r₁, ∑ d ∈ Ico l₂ r₂, ∑ k : Fin 3, _) =
        ∑ b ∈ Ico l₁ r₁, ∑ k : Fin 3, ∑ d ∈ Ico l₂ r₂, _ from
          sum_congr rfl (fun _ _ => sum_comm)]
      exact sum_comm
    _ ≤ ∑ _k : Fin 3, K₀ * A * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) :=
      sum_le_sum (fun k _ => hsingle k)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [A] <;> ring

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

theorem signedSplitProductMass_coefficient_bound
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in Filter.atTop,
      ∀ (g : Finset ℕ → ℝ), (∀ S ⊆ auxiliaryPrimes B, |g S| ≤ 1) →
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) →
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        C*coefficientWeight B n/((B : ℝ)*n) := by
  obtain ⟨C,hC,hbound⟩ := primeProductMass_coefficient_domination hM
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with B hboundB
  intro g hg n hn hsize
  exact (signedSplitProductMass_abs_le (auxiliaryPrimes_prime B) hg n).trans
    (hboundB n hn hsize)

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_SmoothDyadicPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A concrete smooth geometric partition of unity -/

namespace JointDickman
open Finset
open scoped SchwartzMap

theorem dyadicPartitionWeight_zero {x : ℝ} (hx : x ≤ 1/2 ∨ 2 < x) :
    dyadicPartitionWeight x = 0 := by
  unfold dyadicPartitionWeight
  rcases hx with h | h
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith),sub_self]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith),sub_self]

theorem dyadicPartitionWeight_bounds (x : ℝ) :
    0 ≤ dyadicPartitionWeight x ∧ dyadicPartitionWeight x ≤ 1 := by
  by_cases hx : x ≤ 1/2
  · rw [dyadicPartitionWeight_zero (Or.inl hx)]
    norm_num
  · have hx0 : 0 ≤ x := by linarith
    unfold dyadicPartitionWeight
    have hm := Real.smoothTransition.monotone (show 2-2*x ≤ 2-x by linarith)
    have h0 := Real.smoothTransition.nonneg (2-2*x)
    have h1 := Real.smoothTransition.le_one (2-x)
    constructor <;> linarith

theorem dyadicPartition_step (z : ℝ) (k : ℕ) :
    dyadicPartitionWeight (z/(2 : ℝ)^(k+1)) =
      Real.smoothTransition (2-z/(2 : ℝ)^(k+1))-
        Real.smoothTransition (2-z/(2 : ℝ)^k) := by
  unfold dyadicPartitionWeight
  have he : 2*(z/(2 : ℝ)^(k+1)) = z/(2 : ℝ)^k := by rw [pow_succ]; field_simp
  rw [he]

theorem dyadicPartition_sum {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ Ico L U, dyadicPartitionWeight (z/(2 : ℝ)^(k+1))) = 1 := by
  simp_rw [dyadicPartition_step]
  rw [sum_Ico_sub (fun k => Real.smoothTransition (2-z/(2 : ℝ)^k)) hLU]
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  norm_num

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationTensorProfile
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual amplification weight in normalized geometric-box coordinates -/

namespace JointDickman
open scoped Topology

theorem amplificationSpatialProfile_bounds (x y z : ℝ) :
    0 ≤ amplificationSpatialProfile x y z ∧ amplificationSpatialProfile x y z ≤ 1 := by
  obtain ⟨ha,ha'⟩ := amplificationBump_bounds (x/z)
  obtain ⟨hb,hb'⟩ := amplificationBump_bounds (y/z)
  obtain ⟨hc,hc'⟩ := dyadicPartitionWeight_bounds z
  exact ⟨mul_nonneg (mul_nonneg ha hb) hc,
    (mul_le_mul (mul_le_mul ha' hb' hb zero_le_one) hc' hc (by norm_num)).trans_eq (by ring)⟩

theorem amplificationSpatialProfile_support {x y z : ℝ}
    (h : amplificationSpatialProfile x y z ≠ 0) : x ∈ Set.Icc (1/2 : ℝ) 4 ∧ y ∈ Set.Icc (1/2 : ℝ) 4 ∧
      z ∈ Set.Icc (1/2 : ℝ) 2 := by
  have hprod : amplificationBump (x/z)*amplificationBump (y/z) ≠ 0 :=
    left_ne_zero_of_mul h
  have hx := amplificationBump_support (left_ne_zero_of_mul hprod)
  have hy := amplificationBump_support (right_ne_zero_of_mul hprod)
  have hz : dyadicPartitionWeight z ≠ 0 := right_ne_zero_of_mul h
  have hzlo : (1/2 : ℝ) < z := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inl (le_of_not_gt hn)))
  have hzhi : z ≤ 2 := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inr (lt_of_not_ge hn)))
  have hzpos : 0 < z := by linarith
  have hxb : x ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hx.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hx.2
      nlinarith
  have hyb : y ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hy.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hy.2
      nlinarith
  exact ⟨hxb,hyb,⟨hzlo.le,hzhi⟩⟩

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

theorem geometric_dyadic_partition {L U : ℕ} (hLU : L ≤ U) (z : ℝ)
    (hlo : 2 ≤ z/(2 : ℝ)^L) (hhi : z/(2 : ℝ)^U ≤ 1) :
    (∑ k ∈ dyadicBoxIndices L U, dyadicPartitionWeight (z/Real.exp ((k : ℝ)*Real.log 2))) = 1 := by
  classical
  rw [dyadicBoxIndices,sum_image]
  · simpa only [Int.cast_natCast,exp_nat_log_two] using dyadicPartition_sum hLU z hlo hhi
  · intro a _ b _ h
    exact Nat.add_right_cancel (Int.ofNat_inj.mp h)

theorem amplificationBoxWeight_normalized (B : ℕ) {T N c : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hc : 0 < c) (a b : ℝ) :
    amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) =
      amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c))*dyadicPartitionWeight (c/(N/T)) := by
  have hX := div_pos hN hT
  have hlog : Real.log (N/T)/B+Real.log (c/(N/T))/B = Real.log c/B := by
    rw [Real.log_div hc.ne' hX.ne']
    ring
  have ha : (a/N)/(c/(N/T)) = a/(T*c) := by field_simp
  have hb : (b/N)/(c/(N/T)) = b/(T*c) := by field_simp
  simp only [amplificationBoxWeight,amplificationSpatialProfile,hlog,ha,hb]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationBoxSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact support of the amplification integrand in each geometric box -/

namespace JointDickman
open Finset

theorem mem_tensor_interval_of_ratio {n : ℕ} {N : ℝ} (hN : 0 < N)
    (hn : (n : ℝ)/N ∈ Set.Icc (1/2 : ℝ) 4) :
    n ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hlo := (le_div_iff₀ hN).mp hn.1
  have hhi := (div_le_iff₀ hN).mp hn.2
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (show 0 ≤ (1/4 : ℝ)*N by positivity)).mpr
    nlinarith
  · apply (Nat.le_floor_iff (show 0 ≤ (17/4 : ℝ)*N by positivity)).mpr
    nlinarith

theorem amplificationBoxWeight_integer_support (B : ℕ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (s : ℝ) (a b c : ℕ)
    (hw : amplificationBoxWeight B s (a/N) (b/N) (c/(N/T)) ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  obtain ⟨ha,hb,hc⟩ := amplificationSpatialProfile_support (right_ne_zero_of_mul hw)
  exact ⟨mem_tensor_interval_of_ratio (div_pos hN hT) ⟨hc.1,hc.2.trans (by norm_num)⟩,
    mem_tensor_interval_of_ratio hN ha,mem_tensor_interval_of_ratio hN hb⟩

theorem amplificationBoxTerm_support (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationBoxTerm B j T N g h c b a ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hw : amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) ≠ 0 := by
    intro hz
    apply hf
    simp only [amplificationBoxTerm,hz,mul_zero,ite_self]
  obtain ⟨hc,ha,hb⟩ := amplificationBoxWeight_integer_support B hT hN _ a b c hw
  exact ⟨hc,hb,ha⟩

theorem amplificationBoxTerm_eq (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationBoxTerm B j T N g h c b a =
      amplificationArithmeticTerm B j T g h c b a*dyadicPartitionWeight (c/(N/T)) := by
  by_cases hc : c = 0
  · simp [amplificationBoxTerm,amplificationArithmeticTerm,hc,coefficientWeight]
  · have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
    unfold amplificationBoxTerm amplificationArithmeticTerm
    rw [amplificationBoxWeight_normalized B hT hN hcpos]
    split_ifs <;> ring


theorem amplificationArithmeticTerm_log_support {B : ℕ} (hB : 0 < B) (j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationArithmeticTerm B j T g h c b a ≠ 0) :
    (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B := by
  have hne : amplificationBump (Real.log c/B) ≠ 0 := by
    intro hz
    apply hf
    simp [amplificationArithmeticTerm,hz]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := amplificationBump_support hne
  have hlo := (lt_div_iff₀ hBr).mp hh.1
  have hhi := (div_lt_iff₀ hBr).mp hh.2
  constructor <;> nlinarith

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationDyadicIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact reconstruction of the unpartitioned amplification triple sum -/

namespace JointDickman
open Finset

theorem sum_triple_interchange {ι α β : Type*} (S : Finset ι) (A : Finset α) (C : Finset β)
    (f : ι → β → α → α → ℝ) :
    (∑ k ∈ S, ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, f k c b a) =
      ∑ c ∈ C, ∑ b ∈ A, ∑ a ∈ A, ∑ k ∈ S, f k c b a := by
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  exact sum_comm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SignedCoefficientSums
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact sign reversal for the coefficient relation a - b = jc -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientRelationWeight_neg (B : ℕ) (j : ℤ) (a b c : ℕ) :
    coefficientRelationWeight B (-j) a b c = coefficientRelationWeight B j b a c := by
  have hh : ((a : ℤ) = b + -j * c) ↔ ((b : ℤ) = a + j * c) := by constructor <;> intro h <;> linarith
  unfold coefficientRelationWeight
  simp only [hh]
  split_ifs <;> ring

theorem coefficientRelationWeight_nat (B j a b c : ℕ) :
    coefficientRelationWeight B (j : ℤ) a b c =
      if a = b + j * c then tripleCoefficientWeight B j b c else 0 := by
  have hh : ((a : ℤ) = b + (j : ℤ) * c) ↔ a = b + j * c := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.cast_inj]
  unfold coefficientRelationWeight
  simp only [hh]
  split_ifs with h
  · rw [h]
    unfold tripleCoefficientWeight
    ring
  · rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss on the signed coefficient support -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem coefficientTripleRegular_swap (B L : ℕ) (τ C : ℝ) (a b c : ℕ) :
    coefficientTripleRegular B L τ C a b c ↔ coefficientTripleRegular B L τ C b a c := by
  simp only [coefficientTripleRegular, and_left_comm]

theorem coefficientForm_regular_iff (B L j b c : ℕ) (τ C : ℝ) :
    (∀ k : Fin 3, RegularPrimeSet B L τ C (coefficientPrimeSet B (coefficientForm k j b c))) ↔
      coefficientTripleRegular B L τ C (b + j * c) b c := by
  constructor
  · intro h
    exact ⟨by simpa [coefficientForm] using h 2,
      by simpa [coefficientForm] using h 0, by simpa [coefficientForm] using h 1⟩
  · rintro ⟨ha, hb, hc⟩ k
    fin_cases k <;> simpa [coefficientForm] using (by assumption)

theorem discardedRelationWeight_neg (B L : ℕ) (τ C : ℝ) (j : ℤ) (a b c : ℕ) :
    discardedRelationWeight B L τ C (-j) a b c = discardedRelationWeight B L τ C j b a c := by
  by_cases h : coefficientTripleRegular B L τ C a b c
  · have h' := (coefficientTripleRegular_swap B L τ C a b c).mp h
    simp only [discardedRelationWeight, h, h', ite_true, if_true]
  · have h' := (coefficientTripleRegular_swap B L τ C a b c).not.mp h
    simp only [discardedRelationWeight, h, h', ite_false, if_false, coefficientRelationWeight_neg]

theorem signedDiscardedCoefficientMass_neg (B L : ℕ) (τ C : ℝ) (j : ℤ) (I J : Finset ℕ) :
    signedDiscardedCoefficientMass B L τ C (-j) I J = signedDiscardedCoefficientMass B L τ C j I J := by
  unfold signedDiscardedCoefficientMass
  simp_rw [discardedRelationWeight_neg]
  exact sum_comm

theorem discardedRelationWeight_nat (B L j a b c : ℕ) (τ C : ℝ) :
    discardedRelationWeight B L τ C (j : ℤ) a b c =
      if a = b + j * c then discardedCoefficientWeight B L j b c τ C else 0 := by
  classical
  unfold discardedRelationWeight
  rw [coefficientRelationWeight_nat]
  by_cases h : a = b + j * c
  · subst a
    simp only [ite_true, if_true, discardedCoefficientWeight, coefficientForm_regular_iff]
  · simp only [h, ite_false, if_false, ite_self]

theorem discardedCoefficientWeight_nonneg (B L j b c : ℕ) (τ C : ℝ) :
    0 ≤ discardedCoefficientWeight B L j b c τ C := by
  unfold discardedCoefficientWeight
  split_ifs
  · rfl
  · exact tripleCoefficientWeight_nonneg ..

theorem signedDiscardedCoefficientMass_nat_le (B L j : ℕ) (τ C : ℝ) (I J : Finset ℕ) :
    signedDiscardedCoefficientMass B L τ C (j : ℤ) I J ≤
      ∑ b ∈ I, ∑ c ∈ J, discardedCoefficientWeight B L j b c τ C := by
  classical
  unfold signedDiscardedCoefficientMass
  rw [sum_comm]
  apply sum_le_sum
  intro b _
  rw [sum_comm]
  apply sum_le_sum
  intro c _
  simp_rw [discardedRelationWeight_nat]
  rw [sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact discardedCoefficientWeight_nonneg ..

/-- Manuscript (9) on the actual signed support a - b = jc. -/
theorem signed_coefficient_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {δ : ℝ} (hδ : 0 < δ) (hδ32 : δ ≤ 32) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (j : ℤ) (l₁ r₁ l₂ r₂ : ℕ),
          0 ≤ C → j ≠ 0 → l₁ ≤ r₁ → l₂ ≤ r₂ →
          Real.exp (δ * B) ≤ (r₁ : ℝ) - l₁ → Real.exp (δ * B) ≤ (r₂ : ℝ) - l₂ →
          signedDiscardedCoefficientMass B L τ C j (Ico l₁ r₁) (Ico l₂ r₂) ≤
            K * ((r₁ : ℝ) - l₁) * ((r₂ : ℝ) - l₂) * singularFactor 24 j.natAbs *
              (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  obtain ⟨K, hK, hbound⟩ := coefficient_regularity_loss hFord hM hδ hδ32
  refine ⟨K, hK, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε, hlim, hevent⟩ := hbound L τ hL hτ
  refine ⟨ε, hε, hlim, ?_⟩
  filter_upwards [hevent] with B hB
  intro C j l₁ r₁ l₂ r₂ hC hj hI hJ hlen₁ hlen₂
  have hh := (signedDiscardedCoefficientMass_nat_le B L j.natAbs τ C (Ico l₁ r₁) (Ico l₂ r₂)).trans
    (hB C j.natAbs l₁ r₁ l₂ r₂ hC (Int.natAbs_ne_zero.mpr hj) hI hJ hlen₁ hlen₂)
  rcases Int.natAbs_eq j with hsign | hsign
  · simpa only [← hsign] using hh
  · rw [hsign, signedDiscardedCoefficientMass_neg]
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedLocalRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local regularity loss for the actual signed endpoint weights -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem signed_local_regularity_domination
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ L j : ℕ, ∀ τ C : ℝ,
      ∀ X : ℝ, 0 < X → ∀ I J : Finset ℕ,
      (∀ n ∈ I, X ≤ n ∧ (n : ℝ) ≤ Real.exp ((16/5 : ℝ)*B)) →
      ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ∀ W : ℕ → ℕ → ℕ → ℝ, (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ J, |W a b c| ≤ 1) →
      signedLocalRegularityError B L j τ C I J g h W ≤
        (K^2/((B : ℝ)*X^2))*signedDiscardedCoefficientMass B L τ C j I J := by
  obtain ⟨K,hK,hbound⟩ := signedSplitProductMass_coefficient_bound hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop 0] with B hb hB
  intro L j τ C X hX I J hI g h hg hh W hW
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hBX : 0 < (B : ℝ)*X := mul_pos hBr hX
  have htest (f : (auxiliaryPrimes B → Bool) → ℝ) (hf : ∀ x, |f x| ≤ 1)
      (n : ℕ) (hn : n ∈ I) :
      |signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) f) n| ≤
        (K/((B : ℝ)*X))*coefficientWeight B n := by
    have hnpos : 0 < n := by exact_mod_cast (hX.trans_le (hI n hn).1)
    have hh := hb (subsetSiteTest (auxiliaryPrimes B) f) (fun S _ => hf _) n hnpos (hI n hn).2
    calc
      _ ≤ K*coefficientWeight B n/((B : ℝ)*n) := hh
      _ ≤ K*coefficientWeight B n/((B : ℝ)*X) :=
        div_le_div_of_nonneg_left (mul_nonneg hK.le (coefficientWeight_nonneg _ _)) hBX
          (mul_le_mul_of_nonneg_left (hI n hn).1 hBr.le)
      _ = _ := by ring
  unfold signedLocalRegularityError signedDiscardedCoefficientMass
  rw [mul_sum]
  apply sum_le_sum
  intro a ha
  rw [mul_sum]
  apply sum_le_sum
  intro b hbI
  rw [mul_sum]
  apply sum_le_sum
  intro c hc
  by_cases hrel : a = b+j*c
  · by_cases hreg : coefficientTripleRegular B L τ C a b c
    · simp only [hreg,not_true_eq_false,and_false,ite_false, if_false,discardedRelationWeight,
        ite_true, if_true,mul_zero]
      exact le_rfl
    · rw [ite_eq_left ⟨hrel,hreg⟩,discardedRelationWeight,ite_eq_right hreg,
        coefficientRelationWeight_nat,ite_eq_left hrel]
      have hga := htest g hg a ha
      have hhb := htest h hh b hbI
      have hA := coefficientWeight_nonneg B a
      have hD := coefficientWeight_nonneg B b
      have hC := coefficientWeight_nonneg B c
      have hpair := mul_le_mul hga hhb (abs_nonneg _) (by positivity)
      rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos hBr,abs_of_nonneg hC]
      calc
        _ ≤ (B : ℝ)*((K/((B : ℝ)*X))*coefficientWeight B a*
            ((K/((B : ℝ)*X))*coefficientWeight B b))*coefficientWeight B c*1 := by
          apply mul_le_mul
          · simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hBr.le) hC
          · exact hW a ha b hbI c hc
          · exact abs_nonneg _
          · positivity
        _ = _ := by
          unfold tripleCoefficientWeight
          rw [← hrel]
          field_simp
  · have hz : coefficientRelationWeight B (j : ℤ) a b c = 0 := by
      rw [coefficientRelationWeight_nat,ite_eq_right hrel]
    simp [hrel,discardedRelationWeight,hz]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_TensorBoxRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published regularity loss on the actual compact tensor boxes -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem tensorInterval_width {X : ℝ} (hX : 1 ≤ X) :
    3*X ≤ (tensorIntervalUpper X : ℝ)-tensorIntervalLower X ∧
      (tensorIntervalUpper X : ℝ)-tensorIntervalLower X ≤ 5*X := by
  have hl := Nat.floor_le (show 0 ≤ (1/4 : ℝ)*X by linarith)
  have hl' := Nat.lt_floor_add_one ((1/4 : ℝ)*X)
  have hu := Nat.floor_le (show 0 ≤ (17/4 : ℝ)*X by linarith)
  have hu' := Nat.lt_floor_add_one ((17/4 : ℝ)*X)
  simp only [tensorIntervalUpper,tensorIntervalLower,Nat.cast_add,Nat.cast_one]
  constructor <;> linarith

theorem tensorInterval_order {X : ℝ} (hX : 0 ≤ X) :
    tensorIntervalLower X ≤ tensorIntervalUpper X := by
  unfold tensorIntervalLower tensorIntervalUpper
  exact Nat.add_le_add_right (Nat.floor_mono (by linarith : (1/4 : ℝ)*X ≤ (17/4 : ℝ)*X)) 1

theorem tensorInterval_point {X : ℝ} (hX : 0 ≤ X) {n : ℕ}
    (hn : n ∈ Ico (tensorIntervalLower X) (tensorIntervalUpper X)) :
    X/4 ≤ n ∧ (n : ℝ) ≤ (17/4 : ℝ)*X := by
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hn
  have hl : ⌊(1/4 : ℝ)*X⌋₊ < n := by
    change ⌊(1/4 : ℝ)*X⌋₊+1 ≤ n at hlo
    omega
  have hl' := (Nat.floor_lt (show 0 ≤ (1/4 : ℝ)*X by positivity)).mp hl
  have hu : n ≤ ⌊(17/4 : ℝ)*X⌋₊ := by
    change n < ⌊(17/4 : ℝ)*X⌋₊+1 at hhi
    omega
  have hu' : (n : ℝ) ≤ ⌊(17/4 : ℝ)*X⌋₊ := by exact_mod_cast hu
  exact ⟨by linarith,hu'.trans (Nat.floor_le (by positivity))⟩

open Classical in
/-- At a fixed dyadic box, the published three-form sieve bound has the
normalization 1/(B*T) required before summing the dyadic partition. -/
theorem tensorBox_signed_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C N T : ℝ) (j : ℕ),
          0 ≤ C → 1 ≤ N → 0 < T → 1 ≤ N/T → j ≠ 0 →
          Real.exp ((1/2 : ℝ)*B) ≤ 3*N →
          Real.exp ((1/2 : ℝ)*B) ≤ 3*(N/T) →
          (17/4 : ℝ)*N ≤ Real.exp ((16/5 : ℝ)*B) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          ∀ W : ℕ → ℕ → ℕ → ℝ,
          (∀ a ∈ Ico (tensorIntervalLower N) (tensorIntervalUpper N),
            ∀ b ∈ Ico (tensorIntervalLower N) (tensorIntervalUpper N),
            ∀ c ∈ Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T)), |W a b c| ≤ 1) →
          signedLocalRegularityError B L j τ C
            (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
            (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h W ≤
              K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K₀,hK₀,hpoint⟩ := signed_local_regularity_domination hM
  obtain ⟨K₁,hK₁,hbox⟩ := signed_coefficient_regularity_loss hFord hM
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 32)
  refine ⟨400*K₀^2*K₁,by positivity,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hpoint,hbox,eventually_gt_atTop 0] with B hp hb hB
  intro C N T j hC hN hT hNT hj hlen hlen' hsize g h hg hh W hW
  have hN0 : 0 < N := by linarith
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hwidth := tensorInterval_width hN
  have hwidth' := tensorInterval_width hNT
  have hbound := hb C j (tensorIntervalLower N) (tensorIntervalUpper N)
    (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T)) hC
    (by exact_mod_cast hj) (tensorInterval_order hN0.le)
    (tensorInterval_order (div_pos hN0 hT).le) (hlen.trans hwidth.1) (hlen'.trans hwidth'.1)
  have hpoint := hp L j τ C (N/4) (by positivity) _ _
    (fun n hn => by
      have hn' := tensorInterval_point hN0.le hn
      exact ⟨hn'.1,hn'.2.trans hsize⟩) g h hg hh W hW
  have he0 : 0 ≤ ε B+Real.exp (-(1/10 : ℝ)*C) := add_nonneg (hε0 B) (Real.exp_pos _).le
  have hs0 : 0 ≤ singularFactor 24 j := zero_le_one.trans (singularFactor_one_le (by norm_num) j)
  calc
    _ ≤ K₀^2/((B : ℝ)*(N/4)^2)*
        (K₁*((tensorIntervalUpper N : ℝ)-tensorIntervalLower N)*
          ((tensorIntervalUpper (N/T) : ℝ)-tensorIntervalLower (N/T))*
          singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C))) :=
      hpoint.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ ≤ K₀^2/((B : ℝ)*(N/4)^2)*
        (K₁*(5*N)*(5*(N/T))*singularFactor 24 j*
          (ε B+Real.exp (-(1/10 : ℝ)*C))) := by
      gcongr
      · linarith [hwidth'.1]
      · exact hwidth.2
      · exact hwidth'.2
    _ = _ := by field_simp <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DyadicBoxRegularity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularity loss for the manuscript's concrete dyadic amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem dyadic_tensor_box_conditions {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlog : Real.log T ≤ (B : ℝ)/10) {k : ℤ}
    (hk : k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)) :
    let N := Real.exp ((k : ℝ)*Real.log 2)
    1 ≤ N ∧ 1 ≤ N/T ∧ Real.exp ((1/2 : ℝ)*B) ≤ 3*N ∧
      Real.exp ((1/2 : ℝ)*B) ≤ 3*(N/T) ∧
      (17/4 : ℝ)*N ≤ Real.exp ((16/5 : ℝ)*B) := by
  dsimp only
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hwin := (dyadic_scale_window hB hT hlog).2.1 k hk
  have hmin : Real.exp ((9/10 : ℝ)*B) ≤ Real.exp ((k : ℝ)*Real.log 2) :=
    Real.exp_le_exp.mpr hwin.1.1
  have hmax : Real.exp ((k : ℝ)*Real.log 2) ≤ Real.exp ((5/2 : ℝ)*B) :=
    Real.exp_le_exp.mpr hwin.1.2
  have hdiv : Real.exp ((9/10 : ℝ)*B) ≤ Real.exp ((k : ℝ)*Real.log 2)/T := by
    have he := Real.exp_le_exp.mpr hwin.2.1
    rwa [Real.exp_log (div_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hT))] at he
  have hone : 1 ≤ Real.exp ((9/10 : ℝ)*B) := Real.one_le_exp_iff.mpr (by linarith)
  have hmid : Real.exp ((1/2 : ℝ)*B) ≤ Real.exp ((9/10 : ℝ)*B) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfactor : (17/4 : ℝ) ≤ Real.exp ((7/10 : ℝ)*B) := by
    have hh := Real.add_one_le_exp ((7/10 : ℝ)*B)
    linarith
  refine ⟨hone.trans hmin,hone.trans hdiv,by linarith,by linarith,?_⟩
  calc
    _ ≤ Real.exp ((7/10 : ℝ)*B)*Real.exp ((5/2 : ℝ)*B) :=
      mul_le_mul hfactor hmax (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

open Classical in
/-- The actual smooth summand loses only a vanishing error plus the explicit
regularity tail, with the uniform 1/(B*T) normalization on each dyadic box. -/
theorem dyadicBox_signed_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 →
          ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
          ∀ (C : ℝ) (j : ℕ), 0 ≤ C → j ≠ 0 →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          let N := Real.exp ((k : ℝ)*Real.log 2)
          signedLocalRegularityError B L j τ C
            (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
            (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h
            (fun a b c => amplificationBoxWeight B (Real.log (N/T)/B)
              (a/N) (b/N) (c/(N/T))) ≤
            K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hbox⟩ := tensorBox_signed_regularity_loss hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hbox,eventually_ge_atTop 30] with B hb hB
  intro T hT hlog k hk C j hC hj g h hg hh
  have hs := dyadic_tensor_box_conditions hB hT hlog hk
  dsimp only at hs ⊢
  apply hb C _ T j hC hs.1 (lt_of_lt_of_le zero_lt_one hT) hs.2.1 hj
    hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 g h hg hh
  intro a _ b _ c _
  unfold amplificationBoxWeight
  have h1 := amplificationBump_bounds
    (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B+
      Real.log (c/(Real.exp ((k : ℝ)*Real.log 2)/T))/B)
  have h2 := amplificationSpatialProfile_bounds (a/Real.exp ((k : ℝ)*Real.log 2))
    (b/Real.exp ((k : ℝ)*Real.log 2)) (c/(Real.exp ((k : ℝ)*Real.log 2)/T))
  rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
  exact (mul_le_mul h1.2 h2.2 h2.1 zero_le_one).trans_eq (mul_one 1)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationRegularityIdentity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dyadic recombination of the discarded regularity mass -/

namespace JointDickman
open Finset

open Classical in
theorem discardedAmplificationBoxTerm_eq (B L j : ℕ) (τ C : ℝ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    discardedAmplificationBoxTerm B L j τ C T N g h c b a =
      discardedAmplificationTerm B L j τ C T g h c b a*dyadicPartitionWeight (c/(N/T)) := by
  unfold discardedAmplificationBoxTerm discardedAmplificationTerm
  rw [amplificationBoxTerm_eq B j hT hN]
  by_cases hr : coefficientTripleRegular B L τ C a b c
  · simp only [hr,ite_true, if_true,zero_mul]
  · simp only [hr,ite_false, if_false]
    rw [← mul_assoc,abs_mul,abs_of_nonneg (dyadicPartitionWeight_bounds _).1]

open Classical in
theorem discardedAmplificationBoxTerm_support (B L j : ℕ) (τ C : ℝ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hn : discardedAmplificationBoxTerm B L j τ C T N g h c b a ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  apply amplificationBoxTerm_support B j hT hN g h
  intro hz
  exact hn (by simp [discardedAmplificationBoxTerm,hz])

open Classical in
theorem discardedAmplificationBox_sum (B L j : ℕ) (τ C T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    (∑ c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊,
      ∑ b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊,
      ∑ a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊,
        discardedAmplificationBoxTerm B L j τ C T N g h c b a) =
    signedLocalRegularityError B L j τ C
      (Ico (tensorIntervalLower N) (tensorIntervalUpper N))
      (Ico (tensorIntervalLower (N/T)) (tensorIntervalUpper (N/T))) g h
      (fun a b c => amplificationBoxWeight B (Real.log (N/T)/B)
        (a/N) (b/N) (c/(N/T))) := by
  have hi (a b : ℕ) : Ico (a+1) (b+1) = Ioc a b := by
    ext n
    simp only [mem_Ico,mem_Ioc]
    omega
  unfold signedLocalRegularityError
  simp only [tensorIntervalLower,tensorIntervalUpper,hi]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊)
    (t := Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊)]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro c _
  unfold discardedAmplificationBoxTerm amplificationBoxTerm
  by_cases hr : coefficientTripleRegular B L τ C a b c
  · rw [ite_eq_left hr,ite_eq_right (show ¬ (a = b+j*c ∧
        ¬ coefficientTripleRegular B L τ C a b c) from fun hh => hh.2 hr)]
  · rw [ite_eq_right hr]
    by_cases he : a = b+j*c
    · rw [ite_eq_left he,ite_eq_left ⟨he,hr⟩]
      congr 1
      ring
    · rw [ite_eq_right he,ite_eq_right (fun hh => he hh.1)]
      simp only [mul_zero,abs_zero]

open Classical in
theorem discarded_amplification_dyadic_identity {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlogT : Real.log T ≤ (B : ℝ)/10) (L j U V : ℕ) (τ C : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hU : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U)
    (hV : ∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) :
    (∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
      discardedAmplificationTerm B L j τ C T g h c b a) =
    ∑ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
      signedLocalRegularityError B L j τ C
        (Ico (tensorIntervalLower (Real.exp ((k : ℝ)*Real.log 2)))
          (tensorIntervalUpper (Real.exp ((k : ℝ)*Real.log 2))))
        (Ico (tensorIntervalLower (Real.exp ((k : ℝ)*Real.log 2)/T))
          (tensorIntervalUpper (Real.exp ((k : ℝ)*Real.log 2)/T))) g h
        (fun a b c => amplificationBoxWeight B (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
          (a/Real.exp ((k : ℝ)*Real.log 2)) (b/Real.exp ((k : ℝ)*Real.log 2))
          (c/(Real.exp ((k : ℝ)*Real.log 2)/T))) := by
  have hTpos := lt_of_lt_of_le zero_lt_one hT
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  obtain ⟨hLU,_,hbracket⟩ := dyadic_scale_window hB hT hlogT
  symm
  simp_rw [← discardedAmplificationBox_sum]
  change (∑ k ∈ S, ∑ c ∈ _, ∑ b ∈ _, ∑ a ∈ _,
    discardedAmplificationBoxTerm B L j τ C T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a) = _
  calc
    _ = ∑ k ∈ S, ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        discardedAmplificationBoxTerm B L j τ C T (Real.exp ((k : ℝ)*Real.log 2)) g h c b a := by
      apply sum_congr rfl
      intro k hk
      apply finite_triple_sum_extend
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hU k hk)⟩
      · intro n hn
        obtain ⟨hnl,hnu⟩ := mem_Ioc.mp hn
        exact mem_Ioc.mpr ⟨Nat.lt_of_le_of_lt (Nat.zero_le _) hnl,hnu.trans (hV k hk)⟩
      · exact discardedAmplificationBoxTerm_support B L j τ C hTpos (Real.exp_pos _) g h
    _ = ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        ∑ k ∈ S, discardedAmplificationBoxTerm B L j τ C T
          (Real.exp ((k : ℝ)*Real.log 2)) g h c b a :=
      sum_triple_interchange S (Ioc 0 U) (Ioc 0 V) _
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      simp_rw [discardedAmplificationBoxTerm_eq B L j τ C hTpos (Real.exp_pos _) g h c b a,
        div_div_eq_mul_div]
      rw [← mul_sum]
      by_cases he : discardedAmplificationTerm B L j τ C T g h c b a = 0
      · simp [he]
      · have harith : amplificationArithmeticTerm B j T g h c b a ≠ 0 := by
          intro hz
          exact he (by simp [discardedAmplificationTerm,hz])
        have hBp : 0 < B := lt_of_lt_of_le (by norm_num) hB
        obtain ⟨hlo,hhi⟩ := amplificationArithmeticTerm_log_support hBp j T g h c b a harith
        have hcp : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
        obtain ⟨hcl,hcu⟩ := hbracket c hcp hlo hhi
        rw [geometric_dyadic_partition hLU (c*T) hcl hcu,mul_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationRegularityLoss
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unpartitioned signed regularity error in the amplification argument -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem dyadicBoxIndices_card_bound {B : ℕ} (hB : 30 ≤ B) {T : ℝ}
    (hT : 1 ≤ T) (hlog : Real.log T ≤ (B : ℝ)/10) :
    ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ) ≤ 5*B := by
  have hBr : (30 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnon : 0 ≤ (2*(B : ℝ)+Real.log T)/Real.log 2 :=
    div_nonneg (by linarith [Real.log_nonneg hT]) (by linarith)
  have hceil := Nat.ceil_lt_add_one hnon
  have hfrac : (2*(B : ℝ)+Real.log T)/Real.log 2 ≤ (21/5 : ℝ)*B := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  have hU : (dyadicBoxUpper B T : ℝ) ≤ 5*B := by
    simp only [dyadicBoxUpper,Nat.cast_add,Nat.cast_one]
    linarith
  have hcard : (dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card ≤
      dyadicBoxUpper B T := by
    unfold dyadicBoxIndices
    exact card_image_le.trans (by rw [Nat.card_Ico]; exact Nat.sub_le _ _)
  exact (by exact_mod_cast hcard :
    ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ) ≤
      dyadicBoxUpper B T).trans hU

open Classical in
/-- The published sieve input controls the entire signed smooth regularity
loss; the dyadic number of boxes cancels the local factor 1/B. -/
theorem amplification_signed_regularity_loss
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℝ, 1 ≤ T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → j ≠ 0 →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          (∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
            discardedAmplificationTerm B L j τ C T g h c b a) ≤
            K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hbox⟩ := dyadicBox_signed_regularity_loss hFord hM
  refine ⟨5*K,by positivity,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hbox⟩ := hbox L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hbox,eventually_ge_atTop 30] with B hb hB
  intro T hT hlog C j U V hC hj hU hV g h hg hh
  rw [discarded_amplification_dyadic_identity hB hT hlog L j U V τ C g h hU hV]
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hA0 : 0 ≤ K/((B : ℝ)*T)*singularFactor 24 j*
      (ε B+Real.exp (-(1/10 : ℝ)*C)) := by
    apply mul_nonneg
    · exact mul_nonneg (by positivity)
        (zero_le_one.trans (singularFactor_one_le (by norm_num) j))
    · exact add_nonneg (hε0 B) (Real.exp_pos _).le
  calc
    _ ≤ ∑ _k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
        K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
      apply sum_le_sum
      intro k hk
      exact hb T hT hlog k hk C j hC hj g h hg hh
    _ = ((dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)).card : ℝ)*
        (K/((B : ℝ)*T)*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C))) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ (5*(B : ℝ))*(K/((B : ℝ)*T)*singularFactor 24 j*
        (ε B+Real.exp (-(1/10 : ℝ)*C))) :=
      mul_le_mul_of_nonneg_right (dyadicBoxIndices_card_bound hB hT hlog) hA0
    _ = _ := by field_simp

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
-- module Solutions.OAIQ083_JD.JointDickman_Counting_CoefficientProductSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero coefficients on the application range are auxiliary-prime products -/

namespace JointDickman
open Finset

/-- The elementary global cap used only for the rare common-prime error. -/
theorem coefficientWeight_le_scale (B n : ℕ) : coefficientWeight B n ≤ coefficientScale B := by
  classical
  have h : roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2) n ≤ (1 : ℝ) := by
    unfold roughSquarefreeWeight squarefreeWeight
    simp only [ArithmeticFunction.coe_mk]
    split_ifs
    · exact pow_le_one₀ (by norm_num) (by norm_num)
    all_goals norm_num
  exact (mul_le_mul_of_nonneg_left h (coefficientScale_nonneg B)).trans_eq (mul_one _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedPairPushforward
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact two-endpoint fair-split pushforward -/

namespace JointDickman
open Finset

open Classical in
theorem signedSplitProductMass_zero_off_support (P : Finset ℕ)
    (g : Finset ℕ → ℝ) (n : ℕ) (hn : n ∉ primeSplitProductSupport P) :
    signedSplitProductMass P g n = 0 := by
  have hprod : ∀ A ∈ P.powerset, (∏ p ∈ A, p) ≠ n := by
    intro A hA he
    exact hn (mem_image.mpr ⟨A,hA,he⟩)
  unfold signedSplitProductMass
  apply sum_eq_zero
  intro S _
  have hz : splitProductMass P S n = 0 := by
    unfold splitProductMass
    apply sum_eq_zero
    intro A hA
    rw [ite_eq_right (hprod A hA),mul_zero]
  rw [hz,mul_zero]

open Classical in
/-- The unsigned law pushed to products, retaining an arbitrary test. -/
theorem primeProductMass_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℝ) :
    (∑ n ∈ primeSplitProductSupport P, primeProductMass P z n*F n) =
      ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*F (∏ p ∈ A,p) := by
  unfold primeSplitProductSupport
  rw [sum_image]
  · apply sum_congr rfl
    intro A hA
    rw [primeProductMass_at_product z hP (mem_powerset.mp hA)]
  · intro A hA D hD he
    exact primeProduct_injective hP (mem_powerset.mp hA) (mem_powerset.mp hD) he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_AmplificationFairKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth amplification sum as the actual fair-split kernel -/

namespace JointDickman
open Finset

theorem primeSplitProductSupport_subset_Ioc {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {U : ℕ} (hU : (∏ p ∈ P, p) ≤ U) :
    primeSplitProductSupport P ⊆ Ioc 0 U := by
  classical
  intro n hn
  obtain ⟨A,hA,rfl⟩ := mem_image.mp hn
  have hAP := mem_powerset.mp hA
  refine mem_Ioc.mpr ⟨prod_pos (fun p hp => (hP p (hAP hp)).pos),?_⟩
  exact (prod_le_prod_of_subset_of_one_le' hAP (fun p hp _ => (hP p hp).one_le)).trans hU

open Classical in
theorem amplificationArithmeticTerm_factor (B j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationArithmeticTerm B j T g h c b a =
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
      signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        amplificationScalarWeight B j T c b a := by
  unfold amplificationArithmeticTerm amplificationScalarWeight
  split_ifs <;> ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AmplificationWeightBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique-quotient bound used when removing coprimality -/

namespace JointDickman
open Finset

open Classical in
theorem amplificationScalarWeight_bounds (B j : ℕ) (T : ℝ) (c b a : ℕ) :
    0 ≤ amplificationScalarWeight B j T c b a ∧
      amplificationScalarWeight B j T c b a ≤ coefficientScale B := by
  unfold amplificationScalarWeight
  split_ifs
  · have h1 := amplificationBump_bounds (Real.log c/B)
    have h2 := amplificationBump_bounds (a/(T*c))
    have h3 := amplificationBump_bounds (b/(T*c))
    have hprod : 0 ≤ amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) := mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    have hprod1 : amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) ≤ 1 := by
      calc
        _ ≤ (1 : ℝ)*1*1 := mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num))
          h3.2 h3.1 (by norm_num)
        _ = _ := by norm_num
    exact ⟨mul_nonneg (coefficientWeight_nonneg B c) hprod,
      (mul_le_of_le_one_right (coefficientWeight_nonneg B c) hprod1).trans
        (coefficientWeight_le_scale B c)⟩
  · exact ⟨le_rfl,coefficientScale_nonneg B⟩

open Classical in
theorem amplificationScalarWeight_sum_le (B : ℕ) {j : ℕ} (hj : 0 < j)
    (T : ℝ) (V a b : ℕ) :
    (∑ c ∈ Ioc 0 V, amplificationScalarWeight B j T c b a) ≤ coefficientScale B := by
  let C := (Ioc 0 V).filter (fun c => a = b+j*c)
  have hcard : C.card ≤ 1 := by
    apply card_le_one.mpr
    intro c hc d hd
    have hc' := (mem_filter.mp hc).2
    have hd' := (mem_filter.mp hd).2
    exact Nat.mul_left_cancel hj (Nat.add_left_cancel (hc'.symm.trans hd'))
  calc
    _ = ∑ c ∈ C, amplificationScalarWeight B j T c b a := by
      symm
      apply sum_subset (filter_subset _ _)
      intro c hc hnot
      have hrel : a ≠ b+j*c := by
        intro he
        exact hnot (mem_filter.mpr ⟨hc,he⟩)
      simp [amplificationScalarWeight,hrel]
    _ ≤ ∑ _c ∈ C, coefficientScale B :=
      sum_le_sum (fun c _ => (amplificationScalarWeight_bounds B j T c b a).2)
    _ = (C.card : ℝ)*coefficientScale B := by simp
    _ ≤ (1 : ℝ)*coefficientScale B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (coefficientScale_nonneg B)
    _ = _ := one_mul _

theorem amplificationProductWeight_bounds (B : ℕ) {j : ℕ} (hj : 0 < j)
    (T : ℝ) (V a b : ℕ) :
    0 ≤ amplificationProductWeight B j T V a b ∧
      amplificationProductWeight B j T V a b ≤ (B : ℝ)*coefficientScale B := by
  unfold amplificationProductWeight
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg
    (fun c _ => (amplificationScalarWeight_bounds B j T c b a).1)),
    mul_le_mul_of_nonneg_left (amplificationScalarWeight_sum_le B hj T V a b) (Nat.cast_nonneg _)⟩

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
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_PrimeProductGcdError
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing GCD restrictions on two independent selected prime products

The probability of a common selected prime is bounded by the sum of the
products of the two marginal hit probabilities. For the independent
`1/(2p)` selection laws this is at most `1/(4N)` when all allowed primes
exceed `N`. The same bound controls any bounded test of the selected pair.
-/

namespace JointDickman

open Finset PublishedInputs

theorem primeSubsetPairMass_nonneg (P : Finset ℕ) (q r : ℕ → ℝ)
    (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1) (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1)
    (x : P.powerset × P.powerset) : 0 ≤ primeSubsetPairMass P q r x :=
  mul_nonneg (bernoulliSubsetMass_nonneg (mem_powerset.mp x.1.property) hq)
    (bernoulliSubsetMass_nonneg (mem_powerset.mp x.2.property) hr)

open Classical in
theorem bernoulliSubsetMass_single_hit (P : Finset ℕ) (q : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    (∑ S : P.powerset, if p ∈ S.val then bernoulliSubsetMass P q S.val else 0) = q p := by
  rw [sum_coe_sort P.powerset (fun S => if p ∈ S then bernoulliSubsetMass P q S else 0)]
  simpa only [singleton_subset_iff, prod_singleton] using
    bernoulliSubsetMass_required P {p} q (singleton_subset_iff.mpr hp)

open Classical in
theorem primeSubsetPairMass_common_hit (P : Finset ℕ) (q r : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    finiteProbability (primeSubsetPairMass P q r) (fun x => p ∈ x.1.val ∧ p ∈ x.2.val) =
      q p * r p := by
  unfold finiteProbability
  rw [Fintype.sum_prod_type]
  have he (S T : P.powerset) :
      (@ite ℝ (p ∈ S.val ∧ p ∈ T.val) (Classical.propDecidable _)
        (primeSubsetPairMass P q r (S, T)) 0) =
      (if p ∈ S.val then bernoulliSubsetMass P q S.val else 0) *
        (if p ∈ T.val then bernoulliSubsetMass P r T.val else 0) := by
    by_cases hS : p ∈ S.val <;> by_cases hT : p ∈ T.val <;>
      simp [hS, hT, primeSubsetPairMass]
  simp_rw [he]
  rw [← sum_mul_sum, bernoulliSubsetMass_single_hit P q hp,
    bernoulliSubsetMass_single_hit P r hp]

theorem primeProducts_coprime_iff_disjoint {P A D : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hA : A ⊆ P) (hD : D ⊆ P) :
    (∏ p ∈ A, p).Coprime (∏ p ∈ D, p) ↔ Disjoint A D := by
  rw [Nat.coprime_prod_left_iff]
  simp_rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h
    apply disjoint_left.mpr
    intro p hp hpd
    exact (Nat.coprime_primes (hP p (hA hp)) (hP p (hD hpd))).mp (h p hp p hpd) rfl
  · intro h p hp q hq
    apply (Nat.coprime_primes (hP p (hA hp)) (hP q (hD hq))).mpr
    intro heq
    subst q
    exact disjoint_left.mp h hp hq

open Classical in
/-- A genuine finite union bound for the failure of endpoint coprimality. -/
theorem primeSubsetPairMass_gcd_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (q r : ℕ → ℝ) (hq : ∀ p ∈ P, 0 ≤ q p ∧ q p ≤ 1)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1) :
    finiteProbability (primeSubsetPairMass P q r)
      (fun x => ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)) ≤
        ∑ p ∈ P, q p * r p := by
  have hw := primeSubsetPairMass_nonneg P q r hq hr
  calc
    _ ≤ finiteProbability (primeSubsetPairMass P q r)
        (fun x => ∃ p ∈ P, p ∈ x.1.val ∧ p ∈ x.2.val) := by
      apply finiteProbability_mono _ hw
      intro x hx
      have hd : ¬Disjoint x.1.val x.2.val := by
        simpa only [primeProducts_coprime_iff_disjoint hP
          (mem_powerset.mp x.1.property) (mem_powerset.mp x.2.property)] using hx
      obtain ⟨p, hp, hpd⟩ := not_disjoint_iff.mp hd
      exact ⟨p, mem_powerset.mp x.1.property hp, hp, hpd⟩
    _ ≤ ∑ p ∈ P, finiteProbability (primeSubsetPairMass P q r)
        (fun x => p ∈ x.1.val ∧ p ∈ x.2.val) :=
      finiteProbability_exists_mem _ hw P _
    _ = _ := sum_congr rfl (fun p hp => primeSubsetPairMass_common_hit P q r hp)

theorem halfPrimeSelection_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P, 0 ≤ (1 / 2 : ℝ) / p ∧ (1 / 2 : ℝ) / p ≤ 1 := by
  intro p hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
  refine ⟨by positivity, (div_le_one hp₀).mpr ?_⟩
  linarith

open Classical in
/-- The two independent selected products have the manuscript's `1/(2p)`
law. Their common-prime probability is at most `1/(4N)`. -/
theorem halfPrimeSubsetPair_gcd_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p) :
    finiteProbability (primeSubsetPairMass P (fun p => (1 / 2 : ℝ) / p)
      (fun p => (1 / 2 : ℝ) / p))
      (fun x => ¬(∏ p ∈ x.1.val, p).Coprime (∏ p ∈ x.2.val, p)) ≤ 1 / (4 * N : ℝ) := by
  have hb := primeSubsetPairMass_gcd_error P hP _ _
    (halfPrimeSelection_bounds P hP) (halfPrimeSelection_bounds P hP)
  refine hb.trans ?_
  have he (p : ℕ) : ((1 / 2 : ℝ) / p) * ((1 / 2 : ℝ) / p) = (1 / 4 : ℝ) * (1 / (p : ℝ) ^ 2) := by
    ring
  simp_rw [he]
  rw [← mul_sum]
  calc
    _ ≤ (1 / 4 : ℝ) * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_square_tail P hN hcut) (by norm_num)
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularizedProductWeight
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient-regularized product weight in the candidate mean -/

namespace JointDickman
open Finset

open Classical in
theorem regularizedProductWeight_bounds (B L j : ℕ) (τ C : ℝ) (T V a b : ℕ) :
    0 ≤ regularizedProductWeight B L j τ C T V a b ∧
      regularizedProductWeight B L j τ C T V a b ≤ amplificationProductWeight B j T V a b := by
  unfold regularizedProductWeight amplificationProductWeight
  have hterm (c : ℕ) :
      0 ≤ (if coefficientTripleRegular B L τ C a b c then amplificationScalarWeight B j T c b a else 0) ∧
      (if coefficientTripleRegular B L τ C a b c then amplificationScalarWeight B j T c b a else 0) ≤
        amplificationScalarWeight B j T c b a := by
    split_ifs
    · exact ⟨(amplificationScalarWeight_bounds ..).1,le_rfl⟩
    · exact ⟨le_rfl,(amplificationScalarWeight_bounds ..).1⟩
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun c _ => (hterm c).1)),
    mul_le_mul_of_nonneg_left (sum_le_sum (fun c _ => (hterm c).2)) (Nat.cast_nonneg _)⟩

open Classical in
theorem candidateRetainedWeight_eq_product (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    {A D : Finset ℕ} (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) :
    candidateRetainedWeight B L j τ C T V A D =
      if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
        regularizedProductWeight B L j τ C T V (∏ p ∈ D,p) (∏ p ∈ A,p) else 0 := by
  unfold candidateRetainedWeight regularizedProductWeight regularArithmeticScalar
  simp only [coefficientTripleRegular,coefficientPrimeSet_primeProduct hA,
    coefficientPrimeSet_primeProduct hD]
  by_cases hc : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p)
  · simp_rw [ite_and,ite_eq_left hc]
    by_cases ha : RegularPrimeSet B L τ C A
    all_goals by_cases hd : RegularPrimeSet B L τ C D
    all_goals simp only [ha,hd,ite_true, if_true,ite_false, if_false,sum_const_zero,mul_zero]
  · simp_rw [ite_and,ite_eq_right hc]
    simp only [sum_const_zero,mul_zero,ite_self]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_SubsetKernelProductLaw
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite retention-kernel mean as a signed integer-product law -/

namespace JointDickman
open Finset

open Classical in
theorem subsetKernel_product_mean (B : ℕ) (g h : Finset ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
      (fun A D => f (∏ p ∈ A,p) (∏ p ∈ D,p))) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) g a*
        signedSplitProductMass (auxiliaryPrimes B) h b*f a b := by
  let P := auxiliaryPrimes B
  let μ := bernoulliSubsetMass P (fun p => 1/(p : ℝ))
  have hone (a : ℕ) :
      (∑ b ∈ primeSplitProductSupport P, signedSplitProductMass P h b*f a b) =
      ∑ R ∈ P.powerset, μ R*h R*∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p) :=
    signedSplitProductMass_sum P h (f a)
  symm
  calc
    _ = ∑ a ∈ primeSplitProductSupport P, signedSplitProductMass P g a*
        (∑ b ∈ primeSplitProductSupport P, signedSplitProductMass P h b*f a b) := by
      simp only [P,mul_sum,mul_assoc]
    _ = ∑ a ∈ primeSplitProductSupport P, signedSplitProductMass P g a*
        (∑ R ∈ P.powerset, μ R*h R*
          ∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p)) := by
      simp_rw [hone]
    _ = ∑ S ∈ P.powerset, μ S*g S*
        ∑ A ∈ P.powerset, subsetRetentionMass S A*
          (∑ R ∈ P.powerset, μ R*h R*
            ∑ D ∈ P.powerset, subsetRetentionMass R D*f (∏ p ∈ A,p) (∏ p ∈ D,p)) :=
      signedSplitProductMass_sum P g (fun a =>
        ∑ R ∈ P.powerset, μ R*h R*
          ∑ D ∈ P.powerset, subsetRetentionMass R D*f a (∏ p ∈ D,p))
    _ = _ := by
      unfold subsetKernelBilinear retainedSubsetKernel
      simp_rw [mul_sum]
      conv_lhs => arg 2; ext S; rw [sum_comm]
      apply sum_congr rfl
      intro S _
      apply sum_congr rfl
      intro R _
      apply sum_congr rfl
      intro A _
      apply sum_congr rfl
      intro D _
      dsimp only [μ]
      ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateProductMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The candidate mean as the regularized signed product sum -/

namespace JointDickman
open Finset

open Classical in
theorem signedProductPair_sum_on (P : Finset ℕ) (g h : Finset ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (I : Finset ℕ) (hI : primeSplitProductSupport P ⊆ I) :
    (∑ a ∈ I, ∑ b ∈ I, signedSplitProductMass P g a*signedSplitProductMass P h b*f a b) =
    ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      signedSplitProductMass P g a*signedSplitProductMass P h b*f a b := by
  symm
  calc
    _ = ∑ a ∈ I, ∑ b ∈ primeSplitProductSupport P,
        signedSplitProductMass P g a*signedSplitProductMass P h b*f a b := by
      apply sum_subset hI
      intro a _ ha
      rw [signedSplitProductMass_zero_off_support P g a ha]
      simp only [zero_mul,sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro a _
      apply sum_subset hI
      intro b _ hb
      rw [signedSplitProductMass_zero_off_support P h b hb]
      simp only [mul_zero,zero_mul]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SignedProductGcd
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coprimality removal for the actual signed product masses -/

namespace JointDickman
open Finset Filter

open Classical in
theorem primeProductMass_pair_sum_test (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (z : ℝ) (F : ℕ → ℕ → ℝ) :
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      primeProductMass P z a*primeProductMass P z b*F a b) =
      ∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
        bernoulliSubsetMass P (fun p => z/p) A*
          bernoulliSubsetMass P (fun p => z/p) D*F (∏ p ∈ A,p) (∏ p ∈ D,p) := by
  calc
    _ = ∑ a ∈ primeSplitProductSupport P, primeProductMass P z a*
        (∑ b ∈ primeSplitProductSupport P, primeProductMass P z b*F a b) := by
      simp_rw [mul_sum,mul_assoc]
    _ = ∑ A ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) A*
        (∑ D ∈ P.powerset, bernoulliSubsetMass P (fun p => z/p) D*
          F (∏ p ∈ A,p) (∏ p ∈ D,p)) := by
      rw [primeProductMass_sum_test P hP]
      simp_rw [primeProductMass_sum_test P hP]
    _ = _ := by simp_rw [mul_sum,mul_assoc]

open Classical in
theorem halfPrimeProduct_bad_pair_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p) :
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      primeProductMass P (1/2) a*primeProductMass P (1/2) b*
        (if a.Coprime b then 0 else 1)) ≤ 1/(4*N : ℝ) := by
  rw [primeProductMass_pair_sum_test P hP]
  have he : (∑ A ∈ P.powerset, ∑ D ∈ P.powerset,
      bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D*
          (if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then 0 else 1)) =
      finiteProbability (primeSubsetPairMass P (fun p => (1/2 : ℝ)/p) (fun p => (1/2 : ℝ)/p))
        (fun x => ¬(∏ p ∈ x.1.val,p).Coprime (∏ p ∈ x.2.val,p)) := by
    classical
    simp only [finiteProbability,primeSubsetPairMass,Fintype.sum_prod_type]
    have hout := sum_coe_sort P.powerset (fun A =>
      ∑ D : P.powerset, if ¬(∏ p ∈ A,p).Coprime (∏ p ∈ D.val,p) then
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
          bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D.val else 0)
    convert hout.symm using 1
    all_goals try with_reducible_and_instances rfl
    apply sum_congr rfl
    intro A _
    have hin := sum_coe_sort P.powerset (fun D =>
      if ¬(∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
        bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) A*
          bernoulliSubsetMass P (fun p => (1/2 : ℝ)/p) D else 0)
    rw [hin]
    apply sum_congr rfl
    intro D _
    by_cases h : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) <;> simp [h]
  rw [he]
  exact halfPrimeSubsetPair_gcd_error P hP hN hcut

open Classical in
theorem signedPrimeProductPair_coprime_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {N : ℕ} (hN : N ≠ 0) (hcut : ∀ p ∈ P, N < p)
    (g h : (P → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (F : ℕ → ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hF : ∀ a b, |F a b| ≤ L) :
    |(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      signedSplitProductMass P (subsetSiteTest P g) a*
        signedSplitProductMass P (subsetSiteTest P h) b*F a b)-
      (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then signedSplitProductMass P (subsetSiteTest P g) a*
          signedSplitProductMass P (subsetSiteTest P h) b*F a b else 0)| ≤ L/(4*N : ℝ) := by
  let γ := signedSplitProductMass P (subsetSiteTest P g)
  let δ := signedSplitProductMass P (subsetSiteTest P h)
  let p := primeProductMass P (1/2)
  have hg' (a : ℕ) : |γ a| ≤ p a := signedSplitProductMass_abs_le hP (fun S _ => hg _) a
  have hh' (b : ℕ) : |δ b| ≤ p b := signedSplitProductMass_abs_le hP (fun S _ => hh _) b
  have hp (a : ℕ) : 0 ≤ p a := (abs_nonneg _).trans (hg' a)
  change |(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P, γ a*δ b*F a b)-
    (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
      if a.Coprime b then γ a*δ b*F a b else 0)| ≤ _
  have he : (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P, γ a*δ b*F a b)-
      (∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then γ a*δ b*F a b else 0) =
      ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        if a.Coprime b then 0 else γ a*δ b*F a b := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        |if a.Coprime b then 0 else γ a*δ b*F a b| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun a _ => abs_sum_le_sum_abs _ _))
    _ ≤ ∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        p a*p b*L*(if a.Coprime b then 0 else 1) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      by_cases hab : a.Coprime b
      · rw [ite_eq_left hab,ite_eq_left hab,abs_zero,mul_zero]
      · simp only [hab,ite_false, if_false,mul_one,abs_mul]
        exact mul_le_mul (mul_le_mul (hg' a) (hh' b) (abs_nonneg _) (hp a))
          (hF a b) (abs_nonneg _) (mul_nonneg (hp a) (hp b))
    _ = L*(∑ a ∈ primeSplitProductSupport P, ∑ b ∈ primeSplitProductSupport P,
        p a*p b*(if a.Coprime b then 0 else 1)) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ L*(1/(4*N : ℝ)) := mul_le_mul_of_nonneg_left (halfPrimeProduct_bad_pair_mass P hP hN hcut) hL
    _ = _ := by ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateProduct
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product-dependent cutoffs in the exact candidate mean -/
namespace JointDickman
open Finset

open Classical in
theorem weightedCandidateRetained_mean (B L j : ℕ) (τ C : ℝ) (T V : ℕ)
    (q : ℕ → ℕ → ℝ) (g h : Finset ℕ → ℝ) :
    subsetKernelBilinear B g h (retainedSubsetKernel (auxiliaryPrimes B)
      (weightedCandidateRetained B L j τ C T V q)) =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        if b.Coprime a then signedSplitProductMass (auxiliaryPrimes B) h a*
          signedSplitProductMass (auxiliaryPrimes B) g b*
          (regularizedProductWeight B L j τ C T V a b*q a b) else 0 := by
  have hk : retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q) =
      retainedSubsetKernel (auxiliaryPrimes B) (fun A D =>
        if (∏ p ∈ A,p).Coprime (∏ p ∈ D,p) then
          regularizedProductWeight B L j τ C T V (∏ p ∈ D,p) (∏ p ∈ A,p)*
            q (∏ p ∈ D,p) (∏ p ∈ A,p) else 0) := by
    funext S R
    unfold retainedSubsetKernel
    apply sum_congr rfl
    intro A hA
    apply sum_congr rfl
    intro D hD
    rw [weightedCandidateRetained,candidateRetainedWeight_eq_product B L j τ C T V
      (mem_powerset.mp hA) (mem_powerset.mp hD)]
    dsimp only
    by_cases hc : (∏ p ∈ A,p).Coprime (∏ p ∈ D,p)
    · rw [ite_eq_left hc,ite_eq_left hc]
    · rw [ite_eq_right hc,ite_eq_right hc,zero_mul]
  rw [hk,subsetKernel_product_mean B g h (fun b a =>
    if b.Coprime a then regularizedProductWeight B L j τ C T V a b*q a b else 0),sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  by_cases hc : b.Coprime a
  · rw [ite_eq_left hc,ite_eq_left hc]
    ring
  · rw [ite_eq_right hc,ite_eq_right hc,mul_zero]

open Classical in
theorem weightedRegularizedArithmeticSum_eq_product (B L j : ℕ) (τ C : ℝ)
    (T U V : ℕ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (q : ℕ → ℕ → ℝ) (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    weightedRegularizedArithmeticSum B L j τ C T U V q g h =
    ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
      ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
        signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
        (regularizedProductWeight B L j τ C T V a b*q a b) := by
  rw [← signedProductPair_sum_on (auxiliaryPrimes B) _ _ _ (Ioc 0 U)
    (primeSplitProductSupport_subset_Ioc (auxiliaryPrimes_prime B) hU)]
  unfold weightedRegularizedArithmeticSum regularizedProductWeight
  simp_rw [amplificationArithmeticTerm_factor,mul_sum,sum_mul]
  conv_lhs => arg 2; ext c; rw [sum_comm]
  rw [sum_comm]
  conv_lhs => arg 2; ext a; rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  simp only [mul_sum]
  apply sum_congr rfl
  intro c _
  split_ifs <;> ring

open Classical in
theorem weighted_amplification_regularization_error (B L j : ℕ) (τ C T : ℝ) (U V : ℕ)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, |q a b| ≤ 1)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) :
    |weightedAmplificationArithmeticSum B j T U V q g h-
        weightedRegularizedArithmeticSum B L j τ C T U V q g h| ≤
      ∑ c ∈ Ioc 0 V, ∑ b ∈ Ioc 0 U, ∑ a ∈ Ioc 0 U,
        discardedAmplificationTerm B L j τ C T g h c b a := by
  unfold weightedAmplificationArithmeticSum weightedRegularizedArithmeticSum
  simp_rw [mul_sum,← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro c _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro b _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro a _
  unfold discardedAmplificationTerm
  split_ifs
  · simp
  · simp only [mul_zero,sub_zero]
    rw [← mul_assoc,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hq a b) (abs_nonneg _)).trans_eq (mul_one _)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateGcd
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the candidate's coefficient and coprimality restrictions -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weightedCandidateMean_coprime_error {B j : ℕ} (hB : 0 < B) (hj : 0 < j)
    (L T U V : ℕ) (τ C : ℝ) (hU : (∏ p ∈ auxiliaryPrimes B,p) ≤ U)
    (q : ℕ → ℕ → ℝ) (hq : ∀ a b, |q a b| ≤ 1)
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1) :
    |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
        (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
      weightedRegularizedArithmeticSum B L j τ C T U V q h g| ≤
      ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)) := by
  rw [abs_sub_comm,weightedRegularizedArithmeticSum_eq_product B L j τ C T U V hU,
    weightedCandidateRetained_mean]
  have he :
      (∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if b.Coprime a then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            (regularizedProductWeight B L j τ C T V a b*q a b) else 0) =
      ∑ a ∈ primeSplitProductSupport (auxiliaryPrimes B),
        ∑ b ∈ primeSplitProductSupport (auxiliaryPrimes B),
          if a.Coprime b then
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) a*
            signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) b*
            (regularizedProductWeight B L j τ C T V a b*q a b) else 0 := by
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    by_cases hc : a.Coprime b
    · rw [ite_eq_left hc.symm,ite_eq_left hc]
    · rw [ite_eq_right (fun hba => hc hba.symm),ite_eq_right hc]
  rw [he]
  apply signedPrimeProductPair_coprime_error (auxiliaryPrimes B) (auxiliaryPrimes_prime B)
    (show auxiliaryCutoff B ≠ 0 by exact pow_ne_zero _ (Nat.ne_of_gt hB))
    (fun p hp => by exact_mod_cast (mem_filter.mp hp).2) h g hh hg
    (fun a b => regularizedProductWeight B L j τ C T V a b*q a b) (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg B))
  intro a b
  rw [abs_mul,abs_of_nonneg (regularizedProductWeight_bounds B L j τ C T V a b).1]
  calc
    _ ≤ regularizedProductWeight B L j τ C T V a b := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hq a b)
        (regularizedProductWeight_bounds B L j τ C T V a b).1
    _ ≤ _ := (regularizedProductWeight_bounds B L j τ C T V a b).2.trans
      (amplificationProductWeight_bounds B hj T V a b).2

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_WeightedCandidateComparison
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform removal errors with the actual bounded counting restriction -/
namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
theorem weighted_candidate_coefficient_removal_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℕ, ∀ τ : ℝ, 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, 0 < T → Real.log T ≤ (B : ℝ)/10 →
          ∀ (C : ℝ) (j U V : ℕ), 0 ≤ C → 0 < j → (∏ p ∈ auxiliaryPrimes B,p) ≤ U →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
          (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T),
            ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/T)⌋₊ ≤ V) →
          ∀ q : ℕ → ℕ → ℝ, (∀ a b, |q a b| ≤ 1) →
          ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
          (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
          |subsetKernelBilinear B (subsetSiteTest (auxiliaryPrimes B) g) (subsetSiteTest (auxiliaryPrimes B) h)
              (retainedSubsetKernel (auxiliaryPrimes B) (weightedCandidateRetained B L j τ C T V q))-
            weightedAmplificationArithmeticSum B j T U V q h g| ≤
            ((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))+
              K/T*singularFactor 24 j*(ε B+Real.exp (-(1/10 : ℝ)*C)) := by
  obtain ⟨K,hK,hloss⟩ := amplification_signed_regularity_loss hFord hM
  refine ⟨K,hK,?_⟩
  intro L τ hL hτ
  obtain ⟨ε,hε0,hε,hloss⟩ := hloss L τ hL hτ
  refine ⟨ε,hε0,hε,?_⟩
  filter_upwards [hloss,eventually_gt_atTop 0] with B hb hB
  intro T hT hlog C j U V hC hj hU hdyU hdyV q hq g h hg hh
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hc := (weighted_amplification_regularization_error B L j τ C T U V q hq h g).trans
    (hb T hT1 hlog C j U V hC (Nat.ne_of_gt hj) hdyU hdyV h g hh hg)
  rw [abs_sub_comm] at hc
  exact (abs_sub_le _ (weightedRegularizedArithmeticSum B L j τ C T U V q h g) _).trans
    (add_le_add (weightedCandidateMean_coprime_error hB hj L T U V τ C hU q hq g h hg hh) hc)

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.weighted_candidate_coefficient_removal_jd_oai := @OAI.JointDickman.weighted_candidate_coefficient_removal_jd_oai
