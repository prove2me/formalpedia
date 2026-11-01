-- Prove2me | solution 1 for OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:56:44.861282+00:00
-- url     : https://prove2.me/submissions/39689851-ec8c-4706-8bab-c0496ef65c0c

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_JointDickman
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_finite_graph_centered_mean_proved_jd
import Theorems.Thm_OAI_JointDickman_nonzero_binLabel_correlation_along_forces_energy_jd
import Theorems.Thm_OAI_JointDickman_positive_blocks_of_graph_jd
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
-- module Solutions.OAIQ083_JD.JointDickman_Basic
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem Nat.maxPrimeFac_mem_of_one_lt {n : ℕ} (h : 1 < n) : n.maxPrimeFac ∈ n.primeFactorsList := by
  have hne : n.primeFactorsList ≠ [] := by
    intro h0
    rw [Nat.primeFactorsList_eq_nil] at h0
    omega
  unfold Nat.maxPrimeFac
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
  exact List.getLast_mem hne

theorem Nat.prime_maxPrimeFac_of_one_lt {n : ℕ} (h : 1 < n) : (n.maxPrimeFac).Prime :=
  Nat.prime_of_mem_primeFactorsList (Nat.maxPrimeFac_mem_of_one_lt h)

theorem Nat.maxPrimeFac_dvd {n : ℕ} : n.maxPrimeFac ∣ n := by
  rcases Nat.lt_or_ge 1 n with h | h
  · exact Nat.dvd_of_mem_primeFactorsList (Nat.maxPrimeFac_mem_of_one_lt h)
  · interval_cases n <;> simp [Nat.maxPrimeFac]

theorem Nat.maxPrimeFac_le {n : ℕ} : n.maxPrimeFac ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [Nat.maxPrimeFac]
  · exact Nat.le_of_dvd h Nat.maxPrimeFac_dvd

theorem Nat.le_maxPrimeFac {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (h : p ∣ n) : p ≤ n.maxPrimeFac := by
  have hmem : p ∈ n.primeFactorsList := (Nat.mem_primeFactorsList hn).2 ⟨hp, h⟩
  have hne : n.primeFactorsList ≠ [] := List.ne_nil_of_mem hmem
  unfold Nat.maxPrimeFac
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast_of_ne_nil hne]
  simp only [Option.getD_some]
  have hs := Nat.primeFactorsList_sorted n
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  rw [List.getLast_eq_getElem]
  have hl := List.length_pos_of_ne_nil hne
  exact hs (show (⟨i, hi⟩ : Fin n.primeFactorsList.length) ≤ ⟨n.primeFactorsList.length - 1, by omega⟩ from
    Fin.mk_le_mk.2 (by omega))
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

theorem bernoulliSubsetMass_sum {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) :
    ∑ S ∈ P.powerset, bernoulliSubsetMass P q S = 1 := by
  simp only [bernoulliSubsetMass]
  rw [← Finset.prod_add]
  simp

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

theorem amplificationSmoothWeight_bounds (B T a c : ℕ) :
    0 ≤ amplificationSmoothWeight B T a c ∧ amplificationSmoothWeight B T a c ≤ 1 := by
  obtain ⟨h0,h1⟩ := amplificationBump_bounds (Real.log c / B)
  obtain ⟨h0',h1'⟩ := amplificationBump_bounds ((a : ℝ) / ((T : ℝ)*c))
  exact ⟨mul_nonneg h0 h0', (mul_le_mul h1 h1' h0' (by norm_num)).trans_eq (by norm_num)⟩

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

theorem arithmeticAmplification_moment_tendsto (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (arithmeticSubsetAmplification B L τ C w n)^k) / (N : ℝ))
      atTop (nhds (arithmeticAmplificationMoment B L τ C w k)) := by
  have h := real_periodic_moment_tendsto (q := auxiliarySquarePeriod B)
    (residueAmplification B L τ C w) k
  have he : (fun N : ℕ => (∑ n ∈ range N,
      (residueAmplification B L τ C w (n : ZMod (auxiliarySquarePeriod B)))^k) / (N : ℝ)) =
      (fun N : ℕ => (∑ n ∈ range N,
        (arithmeticSubsetAmplification B L τ C w n)^k) / (N : ℝ)) := by
    funext N
    congr 1
    apply sum_congr rfl
    intro n _
    rw [residueAmplification_natCast B L n τ C w]
  rw [he] at h
  exact h

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

theorem power_div_amplificationMultiplier {r : ℝ} (hr : r < 8/25) :
    Tendsto (fun B : ℕ => (B : ℝ)^r / amplificationMultiplier B) atTop (nhds 0) := by
  have hp := (power_div_power_tendsto_zero hr).comp tendsto_natCast_atTop_atTop
  have hu : ∀ᶠ B : ℕ in atTop,
      (B : ℝ)^r / amplificationMultiplier B ≤ 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) := by
    filter_upwards [amplificationMultiplier_comparable,eventually_gt_atTop 0] with B hB hB0
    have hpow : 0 < (B : ℝ)^(8/25 : ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hB0) _
    have hT : (0 : ℝ) < amplificationMultiplier B := by exact_mod_cast hB.1
    apply (div_le_iff₀ hT).mpr
    have hnon := Real.rpow_nonneg (Nat.cast_nonneg B) r
    calc
      _ = 2*((B : ℝ)^r / (B : ℝ)^(8/25 : ℝ)) * ((B : ℝ)^(8/25 : ℝ)/2) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hB.2.1 (by positivity)
  apply squeeze_zero' (Eventually.of_forall fun B => div_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) hu
  simpa using hp.const_mul 2

/-- Both regular weights together are bounded by one power strictly below
T's exponent, uniformly in the later tail cutoff. -/
theorem regular_pair_cap_negligible {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ Q : ℕ → ℝ,
      Tendsto (fun B => Q B / amplificationMultiplier B) atTop (nhds 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (a : ℕ) (S : Finset ℕ),
        regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S ≤ Q B := by
  let ε : ℝ := ((8/25 : ℝ) - 2*weightExponent τ)/4
  have hm := (weight_margins_of_le_samplingTau hτsmall).1
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  have hr : 2*(weightExponent τ + ε) < 8/25 := by dsimp [ε] <;> linarith
  refine ⟨fun B => (B : ℝ)^(2*(weightExponent τ+ε)),power_div_amplificationMultiplier hr,?_⟩
  filter_upwards [regular_weights_cap hL hτ hε,eventually_gt_atTop 0] with B hB hB0
  intro C a S
  have hab : regularCoefficientWeight B L τ C a * regularResidueWeight B L τ C S ≤
      (B : ℝ)^(weightExponent τ+ε) * (B : ℝ)^(weightExponent τ+ε) :=
    mul_le_mul ((hB C).2 a) ((hB C).1 S) (regularResidueWeight_nonneg B L τ C S)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB0
  rw [← Real.rpow_add hBpos] at hab
  convert hab using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

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

/-- Both old divisibility conditions imply the coefficient difference is
divisible by `c`, because the multiplier is a unit modulo `c`. -/
theorem common_divisor_difference {a b c m : ℤ}
    (ha : c ∣ a * m + 1) (hb : c ∣ b * m + 1) : c ∣ a - b := by
  have hm : IsCoprime c m := by
    obtain ⟨z, hz⟩ := ha
    refine ⟨z, -a, ?_⟩
    linear_combination -hz
  apply hm.dvd_of_dvd_mul_right
  convert dvd_sub ha hb using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

theorem norm_centered_binLabel_le_two (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (n : ℕ) : ‖binLabel E z n - μ‖ ≤ 2 := by
  calc
    _ ≤ ‖binLabel E z n‖ + ‖μ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_binLabel_le_one E z hz n) hμ
    _ = 2 := by norm_num

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstFormDiagonal
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The diagonal is bounded by one weight cap times the linear mass -/

namespace JointDickman
open Finset

theorem firstFormAtom_diagonal_bound (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (φ : ℕ → ℝ) (N : ℕ) (Q : ℝ)
    (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖^2 ≤ 4*φ n)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q)
    (D : Finset ℕ) (m : ℕ) (A : Finset ℕ) :
    ‖firstFormAtom B L τ C v J N D m A‖^2 ≤
      4*Q*(firstFormAtom B L τ C v (fun n => (φ n : ℂ)) N D m A).re := by
  classical
  unfold firstFormAtom
  dsimp only
  split_ifs with h
  · let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    let x := regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C ((a*m+1)/c)
    have hx : 0 ≤ x := mul_nonneg (regularCoefficientWeight_nonneg B L τ C _)
      (regularResidueWeight_nonneg B L τ C _)
    have hv0 := (hv a c).1
    have hv1 := (hv a c).2
    have hcoef : x*v a c ≤ Q := (mul_le_of_le_one_right hx hv1).trans (hcap a ((a*m+1)/c))
    have hz : 0 ≤ x*v a c := mul_nonneg hx hv0
    have hsq : (x*v a c)^2 ≤ Q*(x*v a c) := by nlinarith
    have hh := mul_le_mul hsq (hJ (a*m)) (sq_nonneg _) (mul_nonneg (le_trans hz hcoef) hz)
    change ‖((x*v a c : ℝ) : ℂ) * J (a*m)‖^2 ≤
      4*Q*(((x*v a c : ℝ) : ℂ) * (φ (a*m) : ℂ)).re
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  · simp

/-- Bounding one regular coefficient/residue factor pays only one Q. -/
theorem firstFormDiagonal_le (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (φ : ℕ → ℝ) (N : ℕ) (Q : ℝ)
    (hu : ∀ c, 0 ≤ u c) (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖^2 ≤ 4*φ n)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q) :
    firstFormDiagonal B L τ C u v J N ≤ 4*Q*firstFormMass B L τ C u v φ N := by
  classical
  have hp (D : Finset ℕ) (m : ℕ) :
      ∑ A ∈ (auxiliaryPrimes B).powerset, ‖firstFormAtom B L τ C v J N D m A‖^2 ≤
        4*Q*(firstFormInner B L τ C v (fun n => (φ n : ℂ)) N D m).re := by
    unfold firstFormInner
    rw [Complex.re_sum, mul_sum]
    exact sum_le_sum fun A _ => firstFormAtom_diagonal_bound B L τ C v J φ N Q hv hJ hcap D m A
  unfold firstFormDiagonal firstFormMass firstDivisorForm
  simp only [star_one, mul_one]
  simp only [Complex.div_natCast_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (hp i.1 i.2) (firstFormWeight_nonneg B L τ C u hu i.1 i.2)
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstFormMass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear diagonal majorant is the ordinary divisor-weight mean -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormMass_reindex {B : ℕ} (hB : 0 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (φ : ℕ → ℝ) (N : ℕ) :
    firstFormMass B L τ C u v φ N = (B : ℝ) *
      ((∑ n ∈ range N, φ n * arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n) /
        (N : ℝ)) := by
  have he := arithmeticAmplification_reindex B L τ C (fun a c => u c * v a c)
    (fun n => (φ n : ℂ)) N
  have hf := amplification_first_form B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N
    (fun _ _ _ => rfl)
  simp only [star_one, one_mul] at hf
  have hz : (∑ n ∈ range N, (φ n : ℂ) *
      (arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n : ℂ)) / (N : ℂ) =
      (1/(B : ℂ)) * firstDivisorForm B L τ C u v (fun _ => 1) (fun n => (φ n : ℂ)) N := by
    rw [he, mul_div_assoc, hf]
  have hr := congrArg Complex.re hz
  simp only [Complex.div_natCast_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.one_re, Complex.one_im, zero_div, Complex.div_natCast_im] at hr
  change _ = (1/(B : ℝ)) * firstFormMass B L τ C u v φ N at hr
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hh := congrArg (fun x : ℝ => (B : ℝ)*x) hr
  have hc : (B : ℝ)*(1/(B : ℝ)*firstFormMass B L τ C u v φ N) =
      firstFormMass B L τ C u v φ N := by field_simp
  rw [hc] at hh
  exact hh.symm

theorem arithmeticMoment_first_sq_le_second (B L : ℕ) (τ C : ℝ) (w : ℕ → ℕ → ℝ) :
    (arithmeticAmplificationMoment B L τ C w 1)^2 ≤ arithmeticAmplificationMoment B L τ C w 2 := by
  have h := residueMean_mul_norm_sq
    (fun a => (residueAmplification B L τ C w a : ℂ)) (fun _ => 1)
  have hc : residueEnergy (fun _ : ZMod (auxiliarySquarePeriod B) => (1 : ℂ)) = 1 := by
    simp [residueEnergy, NeZero.ne (auxiliarySquarePeriod B)]
  have he : residueEnergy (fun a => (residueAmplification B L τ C w a : ℂ)) =
      arithmeticAmplificationMoment B L τ C w 2 := by
    unfold residueEnergy residueAmplification arithmeticAmplificationMoment
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [mul_one, hc, he, residueAmplification_mean, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using h

theorem smooth_arithmetic_first_upper
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (L : ℕ) (τ C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 ≤ K := by
  obtain ⟨K,hK,hb⟩ := smooth_arithmetic_second_bound hFord hM L τ C
  refine ⟨K+1,by linarith,?_⟩
  filter_upwards [hb] with B hB
  intro T hT hTs
  have hsq := arithmeticMoment_first_sq_le_second B L τ C (amplificationSmoothWeight B T)
  have h := hB T hT hTs
  nlinarith [sq_nonneg K]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_DiagonalRemoval
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual smooth amplification has a negligible diagonal -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormDiagonal_arithmetic_le {B : ℕ} (hB : 0 < B) (L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (Q : ℝ)
    (hu : ∀ c, 0 ≤ u c) (hv : ∀ a c, v a c ∈ Set.Icc (0 : ℝ) 1)
    (hJ : ∀ n, ‖J n‖ ≤ 2)
    (hcap : ∀ a m, regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m ≤ Q) :
    firstFormDiagonal B L τ C u v J N ≤ 4*Q*(B : ℝ)*
      ((∑ n ∈ range N, arithmeticSubsetAmplification B L τ C (fun a c => u c * v a c) n)/(N : ℝ)) := by
  have h := firstFormDiagonal_le B L τ C u v J (fun _ => 1) N Q hu hv
    (fun n => by nlinarith [norm_nonneg (J n), hJ n]) hcap
  rw [firstFormMass_reindex hB] at h
  simpa only [one_mul, mul_assoc] using h

/-- The limits are taken in the manuscript's order: first the counting
scale N, then B. This statement is uniform over all bounded second labels. -/
theorem smooth_diagonal_negligible
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau)
    (C : ℝ) (J : ℕ → ℕ → ℂ) (hJ : ∀ N n, ‖J N n‖ ≤ 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      firstFormDiagonal B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J N) N /
        ((B : ℝ)*amplificationMultiplier B) ≤ ε := by
  obtain ⟨Q,hQlim,hQbound⟩ := regular_pair_cap_negligible hL hτ hτsmall
  obtain ⟨K,hK,hKbound⟩ := smooth_arithmetic_first_upper hFord hM L τ C
  intro ε hε
  have hlim := hQlim.const_mul (4*(K+1))
  simp only [mul_zero] at hlim
  have hsmall := hlim.eventually (eventually_le_nhds hε)
  filter_upwards [hQbound,hKbound,amplificationMultiplier_valid,hsmall,eventually_gt_atTop 0]
    with B hcap hmoment hT hsmallB hB
  have hBT : (0 : ℝ) < (B : ℝ)*amplificationMultiplier B :=
    mul_pos (by exact_mod_cast hB) (by exact_mod_cast hT.1)
  have hm := hmoment (amplificationMultiplier B) hT.1 hT.2
  have hmean := arithmeticAmplification_moment_tendsto B L τ C
    (amplificationSmoothWeight B (amplificationMultiplier B)) 1
  have havg : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, arithmeticSubsetAmplification B L τ C
        (amplificationSmoothWeight B (amplificationMultiplier B)) n)/(N : ℝ) ≤ K+1 := by
    simpa only [pow_one] using hmean.eventually
      (eventually_le_nhds (lt_of_le_of_lt hm (by linarith)))
  filter_upwards [havg] with N havgN
  have hQ0 : 0 ≤ Q B := (mul_nonneg (regularCoefficientWeight_nonneg B L τ C 0)
    (regularResidueWeight_nonneg B L τ C ∅)).trans (hcap C 0 ∅)
  have hd := firstFormDiagonal_arithmetic_le hB L τ C
    (amplificationOuterWeight B) (amplificationInnerWeight (amplificationMultiplier B))
    (J N) N (Q B) (fun c => (amplificationBump_bounds _).1)
    (fun a c => amplificationBump_bounds _) (hJ N)
    (fun a m => hcap C a (coefficientPrimeSet B m))
  have hratio : 0 ≤ Q B / (amplificationMultiplier B : ℝ) := div_nonneg hQ0 (Nat.cast_nonneg _)
  have hquot := div_le_div_of_nonneg_right hd hBT.le
  have he (A : ℝ) : (4*Q B*(B : ℝ)*A)/((B : ℝ)*amplificationMultiplier B) =
      4*(Q B/(amplificationMultiplier B : ℝ))*A := by
    have hb0 : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
    have ht0 : (amplificationMultiplier B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT.1)
    field_simp
  rw [he] at hquot
  have heq : (fun a c => amplificationOuterWeight B c *
      amplificationInnerWeight (amplificationMultiplier B) a c) =
      amplificationSmoothWeight B (amplificationMultiplier B) := rfl
  rw [heq] at hquot
  calc
    _ ≤ _ := hquot
    _ ≤ 4*(Q B/(amplificationMultiplier B : ℝ))*(K+1) :=
      mul_le_mul_of_nonneg_left havgN (mul_nonneg (by norm_num) hratio)
    _ ≤ ε := by nlinarith [hsmallB]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_OffDiagonalEnergy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unequal-coefficient terms of the actual quadratic energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem complex_norm_sq_eq_re_star_mul (z : ℂ) : ‖z‖^2 = (star z * z).re := by
  rw [Complex.sq_norm]
  change Complex.normSq z = ((starRingEnd ℂ) z * z).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

theorem norm_sum_sq_eq_double {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖^2 = ∑ a ∈ s, ∑ b ∈ s, (star (f a) * f b).re := by
  rw [complex_norm_sq_eq_re_star_mul, star_sum, sum_mul, Complex.re_sum]
  apply sum_congr rfl
  intro a _
  rw [mul_sum, Complex.re_sum]

theorem norm_sum_sq_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ a ∈ s, f a‖^2 = (∑ a ∈ s, ‖f a‖^2) +
      ∑ a ∈ s, ∑ b ∈ s, if a = b then 0 else (star (f a) * f b).re := by
  rw [norm_sum_sq_eq_double, ← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [complex_norm_sq_eq_re_star_mul]
  have hdiag : (star (f a) * f a).re =
      ∑ b ∈ s, if a = b then (star (f a) * f b).re else 0 := by simp [ha]
  rw [hdiag, ← sum_add_distrib]
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp_all

theorem firstFormEnergy_eq_diagonal_add (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) :
    firstFormEnergy B L τ C u v J N = firstFormDiagonal B L τ C u v J N +
      firstFormOffDiagonal B L τ C u v J N := by
  classical
  unfold firstFormEnergy firstFormDiagonal firstFormOffDiagonal
  rw [← add_div, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [← mul_add]
  congr 1
  exact norm_sum_sq_split (auxiliaryPrimes B).powerset
    (firstFormAtom B L τ C v J N i.1 i.2)

/-- Diagonal removal retains half of any positive lower energy constant. -/
theorem positive_offDiagonal_of_energy
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau)
    (C : ℝ) (J : ℕ → ℕ → ℂ) (hJ : ∀ N n, ‖J N n‖ ≤ 2)
    (s : ℕ → ℕ) (hs : StrictMono s) {e : ℝ} (he : 0 < e)
    (henergy : ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      e ≤ firstFormEnergy B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J (s N)) (s N) /
          ((B : ℝ)*amplificationMultiplier B)) :
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      e/2 ≤ firstFormOffDiagonal B L τ C (amplificationOuterWeight B)
        (amplificationInnerWeight (amplificationMultiplier B)) (J (s N)) (s N) /
          ((B : ℝ)*amplificationMultiplier B) := by
  have hd := smooth_diagonal_negligible hFord hM hL hτ hτsmall C J hJ (e/2) (half_pos he)
  filter_upwards [henergy,hd] with B hE hD
  filter_upwards [hE, hs.tendsto_atTop.eventually hD] with N hEN hDN
  rw [firstFormEnergy_eq_diagonal_add, add_div] at hEN
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_DivisorGraphSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
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

theorem amplificationInnerWeight_support {T a c : ℕ}
    (h : amplificationInnerWeight T a c ≠ 0) :
    T*c < a ∧ a < 2*(T*c) := by
  have hs := amplificationBump_support h
  have hd : T*c ≠ 0 := by
    intro he
    have hz : (T : ℝ)*(c : ℝ) = 0 := by exact_mod_cast he
    simp only [amplificationInnerWeight, hz, div_zero] at h
    exact h (amplificationBump_zero (Or.inl (by norm_num)))
  have hp : (0 : ℝ) < (T : ℝ)*c := by exact_mod_cast Nat.pos_of_ne_zero hd
  constructor
  · have hl : (T : ℝ)*c < a := by simpa only [one_mul] using (lt_div_iff₀ hp).mp hs.1
    exact_mod_cast hl
  · exact_mod_cast (div_lt_iff₀ hp).mp hs.2

/-- Both congruences and the coefficient window force a small nonzero lag. -/
theorem divisor_pair_small_lag {T a b c m : ℕ}
    (ha : c ∣ a*m+1) (hb : c ∣ b*m+1) (hab : a ≠ b)
    (hwa : T*c < a ∧ a < 2*(T*c)) (hwb : T*c < b ∧ b < 2*(T*c)) :
    ∃ j : ℤ, j ≠ 0 ∧ (a : ℤ)-b = j*c ∧ j.natAbs < T := by
  have hc : 0 < c := by nlinarith [hwa.1, hwa.2]
  have hdiv : (c : ℤ) ∣ (a : ℤ)-b := common_divisor_difference (m := (m : ℤ))
    (by exact_mod_cast ha) (by exact_mod_cast hb)
  obtain ⟨j,hj⟩ := hdiv
  have he : (a : ℤ)-b = j*c := by simpa only [mul_comm] using hj
  have hj0 : j ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul, sub_eq_zero] at he
    exact hab (by exact_mod_cast he)
  have hbnd : |(a : ℤ)-b| < (T : ℤ)*c := by
    apply abs_lt.mpr
    constructor <;> omega
  rw [he, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ c)] at hbnd
  have hjs : |j| < (T : ℤ) := (mul_lt_mul_iff_left₀ (by exact_mod_cast hc : (0 : ℤ) < c)).mp
    (by simpa only [mul_comm] using hbnd)
  refine ⟨j,hj0,he,?_⟩
  rw [← Int.natCast_natAbs] at hjs
  exact_mod_cast hjs

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_NonzeroGraphAtoms
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonzero summands give genuine coprime small-lag graph edges -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem firstFormAtom_nonzero_support (B L T : ℕ) (τ C : ℝ) (J : ℕ → ℂ)
    (N : ℕ) (D A : Finset ℕ) (m : ℕ)
    (h : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0) :
    (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧
      T*(∏ p ∈ D, p) < (∏ p ∈ A, p) ∧
      (∏ p ∈ A, p) < 2*(T*(∏ p ∈ D, p)) := by
  classical
  unfold firstFormAtom at h
  dsimp only at h
  split_ifs at h with hc
  · have hw : amplificationInnerWeight T (∏ p ∈ A, p) (∏ p ∈ D, p) ≠ 0 := by
      intro he
      simp only [he, mul_zero, Complex.ofReal_zero, zero_mul, ne_eq, not_true_eq_false] at h
    exact ⟨hc.1,hc.2,amplificationInnerWeight_support hw⟩
  · exact False.elim (h rfl)

/-- The actual nonzero atoms satisfy every arithmetic condition used in the
change of variables. Distinct subsets give distinct coefficient integers. -/
theorem nonzero_atoms_small_coprime_lag {B L T : ℕ} (τ C : ℝ) (J : ℕ → ℂ)
    (N : ℕ) {D A E : Finset ℕ} (_hD : D ⊆ auxiliaryPrimes B)
    (hA : A ⊆ auxiliaryPrimes B) (hE : E ⊆ auxiliaryPrimes B) (hAE : A ≠ E)
    (hT : T ≤ auxiliaryCutoff B) (m : ℕ)
    (ha : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0)
    (hb : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m E ≠ 0) :
    ∃ j : ℤ, j ≠ 0 ∧ j.natAbs < T ∧
      ((∏ p ∈ A, p : ℕ) : ℤ) - (∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ) ∧
      (∏ p ∈ A, p).Coprime (∏ p ∈ E, p) ∧
      (∏ p ∈ A, p).Coprime (∏ p ∈ D, p) ∧
      (∏ p ∈ E, p).Coprime (∏ p ∈ D, p) ∧
      (∏ p ∈ A, p).Coprime j.natAbs ∧ (∏ p ∈ E, p).Coprime j.natAbs := by
  obtain ⟨haN,hac,hwa⟩ := firstFormAtom_nonzero_support B L T τ C J N D A m ha
  obtain ⟨hbN,hbc,hwb⟩ := firstFormAtom_nonzero_support B L T τ C J N D E m hb
  have hab : (∏ p ∈ A, p) ≠ ∏ p ∈ E, p :=
    fun he => hAE (primeProduct_injective (auxiliaryPrimes_prime B) hA hE he)
  obtain ⟨j,hj0,hj,hjs⟩ := divisor_pair_small_lag hac hbc hab hwa hwb
  have haj := auxiliaryProduct_coprime_small hA (Int.natAbs_pos.mpr hj0) (hjs.le.trans hT)
  have hbj := auxiliaryProduct_coprime_small hE (Int.natAbs_pos.mpr hj0) (hjs.le.trans hT)
  have hac' := (coprime_of_divisor_linear_succ hac).1
  have hbc' := (coprime_of_divisor_linear_succ hbc).1
  exact ⟨j,hj0,hjs,hj,divisor_edge_coprime hac' haj hj,hac',hbc',haj,hbj⟩

/-- The prescribed multiplier is eventually below the lower prime cutoff. -/
theorem amplificationMultiplier_le_cutoff : ∀ᶠ B : ℕ in atTop,
    amplificationMultiplier B ≤ auxiliaryCutoff B := by
  filter_upwards [amplificationMultiplier_comparable,eventually_ge_atTop 1] with B hT hB
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ)^(8/25 : ℝ) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hBr (by norm_num : (8/25 : ℝ) ≤ 1)
  have hTB : amplificationMultiplier B ≤ B := by exact_mod_cast hT.2.2.trans hpow
  have hbpow : B ≤ B ^ (1000 : ℕ) := le_self_pow₀ hB (by decide : (1000 : ℕ) ≠ 0)
  exact hTB.trans hbpow

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

/-- A bijective finite-sum reindexing, with no error term or multiplicity. -/
theorem sum_divisorEdge_reindex {M : Type*} [AddCommMonoid M]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {j : ℤ} (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (N : ℕ) (F : ℕ → M) :
    (∑ m ∈ divisorEdgeOld a b c N, F m) =
      ∑ n ∈ divisorEdgeNew a b c N j, F (divisorEdgeInverse a b c n) := by
  classical
  apply sum_bij (fun m _ => b*((a*m+1)/c))
  · intro m hm
    exact (divisorEdge_forward_mem ha hb hc he hm).1
  · intro m hm k hk heq
    have hm' := (divisorEdge_forward_mem ha hb hc he hm).2
    have hk' := (divisorEdge_forward_mem ha hb hc he hk).2
    rw [← hm',← hk',heq]
  · intro n hn
    have h := divisorEdge_inverse_mem ha hc he hcop hn
    exact ⟨_,h.1,h.2⟩
  · intro m hm
    rw [(divisorEdge_forward_mem ha hb hc he hm).2]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_WeightedDivisorEdge
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting weighted centered labels to the additive endpoints -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- Exact transport of a weighted pair, with fixed-multiplier invariance
as its only label property. The centered label need not be multiplicative. -/
theorem weighted_divisor_edge_reindex {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {j : ℤ}
    (he : (a : ℤ)-b = j*c) (hcop : a.Coprime j.natAbs)
    (N : ℕ) (w : ℕ → ℝ) (F : ℕ → ℂ)
    (hFa : ∀ n, F (a*n) = F n) (hFb : ∀ n, F (b*n) = F n)
    (hFc : ∀ n, F (c*n) = F n) :
    (∑ m ∈ divisorEdgeOld a b c N,
      w m * (star (F (a*m+1)) * F (b*m+1)).re) =
    ∑ n ∈ divisorEdgeNew a b c N j,
      w (divisorEdgeInverse a b c n) * (star (F n) * F ((n : ℤ)+j).toNat).re := by
  rw [sum_divisorEdge_reindex ha hb hc he hcop]
  apply sum_congr rfl
  intro n hn
  let m := divisorEdgeInverse a b c n
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,hcb⟩ := mem_filter.mp hm
  have hfirst : F (a*m+1) = F n := by
    have hq : c*((a*m+1)/c) = a*m+1 := Nat.mul_div_cancel' hca
    calc
      _ = F ((a*m+1)/c) := by
        have ht := hFc ((a*m+1)/c)
        rwa [hq] at ht
      _ = F (b*((a*m+1)/c)) := (hFb _).symm
      _ = F n := by rw [hback]
  have hend : (n : ℤ)+j = ((a*((b*m+1)/c) : ℕ) : ℤ) := by
    rw [← hback]
    exact natural_divisor_edge_endpoints hc hca hcb he
  have hsecond : F (b*m+1) = F ((n : ℤ)+j).toNat := by
    have hq : c*((b*m+1)/c) = b*m+1 := Nat.mul_div_cancel' hcb
    rw [hend, Int.toNat_natCast, hFa]
    have ht := hFc ((b*m+1)/c)
    rwa [hq] at ht
  change w m * (star (F (a*m+1)) * F (b*m+1)).re = _
  rw [hfirst,hsecond]

/-- The required invariances hold for the actual moving centered labels,
simultaneously over the fixed auxiliary coefficient family. -/
theorem centered_movingBinLabel_invariant {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ n,
      movingBinLabel J k z N ((∏ p ∈ A, p)*n)-μ = movingBinLabel J k z N n-μ := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (binLabel_auxiliary_multipliers J hJ k hk z B)] with N hN A hA n
  exact congrArg (fun v : ℂ => v-μ) (hN A hA n)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FirstFormPairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual arithmetic weight of each unequal-coefficient pair -/

namespace JointDickman
open Finset

theorem real_weighted_pair (r s : ℝ) (z w : ℂ) :
    (star ((r : ℂ)*z) * ((s : ℂ)*w)).re = r*s*(star z*w).re := by
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.conj_re, Complex.conj_im]
  ring

theorem firstFormPairEnergy_as_old (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) (D A E : Finset ℕ) :
    firstFormPairEnergy B L τ C u v J N D A E =
      ∑ m ∈ divisorEdgeOld (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N,
        firstFormPairWeight B L τ C u v D A E m *
          (star (J ((∏ p ∈ A, p)*m)) * J ((∏ p ∈ E, p)*m)).re := by
  classical
  unfold firstFormPairEnergy divisorEdgeOld
  rw [sum_filter]
  apply sum_congr rfl
  intro m _
  unfold firstFormAtom
  dsimp only
  by_cases ha : (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1
  · by_cases hb : (∏ p ∈ E, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1
    · rw [ite_eq_left ha,ite_eq_left hb,ite_eq_left ⟨ha.1,hb.1,ha.2,hb.2⟩,real_weighted_pair]
      unfold firstFormPairWeight
      ring
    · have hh : ¬ ((∏ p ∈ A, p)*m < N ∧ (∏ p ∈ E, p)*m < N ∧
        (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1) :=
        fun h => hb ⟨h.2.1,h.2.2.2⟩
      simp only [ite_eq_right hb,ite_eq_right hh,mul_zero,Complex.zero_re]
  · have hh : ¬ ((∏ p ∈ A, p)*m < N ∧ (∏ p ∈ E, p)*m < N ∧
        (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1 ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ E, p)*m+1) :=
        fun h => ha ⟨h.1,h.2.2.1⟩
    simp only [ite_eq_right ha,ite_eq_right hh,star_zero,zero_mul,Complex.zero_re,mul_zero]

theorem firstFormOffDiagonal_eq_pairSum (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (J : ℕ → ℂ) (N : ℕ) :
    firstFormOffDiagonal B L τ C u v J N =
      (∑ D ∈ (auxiliaryPrimes B).powerset, ∑ A ∈ (auxiliaryPrimes B).powerset,
        ∑ E ∈ (auxiliaryPrimes B).powerset,
          if A = E then 0 else firstFormPairEnergy B L τ C u v J N D A E)/(N : ℝ) := by
  classical
  unfold firstFormOffDiagonal firstFormPairEnergy
  congr 1
  rw [sum_product]
  apply sum_congr rfl
  intro D _
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  rw [sum_comm]
  apply sum_congr rfl
  intro E _
  by_cases h : A = E <;> simp only [h,ite_true, if_true,ite_false, if_false,mul_zero,sum_const_zero]

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

/-- This is the exact arithmetic graph expression for a fixed coefficient
pair in the original energy. It includes both signs of the additive lag. -/
theorem firstFormPairEnergy_graph {B L : ℕ} (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) {D A E : Finset ℕ} {j : ℤ}
    (ha : 0 < ∏ p ∈ A, p) (hb : 0 < ∏ p ∈ E, p) (hc : 0 < ∏ p ∈ D, p)
    (he : ((∏ p ∈ A, p : ℕ) : ℤ)-(∏ p ∈ E, p : ℕ) = j*(∏ p ∈ D, p : ℕ))
    (hcop : (∏ p ∈ A, p).Coprime j.natAbs) (N : ℕ) (F : ℕ → ℂ)
    (hFa : ∀ n, F ((∏ p ∈ A, p)*n) = F n)
    (hFb : ∀ n, F ((∏ p ∈ E, p)*n) = F n)
    (hFc : ∀ n, F ((∏ p ∈ D, p)*n) = F n) :
    firstFormPairEnergy B L τ C u v (fun m => F (m+1)) N D A E =
      ∑ n ∈ divisorEdgeNew (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) N j,
        arithmeticGraphPairWeight B L τ C u v
          (∏ p ∈ A, p) (∏ p ∈ E, p) (∏ p ∈ D, p) j n *
          (star (F n) * F ((n : ℤ)+j).toNat).re := by
  rw [firstFormPairEnergy_as_old,
    weighted_divisor_edge_reindex ha hb hc he hcop N
      (firstFormPairWeight B L τ C u v D A E) F hFa hFb hFc]
  apply sum_congr rfl
  intro n hn
  rw [firstFormPairWeight_graph τ C u v ha hb hc he hcop hn]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCoefficientSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical lags and the finite coefficient support of the graph -/

namespace JointDickman
open Finset

/-- Nonzero unequal-pair energy can only occur at an admissible small lag.
Thus discarding the other coefficient triples is an exact operation. -/
theorem nonzero_pairEnergy_admissible {B L T : ℕ} (τ C : ℝ) (u : ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) {D A E : Finset ℕ}
    (hD : D ⊆ auxiliaryPrimes B) (hA : A ⊆ auxiliaryPrimes B)
    (hE : E ⊆ auxiliaryPrimes B) (hAE : A ≠ E) (hT : T ≤ auxiliaryCutoff B)
    (h : firstFormPairEnergy B L τ C u (amplificationInnerWeight T) J N D A E ≠ 0) :
    GraphCoefficientAdmissible T D A E := by
  obtain ⟨m,_,hm⟩ := exists_ne_zero_of_sum_ne_zero h
  have hr := (mul_ne_zero_iff.mp hm).2
  have hp : star (firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A) *
      firstFormAtom B L τ C (amplificationInnerWeight T) J N D m E ≠ 0 := by
    intro he
    exact hr (by rw [he]; rfl)
  have ha : firstFormAtom B L τ C (amplificationInnerWeight T) J N D m A ≠ 0 := by
    intro he
    apply hp
    rw [he,star_zero,zero_mul]
  have hb := (mul_ne_zero_iff.mp hp).2
  obtain ⟨j,hj0,hjT,hj,_,_,_,haj,_⟩ :=
    nonzero_atoms_small_coprime_lag τ C J N hD hA hE hAE hT m ha hb
  have hc : (∏ p ∈ D, p : ℕ) ≠ 0 := prod_ne_zero_iff.mpr
    (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).ne_zero)
  have hlag : coefficientPairLag D A E = j := by
    unfold coefficientPairLag
    rw [hj,Int.mul_ediv_cancel _ (by exact_mod_cast hc)]
  exact ⟨hAE,by rwa [hlag],by rwa [hlag],by rwa [hlag],by rwa [hlag]⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_ArithmeticOffDiagonalGraph
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact graph representation of the full off-diagonal energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- The original off-diagonal energy equals the arithmetic graph, including
its actual coefficient/residue weights and exact finite endpoints. -/
theorem firstFormOffDiagonal_graph (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (hT : T ≤ auxiliaryCutoff B) (F : ℕ → ℂ)
    (hF : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ n, F ((∏ p ∈ A, p)*n) = F n) :
    firstFormOffDiagonal B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
      (fun m => F (m+1)) N = arithmeticOffDiagonalGraph B L τ C T N F := by
  classical
  rw [firstFormOffDiagonal_eq_pairSum]
  unfold arithmeticOffDiagonalGraph
  congr 1
  apply sum_congr rfl
  intro D hD
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro E hE
  have hp (S : Finset ℕ) (hS : S ∈ (auxiliaryPrimes B).powerset) : 0 < ∏ p ∈ S, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (mem_powerset.mp hS hp)).pos)
  by_cases hg : GraphCoefficientAdmissible T D A E
  · rw [ite_eq_left hg,ite_eq_right hg.1]
    exact firstFormPairEnergy_graph τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
      (hp A hA) (hp E hE) (hp D hD) hg.2.2.2.1 hg.2.2.2.2 N F (hF A hA) (hF E hE) (hF D hD)
  · rw [ite_eq_right hg]
    by_cases hAE : A = E
    · rw [ite_eq_left hAE]
    · rw [ite_eq_right hAE]
      by_contra hn
      exact hg (nonzero_pairEnergy_admissible τ C (amplificationOuterWeight B)
        (fun m => F (m+1)) N (mem_powerset.mp hD) (mem_powerset.mp hA) (mem_powerset.mp hE) hAE hT hn)

/-- The exact graph identity for the moving centered second bin label. -/
theorem centered_binLabel_offDiagonal_graph {ι : Type*} [Fintype ι]
    (J : ℕ) (hJ : 0 < J) (k : ι → ℕ) (hk : ∀ i, 1 ≤ k i)
    (z : ι → ℂ) (μ : ℂ) (B L : ℕ) (τ C : ℝ) (T : ℕ) (hT : T ≤ auxiliaryCutoff B) :
    ∀ᶠ N : ℕ in atTop,
      firstFormOffDiagonal B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
        (fun m => movingBinLabel J k z N (m+1)-μ) N =
      arithmeticOffDiagonalGraph B L τ C T N (fun n => movingBinLabel J k z N n-μ) := by
  filter_upwards [centered_movingBinLabel_invariant J hJ k hk z μ B] with N hN
  exact firstFormOffDiagonal_graph B L τ C T N hT
    (fun n => movingBinLabel J k z N n-μ) hN

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_ArithmeticGraphKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual arithmetic graph by lag and endpoint -/

namespace JointDickman
open Finset

theorem graphTriple_edges_subset {B T N : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleEdges N i ⊆ Icc 1 (arithmeticGraphVertexCap B N) := by
  classical
  intro n hn
  have hE := mem_powerset.mp (mem_product.mp (mem_product.mp (mem_filter.mp hi).1).2).2
  have hb : (∏ p ∈ i.2.2, p) ∣ ∏ p ∈ auxiliaryPrimes B, p :=
    prod_dvd_prod_of_subset _ _ id hE
  have hp : 0 < ∏ p ∈ auxiliaryPrimes B, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p hp).pos)
  have hb_le := Nat.le_of_dvd hp hb
  have hn' := mem_Icc.mp (mem_filter.mp hn).1
  exact mem_Icc.mpr ⟨hn'.1,hn'.2.trans (Nat.mul_le_mul_right N hb_le)⟩

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

theorem rawArithmeticGraphKernel_large_lag (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (j : ℤ) (n : ℕ) (hj : T ≤ j.natAbs) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  classical
  apply sum_eq_zero
  intro i hi
  have hlt := (mem_filter.mp hi).2.2.2.1
  have hn : ¬ (graphTripleLag i = j ∧ n ∈ graphTripleEdges N i) := by
    intro h
    change (graphTripleLag i).natAbs < T at hlt
    rw [h.1] at hlt
    omega
  exact ite_eq_right hn

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

/-- A linear test bounded for all sign vectors is bounded throughout the cube. -/
theorem linear_bound_of_signs {ι : Type*} [Fintype ι] (a : ι → ℝ) (C : ℝ)
    (hsign : ∀ s : ι → Bool, |∑ i, a i * cutSign (s i)| ≤ C)
    (f : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) : |∑ i, a i * f i| ≤ C := by
  classical
  let s : ι → Bool := fun i => decide (0 ≤ a i)
  have heq : (∑ i, a i * cutSign (s i)) = ∑ i, |a i| := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ a i
    · simp [s, cutSign, hi, abs_of_nonneg hi]
    · simp [s, cutSign, hi, abs_of_neg (lt_of_not_ge hi)]
  have hsum : (∑ i, |a i|) ≤ C := by
    have h := hsign s
    rw [heq, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)] at h
    exact h
  calc
    |∑ i, a i * f i| ≤ ∑ i, |a i * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)).trans_eq (mul_one _)
    _ ≤ C := hsum

/-- The two applications of the linear sign lemma give the exact extension
from the finite sign maximum to arbitrary real test coordinates in `[-1,1]`. -/
theorem realBilinear_bound_of_signs {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |realBilinear K f g| ≤ C := by
  have hrow (u v : ι → ℝ) :
      realBilinear K u v = ∑ i, (∑ j, K i j * v j) * u i := by
    simp only [realBilinear, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcol (u v : ι → ℝ) :
      realBilinear K u v = ∑ j, (∑ i, K i j * u i) * v j := by
    simp only [realBilinear, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hs (s : ι → Bool) : |realBilinear K (fun i => cutSign (s i)) g| ≤ C := by
    rw [hcol]
    apply linear_bound_of_signs _ C _ g hg
    intro t
    rw [← hcol]
    exact hcut s t
  rw [hrow]
  apply linear_bound_of_signs _ C _ f hf
  intro s
  rw [← hrow]
  exact hs s

theorem realBilinear_rescale {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (f g : ι → ℝ) :
    realBilinear K f g =
      4 * realBilinear K (fun i => f i / 2) (fun i => g i / 2) := by
  simp only [realBilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem realBilinear_bound_two {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (f g : ι → ℝ) (hf : ∀ i, |f i| ≤ 2) (hg : ∀ i, |g i| ≤ 2) :
    |realBilinear K f g| ≤ 4 * C := by
  rw [realBilinear_rescale, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply hcut
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hf i]
  · intro i
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hg i]

theorem complexEnergy_re {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).re =
      realBilinear K (fun i => (z i).re) (fun i => (z i).re) +
      realBilinear K (fun i => (z i).im) (fun i => (z i).im) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib]

theorem complexEnergy_im {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).im =
      realBilinear K (fun i => (z i).re) (fun i => (z i).im) -
      realBilinear K (fun i => (z i).im) (fun i => (z i).re) := by
  simp [complexEnergy, realBilinear, Complex.mul_re, Complex.mul_im,
    Finset.sum_add_distrib, sub_eq_add_neg]

/-- The factor 16 is the one used when the centered labels have norm at most 2. -/
theorem complexEnergy_le_sixteen {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (C : ℝ)
    (hcut : ∀ f g : ι → ℝ, (∀ i, |f i| ≤ 1) → (∀ i, |g i| ≤ 1) →
      |realBilinear K f g| ≤ C)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16 * C := by
  have hre (i : ι) : |(z i).re| ≤ 2 := (Complex.abs_re_le_norm _).trans (hz i)
  have him (i : ι) : |(z i).im| ≤ 2 := (Complex.abs_im_le_norm _).trans (hz i)
  have hrr := realBilinear_bound_two K C hcut _ _ hre hre
  have hii := realBilinear_bound_two K C hcut _ _ him him
  have hri := realBilinear_bound_two K C hcut _ _ hre him
  have hir := realBilinear_bound_two K C hcut _ _ him hre
  calc
    ‖complexEnergy K z‖ ≤ |(complexEnergy K z).re| + |(complexEnergy K z).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 16 * C := by
      rw [complexEnergy_re, complexEnergy_im]
      have ha := abs_add_le
        (realBilinear K (fun i => (z i).re) (fun i => (z i).re))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).im))
      have hb := abs_sub
        (realBilinear K (fun i => (z i).re) (fun i => (z i).im))
        (realBilinear K (fun i => (z i).im) (fun i => (z i).re))
      linarith

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

section CutFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernelCutMaximum_le (K : ι → ι → ℝ) (C : ℝ)
    (hC : ∀ s t : ι → Bool,
      |realBilinear K (fun i => cutSign (s i)) (fun j => cutSign (t j))| ≤ C) :
    kernelCutMaximum K ≤ C := by
  apply Finset.sup'_le
  intro st _
  exact hC st.1 st.2

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphEdgeMajorant
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three-root majorant for the actual arithmetic edge weights -/

namespace JointDickman
open Finset

theorem divisorEdge_small_endpoint {a b c T N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) (hbT : b < 2*(T*c))
    {n : ℕ} (hn : n ∈ divisorEdgeNew a b c N j) : n < 2*T*N := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨hmN,ham,_,hca,_⟩ := mem_filter.mp hm
  have hN : 0 < N := Nat.pos_of_ne_zero (by intro h; simp [h] at hmN)
  have hcn : c*n = b*(a*divisorEdgeInverse a b c n+1) := by
    calc
      c*n = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) :=
        congrArg (fun x : ℕ => c*x) hback.symm
      _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
      _ = _ := by rw [Nat.mul_div_cancel' hca]
  have h1 : c*n ≤ b*N := by rw [hcn]; exact Nat.mul_le_mul_left b (by omega)
  have h2 : b*N < (2*(T*c))*N := Nat.mul_lt_mul_of_pos_right hbT hN
  have hh : c*n < c*(2*T*N) := by nlinarith [h1.trans_lt h2]
  exact Nat.lt_of_mul_lt_mul_left hh

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ShortLagSet
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The singular factor has bounded mean on both signs of the short lags -/

namespace JointDickman
open Finset

theorem mem_nonzeroShortLags {H : ℕ} {j : ℤ} :
    j ∈ nonzeroShortLags H ↔ j ≠ 0 ∧ j.natAbs ≤ H := by
  simp only [nonzeroShortLags, mem_erase, mem_Icc]
  constructor
  · rintro ⟨hj,hl,hu⟩
    refine ⟨hj,?_⟩
    have h : |j| ≤ (H : ℤ) := abs_le.mpr ⟨hl,hu⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · rintro ⟨hj,h⟩
    have h' : |j| ≤ (H : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h
    exact ⟨hj,(abs_le.mp h').1,(abs_le.mp h').2⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockReindex
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact block averaging and reindexing into square matrices -/

namespace JointDickman
open Finset

theorem sum_lag_pairs (M : ℕ) (J : Finset ℤ) (K : ℤ → ℤ → ℝ) :
    (∑ j ∈ J, ∑ i ∈ blockOverlap M j, K j i) =
      ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ J then K (k-i) i else 0 := by
  classical
  simp only [blockOverlap, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter, ← sum_filter]
  apply sum_bij (fun j _ => i+j)
  · intro j hj
    have h := mem_filter.mp hj
    exact mem_filter.mpr ⟨h.2,by simpa using h.1⟩
  · intro a _ b _ hab
    omega
  · intro k hk
    have h := mem_filter.mp hk
    refine ⟨k-i, mem_filter.mpr ⟨h.2,?_⟩,?_⟩
    · simpa only [add_sub_cancel] using h.1
    · simp
  · intro j _
    simp

theorem finiteBlockAverage_square (M V : ℕ) (J : Finset ℤ)
    (K : ℤ → ℤ → ℝ) :
    finiteBlockAverage M V J K =
      (∑ s ∈ blockOrigins M V, ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ J ∧ s+i ∈ Icc 1 (V : ℤ) then K (k-i) (s+i) else 0)/(M : ℝ) := by
  unfold finiteBlockAverage
  congr 1
  apply sum_congr rfl
  intro s _
  rw [sum_lag_pairs]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  by_cases h : k-i ∈ J <;> simp [h]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite block expression for the arithmetic graph energy -/

namespace JointDickman
open Finset

theorem arithmeticBlockAverage_square (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      (∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
          if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
              s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
            arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0)/(M : ℝ) := by
  exact finiteBlockAverage_square ..

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockMatrixIndices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The block positions as a finite matrix index type -/

namespace JointDickman
open Finset

theorem sum_block_indices (M : ℕ) (f : ℤ → ℝ) :
    (∑ i : Fin M, f ((i.val : ℤ)+1)) = ∑ i ∈ Icc (1 : ℤ) M, f i := by
  calc
    _ = ∑ i : (Icc (1 : ℤ) M), f i.val := (blockIndexEquiv M).sum_comp (fun i => f i.val)
    _ = _ := sum_coe_sort _ _

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockMatrix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual block energy as a quadratic form of a finite matrix -/

namespace JointDickman
open Finset

theorem complexEnergy_re_pair {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) :
    (complexEnergy K z).re = ∑ i, ∑ k, K i k*(star (z i)*z k).re := by
  simp [complexEnergy, mul_assoc]

theorem arithmeticBlockMatrix_energy (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (s : ℤ) (F : ℕ → ℂ) :
    (complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re =
      ∑ i ∈ Icc 1 (M : ℤ), ∑ k ∈ Icc 1 (M : ℤ),
        if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0 := by
  rw [complexEnergy_re_pair]
  have hp (i k : Fin M) :
      arithmeticBlockMatrix B L τ C T N H M s i k *
          (star (blockLabels M s F i)*blockLabels M s F k).re =
        if ((k.val : ℤ)+1)-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (((k.val : ℤ)+1)-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0 := by
    unfold arithmeticBlockMatrix blockLabels
    dsimp only
    split_ifs with h
    · have hn : 0 ≤ s+((i.val : ℤ)+1) := le_trans (by norm_num) (mem_Icc.mp h.2).1
      have he : ((s+((i.val : ℤ)+1)).toNat : ℤ)+
          (((k.val : ℤ)+1)-((i.val : ℤ)+1)) = s+((k.val : ℤ)+1) := by
        rw [Int.toNat_of_nonneg hn]
        ring
      unfold arithmeticVertexCorrelation
      rw [he]
      ring
    · simp
  simp_rw [hp]
  calc
    _ = ∑ i : Fin M, ∑ k ∈ Icc 1 (M : ℤ),
        if k-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (k-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0 := by
      apply sum_congr rfl
      intro i _
      exact sum_block_indices M (fun k : ℤ =>
        if k-((i.val : ℤ)+1) ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
            s+((i.val : ℤ)+1) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
          arithmeticVertexCorrelation B L τ C T N F
            (k-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)) else 0)
    _ = _ := sum_block_indices M (fun i : ℤ => ∑ k ∈ Icc 1 (M : ℤ),
      if k-i ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
          s+i ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ) then
        arithmeticVertexCorrelation B L τ C T N F (k-i) (s+i) else 0)

theorem arithmeticBlockAverage_matrix (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    arithmeticBlockAverage B L τ C T N H M F =
      (∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N),
        (complexEnergy (arithmeticBlockMatrix B L τ C T N H M s)
          (blockLabels M s F)).re)/(M : ℝ) := by
  rw [arithmeticBlockAverage_square]
  simp_rw [arithmeticBlockMatrix_energy]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockCutNorm
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite cut norm controls every choice of bounded block labels -/

namespace JointDickman
open Finset

theorem complexEnergy_cutMaximum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    ‖complexEnergy K z‖ ≤ 16*kernelCutMaximum K := by
  classical
  apply complexEnergy_le_sixteen K (kernelCutMaximum K) _ z hz
  intro f g hf hg
  apply realBilinear_bound_of_signs K (kernelCutMaximum K) _ f g hf hg
  intro s t
  exact le_sup' (fun st : (ι → Bool) × (ι → Bool) =>
    |realBilinear K (fun i => cutSign (st.1 i)) (fun j => cutSign (st.2 j))|)
    (mem_univ (s,t))

theorem complexEnergy_re_cutNorm_le (M : ℕ) (K : Fin M → Fin M → ℝ)
    (z : Fin M → ℂ) (hz : ∀ i, ‖z i‖ ≤ 2) :
    |(complexEnergy K z).re|/(M : ℝ) ≤ 16*kernelCutNorm K := by
  have h := (Complex.abs_re_le_norm (complexEnergy K z)).trans
    (complexEnergy_cutMaximum_le K z hz)
  have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  simpa only [kernelCutNorm,Fintype.card_fin,mul_div_assoc] using hd

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Probability_NormalizedGraphKernel
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite graph kernel is the original block matrix before normalization -/

namespace JointDickman
open Finset Classical

theorem rawArithmeticGraphKernel_outside {B L T N n : ℕ} {τ C : ℝ} {j : ℤ}
    (hn : n ∉ Icc 1 (arithmeticGraphVertexCap B N)) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  unfold rawArithmeticGraphKernel
  apply sum_eq_zero
  intro g hg
  have hh : ¬ (graphTripleLag g = j ∧ n ∈ graphTripleEdges N g) :=
    fun h => hn (graphTriple_edges_subset hg h.2)
  exact ite_eq_right hh

theorem arithmeticBlockMatrix_eq_finiteGraph (B L T H M N u : ℕ) (τ C : ℝ) (i k : Fin M) :
    arithmeticBlockMatrix B L τ C T N H M (u : ℤ) i k =
      finiteGraphKernel B L T H M N u τ C i k/((T : ℝ)*N) := by
  have hj : ((k.val : ℤ)+1)-((i.val : ℤ)+1) = (k.val : ℤ)-i.val := by ring
  have hn : (u : ℤ)+((i.val : ℤ)+1) = ((u+(i.val+1) : ℕ) : ℤ) := by push_cast <;> ring
  unfold arithmeticBlockMatrix finiteGraphKernel
  dsimp only
  rw [hj,hn,Int.toNat_natCast]
  let j : ℤ := (k.val : ℤ)-i.val
  let n := u+(i.val+1)
  change (if j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
      (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)
    then rawArithmeticGraphKernel B L τ C T N j n/((B : ℝ)*T*N) else 0) =
      (if H < j.natAbs then rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) else 0)/((T : ℝ)*N)
  by_cases hlag : j ∈ nonzeroShortLags T \ nonzeroShortLags H
  · have hspec : (j ≠ 0 ∧ j.natAbs ≤ T) ∧ ¬ (j ≠ 0 ∧ j.natAbs ≤ H) := by
      simpa only [mem_sdiff,mem_nonzeroShortLags] using hlag
    have hH : H < j.natAbs := by omega
    by_cases hv : (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)
    · rw [ite_eq_left ⟨hlag,hv⟩,ite_eq_left hH,div_div]
      congr 1
      ring
    · have hvn : n ∉ Icc 1 (arithmeticGraphVertexCap B N) := by
        intro h
        apply hv
        exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp h).1,by exact_mod_cast (mem_Icc.mp h).2⟩
      rw [ite_eq_right (fun h => hv h.2),ite_eq_left hH,rawArithmeticGraphKernel_outside hvn]
      simp only [zero_div]
  · have hcond : ¬ (j ∈ nonzeroShortLags T \ nonzeroShortLags H ∧
        (n : ℤ) ∈ Icc 1 (arithmeticGraphVertexCap B N : ℤ)) := fun h => hlag h.1
    rw [ite_eq_right hcond]
    by_cases hH : H < j.natAbs
    · have hj0 : j ≠ 0 := by intro hz; simp [hz] at hH
      have hlarge : T ≤ j.natAbs := by
        by_contra hh
        apply hlag
        exact mem_sdiff.mpr ⟨mem_nonzeroShortLags.mpr ⟨hj0,by omega⟩,
          fun h => (Nat.not_le_of_lt hH) (mem_nonzeroShortLags.mp h).2⟩
      rw [ite_eq_left hH,rawArithmeticGraphKernel_large_lag B L τ C T N j n hlarge]
      simp only [zero_div]
    · simp only [hH,ite_false, if_false,zero_div]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_GraphCountingSupport
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original finite graph is supported at the counting scale -/
namespace JointDickman
open Finset Classical

theorem graphTriple_edge_counting_bound {B L T N n : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) {g : GraphCoefficientTriple}
    (hg : g ∈ arithmeticGraphTriples B T) (he : n ∈ graphTripleEdges N g)
    (hw : graphTripleWeight B L τ C T g n ≠ 0) : n < 2*T*N := by
  have hs := graphTripleWeight_nonzero_supported hB hT τ C hg rfl hw
  have hsub := graphTriple_subsets hg
  have ha : 0 < ∏ p ∈ g.2.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hsub.2.1 hp)).pos)
  have hc : 0 < ∏ p ∈ g.1, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hsub.1 hp)).pos)
  have hrel := (mem_filter.mp hg).2
  have hb := ((mem_amplificationCoefficientPairs hB).mp (mem_filter.mp hs).2.2.2).2.2.2
  exact divisorEdge_small_endpoint ha hc hrel.2.2.2.1 hrel.2.2.2.2
    (by simpa only [graphTriplePair,mul_assoc] using hb) he

theorem rawArithmeticGraphKernel_counting_support {B L T N n : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (j : ℤ) (hn : 2*T*N ≤ n) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  unfold rawArithmeticGraphKernel
  apply sum_eq_zero
  intro g hg
  split_ifs with hh
  · by_contra hw
    exact (not_lt_of_ge hn) (graphTriple_edge_counting_bound hB hT hg hh.2 hw)
  · rfl

theorem finiteGraphKernel_counting_support {B L T H M N u : ℕ} {τ C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hu : 2*T*N ≤ u) :
    finiteGraphKernel B L T H M N u τ C = fun _ _ => 0 := by
  funext i k
  unfold finiteGraphKernel
  split_ifs
  · rw [rawArithmeticGraphKernel_counting_support hB hT _ (by omega),zero_div]
  · rfl

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

theorem kernelAbsoluteMass_entry_bound {M : ℕ} (hM : 0 < M)
    (K : Fin M → Fin M → ℝ) {C : ℝ} (hentry : ∀ i k, |K i k| ≤ C) :
    kernelAbsoluteMass K ≤ (M : ℝ)*C := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  unfold kernelAbsoluteMass
  simp only [Fintype.card_fin]
  apply (div_le_iff₀ hMr).mpr
  exact (sum_le_sum (fun i _ => sum_le_sum (fun k _ => hentry i k))).trans_eq (by simp <;> ring)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GraphBoundaryCap
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform bound for the finitely many left boundary blocks -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem rawArithmeticGraphKernel_uniform_bound {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T N : ℕ) (j : ℤ) (n : ℕ),
      rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ (arithmeticGraphTriples B T).card := by
  filter_upwards [graphTripleWeight_le_one hL hτ hτsmall] with B hb
  intro C T N j n
  unfold rawArithmeticGraphKernel
  rw [sum_div]
  calc
    _ ≤ ∑ _g ∈ arithmeticGraphTriples B T, (1 : ℝ) := by
      apply sum_le_sum
      intro g _
      split_ifs
      · exact hb C T n g
      · simp
    _ = _ := by simp

theorem arithmeticBlockMatrix_entry_bound {B L T N H M : ℕ} {τ C R : ℝ}
    (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (s : ℤ) (i k : Fin M) :
    |arithmeticBlockMatrix B L τ C T N H M s i k| ≤ R/((T : ℝ)*N) := by
  unfold arithmeticBlockMatrix
  dsimp only
  split_ifs
  · have hp := rawArithmeticGraphKernel_nonneg B L τ C T N
      (((k.val : ℤ)+1)-((i.val : ℤ)+1)) (s+((i.val : ℤ)+1)).toNat
    rw [abs_of_nonneg (div_nonneg hp (by positivity)),
      show (B : ℝ)*T*N = (B : ℝ)*((T : ℝ)*N) by ring,← div_div]
    exact div_le_div_of_nonneg_right (hraw _ _) (by positivity)
  · simp only [abs_zero]
    positivity

theorem arithmeticBlockMatrix_energy_cap {B L T N H M : ℕ} {τ C R : ℝ}
    (hM : 0 < M) (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (s : ℤ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re|/(M : ℝ) ≤
      16*(M : ℝ)*(R/((T : ℝ)*N)) := by
  apply (complexEnergy_re_cutNorm_le M _ _ (fun i => hF _)).trans
  have hc := kernelAbsoluteMass_entry_bound hM (arithmeticBlockMatrix B L τ C T N H M s)
    (arithmeticBlockMatrix_entry_bound hR hraw s)
  exact (mul_le_mul_of_nonneg_left ((kernelCutNorm_le_absolute_mass _).trans hc)
    (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by ring)

theorem complexEnergy_div_real {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (z : ι → ℂ) (c : ℝ) :
    complexEnergy (fun i k => K i k/c) z = complexEnergy K z/(c : ℂ) := by
  simp only [complexEnergy,Complex.ofReal_div,div_mul_eq_mul_div,sum_div]

theorem arithmeticBlockMatrix_energy_scale (B L T H M N u : ℕ) (τ C : ℝ) (F : ℕ → ℂ) :
    (complexEnergy (arithmeticBlockMatrix B L τ C T N H M (u : ℤ))
      (blockLabels M (u : ℤ) F)).re =
    (complexEnergy (finiteGraphKernel B L T H M N u τ C) (fun i => F (u+(i.val+1)))).re/
      ((T : ℝ)*N) := by
  have hmat := funext (fun i => funext (fun k => arithmeticBlockMatrix_eq_finiteGraph B L T H M N u τ C i k))
  have hz : blockLabels M (u : ℤ) F = fun i => F (u+(i.val+1)) := by
    funext i
    apply congrArg F
    omega
  rw [hmat,hz,complexEnergy_div_real]
  generalize complexEnergy (finiteGraphKernel B L T H M N u τ C) (fun i => F (u+(i.val+1))) = z
  change (z/(((T : ℝ)*N : ℝ) : ℂ)).re = z.re/((T : ℝ)*N)
  rw [Complex.div_ofReal_re]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_BlockOriginSum
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting block origins into the left boundary and counting range -/
namespace JointDickman
open Finset Classical

theorem blockOrigins_sum_bound (M V K : ℕ) (f : ℤ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ s, 0 ≤ f s) (hleft : ∀ s < 0, f s ≤ D)
    (hsupport : ∀ s : ℤ, (K : ℤ) ≤ s → f s = 0) :
    (∑ s ∈ blockOrigins M V, f s) ≤ (M : ℝ)*D+∑ u ∈ range K, f (u : ℤ) := by
  let U := Ico (1-(M : ℤ)) 0 ∪ (range K).image (fun u : ℕ => (u : ℤ))
  have heq : (∑ s ∈ blockOrigins M V ∩ U, f s) = ∑ s ∈ blockOrigins M V, f s := by
    apply sum_subset inter_subset_left
    intro s hs hn
    have hs' := mem_Icc.mp hs
    have hsu : s ∉ U := by intro hu; exact hn (mem_inter.mpr ⟨hs,hu⟩)
    apply hsupport
    by_contra hk
    have hk' : s < (K : ℤ) := lt_of_not_ge hk
    apply hsu
    by_cases hz : s < 0
    · exact mem_union_left _ (mem_Ico.mpr ⟨hs'.1,hz⟩)
    · apply mem_union_right
      apply mem_image.mpr
      refine ⟨s.toNat,mem_range.mpr ?_,?_⟩
      · omega
      · exact Int.toNat_of_nonneg (le_of_not_gt hz)
  rw [← heq]
  calc
    _ ≤ ∑ s ∈ U, f s := sum_le_sum_of_subset_of_nonneg inter_subset_right (fun s _ _ => hf s)
    _ ≤ (∑ s ∈ Ico (1-(M : ℤ)) 0, f s)+∑ s ∈ (range K).image (fun u : ℕ => (u : ℤ)), f s :=
      sum_union_le_nonneg _ _ f hf
    _ ≤ (M : ℝ)*D+∑ u ∈ range K, f (u : ℤ) := by
      apply add_le_add
      · calc
          _ ≤ ((Ico (1-(M : ℤ)) 0).card : ℝ)*D :=
            (sum_le_sum (fun s hs => hleft s (mem_Ico.mp hs).2)).trans_eq (by simp)
          _ ≤ (M : ℝ)*D := by
            apply mul_le_mul_of_nonneg_right _ hD
            exact_mod_cast (show (Ico (1-(M : ℤ)) 0).card ≤ M by rw [Int.card_Ico]; omega)
      · rw [sum_image]
        intro a _ b _ hab
        exact Int.ofNat_injective hab

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockPrefix
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original block average reduces to a finite counting prefix -/
namespace JointDickman
open Finset Classical

theorem arithmeticBlockAverage_prefix_bound {B L T H M N : ℕ} {τ C R : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hM : 0 < M) (hR : 0 ≤ R)
    (hraw : ∀ j n, rawArithmeticGraphKernel B L τ C T N j n/(B : ℝ) ≤ R)
    (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |arithmeticBlockAverage B L τ C T N H M F| ≤
      16*(M : ℝ)^2*R/((T : ℝ)*N)+
      (∑ u ∈ range (2*T*N),
        |(complexEnergy (finiteGraphKernel B L T H M N u τ C)
          (fun i => F (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
  let f := fun s : ℤ =>
    |(complexEnergy (arithmeticBlockMatrix B L τ C T N H M s) (blockLabels M s F)).re|/(M : ℝ)
  have hf : ∀ s, 0 ≤ f s := fun s => div_nonneg (abs_nonneg _) (Nat.cast_nonneg M)
  have hs : ∀ s : ℤ, (2*T*N : ℕ) ≤ s → f s = 0 := by
    intro s hs
    have hs0 : 0 ≤ s := (by positivity : (0 : ℤ) ≤ (2*T*N : ℕ)).trans hs
    have he : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
    have hn : 2*T*N ≤ s.toNat := by omega
    dsimp only [f]
    rw [← he,arithmeticBlockMatrix_energy_scale,
      finiteGraphKernel_counting_support hB hT hn]
    simp [complexEnergy]
  have hsum := blockOrigins_sum_bound M (arithmeticGraphVertexCap B N) (2*T*N) f
    (show 0 ≤ 16*(M : ℝ)*(R/((T : ℝ)*N)) by positivity) hf
    (fun s _ => arithmeticBlockMatrix_energy_cap hM hR hraw s F hF) hs
  have hstart : |arithmeticBlockAverage B L τ C T N H M F| ≤
      ∑ s ∈ blockOrigins M (arithmeticGraphVertexCap B N), f s := by
    rw [arithmeticBlockAverage_matrix]
    simp only [abs_div,abs_of_nonneg (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)]
    exact (div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)).trans_eq (sum_div _ _ _)
  apply hstart.trans (hsum.trans_eq ?_)
  have hpoint (u : ℕ) : f (u : ℤ) =
      (|(complexEnergy (finiteGraphKernel B L T H M N u τ C)
          (fun i => F (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
    dsimp only [f]
    rw [arithmeticBlockMatrix_energy_scale,abs_div,abs_of_nonneg (by positivity : 0 ≤ (T : ℝ)*N)]
    ring
  simp_rw [hpoint]
  rw [← sum_div]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCounts
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded multiplicity counts and smoothness at bin endpoints

A product of the prime powers counted in a bin divides the integer. This
bounds every bin count uniformly on fixed windows `n ≤ C*x`. The endpoint
criterion identifies smoothness with vanishing counts in all higher bins.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem mem_primeBin_iff {x : ℝ} (hx : 0 ≤ x) (J k p : ℕ) :
    p ∈ primeBin x J k ↔ p.Prime ∧
      x ^ ((k : ℝ) / J) < (p : ℝ) ∧ (p : ℝ) ≤ x ^ (((k : ℝ) + 1) / J) := by
  classical
  simp only [primeBin, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨hp, Nat.lt_of_floor_lt hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mp hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨(Nat.floor_lt (Real.rpow_nonneg hx _)).mpr hl,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).mpr hu⟩, hp⟩

/-- The product of the complete prime powers selected by a finite bin divides `n`. -/
theorem bin_primePower_prod_dvd (E : Finset ℕ) (n : ℕ) :
    (∏ p ∈ E, p ^ n.factorization p) ∣ n := by
  classical
  let f : ℕ →₀ ℕ := n.factorization.filter (fun p => p ∈ E)
  have hf : f ≤ n.factorization := by
    intro p
    simp only [f, Finsupp.filter_apply]
    split_ifs <;> simp
  have hsupp : f.support ⊆ E := by
    intro p hp
    exact (Finset.mem_filter.mp (show p ∈ n.factorization.support.filter (fun p => p ∈ E) from hp)).2
  have heq : f.prod (fun p a => p ^ a) = ∏ p ∈ E, p ^ n.factorization p := by
    rw [Finsupp.prod_of_support_subset f hsupp _ (by simp)]
    apply Finset.prod_congr rfl
    intro p hp
    simp only [f, Finsupp.filter_apply, ite_eq_left hp]
  rw [← heq]
  exact Nat.prod_pow_dvd_of_le_factorization hf

/-- A lower bound for every counted prime gives a power lower bound for `n`. -/
theorem binCount_pow_le (E : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    {q : ℝ} (hq : 0 ≤ q) (hE : ∀ p ∈ E, q ≤ (p : ℝ)) :
    q ^ binCount E n ≤ (n : ℝ) := by
  calc
    q ^ binCount E n = ∏ p ∈ E, q ^ n.factorization p :=
      (Finset.prod_pow_eq_pow_sum E n.factorization q).symm
    _ ≤ ∏ p ∈ E, (p : ℝ) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => pow_nonneg hq _)
        (fun p hp => pow_le_pow_left₀ hq (hE p hp) _)
    _ = ((∏ p ∈ E, p ^ n.factorization p : ℕ) : ℝ) := by norm_cast
    _ ≤ n := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (bin_primePower_prod_dvd E n)

/-- Uniform boundedness of every relevant count, sufficient for interpolation.
The bound holds simultaneously for all bin indices `k ≥ 1`. -/
theorem primeBin_count_eventually_le (J : ℕ) (hJ : 0 < J) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ≤ C * x → binCount (primeBin x J k) n ≤ J := by
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hroot := (tendsto_rpow_atTop (div_pos zero_lt_one hJreal)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hroot, eventually_ge_atTop (1 : ℝ)] with x hxC hxone
  intro k hk n hn hnupper
  let q : ℝ := x ^ ((1 : ℝ) / J)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hq : 1 ≤ q := Real.one_le_rpow hxone (div_nonneg zero_le_one hJreal.le)
  have hprimes : ∀ p ∈ primeBin x J k, q ≤ (p : ℝ) := by
    intro p hp
    have hl := ((mem_primeBin_iff hxpos.le J k p).mp hp).2.1
    have hexp : (1 : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast hk) hJreal.le
    exact (Real.rpow_le_rpow_of_exponent_le hxone hexp).trans hl.le
  have hpow := binCount_pow_le (primeBin x J k) (by omega : n ≠ 0) (le_trans zero_le_one hq) hprimes
  have hrootpow : q ^ J = x := by
    simpa only [q, one_div] using Real.rpow_inv_natCast_pow hxpos.le (by omega : J ≠ 0)
  by_contra hcount
  have hjcount : J + 1 ≤ binCount (primeBin x J k) n := by omega
  have hmon := pow_le_pow_right₀ hq hjcount
  have hbig : C * x < q ^ (J + 1) := by
    rw [pow_succ, hrootpow]
    dsimp [q] at hxC ⊢
    nlinarith
  linarith

/-- A finite sequence crossing a level has an adjacent pair straddling it. -/
private theorem exists_adjacent_crossing (y : ℕ → ℝ) (a : ℝ) {d : ℕ}
    (hzero : y 0 < a) (hend : a ≤ y d) :
    ∃ k : ℕ, k < d ∧ y k < a ∧ a ≤ y (k + 1) := by
  induction d with
  | zero => exact False.elim (not_lt_of_ge hend hzero)
  | succ d ih =>
    by_cases hd : a ≤ y d
    · obtain ⟨k, hk, hl, hu⟩ := ih hd
      exact ⟨k, Nat.lt_trans hk (Nat.lt_succ_self d), hl, hu⟩
    · exact ⟨d, Nat.lt_succ_self d, lt_of_not_ge hd, hend⟩

/-- Every number between a bin endpoint and `x` belongs to a higher bin. -/
theorem exists_higher_primeBin {x : ℝ} (hx : 0 ≤ x) {J r p : ℕ}
    (hJ : 0 < J) (hr : r ≤ J) (hp : p.Prime)
    (hlow : x ^ ((r : ℝ) / J) < (p : ℝ)) (hhigh : (p : ℝ) ≤ x) :
    ∃ k ∈ Finset.Ico r J, p ∈ primeBin x J k := by
  let y : ℕ → ℝ := fun i => x ^ (((r + i : ℕ) : ℝ) / J)
  have hzero : y 0 < (p : ℝ) := by simpa only [y, Nat.add_zero] using hlow
  have hend : (p : ℝ) ≤ y (J - r) := by
    have hindices : r + (J - r) = J := by omega
    change (p : ℝ) ≤ x ^ (((r + (J - r) : ℕ) : ℝ) / J)
    rw [hindices, div_self (by exact_mod_cast (Nat.ne_of_gt hJ) : (J : ℝ) ≠ 0),
      Real.rpow_one]
    exact hhigh
  obtain ⟨i, hi, hlo, hhi⟩ := exists_adjacent_crossing y (p : ℝ) hzero hend
  refine ⟨r + i, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
  apply (mem_primeBin_iff hx J (r + i) p).mpr
  refine ⟨hp, hlo, ?_⟩
  simpa only [y, Nat.cast_add, Nat.cast_one, add_assoc] using hhi

/-- Smoothness at a rational endpoint is exactly vanishing of the higher-bin
multiplicity counts, provided `1 ≤ n ≤ x`. -/
theorem maxPrimeFac_le_iff_higher_counts_zero {x : ℝ} (hx : 1 ≤ x)
    {J r n : ℕ} (hJ : 0 < J) (hr : r ≤ J) (hn : 1 ≤ n) (hnx : (n : ℝ) ≤ x) :
    (n.maxPrimeFac : ℝ) ≤ x ^ ((r : ℝ) / J) ↔
      ∀ k ∈ Finset.Ico r J, binCount (primeBin x J k) n = 0 := by
  have hnzero : n ≠ 0 := by omega
  have hxzero : 0 ≤ x := le_trans zero_le_one hx
  constructor
  · intro hsmooth k hk
    apply binCount_eq_zero_of_no_factor
    intro p hp hpdiv
    obtain ⟨hpprime, hplower, _⟩ := (mem_primeBin_iff hxzero J k p).mp hp
    have hpmax : (p : ℝ) ≤ n.maxPrimeFac := by
      exact_mod_cast Nat.le_maxPrimeFac hnzero hpprime hpdiv
    have hexp : (r : ℝ) / J ≤ (k : ℝ) / J :=
      div_le_div_of_nonneg_right (by exact_mod_cast (Finset.mem_Ico.mp hk).1) (Nat.cast_nonneg _)
    have hpower := Real.rpow_le_rpow_of_exponent_le hx hexp
    linarith
  · intro hcounts
    by_cases hone : n = 1
    · subst n
      simpa using Real.one_le_rpow hx (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg J))
    by_contra hsmooth
    have hpprime := Nat.prime_maxPrimeFac_of_one_lt (show 1 < n by omega)
    have hpupper : (n.maxPrimeFac : ℝ) ≤ x := by
      have hpn : (n.maxPrimeFac : ℝ) ≤ n := by exact_mod_cast Nat.maxPrimeFac_le (n := n)
      exact hpn.trans hnx
    obtain ⟨k, hk, hpmem⟩ := exists_higher_primeBin hxzero hJ hr hpprime
      (lt_of_not_ge hsmooth) hpupper
    have hpcount : 0 < n.factorization n.maxPrimeFac :=
      hpprime.factorization_pos_of_dvd hnzero Nat.maxPrimeFac_dvd
    have hle : n.factorization n.maxPrimeFac ≤ binCount (primeBin x J k) n :=
      Finset.single_le_sum (fun p _ => Nat.zero_le (n.factorization p)) hpmem
    rw [hcounts k hk] at hle
    omega


end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalInput
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published one-variable distribution input

G. Tenenbaum, *A rate estimate in Billingsley's theorem for the size
distribution of large prime factors*, Quart. J. Math. 51 (2000), 385–403:
the unnumbered main Theorem, parts (i), (iii) at H = 0, equations (1.1),
(1.3), and the multiplicity remark following (1.7), printed pp. 386–388.
Author's corrected version: https://tenenb.perso.math.cnrs.fr/PPP/Billingsley.pdf

The input below is only its finite-bin consequence. Thresholds are the
fixed positive numbers k/J; hence finitely many ranks suffice. Continuity
of the limiting distribution permits replacing the counting endpoint by
A*x and the rank thresholds by powers of x. Its first-rank marginal is
the classical Dickman law. No statement about two different integers,
residue restrictions, weights, or short intervals is included.
-/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem canonicalBinVector_val {J : ℕ} (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A*x →
      ∀ i : Fin (J-1), (canonicalBinVector J x n i).val =
        binCount (primeBin x J (i.val+1)) n := by
  filter_upwards [primeBin_count_eventually_le J hJ A] with x hx n hn hnx i
  exact min_eq_left (hx (i.val+1) (by omega) n hn hnx)

theorem finite_state_sum {G R : Type*} [Fintype G] [DecidableEq G]
    [CommSemiring R] (S : Finset ℕ) (v : ℕ → G) (f : G → R) :
    (∑ n ∈ S, f (v n)) = ∑ r : G, ((S.filter (fun n => v n = r)).card : R)*f r := by
  classical
  calc
    _ = ∑ n ∈ S, ∑ r : G, if v n = r then f r else 0 := by simp
    _ = ∑ r : G, ∑ n ∈ S, if v n = r then f r else 0 := sum_comm
    _ = _ := by simp only [← sum_filter,sum_const,nsmul_eq_mul]

theorem canonical_binLabel_mean
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ =>
      (∑ n ∈ Ioc 0 ⌊A*x⌋₊, binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n)/
        (A*x : ℂ)) atTop
      (𝓝 (∑ r : BinCountState J, (ν r : ℂ)*∏ i, ζ i^(r i).val)) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    ((Complex.continuous_ofReal.tendsto _).comp (hν A hA r)).mul_const
      (∏ i : Fin (J-1), ζ i^(r i).val))
  apply ht.congr'
  filter_upwards [canonicalBinVector_val hJ A] with x hx
  symm
  have he : ∀ n ∈ Ioc 0 ⌊A*x⌋₊,
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ n =
        ∏ i, ζ i^(canonicalBinVector J x n i).val := by
    intro n hn
    have hn0 : 1 ≤ n := (mem_Ioc.mp hn).1
    rw [binLabel_apply (by omega : n ≠ 0)]
    apply prod_congr rfl
    intro i _
    rw [hx n hn0 ((Nat.le_floor_iff' (by omega : n ≠ 0)).mp (mem_Ioc.mp hn).2) i]
  rw [sum_congr rfl he,finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x)
    (fun r : BinCountState J => ∏ i, ζ i^(r i).val)]
  simp only [sum_div,Function.comp_apply,binStateDensity,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_mul]
  apply sum_congr rfl
  intro r _
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinMarginalMean
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered prefix means supplied by the one-variable distribution -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem binDistributionMean_norm_le_one {J : ℕ} (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    ‖binDistributionMean ν ζ‖ ≤ 1 := by
  unfold binDistributionMean
  calc
    _ ≤ ∑ r : BinCountState J, ‖(ν r : ℂ)*∏ i, ζ i^(r i).val‖ := norm_sum_le _ _
    _ = ∑ r : BinCountState J, ν r := by
      apply sum_congr rfl
      intro r _
      simp [norm_prod,norm_pow,hζ,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hν r)]
    _ = 1 := hνone

theorem centeredBinPrefix_tendsto {J : ℕ} (hJ : 0 < J)
    (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) {A : ℝ} (hA : 0 < A) :
    Tendsto (centeredBinPrefix J ζ (binDistributionMean ν ζ) A) atTop (𝓝 0) := by
  have hmean := canonical_binLabel_mean hJ ν hν ζ hA
  have hfloor := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp
    ((tendsto_nat_floor_div_atTop (R := ℝ)).comp (tendsto_id.const_mul_atTop hA))
  have hh := hmean.sub (hfloor.const_mul (binDistributionMean ν ζ))
  convert hh using 1
  · funext x
    simp only [centeredBinPrefix,binDistributionMean,sum_sub_distrib,sum_const,
      nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero,sub_div,Complex.ofReal_div,Complex.ofReal_natCast,
      Complex.ofReal_mul,Function.comp_apply,id_eq]
    ring
  · simp [binDistributionMean]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsequencePositiveGraph
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive arithmetic graph energy along a prescribed bad subsequence -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_graph
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    (J₂ : ℕ) (hJ₂ : 0 < J₂) (k₂ : κ → ℕ) (hk₂ : ∀ i, 1 ≤ k₂ i)
    (z₂ : κ → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1) (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J₁ k₁ z₁ (r N) n) * (movingBinLabel J₂ k₂ z₂ (r N) (n+1)-μ)) /
        (r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ e : ℝ, 0 < e ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → τ ≤ samplingTau →
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
          ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
            e ≤ arithmeticOffDiagonalGraph B L τ C (amplificationMultiplier B) (r (s N))
              (fun n => movingBinLabel J₂ k₂ z₂ (r (s N)) n-μ) /
                ((B : ℝ)*amplificationMultiplier B) := by
  let H : ℕ → ℕ → ℂ := fun N n => movingBinLabel J₂ k₂ z₂ N (n+1)-μ
  have hH : ∀ N n, ‖H N n‖ ≤ 2 := fun N n =>
    norm_centered_binLabel_le_two (fun i => primeBin (N : ℝ) J₂ (k₂ i)) z₂ hz₂ μ hμ (n+1)
  obtain ⟨s,hs,e,he,hE⟩ := nonzero_binLabel_correlation_along_forces_energy_jd
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ H hH r hr hβ hmean
  refine ⟨s,hs,e/2,half_pos he,?_⟩
  intro L τ hL hτ hτsmall
  obtain ⟨C₀,hC₀,hC⟩ := hE L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  intro C hCC
  have hOff := positive_offDiagonal_of_energy hFord hM hL hτ.le hτsmall C H hH (r ∘ s) (hr.comp hs) he (hC C hCC)
  filter_upwards [hOff,amplificationMultiplier_le_cutoff] with B hB hT
  have hgraph := centered_binLabel_offDiagonal_graph J₂ hJ₂ k₂ hk₂ z₂ μ B L τ C
    (amplificationMultiplier B) hT
  filter_upwards [hB,(hr.comp hs).tendsto_atTop.eventually hgraph] with N hN hGN
  simp only [Function.comp_apply] at hGN
  change e/2 ≤ firstFormOffDiagonal B L τ C (amplificationOuterWeight B)
    (amplificationInnerWeight (amplificationMultiplier B))
    (fun m => movingBinLabel J₂ k₂ z₂ (r (s N)) (m+1)-μ) (r (s N)) / _ at hN
  rwa [hGN] at hN

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SubsequencePositiveBlocks
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonzero bin-label correlation forces positive finite block energy -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem nonzero_binLabel_correlation_along_forces_blocks
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    (J₂ : ℕ) (hJ₂ : 0 < J₂) (k₂ : κ → ℕ) (hk₂ : ∀ i, 1 ≤ k₂ i)
    (z₂ : κ → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1) (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ} (hβ : β ≠ 0)
    (hmean : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J₁ k₁ z₁ (r N) n) * (movingBinLabel J₂ k₂ z₂ (r N) (n+1)-μ)) /
        (r N : ℂ)) atTop (nhds β)) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧ ∃ (e : ℝ) (A : ℕ), 0 < e ∧ 0 < A ∧
      ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ → τ ≤ samplingTau →
        ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
          ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
            e ≤ arithmeticBlockAverage B L τ C (amplificationMultiplier B) (r (s N))
              (amplificationMultiplier B/A) (A*amplificationMultiplier B)
              (fun n => movingBinLabel J₂ k₂ z₂ (r (s N)) n-μ) := by
  obtain ⟨s,hs,e,he,hgraph⟩ := nonzero_binLabel_correlation_along_forces_graph
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ J₂ hJ₂ k₂ hk₂ z₂ hz₂ μ hμ r hr hβ hmean
  obtain ⟨A,hA,hblocks⟩ := positive_blocks_of_graph_jd hFord hM he
  refine ⟨s,hs,e/2,A,half_pos he,hA,?_⟩
  intro L τ hL hτ hτsmall
  obtain ⟨C₀,hC₀,hC⟩ := hgraph L τ hL hτ hτsmall
  refine ⟨C₀,hC₀,?_⟩
  intro C hCC
  exact hblocks L τ C (r ∘ s) (hr.comp hs)
    (fun N n => movingBinLabel J₂ k₂ z₂ N n-μ)
    (fun N n => norm_centered_binLabel_le_two
      (fun i => primeBin (N : ℝ) J₂ (k₂ i)) z₂ hz₂ μ hμ n) (hC C hCC)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.TwoPointCorrelations_MRTMultiplicativeReduction
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The general-multiplicative reduction in corrected MRT §3.  The completely
multiplicative part keeps the original values at primes; the convolution
correction vanishes at primes and is bounded by two at higher prime powers. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

@[simp] lemma mrtArithmetic_apply_pos (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrtArithmetic f n = f n := ite_eq_right hn.ne'

end TwoPointCorrelations

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_ArithmeticBlockMeanDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem arithmetic_block_centered_mean_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {A L : ℕ} {cap : ℝ} (hA : 0 < A) (hL : 10000 ≤ L) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
    ∀ ε : ℝ, 0 < ε → ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      let T := amplificationMultiplier B
      |arithmeticBlockAverage B L τ C T N (T/A) (A*T)
        (fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ)| < ε := by
  obtain ⟨τ,hτ,hτcap,hτsmall,hfinite⟩ := finite_graph_centered_mean_proved_jd hKMT hFord hSD hSW hM hMP hMC
    hJ ζ hζ μ hμ hmean hA hL hcap
  refine ⟨τ,hτ,hτcap,hτsmall,?_⟩
  intro ε hε
  obtain ⟨Cmin,hCmin,hbound⟩ := hfinite (ε/2) (half_pos hε)
  refine ⟨Cmin,hCmin,?_⟩
  intro C hC
  filter_upwards [hbound C hC,rawArithmeticGraphKernel_uniform_bound (by omega : 1 ≤ L) hτ.le hτsmall,
    amplificationMultiplier_comparable,eventually_gt_atTop 0] with B hb hraw hT hB
  let T := amplificationMultiplier B
  let M := A*T
  let R : ℝ := (arithmeticGraphTriples B T).card
  have hM0 : 0 < M := Nat.mul_pos hA hT.1
  have hbd := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (16*(M : ℝ)^2*R/(T : ℝ))).eventually
    (Iio_mem_nhds (half_pos hε))
  filter_upwards [hb,hbd] with N hN hboundary
  let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
  have hz : ∀ n, ‖z n‖ ≤ 2 := fun n => norm_centered_binLabel_le_two _ ζ hζ μ hμ n
  have hp := arithmeticBlockAverage_prefix_bound (H := T/A) hB hT.1 hM0 (show 0 ≤ R from Nat.cast_nonneg _)
    (hraw C T N) z hz
  have hsub : (∑ u ∈ range (2*T*N), |(complexEnergy (finiteGraphKernel B L T (T/A) M N u τ C)
      (fun i => z (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) ≤
      (∑ u ∈ range (4*T*N), |(complexEnergy (finiteGraphKernel B L T (T/A) M N u τ C)
      (fun i => z (u+(i.val+1)))).re|/(M : ℝ))/((T : ℝ)*N) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply sum_le_sum_of_subset_of_nonneg (range_mono (Nat.mul_le_mul_right N (Nat.mul_le_mul_right T (by decide : 2 ≤ 4))))
    intro u _ _
    positivity
  have he : 16*(M : ℝ)^2*R/((T : ℝ)*N) = (16*(M : ℝ)^2*R/(T : ℝ))/(N : ℝ) := by ring
  rw [he] at hp
  change _ < ε/2 at hN
  change _ < ε/2 at hboundary
  change _ < ε
  linarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinCorrelationLimitDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem bin_correlation_limit_zero_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    {J₂ : ℕ} (hJ₂ : 0 < J₂) (z₂ : Fin (J₂-1) → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hcenter : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J₂ z₂ μ D) atTop (𝓝 0))
    (r : ℕ → ℕ) (hr : StrictMono r) {β : ℂ}
    (hlimit : Tendsto (fun N => (∑ n ∈ range (r N),
      star (movingBinLabel J₁ k₁ z₁ (r N) n) *
        (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ (r N) (n+1)-μ))/(r N : ℂ))
      atTop (𝓝 β)) : β = 0 := by
  by_contra hβ
  obtain ⟨s,hs,e,A,he,hA,hpositive⟩ := nonzero_binLabel_correlation_along_forces_blocks
    hFord hSD hM hMP J₁ hJ₁ k₁ hk₁ z₁ hz₁ J₂ hJ₂ (fun i : Fin (J₂-1) => i.val+1)
    (fun _ => by omega) z₂ hz₂ μ hμ r hr hβ hlimit
  obtain ⟨τ,hτ,_,hτsmall,hzero⟩ := arithmetic_block_centered_mean_proved hKMT hFord hSD hSW hM hMP hMC
    hJ₂ z₂ hz₂ μ hμ hcenter hA (by norm_num : 10000 ≤ (10000 : ℕ)) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C₀,hC₀,hpos⟩ := hpositive 10000 τ (by norm_num) hτ hτsmall
  obtain ⟨C₁,hC₁,hneg⟩ := hzero (e/2) (half_pos he)
  have hp := hpos (max C₀ C₁) (le_max_left _ _)
  have hn := hneg (max C₀ C₁) (le_max_right _ _)
  have hfalse : ∀ᶠ B : ℕ in atTop, False := by
    filter_upwards [hp,hn] with B hb hsmall
    have hsmall' := (hr.comp hs).tendsto_atTop.eventually hsmall
    obtain ⟨N,hN,hNsmall⟩ := (hb.and hsmall').exists
    have hh : e ≤ |arithmeticBlockAverage B 10000 τ (max C₀ C₁) (amplificationMultiplier B)
        (r (s N)) (amplificationMultiplier B/A) (A*amplificationMultiplier B)
        (fun n => movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ (r (s N)) n-μ)| :=
      hN.trans (le_abs_self _)
    change _ < e/2 at hNsmall
    simp only [movingBinLabel,Function.comp_apply] at hh hNsmall
    linarith only [hh,hNsmall,he]
  exact hfalse.exists.elim (fun _ h => h)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinDecorrelation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered bin labels at consecutive integers decorrelate -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem centeredBinCorrelation_norm_le_two {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (k₁ : ι → ℕ) (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    (J₂ : ℕ) (z₂ : Fin (J₂-1) → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1) (N : ℕ) :
    ‖centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ N‖ ≤ 2 := by
  have hterm (n : ℕ) : ‖star (movingBinLabel J₁ k₁ z₁ N n) *
      (movingBinLabel J₂ (fun i : Fin (J₂-1) => i.val+1) z₂ N (n+1)-μ)‖ ≤ 2 := by
    rw [norm_mul,norm_star]
    have h₁ := norm_binLabel_le_one (fun i => primeBin (N : ℝ) J₁ (k₁ i)) z₁ hz₁ n
    have h₂ := norm_centered_binLabel_le_two (fun i : Fin (J₂-1) => primeBin (N : ℝ) J₂ (i.val+1))
      z₂ hz₂ μ hμ (n+1)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  unfold centeredBinCorrelation
  rw [norm_div,Complex.norm_natCast]
  by_cases hN : N = 0
  · simp [hN]
  have hs := norm_sum_le_of_le (range N) (fun n _ => hterm n)
  simp only [sum_const,nsmul_eq_mul,Finset.card_range] at hs
  exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < N)).mpr (by simpa only [mul_comm] using hs)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinDecorrelationDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem centeredBinCorrelation_tendsto_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {ι : Type*} [Fintype ι]
    (J₁ : ℕ) (hJ₁ : 0 < J₁) (k₁ : ι → ℕ) (hk₁ : ∀ i, 1 ≤ k₁ i)
    (z₁ : ι → ℂ) (hz₁ : ∀ i, ‖z₁ i‖ = 1)
    {J₂ : ℕ} (hJ₂ : 0 < J₂) (z₂ : Fin (J₂-1) → ℂ) (hz₂ : ∀ i, ‖z₂ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hcenter : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J₂ z₂ μ D) atTop (𝓝 0)) :
    Tendsto (centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨r,hr,hnr⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hbound (n : ℕ) : centeredBinCorrelation J₁ k₁ z₁ J₂ z₂ μ (ns (r n)) ∈
      Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact centeredBinCorrelation_norm_le_two J₁ k₁ z₁ hz₁ J₂ z₂ hz₂ μ hμ _
  obtain ⟨β,_,s,hs,hlim⟩ := (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq hbound
  have hzero : β = 0 := bin_correlation_limit_zero_proved hKMT hFord hSD hSW hM hMP hMC
    J₁ hJ₁ k₁ hk₁ z₁ hz₁ hJ₂ z₂ hz₂ μ hμ hcenter (ns ∘ r ∘ s) (hnr.comp hs) hlim
  exact ⟨r ∘ s,by simpa only [hzero,Function.comp_def] using hlim⟩

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_FiniteStatistics
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite character tests determine joint statistics

This is the finite Fourier inversion step in `sections/distribution.tex`.
It is an algebraic transfer lemma, not an assumed arithmetic decorrelation
result. The arithmetic correlation limits still have to be established.
-/

open Filter Finset Module
open scoped Topology

namespace JointDickman

private theorem linear_expansion {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Basis ι ℂ E)
    (L : E →ₗ[ℂ] ℂ) (v : E) :
    L v = ∑ i, b.repr v i * L (b i) := by
  calc
    L v = L (∑ i, b.repr v i • b i) := congrArg L (b.sum_repr v).symm
    _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

/-- Convergence of linear statistics on a finite basis determines every statistic. -/
theorem tendsto_linear_of_basis {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Basis ι ℂ E)
    (Q : ℕ → E →ₗ[ℂ] ℂ) (L : E →ₗ[ℂ] ℂ)
    (h : ∀ i, Tendsto (fun N => Q N (b i)) atTop (𝓝 (L (b i))))
    (v : E) : Tendsto (fun N => Q N v) atTop (𝓝 (L v)) := by
  simp_rw [linear_expansion b _ v]
  exact tendsto_finsetSum Finset.univ fun i _ => tendsto_const_nhds.mul (h i)

/-- Convergence on all pairs of finite basis vectors determines a bilinear statistic. -/
theorem tendsto_bilinear_of_bases {ι κ E F : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (b : Basis ι ℂ E) (c : Basis κ ℂ F)
    (Q : ℕ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (L : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ i j, Tendsto (fun N => Q N (b i) (c j)) atTop (𝓝 (L (b i) (c j))))
    (v : E) (w : F) : Tendsto (fun N => Q N v w) atTop (𝓝 (L v w)) := by
  have hb (i : ι) : Tendsto (fun N => Q N (b i) w) atTop (𝓝 (L (b i) w)) :=
    tendsto_linear_of_basis c (fun N => Q N (b i)) (L (b i)) (h i) w
  exact tendsto_linear_of_basis b (fun N => (Q N).flip w) (L.flip w) hb v

/-- For the finite bin-count group, character-pair limits imply limits for every
pair of bin events. This does not assert those character-pair limits. -/
theorem tendsto_of_character_pairs {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (Q : ℕ → (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ)
    (L : (G → ℂ) →ₗ[ℂ] (H → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => Q N χ ψ) atTop (𝓝 (L χ ψ)))
    (f : G → ℂ) (g : H → ℂ) :
    Tendsto (fun N => Q N f g) atTop (𝓝 (L f g)) := by
  exact tendsto_bilinear_of_bases (AddChar.complexBasis G) (AddChar.complexBasis H)
    Q L (by simpa only [AddChar.complexBasis_apply] using h) f g

/-- The concrete empirical form of finite Fourier inversion. Every pair of
test functions has the product limit once every pair of characters does. -/
theorem jointStatistic_factorization {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (s : ℕ → Finset ℕ) (w : ℕ → ℂ) (u : ℕ → ℕ → G) (v : ℕ → ℕ → H)
    (μ : G → ℂ) (ν : H → ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => w N * ∑ n ∈ s N, χ (u N n) * ψ (v N n)) atTop
        (𝓝 ((∑ a, μ a * χ a) * (∑ b, ν b * ψ b))))
    (f : G → ℂ) (g : H → ℂ) :
    Tendsto (fun N => w N * ∑ n ∈ s N, f (u N n) * g (v N n)) atTop
      (𝓝 ((∑ a, μ a * f a) * (∑ b, ν b * g b))) := by
  exact tendsto_of_character_pairs
    (fun N => jointStatistic (s N) (w N) (u N) (v N))
    (productMean (weightedMean μ) (weightedMean ν)) h f g

/-- In particular, all pairs of events factor. These are precisely the
bin events used to test smoothness at rational powers. -/
theorem jointEvent_factorization {G H : Type*}
    [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (s : ℕ → Finset ℕ) (w : ℕ → ℂ) (u : ℕ → ℕ → G) (v : ℕ → ℕ → H)
    (μ : G → ℂ) (ν : H → ℂ)
    (h : ∀ (χ : AddChar G ℂ) (ψ : AddChar H ℂ),
      Tendsto (fun N => w N * ∑ n ∈ s N, χ (u N n) * ψ (v N n)) atTop
        (𝓝 ((∑ a, μ a * χ a) * (∑ b, ν b * ψ b))))
    (A : G → Prop) (B : H → Prop) [DecidablePred A] [DecidablePred B] :
    Tendsto (fun N => w N * ∑ n ∈ s N,
      (if A (u N n) ∧ B (v N n) then (1 : ℂ) else 0)) atTop
      (𝓝 ((∑ a with A a, μ a) * (∑ b with B b, ν b))) := by
  have hind (a : G) (b : H) :
      (if A a then (1 : ℂ) else 0) * (if B b then 1 else 0) =
        if A a ∧ B b then 1 else 0 := by
    by_cases ha : A a <;> by_cases hb : B b <;> simp [ha, hb]
  simpa only [hind, mul_ite, mul_one, mul_zero, ← Finset.sum_filter] using
    jointStatistic_factorization s w u v μ ν h
      (fun a => if A a then 1 else 0) (fun b => if B b then 1 else 0)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_BinCharacters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characters of the finite bin-count group are unit bin labels -/
namespace JointDickman
open Finset Classical
open scoped Fin.NatCast

theorem binCharacterNodes_norm {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (i : Fin (J-1)) : ‖binCharacterNodes χ i‖ = 1 := χ.norm_apply _

theorem binCharacter_apply {J : ℕ} (χ : AddChar (BinCountState J) ℂ) (r : BinCountState J) :
    χ r = ∏ i, binCharacterNodes χ i^(r i).val := by
  have hn (n : ℕ) : n • (1 : Fin (J+1)) = (n : Fin (J+1)) := by
    induction n with
    | zero => simp
    | succ n ih => simp only [succ_nsmul,ih,Nat.cast_add,Nat.cast_one]
  have he : r = ∑ i : Fin (J-1), (r i).val • Pi.single i (1 : Fin (J+1)) := by
    funext j
    simp only [Finset.sum_apply,Pi.smul_apply]
    simp only [Pi.single_apply,smul_ite,smul_zero,sum_ite_eq,mem_univ,ite_true, if_true]
    rw [hn,Fin.cast_val_eq_self]
  conv_lhs => rw [he]
  have hsum (s : Finset (Fin (J-1))) :
      χ (∑ i ∈ s, (r i).val • Pi.single i (1 : Fin (J+1))) =
        ∏ i ∈ s, χ ((r i).val • Pi.single i (1 : Fin (J+1))) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [sum_insert hi,prod_insert hi,χ.map_add_eq_mul,ih]
  rw [hsum]
  apply prod_congr rfl
  intro i _
  exact χ.map_nsmul_eq_pow _ _

theorem binCharacter_canonical {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    {x : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hcounts : ∀ i : Fin (J-1), (canonicalBinVector J x n i).val = binCount (primeBin x J (i.val+1)) n) :
    χ (canonicalBinVector J x n) =
      binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) (binCharacterNodes χ) n := by
  rw [binCharacter_apply,binLabel_apply hn]
  apply prod_congr rfl
  intro i _
  rw [hcounts i]

theorem binCharacter_mean {J : ℕ} (χ : AddChar (BinCountState J) ℂ)
    (ν : BinCountState J → ℝ) :
    binDistributionMean ν (binCharacterNodes χ) = ∑ r, (ν r : ℂ)*χ r := by
  simp only [binDistributionMean,binCharacter_apply]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinPrefixMeans
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary prefix means of the finite bin labels -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem sum_Ioc_zero_eq_range_add {R : Type*} [AddCommGroup R] (f : ℕ → R) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = (∑ n ∈ range N, f n)+f N-f 0 := by
  have hs : insert 0 (Ioc 0 N) = range (N+1) := by
    ext n
    simp only [mem_insert,mem_Ioc,mem_range]
    omega
  have hh := congrArg (fun S : Finset ℕ => ∑ n ∈ S, f n) hs
  rw [sum_insert (by simp),sum_range_succ] at hh
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using hh

theorem binLabel_endpoint_div_tendsto_zero {J : ℕ} (ζ : Fin (J-1) → ℂ)
    (hζ : ∀ i, ‖ζ i‖ = 1) :
    Tendsto (fun N : ℕ => binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) ζ N/(N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun N : ℕ => 1/(N : ℝ))
  · intro N
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_binLabel_le_one _ ζ hζ N) (Nat.cast_nonneg N)
  · exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1

theorem binLabel_prefix_mean
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) ζ n)/(N : ℂ)) atTop
      (𝓝 (binDistributionMean ν ζ)) := by
  have hi := (canonical_binLabel_mean hJ ν hν ζ (by norm_num : (0 : ℝ) < 1)).comp tendsto_natCast_atTop_atTop
  have he := binLabel_endpoint_div_tendsto_zero ζ hζ
  have hres := hi.sub he
  convert hres using 1
  · funext N
    simp only [Function.comp_apply,one_mul,Nat.floor_natCast,Complex.ofReal_natCast,Complex.ofReal_one,
      sum_Ioc_zero_eq_range_add,binLabel_apply_zero,sub_zero,add_div]
    ring
  · simp only [sub_zero,binDistributionMean]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_BinCharacterPairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair limits for the unit bin labels attached to finite characters -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem star_binLabel_star {ι : Type*} [Fintype ι] (E : ι → Finset ℕ) (z : ι → ℂ) (n : ℕ) :
    star (binLabel E (fun i => star (z i)) n) = binLabel E z n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp only [binLabel_apply hn,star_prod,star_pow,star_star]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalCharacterPairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring label pair limits to the finite observed count group -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem canonicalBinVector_zero (J : ℕ) (x : ℝ) : canonicalBinVector J x 0 = 0 := by
  funext i
  apply Fin.ext
  simp [canonicalBinVector,binCount]

theorem canonicalBinVector_one (J : ℕ) (x : ℝ) : canonicalBinVector J x 1 = 0 := by
  funext i
  apply Fin.ext
  simp [canonicalBinVector,binCount]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinJointEvents
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Fourier inversion gives every joint bin event -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem higherBinEvent_iff {J k n : ℕ} {x : ℝ} (hJ : 0 < J) (hk : 0 < k) :
    higherBinEvent J k (canonicalBinVector J x n) ↔
      ∀ i ∈ Ico k J, binCount (primeBin x J i) n = 0 := by
  have hzero (i : Fin (J-1)) : canonicalBinVector J x n i = 0 ↔
      binCount (primeBin x J (i.val+1)) n = 0 := by
    simp only [canonicalBinVector,Fin.ext_iff,Fin.val_zero]
    omega
  constructor
  · intro h i hi
    have hi0 : 0 < i := hk.trans_le (mem_Ico.mp hi).1
    let a : Fin (J-1) := ⟨i-1,by have := (mem_Ico.mp hi).2; omega⟩
    have ha : a.val+1 = i := by dsimp [a]; omega
    have hh := (hzero a).mp (h a (by rw [ha]; exact (mem_Ico.mp hi).1))
    rwa [ha] at hh
  · intro h i hi
    apply (hzero i).mpr
    exact h (i.val+1) (mem_Ico.mpr ⟨hi,by have := i.isLt; omega⟩)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_BinCharacterPairsDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem bin_character_pair_limit_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (χ ψ : AddChar (BinCountState J) ℂ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes χ) n *
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes ψ) (n+1))/(N : ℂ))
      atTop (𝓝 ((∑ r, (ν r : ℂ)*χ r)*(∑ r, (ν r : ℂ)*ψ r))) := by
  let μ := binDistributionMean ν (binCharacterNodes ψ)
  have hμ : ‖μ‖ ≤ 1 := binDistributionMean_norm_le_one ν hν hνone _ (binCharacterNodes_norm ψ)
  have hcenter (A : ℝ) (hA : 0 < A) := centeredBinPrefix_tendsto hJ ν hνmean (binCharacterNodes ψ) hA
  have hcor := centeredBinCorrelation_tendsto_proved hKMT hFord hSD hSW hM hMP hMC
    J hJ (fun i : Fin (J-1) => i.val+1) (fun _ => by omega)
    (fun i => star (binCharacterNodes χ i))
    (fun i => by simpa only [norm_star] using binCharacterNodes_norm χ i)
    hJ (binCharacterNodes ψ) (binCharacterNodes_norm ψ) μ hμ hcenter
  have hfirst := binLabel_prefix_mean hJ ν hνmean (binCharacterNodes χ) (binCharacterNodes_norm χ)
  have hh := hcor.add (hfirst.mul_const μ)
  convert hh using 1
  · funext N
    simp only [centeredBinCorrelation,movingBinLabel,star_binLabel_star]
    rw [div_mul_eq_mul_div,sum_mul,← add_div,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n _
    ring
  · simp only [zero_add,μ,binCharacter_mean]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Analysis_CanonicalCharacterPairsDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem canonical_character_pair_limit_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (χ ψ : AddChar (BinCountState J) ℂ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      χ (canonicalBinVector J (N : ℝ) n)*ψ (canonicalBinVector J (N : ℝ) (n+1)))/(N : ℂ))
      atTop (𝓝 ((∑ r, (ν r : ℂ)*χ r)*(∑ r, (ν r : ℂ)*ψ r))) := by
  have hl := bin_character_pair_limit_proved hKMT hFord hSD hSW hM hMP hMC hJ ν hν hνone hνmean χ ψ
  have hsmall := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℂ) (1 : ℂ)
  have hfull := hl.add hsmall
  rw [add_zero] at hfull
  apply hfull.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (canonicalBinVector_val hJ 2),
    eventually_gt_atTop 0] with N hcounts hN
  have hp (n : ℕ) (hn : n ∈ range N) :
      χ (canonicalBinVector J (N : ℝ) n)*ψ (canonicalBinVector J (N : ℝ) (n+1)) =
      binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes χ) n *
        binLabel (fun i : Fin (J-1) => primeBin (N : ℝ) J (i.val+1)) (binCharacterNodes ψ) (n+1)+
      (if n = 0 then (1 : ℂ) else 0) := by
    have hnN := mem_range.mp hn
    by_cases hn0 : n = 0
    · subst n
      simp [canonicalBinVector_zero,canonicalBinVector_one]
    · have hle : (n : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast (by omega : n ≤ 2*N)
      have hle' : (n+1 : ℕ) ≤ 2*N := by have := mem_range.mp hn; omega
      rw [binCharacter_canonical χ hn0 (hcounts n (by omega) hle),
        binCharacter_canonical ψ (by omega) (hcounts (n+1) (by omega) (by exact_mod_cast hle')),
        ite_eq_right hn0,add_zero]
  have he := sum_congr rfl hp
  rw [sum_add_distrib,sum_ite_eq',ite_eq_left (mem_range.mpr hN)] at he
  rw [he,add_div]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_BinJointEventsDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem bin_joint_event_limit_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (P Q : BinCountState J → Prop) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if P (canonicalBinVector J (N : ℝ) n) ∧ Q (canonicalBinVector J (N : ℝ) (n+1))
        then (1 : ℂ) else 0)/(N : ℂ)) atTop
      (𝓝 (((∑ r with P r, ν r : ℝ) : ℂ)*((∑ r with Q r, ν r : ℝ) : ℂ))) := by
  have hc (χ ψ : AddChar (BinCountState J) ℂ) :=
    canonical_character_pair_limit_proved hKMT hFord hSD hSW hM hMP hMC hJ ν hν hνone hνmean χ ψ
  have he := jointEvent_factorization (G := BinCountState J) (H := BinCountState J)
    (fun N => range N) (fun N => 1/(N : ℂ))
    (fun N n => canonicalBinVector J (N : ℝ) n)
    (fun N n => canonicalBinVector J (N : ℝ) (n+1))
    (fun r => (ν r : ℂ)) (fun r => (ν r : ℂ))
    (fun χ ψ => by simpa only [one_div_mul_eq_div] using hc χ ψ) P Q
  simpa only [one_div_mul_eq_div,Complex.ofReal_sum] using he

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_EmpiricalRangeTransfer
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Passing from range averages to the manuscript's interval 2 ≤ n ≤ N -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem bounded_nat_div_tendsto_zero (f : ℕ → ℂ) {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ C) : Tendsto (fun n => f n/(n : ℂ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (g := fun n : ℕ => C/(n : ℝ))
  · intro n
    rw [norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hf n) (Nat.cast_nonneg n)
  · exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C

theorem sum_Icc_two_eq_range {N : ℕ} (hN : 1 ≤ N) (f : ℕ → ℂ) :
    (∑ n ∈ Icc 2 N, f n) = (∑ n ∈ range N, f n)+f N-f 0-f 1 := by
  have hset : insert 1 (Icc 2 N) = Ioc 0 N := by
    ext n
    simp only [mem_insert,mem_Icc,mem_Ioc]
    omega
  have hh := sum_Ioc_zero_eq_range_add f N
  rw [← hset,sum_insert (by simp)] at hh
  linear_combination hh

theorem empirical_limit_of_range_limit (P : ℕ → ℕ → Prop) {L : ℂ}
    (h : Tendsto (fun N => (∑ n ∈ range N, if P N n then (1 : ℂ) else 0)/(N : ℂ)) atTop (𝓝 L)) :
    Tendsto (fun N => (empiricalCount (P N) N : ℂ)/(N : ℂ)) atTop (𝓝 L) := by
  let f := fun N n => if P N n then (1 : ℂ) else 0
  have hb (g : ℕ → ℕ) : Tendsto (fun N => f N (g N)/(N : ℂ)) atTop (𝓝 0) := by
    apply bounded_nat_div_tendsto_zero _ (by norm_num : (0 : ℝ) ≤ 1)
    intro N
    dsimp [f]
    split_ifs <;> norm_num
  have hh := ((h.add (hb id)).sub (hb (fun _ => 0))).sub (hb (fun _ => 1))
  simp only [add_zero,sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := sum_Icc_two_eq_range hN (f N)
  have hc : (empiricalCount (P N) N : ℂ) = ∑ n ∈ Icc 2 N, f N n := by
    simp [empiricalCount,f]
  rw [hc,he]
  dsimp only [f,id_eq]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RationalBinSmooth
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed-scale joint smoothness law at common-denominator thresholds -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem fixedScaleEvent_bin_equiv {J k l N n : ℕ}
    (hJ : 0 < J) (hk : 0 < k) (hkj : k < J) (hl : 0 < l) (hlj : l < J)
    (hN : 1 ≤ N) (hn : n < N) :
    (higherBinEvent J k (canonicalBinVector J (N : ℝ) n) ∧
      higherBinEvent J l (canonicalBinVector J (N : ℝ) (n+1))) ↔
      fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N n := by
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.zero_add,canonicalBinVector_zero,canonicalBinVector_one,higherBinEvent,Pi.zero_apply,
      implies_true,true_and]
    simp [fixedScaleEvent,Real.rpow_nonneg,Real.one_le_rpow hx (show 0 ≤ (l : ℝ)/J by positivity)]
  · have hn1 : 1 ≤ n := by omega
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.le
    have hsN : (n+1 : ℕ) ≤ N := by omega
    rw [higherBinEvent_iff hJ hk,higherBinEvent_iff hJ hl]
    exact and_congr
      (maxPrimeFac_le_iff_higher_counts_zero hx hJ hkj.le hn1 hnN).symm
      (maxPrimeFac_le_iff_higher_counts_zero hx hJ hlj.le (by omega) (by exact_mod_cast hsN)).symm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalThresholds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact common-denominator thresholds for the rational fixed-scale law -/
namespace JointDickman
open Filter
open scoped Topology

theorem rational_threshold_fraction {c : ℚ} (hc : 0 < c) (hc1 : c < 1) :
    0 < c.num.toNat ∧ c.num.toNat < c.den ∧
      (c : ℝ) = (c.num.toNat : ℝ)/(c.den : ℝ) := by
  have hp : 0 < c.num := Rat.num_pos.mpr hc
  have hn : (c.num.toNat : ℝ) = (c.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hp.le
  have he : (c : ℝ) = (c.num.toNat : ℝ)/(c.den : ℝ) := by rw [Rat.cast_def,hn]
  have hd : (0 : ℝ) < c.den := by exact_mod_cast c.den_pos
  have hlt : (c.num.toNat : ℝ) < c.den := by
    apply (div_lt_one hd).mp
    rw [← he]
    exact_mod_cast hc1
  exact ⟨by omega,by exact_mod_cast hlt,he⟩

theorem rational_common_denominator {c d : ℚ}
    (hc : 0 < c) (hc1 : c < 1) (hd : 0 < d) (hd1 : d < 1) :
    ∃ J k l : ℕ, 2 ≤ J ∧ 0 < k ∧ k < J ∧ 0 < l ∧ l < J ∧
      (c : ℝ) = (k : ℝ)/J ∧ (d : ℝ) = (l : ℝ)/J := by
  obtain ⟨hcpos,hclt,hce⟩ := rational_threshold_fraction hc hc1
  obtain ⟨hdpos,hdlt,hde⟩ := rational_threshold_fraction hd hd1
  refine ⟨c.den*d.den,c.num.toNat*d.den,d.num.toNat*c.den,?_,
    Nat.mul_pos hcpos d.den_pos,Nat.mul_lt_mul_of_pos_right hclt d.den_pos,
    Nat.mul_pos hdpos c.den_pos,?_,?_,?_⟩
  · have hcd : 2 ≤ c.den := by omega
    have hdd : 1 ≤ d.den := d.den_pos
    nlinarith
  · simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right hdlt c.den_pos
  · rw [hce]
    push_cast
    have hdn : (d.den : ℝ) ≠ 0 := by exact_mod_cast d.den_ne_zero
    field_simp
  · rw [hde]
    push_cast
    have hcn : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_ne_zero
    have hdn : (d.den : ℝ) ≠ 0 := by exact_mod_cast d.den_ne_zero
    field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Arithmetic_RationalBinSmoothDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem fixedDensity_common_denominator_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : FiniteBinDistributionInput)
    {J k l : ℕ} (hJ : 2 ≤ J) (hk : 0 < k) (hkj : k < J) (hl : 0 < l) (hlj : l < J) :
    Tendsto (fixedDensity ((k : ℝ)/J) ((l : ℝ)/J)) atTop
      (𝓝 (dickmanCDF ((k : ℝ)/J)*dickmanCDF ((l : ℝ)/J))) := by
  obtain ⟨ν,hν,hνone,hνmean,hCDF⟩ := hBill J hJ
  have hh := bin_joint_event_limit_proved hKMT hFord hSD hSW hM hMP hMC
    (by omega : 0 < J) ν hν hνone hνmean (higherBinEvent J k) (higherBinEvent J l)
  have hkCDF : (∑ r with higherBinEvent J k r, ν r) = dickmanCDF ((k : ℝ)/J) := by
    unfold higherBinEvent
    convert hCDF k hk hkj using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
  have hlCDF : (∑ r with higherBinEvent J l r, ν r) = dickmanCDF ((l : ℝ)/J) := by
    unfold higherBinEvent
    convert hCDF l hl hlj using 1
    all_goals try with_reducible_and_instances rfl
    congr 3
  rw [hkCDF,hlCDF] at hh
  have hjoint : Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N n then (1 : ℂ) else 0)/(N : ℂ)) atTop
      (𝓝 (((dickmanCDF ((k : ℝ)/J) : ℝ) : ℂ)*(dickmanCDF ((l : ℝ)/J) : ℂ))) := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    congr 1
    apply sum_congr rfl
    intro n hn
    simp only [fixedScaleEvent_bin_equiv (by omega : 0 < J) hk hkj hl hlj hN (mem_range.mp hn)]
  have he := empirical_limit_of_range_limit (fun N => fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N) hjoint
  have hr := (Complex.continuous_re.tendsto _).comp he
  change Tendsto (fun N => (empiricalCount (fixedScaleEvent ((k : ℝ)/J) ((l : ℝ)/J) N) N : ℝ)/N)
    atTop (𝓝 (dickmanCDF ((k : ℝ)/J)*dickmanCDF ((l : ℝ)/J)))
  simpa only [Function.comp_def,← Complex.ofReal_natCast,← Complex.ofReal_div,
    ← Complex.ofReal_mul,Complex.ofReal_re] using hr

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RationalThresholdsDischarge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem rationalFixedScaleLaw_of_distance_divergence_proved_jd_oai
    (hKMT : CharacterDistanceDivergence) (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput) (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) (hMP : PublishedInputs.PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, PublishedInputs.FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    (hBill : PublishedInputs.FiniteBinDistributionInput) : RationalFixedScaleLaw := by
  intro c d hc hc1 hd hd1
  obtain ⟨J,k,l,hJ,hk,hkj,hl,hlj,hce,hde⟩ := rational_common_denominator hc hc1 hd hd1
  rw [hce,hde]
  exact fixedDensity_common_denominator_proved hKMT hFord hSD hSW hM hMP hMC hBill hJ hk hkj hl hlj

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd_oai := @OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd_oai
