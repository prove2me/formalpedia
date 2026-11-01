-- Prove2me | solution 1 for OAI.JointDickman.tiltedCandidatePairCount_bound_jd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:17:50.567003+00:00
-- url     : https://prove2.me/submissions/87b7c745-dcab-4db0-b5ab-6b3327f47152

import Mathlib
import Definitions.Def_OAIQ083J003
import Theorems.Thm_OAI_JointDickman_active_high_addition_class_bound_jd
import Theorems.Thm_OAI_JointDickman_active_low_addition_class_bound_jd

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
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
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

theorem samplingTau_pos : 0 < samplingTau := by norm_num [samplingTau]

/-- Fixed logarithmic powers are smaller than every positive real power. -/
theorem log_power_div_power_tendsto_zero (r : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun B : ℝ => (Real.log B) ^ r / B ^ s) atTop (𝓝 0) :=
  (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero

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

theorem RegularPrimeSet.total_lower {B L : ℕ} {τ C : ℝ} {S : Finset ℕ}
    (h : RegularPrimeSet B L τ C S) (hL : 1 ≤ L) :
    (1 / 2 - τ) * auxiliaryLogLength B ≤ (S.card : ℝ) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  simpa only [div_self hL0, primePrefix, lt_self_iff_false, ite_false, if_false] using
    (h.1 L (mem_Icc.mpr ⟨hL, le_rfl⟩)).1

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

/-- Every selected coefficient is a unit modulo an allowed lag. -/
theorem auxiliary_product_coprime_lag {B j : ℕ} {A : Finset ℕ}
    (hA : A ⊆ auxiliaryPrimes B) (hj : 0 < j) (hcut : j ≤ auxiliaryCutoff B) :
    (∏ p ∈ A, p : ℕ).Coprime j := by
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hprime := auxiliaryPrimes_prime B p (hA hp)
  have hbig : auxiliaryCutoff B < p := by exact_mod_cast (mem_filter.mp (hA hp)).2
  exact Nat.coprime_of_lt_prime hj.ne' (lt_of_le_of_lt hcut hbig) hprime

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateCountScale
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

theorem omitted_above_count (A R Q : Finset ℕ) (hadd : R \ A ⊆ Q) :
    (((A \ R) \ Q).card : ℝ) =
      (A.card : ℝ)-R.card-((A ∩ Q).card : ℝ)+(R ∩ Q).card := by
  have hsub : R \ Q ⊆ A \ Q := by
    intro p hp
    obtain ⟨hpR,hpQ⟩ := mem_sdiff.mp hp
    refine mem_sdiff.mpr ⟨?_,hpQ⟩
    by_contra hpA
    exact hpQ (hadd (mem_sdiff.mpr ⟨hpR,hpA⟩))
  have he : (A \ R) \ Q = (A \ Q) \ (R \ Q) := by
    ext p
    simp only [Finset.mem_sdiff]
    tauto
  have h₁ := card_sdiff_add_card_eq_card hsub
  have h₂ := card_sdiff_add_card_inter A Q
  have h₃ := card_sdiff_add_card_inter R Q
  rw [← he] at h₁
  have h₁' : (((A \ R) \ Q).card : ℝ)+(R \ Q).card = (A \ Q).card := by exact_mod_cast h₁
  have h₂' : ((A \ Q).card : ℝ)+(A ∩ Q).card = A.card := by exact_mod_cast h₂
  have h₃' : ((R \ Q).card : ℝ)+(R ∩ Q).card = R.card := by exact_mod_cast h₃
  linarith

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

theorem mem_numericAdditionClass {B L e j b d : ℕ} {τ C W : ℝ} {Z : Finset ℕ} :
    Z ∈ numericAdditionClass B L τ C e j b d W ↔
      Z ⊆ auxiliaryPrimes B ∧ Z.card = d ∧
        W ≤ (∏ p ∈ Z, p : ℕ) ∧ ((∏ p ∈ Z, p : ℕ) : ℝ) ≤ 4*W ∧
        ∃ c : ℕ, 0 < c ∧ e*(∏ p ∈ Z, p) = b+j*c ∧
          RegularPrimeSet B L τ C (coefficientPrimeSet B c) := by
  simp only [numericAdditionClass,mem_filter,mem_powerset]

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
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetCountBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting the few omitted primes above an addition prefix -/

namespace JointDickman
open Finset Classical

/-- The exponential generating function used for small omission sets. -/
theorem subset_count_exp_sum (P : Finset ℕ) (t : ℝ) :
    (∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ))) = (1+Real.exp (-t))^P.card := by
  have hh := Finset.prod_add (s := P) (f := fun _ => Real.exp (-t)) (g := fun _ => (1 : ℝ))
  simp only [prod_const,one_pow,mul_one] at hh
  calc
    _ = ∑ A ∈ P.powerset, (Real.exp (-t))^A.card := by
      apply sum_congr rfl
      intro A _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by rw [← hh]; simp [add_comm]

/-- A real count threshold avoids floor errors in the regularity windows. -/
theorem subset_count_exp_bound (P : Finset ℕ) {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ r)).card : ℝ) ≤
      Real.exp (t*r)*(1+Real.exp (-t))^P.card := by
  let I := P.powerset.filter (fun A => (A.card : ℝ) ≤ r)
  have he : (I.card : ℝ)*Real.exp (-t*r) ≤ (1+Real.exp (-t))^P.card := by
    calc
      _ = ∑ _A ∈ I, Real.exp (-t*r) := by simp
      _ ≤ ∑ A ∈ I, Real.exp (-t*(A.card : ℝ)) := by
        apply sum_le_sum
        intro A hA
        exact Real.exp_le_exp.mpr (by nlinarith [(mem_filter.mp hA).2])
      _ ≤ ∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := subset_count_exp_sum P t
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (t*r)).le
  have hc : Real.exp (t*r)*Real.exp (-t*r) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_left_comm (Real.exp (t*r)) (I.card : ℝ),hc,mul_one] at hm
  exact hm

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OmissionEntropy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy cost of high-prime omissions -/

namespace JointDickman
open Finset Classical

/-- The bound uses an upper bound for the population size, so it applies
uniformly throughout a regularity window. -/
theorem subset_count_entropy_of_card_le (P : Finset ℕ) {θ m : ℝ}
    (hθ : 0 < θ) (hθhalf : θ ≤ 1/2) (hcard : (P.card : ℝ) ≤ m) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ θ*m)).card : ℝ) ≤
      Real.exp (m*Real.binEntropy θ) := by
  have hθ1 : θ < 1 := by linarith
  have h1θ : 0 < 1-θ := by linarith
  let t := Real.log (1-θ)-Real.log θ
  have ht : 0 ≤ t := sub_nonneg.mpr (Real.log_le_log hθ (by linarith))
  have he : Real.exp (-t) = θ/(1-θ) := by
    dsimp [t]
    rw [neg_sub,Real.exp_sub,Real.exp_log hθ,Real.exp_log h1θ]
  have hb : 1+Real.exp (-t) = (1-θ)⁻¹ := by rw [he]; field_simp <;> ring
  have hlog : Real.log (1+Real.exp (-t)) = -Real.log (1-θ) := by rw [hb,Real.log_inv]
  have hnon : 0 ≤ Real.log (1+Real.exp (-t)) :=
    Real.log_nonneg (by linarith [Real.exp_pos (-t)])
  have hp : (1+Real.exp (-t))^P.card =
      Real.exp ((P.card : ℝ)*Real.log (1+Real.exp (-t))) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp (t*(θ*m))*(1+Real.exp (-t))^P.card := subset_count_exp_bound P ht _
    _ = Real.exp (t*(θ*m)+(P.card : ℝ)*Real.log (1+Real.exp (-t))) := by rw [hp,Real.exp_add]
    _ ≤ Real.exp (t*(θ*m)+m*Real.log (1+Real.exp (-t))) :=
      Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right hcard hnon])
    _ = _ := by
      rw [hlog]
      congr 1
      simp only [t,Real.binEntropy,Real.log_inv]
      ring

/-- On each endpoint the higher omissions cost an entropy exponent tending
to zero with τ. This statement keeps the exact real threshold 4τℓ. -/
theorem high_omission_count_bound (P : Finset ℕ) {τ ℓ : ℝ}
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (_hℓ : 0 ≤ ℓ)
    (hcard : (P.card : ℝ) ≤ (1/2+τ)*ℓ) :
    ((P.powerset.filter (fun A => (A.card : ℝ) ≤ 4*τ*ℓ)).card : ℝ) ≤
      Real.exp (((1/2+τ)*Real.binEntropy (4*τ/(1/2+τ)))*ℓ) := by
  have hd : 0 < (1/2 : ℝ)+τ := by linarith
  have hθ : 0 < 4*τ/((1/2 : ℝ)+τ) := div_pos (by positivity) hd
  have hh : 4*τ/((1/2 : ℝ)+τ) ≤ 1/2 := (div_le_iff₀ hd).mpr (by linarith)
  have hb := subset_count_entropy_of_card_le P hθ hh hcard
  have he : 4*τ/((1/2 : ℝ)+τ)*(((1/2 : ℝ)+τ)*ℓ) = 4*τ*ℓ := by field_simp
  rw [he] at hb
  calc
    _ ≤ Real.exp (((1/2+τ)*ℓ)*Real.binEntropy (4*τ/(1/2+τ))) := hb
    _ = _ := by congr 1; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularAlternatives
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoding regular alternatives with small additions -/

namespace JointDickman
open Finset Classical

theorem regularSmallAlternatives_omissions {B L k : ℕ} {τ C : ℝ}
    {A R X : Finset ℕ} (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hA : RegularPrimeSet B L τ C A)
    (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
    (((A \ X) \ primePrefix B ((k : ℝ)/L) (A ∪ R)).card : ℝ) ≤
      4*τ*auxiliaryLogLength B := by
  obtain ⟨hsub,hreg,hadd⟩ := mem_filter.mp hX
  have hsub' := mem_powerset.mp hsub
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hXQ : X ∩ Q = primePrefix B ((k : ℝ)/L) X := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr hsub']
  have hcut : X \ A ⊆ Q := hadd.trans (primePrefix_mono B _ (sdiff_subset.trans hsub'))
  have he := omitted_above_count A X Q hcut
  rw [hAQ,hXQ] at he
  have ha := hA.total_upper hL
  have hx := hreg.total_lower hL
  have hap := (hA.1 k hk).1
  have hxp := (hreg.1 k hk).2
  nlinarith

/-- Prefix membership and omitted higher primes determine an alternative
uniquely. This preserves multiplicities without assuming disjoint first
coefficient and remainder sets. -/
theorem regularSmallAlternatives_count {B L k : ℕ} {τ C : ℝ}
    (A R : Finset ℕ) (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hA : RegularPrimeSet B L τ C A) :
    (regularSmallAlternatives B L k τ C A R).card ≤
      2^(primePrefix B ((k : ℝ)/L) (A ∪ R)).card *
        (((A \ primePrefix B ((k : ℝ)/L) (A ∪ R)).powerset).filter
          (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  let enc (X : Finset ℕ) := (X ∩ Q,(A \ X) \ Q)
  let target := Q.powerset.product
    ((A \ Q).powerset.filter (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B))
  have htarget (X : Finset ℕ) (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
      enc X ∈ target := by
    apply mem_product.mpr
    refine ⟨mem_powerset.mpr inter_subset_right,mem_filter.mpr ⟨?_,?_⟩⟩
    · exact mem_powerset.mpr (sdiff_subset_sdiff sdiff_subset subset_rfl)
    · exact regularSmallAlternatives_omissions hL hk hA hX
  have hcut (X : Finset ℕ) (hX : X ∈ regularSmallAlternatives B L k τ C A R) :
      X \ A ⊆ Q := by
    have h := mem_filter.mp hX
    exact h.2.2.trans (primePrefix_mono B _ (sdiff_subset.trans (mem_powerset.mp h.1)))
  have hinj : Set.InjOn enc (regularSmallAlternatives B L k τ C A R) := by
    intro X hX Y hY he
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    change X ∩ Q = Y ∩ Q at he₁
    change (A \ X) \ Q = (A \ Y) \ Q at he₂
    ext p
    have h₁ := Finset.ext_iff.mp he₁ p
    have h₂ := Finset.ext_iff.mp he₂ p
    have hx : p ∈ X → p ∉ A → p ∈ Q := fun hp ha => hcut X hX (mem_sdiff.mpr ⟨hp,ha⟩)
    have hy : p ∈ Y → p ∉ A → p ∈ Q := fun hp ha => hcut Y hY (mem_sdiff.mpr ⟨hp,ha⟩)
    simp only [Finset.mem_inter,Finset.mem_sdiff] at h₁ h₂
    tauto
  have hc := card_le_card_of_injOn enc htarget hinj
  simpa only [target,Finset.product_eq_sprod,card_product,card_powerset,Q] using hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SmallAdditionCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-addition contribution to representation multiplicity -/

namespace JointDickman
open Finset Classical Filter
open scoped Topology

theorem highOmissionExponent_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (hsmall : τ ≤ 1/100) :
    0 ≤ highOmissionExponent τ := by
  have hd : 0 < (1/2 : ℝ)+τ := by linarith
  apply mul_nonneg (by linarith) (Real.binEntropy_nonneg (div_nonneg (by linarith) hd.le) ?_)
  exact (div_le_one hd).mpr (by linarith)

theorem highOmissionExponent_tendsto :
    Tendsto highOmissionExponent (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt highOmissionExponent 0 := by
    unfold highOmissionExponent
    apply ContinuousAt.mul (by fun_prop)
    apply Real.binEntropy_continuous.continuousAt.comp
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  simpa [highOmissionExponent] using hc.tendsto

theorem regularSmallAlternatives_exp_bound {B L k : ℕ} {τ C : ℝ}
    (A R : Finset ℕ) (hL : 1 ≤ L) (hk : k ∈ Icc 1 L)
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hR : RegularPrimeSet B L τ C R) :
    ((regularSmallAlternatives B L k τ C A R).card : ℝ) ≤
      Real.exp (((((k : ℝ)/L+2*τ)*Real.log 2)+highOmissionExponent τ)*auxiliaryLogLength B) := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ R)
  have hQA : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hQR : R ∩ Q = primePrefix B ((k : ℝ)/L) R := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_right]
  have he : Q = (A ∩ Q) ∪ (R ∩ Q) := by
    have hsub : Q ⊆ A ∪ R := by
      dsimp [Q,primePrefix]
      split_ifs
      · exact filter_subset _ _
      · exact subset_rfl
    rw [← union_inter_distrib_right,inter_eq_right.mpr hsub]
  have hQ : (Q.card : ℝ) ≤ ((k : ℝ)/L+2*τ)*auxiliaryLogLength B := by
    have hh : (Q.card : ℝ) ≤ ((A ∩ Q).card : ℝ)+(R ∩ Q).card := by
      have hc : ((A ∩ Q ∪ R ∩ Q).card : ℝ) ≤ (A ∩ Q).card+(R ∩ Q).card := by
        exact_mod_cast card_union_le (A ∩ Q) (R ∩ Q)
      rwa [← he] at hc
    rw [hQA,hQR] at hh
    have ha := (hA.1 k hk).2
    have hr := (hR.1 k hk).2
    nlinarith
  have hcount : ((regularSmallAlternatives B L k τ C A R).card : ℝ) ≤
      (2 : ℝ)^Q.card*
        (((A \ Q).powerset.filter (fun U => (U.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card : ℝ) := by
    exact_mod_cast regularSmallAlternatives_count A R hL hk hA
  have hregion : ((A \ Q).card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B :=
    (show ((A \ Q).card : ℝ) ≤ A.card by
      exact_mod_cast card_le_card (show A \ Q ⊆ A from sdiff_subset)).trans (hA.total_upper hL)
  have homit := high_omission_count_bound (A \ Q) hτ hτsmall hℓ hregion
  have hp : (2 : ℝ)^Q.card ≤ Real.exp ((((k : ℝ)/L+2*τ)*auxiliaryLogLength B)*Real.log 2) := by
    calc
      _ = Real.exp ((Q.card : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hQ (Real.log_nonneg (by norm_num)))
  refine hcount.trans ((mul_le_mul hp homit (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  dsimp [highOmissionExponent]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_PrefixOmissionWindow
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prefix omission count lies in the addition's entropy window -/

namespace JointDickman
open Finset Classical

theorem omitted_prefix_count (A X Q : Finset ℕ) (hadd : X \ A ⊆ Q) :
    (((A \ X) ∩ Q).card : ℝ)-(X \ A).card = (A ∩ Q).card-(X ∩ Q).card := by
  have he₁ : (A ∩ Q) \ (X ∩ Q) = (A \ X) ∩ Q := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have he₂ : (X ∩ Q) \ (A ∩ Q) = X \ A := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    constructor
    · tauto
    · intro h
      exact ⟨⟨h.1,hadd (mem_sdiff.mpr h)⟩,by tauto⟩
  have h₁ := card_sdiff_add_card_inter (A ∩ Q) (X ∩ Q)
  have h₂ := card_sdiff_add_card_inter (X ∩ Q) (A ∩ Q)
  rw [he₁] at h₁
  rw [he₂,inter_comm (X ∩ Q)] at h₂
  have hc₁ : (((A \ X) ∩ Q).card : ℝ)+((A ∩ Q) ∩ (X ∩ Q)).card = (A ∩ Q).card := by exact_mod_cast h₁
  have hc₂ : ((X \ A).card : ℝ)+((A ∩ Q) ∩ (X ∩ Q)).card = (X ∩ Q).card := by exact_mod_cast h₂
  linarith

theorem regular_omission_prefix_window {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hA : RegularPrimeSet B L τ C A)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    |(((A \ X) ∩ primePrefix B ((k : ℝ)/L) (A ∪ U)).card : ℝ)-
      (X \ A).card| ≤ 2*τ*auxiliaryLogLength B := by
  obtain ⟨hsub,hreg,hadd⟩ := mem_filter.mp hX
  have hsub' := mem_powerset.mp hsub
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  have hAQ : A ∩ Q = primePrefix B ((k : ℝ)/L) A := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr subset_union_left]
  have hXQ : X ∩ Q = primePrefix B ((k : ℝ)/L) X := by
    dsimp [Q]
    rw [← primePrefix_inter,inter_eq_left.mpr hsub']
  have hcut : X \ A ⊆ Q := hadd.trans (primePrefix_mono B _ (sdiff_subset.trans hsub'))
  have he := omitted_prefix_count A X Q hcut
  rw [hAQ,hXQ] at he
  have ha := hA.1 k hk
  have hx := hreg.1 k hk
  apply abs_le.mpr
  constructor <;> linarith [ha.1,ha.2,hx.1,hx.2]

theorem regular_omission_clipped_window {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hU : RegularPrimeSet B L τ C U)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    |(((A \ X) ∩ primePrefix B ((k : ℝ)/L) (A ∪ U)).card : ℝ)/auxiliaryLogLength B-
      ((k : ℝ)/L)*clippedAdditionDensity B ((k : ℝ)/L) (X \ A)| ≤ 3*τ := by
  let g : ℝ := (k : ℝ)/L
  let Z := X \ A
  let q : ℝ := (((A \ X) ∩ primePrefix B g (A ∪ U)).card : ℝ)
  have hkpos : 0 < k := by have := (mem_Icc.mp hk).1; omega
  have hLpos : 0 < L := by have := (mem_Icc.mp hk).2; omega
  have hg : 0 < g := div_pos (by exact_mod_cast hkpos) (by exact_mod_cast hLpos)
  have hpre := regular_omission_prefix_window hk hA hX
  have h₁ : |q/auxiliaryLogLength B-(Z.card : ℝ)/auxiliaryLogLength B| ≤ 2*τ := by
    rw [← sub_div,abs_div,abs_of_pos hℓ]
    exact (div_le_iff₀ hℓ).mpr (by simpa [q,Z,g] using hpre)
  have hZU : Z ⊆ U := by
    intro p hp
    have hx := (mem_powerset.mp (mem_filter.mp hX).1) (mem_sdiff.mp hp).1
    exact (mem_union.mp hx).resolve_left (mem_sdiff.mp hp).2
  have hZpre := (mem_filter.mp hX).2.2
  have hZprefix : Z ⊆ primePrefix B g U := hZpre.trans (primePrefix_mono B g hZU)
  have hcount : (Z.card : ℝ) ≤ (g/2+τ)*auxiliaryLogLength B := by
    exact (show (Z.card : ℝ) ≤ (primePrefix B g U).card by exact_mod_cast card_le_card hZprefix).trans
      (hU.1 k hk).2
  have hcount' : (Z.card : ℝ)/auxiliaryLogLength B ≤ g/2+τ := (div_le_iff₀ hℓ).mpr hcount
  have h₂ : |(Z.card : ℝ)/auxiliaryLogLength B-g*clippedAdditionDensity B g Z| ≤ τ := by
    unfold clippedAdditionDensity
    by_cases hs : (Z.card : ℝ)/(g*auxiliaryLogLength B) ≤ 1/2
    · rw [min_eq_left hs]
      have he : g*((Z.card : ℝ)/(g*auxiliaryLogLength B)) = (Z.card : ℝ)/auxiliaryLogLength B := by
        field_simp
      rw [he,sub_self,abs_zero]
      exact hτ
    · rw [min_eq_right (le_of_not_ge hs)]
      have hlo : g/2 ≤ (Z.card : ℝ)/auxiliaryLogLength B := by
        have hh := (le_div_iff₀ (mul_pos hg hℓ)).mp (le_of_not_ge hs)
        exact (le_div_iff₀ hℓ).mpr (by nlinarith)
      apply abs_le.mpr
      constructor <;> linarith
  have htri := abs_sub_le (q/auxiliaryLogLength B) ((Z.card : ℝ)/auxiliaryLogLength B)
    (g*clippedAdditionDensity B g Z)
  exact htri.trans (by linarith)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SubsetCardEntropy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entropy bound for subsets of a prescribed size -/

namespace JointDickman
open Finset Classical

theorem subset_exact_count_exp_bound (P : Finset ℕ) (k : ℕ) (t : ℝ) :
    ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
      Real.exp (t*k)*(1+Real.exp (-t))^P.card := by
  let I := P.powerset.filter (fun A => A.card = k)
  have he : (I.card : ℝ)*Real.exp (-t*k) ≤ (1+Real.exp (-t))^P.card := by
    calc
      _ = ∑ _A ∈ I, Real.exp (-t*k) := by simp
      _ = ∑ A ∈ I, Real.exp (-t*(A.card : ℝ)) := by
        apply sum_congr rfl
        intro A hA
        rw [(mem_filter.mp hA).2]
      _ ≤ ∑ A ∈ P.powerset, Real.exp (-t*(A.card : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = _ := subset_count_exp_sum P t
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (t*k)).le
  have hc : Real.exp (t*k)*Real.exp (-t*k) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_left_comm (Real.exp (t*k)) (I.card : ℝ),hc,mul_one] at hm
  exact hm

/-- No rounding loss occurs for an exact cardinality. -/
theorem subset_exact_count_entropy (P : Finset ℕ) {k : ℕ} (hk : k ≤ P.card) :
    ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
      Real.exp ((P.card : ℝ)*Real.binEntropy ((k : ℝ)/P.card)) := by
  by_cases hk0 : k = 0
  · subst k
    have hf : P.powerset.filter (fun A => A.card = 0) = {∅} := by
      ext A
      simp only [mem_filter,mem_powerset,card_eq_zero,mem_singleton]
      exact ⟨fun h => h.2,fun h => ⟨by rw [h]; exact empty_subset _,h⟩⟩
    rw [hf]
    simp
  by_cases hkn : k = P.card
  · subst k
    have hf : P.powerset.filter (fun A => A.card = P.card) = {P} := by
      ext A
      simp only [mem_filter,mem_powerset,mem_singleton]
      exact ⟨fun h => eq_of_subset_of_card_le h.1 h.2.ge,fun h => by subst A; simp⟩
    have hn : (P.card : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp [hf,hn]
  have hn : 0 < P.card := lt_of_lt_of_le (Nat.pos_of_ne_zero hk0) hk
  have hnr : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  have hlt : (k : ℝ) < P.card := by exact_mod_cast lt_of_le_of_ne hk hkn
  let θ : ℝ := (k : ℝ)/P.card
  have hθ : 0 < θ := div_pos hkr hnr
  have hθ1 : θ < 1 := (div_lt_one hnr).mpr hlt
  let t := Real.log (1-θ)-Real.log θ
  have he : Real.exp (-t) = θ/(1-θ) := by
    dsimp [t]
    rw [neg_sub,Real.exp_sub,Real.exp_log hθ,Real.exp_log (by linarith)]
  have hb : 1+Real.exp (-t) = (1-θ)⁻¹ := by
    rw [he]
    field_simp [ne_of_gt (show 0 < 1-θ by linarith)]
    ring
  have hlog : Real.log (1+Real.exp (-t)) = -Real.log (1-θ) := by rw [hb,Real.log_inv]
  have hp : (1+Real.exp (-t))^P.card =
      Real.exp ((P.card : ℝ)*Real.log (1+Real.exp (-t))) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  refine (subset_exact_count_exp_bound P k t).trans_eq ?_
  rw [hp,← Real.exp_add,hlog]
  congr 1
  have hθn : θ*(P.card : ℝ) = k := div_mul_cancel₀ _ hnr.ne'
  change _ = (P.card : ℝ)*Real.binEntropy θ
  simp only [Real.binEntropy,Real.log_inv,t]
  rw [← hθn]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_EntropyWindowStability
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform entropy estimates across regularity windows -/

namespace JointDickman
open Set

/-- Uniformity includes both endpoint cardinalities. The population stays
away from zero because the prefix scale g is fixed and positive. -/
theorem entropy_window_stability {g ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ x y r : ℝ), 0 ≤ τ → τ ≤ τ₀ →
      0 ≤ r → r ≤ 1/2 → |x-g/2| ≤ τ → |y-g*r| ≤ 3*τ →
      x*Real.binEntropy (y/x) ≤ (g/2)*Real.binEntropy (2*r)+ε := by
  let D : Set (ℝ × ℝ) := (Icc (g/4) (2*g)) ×ˢ (Icc (-g) (2*g))
  let F : ℝ × ℝ → ℝ := fun z => z.1*Real.binEntropy (z.2/z.1)
  have hcont : ContinuousOn F D := by
    intro z hz
    have hzne : z.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le (by linarith : 0 < g/4) hz.1.1)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_fst
    apply Real.binEntropy_continuous.continuousAt.comp
    exact continuousAt_snd.div continuousAt_fst hzne
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let τ₀ := min (g/4) (δ/4)
  have hτ₀ : 0 < τ₀ := lt_min (by positivity) (by positivity)
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ x y r hτ hτsmall hr hr1 hx hy
  have hτg : τ ≤ g/4 := hτsmall.trans (min_le_left _ _)
  have hτδ : τ ≤ δ/4 := hτsmall.trans (min_le_right _ _)
  have hx' := abs_le.mp hx
  have hy' := abs_le.mp hy
  have hz : (x,y) ∈ D := by
    change (g/4 ≤ x ∧ x ≤ 2*g) ∧ (-g ≤ y ∧ y ≤ 2*g)
    constructor
    · constructor <;> linarith
    · constructor <;> nlinarith
  have hw : (g/2,g*r) ∈ D := by
    change (g/4 ≤ g/2 ∧ g/2 ≤ 2*g) ∧ (-g ≤ g*r ∧ g*r ≤ 2*g)
    constructor
    · constructor <;> linarith
    · constructor <;> nlinarith
  have hd : dist (x,y) (g/2,g*r) < δ := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact max_lt (by linarith) (by linarith)
  have he := hclose (x,y) hz (g/2,g*r) hw hd
  have hratio : g*r/(g/2) = 2*r := by field_simp
  change |x*Real.binEntropy (y/x)-(g/2)*Real.binEntropy (g*r/(g/2))| < ε at he
  rw [hratio] at he
  linarith [(abs_lt.mp he).2]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Counting_SubsetWindowEntropy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting omission subsets in a regularity window -/

namespace JointDickman
open Finset Classical

theorem subset_card_window_entropy {g ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (P : Finset ℕ) (ℓ r τ : ℝ),
      0 < ℓ → 0 ≤ τ → τ ≤ τ₀ → 0 ≤ r → r ≤ 1/2 →
      |(P.card : ℝ)/ℓ-g/2| ≤ τ →
      ((subsetCardWindow P ℓ g r τ).card : ℝ) ≤
        ((P.card : ℝ)+1)*Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
  obtain ⟨τ₁,hτ₁,hstab⟩ := entropy_window_stability hg hε
  let τ₀ := min τ₁ (g/4)
  refine ⟨τ₀,lt_min hτ₁ (by positivity),?_⟩
  intro P ℓ r τ hℓ hτ hτsmall hr hr1 hP
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτg : τ ≤ g/4 := hτsmall.trans (min_le_right _ _)
  have hPpos : (0 : ℝ) < P.card := by
    have ha := (abs_le.mp hP).1
    have hx : 0 < (P.card : ℝ)/ℓ := by linarith
    exact ((div_pos_iff.mp hx).resolve_right (by intro h; linarith)).1
  have hbound (k : ℕ) (hk : k ≤ P.card) (hwin : |(k : ℝ)/ℓ-g*r| ≤ 3*τ) :
      ((P.powerset.filter (fun A => A.card = k)).card : ℝ) ≤
        Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
    have he := hstab τ ((P.card : ℝ)/ℓ) ((k : ℝ)/ℓ) r hτ hτ₁' hr hr1 hP hwin
    have hd : ((k : ℝ)/ℓ)/((P.card : ℝ)/ℓ) = (k : ℝ)/P.card := by
      field_simp
    rw [hd] at he
    have hm := mul_le_mul_of_nonneg_right he hℓ.le
    have hn : (P.card : ℝ)/ℓ*Real.binEntropy ((k : ℝ)/P.card)*ℓ =
        (P.card : ℝ)*Real.binEntropy ((k : ℝ)/P.card) := by field_simp
    rw [hn] at hm
    exact (subset_exact_count_entropy P hk).trans (Real.exp_le_exp.mpr hm)
  let F := subsetCardWindow P ℓ g r τ
  have hcard : F.card = ∑ k ∈ range (P.card+1), (F.filter (fun A => A.card = k)).card := by
    apply card_eq_sum_card_fiberwise
    intro A hA
    exact mem_range.mpr (Nat.lt_succ_of_le (card_le_card (mem_powerset.mp (mem_filter.mp hA).1)))
  rw [hcard,Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ range (P.card+1), Real.exp (((g/2)*Real.binEntropy (2*r)+ε)*ℓ) := by
      apply sum_le_sum
      intro k hk
      by_cases hwin : |(k : ℝ)/ℓ-g*r| ≤ 3*τ
      · have hsub : F.filter (fun A => A.card = k) ⊆ P.powerset.filter (fun A => A.card = k) := by
          intro A hA
          exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hA).1).1,(mem_filter.mp hA).2⟩
        exact (show ((F.filter (fun A => A.card = k)).card : ℝ) ≤
          (P.powerset.filter (fun A => A.card = k)).card by exact_mod_cast card_le_card hsub).trans
            (hbound k (Nat.le_of_lt_succ (mem_range.mp hk)) hwin)
      · have hf : F.filter (fun A => A.card = k) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro A hA
          have ha := mem_filter.mp hA
          have hw := (mem_filter.mp ha.1).2
          rw [ha.2] at hw
          exact hwin hw
        rw [hf,card_empty,Nat.cast_zero]
        exact (Real.exp_pos _).le
    _ = _ := by simp [Nat.cast_add,Nat.cast_one]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_OmissionEnvelope
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An omission envelope independent of the random remainder -/

namespace JointDickman
open Finset Classical

theorem regular_omission_mem_envelope {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hU : RegularPrimeSet B L τ C U)
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    A \ X ∈ omissionEnvelope B L k τ A (X \ A).card := by
  let Q := primePrefix B ((k : ℝ)/L) (A ∪ U)
  let P := primePrefix B ((k : ℝ)/L) A
  have hi : (A \ X) ∩ Q = (A \ X) ∩ P := by
    dsimp only [Q,P]
    rw [← primePrefix_inter,← primePrefix_inter,
      inter_eq_left.mpr (sdiff_subset.trans subset_union_left),inter_eq_left.mpr sdiff_subset]
  have hs : (A \ X) \ Q = (A \ X) \ P := by
    ext p
    have hh := Finset.ext_iff.mp hi p
    simp only [Finset.mem_inter,Finset.mem_sdiff] at *
    tauto
  apply mem_filter.mpr
  refine ⟨mem_powerset.mpr sdiff_subset,?_,?_⟩
  · have hh := regular_omission_clipped_window hk hτ hℓ hA hU hX
    change |(((A \ X) ∩ Q).card : ℝ)/auxiliaryLogLength B-
      ((k : ℝ)/L)*clippedAdditionDensity B ((k : ℝ)/L) (X \ A)| ≤ 3*τ at hh
    rw [hi] at hh
    exact hh
  · have hh := regularSmallAlternatives_omissions
      ((mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2) hk hA hX
    change (((A \ X) \ Q).card : ℝ) ≤ _ at hh
    rw [hs] at hh
    exact hh

theorem omissionEnvelope_count (B L k : ℕ) (τ : ℝ) (A : Finset ℕ) (d : ℕ) :
    (omissionEnvelope B L k τ A d).card ≤
      (subsetCardWindow (primePrefix B ((k : ℝ)/L) A) (auxiliaryLogLength B) ((k : ℝ)/L)
        (min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)) τ).card *
      (((A \ primePrefix B ((k : ℝ)/L) A).powerset).filter
        (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card := by
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  let target := (subsetCardWindow Q (auxiliaryLogLength B) ((k : ℝ)/L) r τ).product
    (((A \ Q).powerset).filter (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B))
  let enc := fun O : Finset ℕ => (O ∩ Q,O \ Q)
  have hmap (O : Finset ℕ) (hO : O ∈ omissionEnvelope B L k τ A d) : enc O ∈ target := by
    obtain ⟨hO,hpre,hhigh⟩ := mem_filter.mp hO
    have hOA := mem_powerset.mp hO
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr inter_subset_right,hpre⟩,
      mem_filter.mpr ⟨mem_powerset.mpr (sdiff_subset_sdiff hOA subset_rfl),hhigh⟩⟩
  have hinj : Set.InjOn enc (omissionEnvelope B L k τ A d) := by
    intro O _ R _ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change O ∩ Q = R ∩ Q at h₁
    change O \ Q = R \ Q at h₂
    ext p
    have h₁ := Finset.ext_iff.mp h₁ p
    have h₂ := Finset.ext_iff.mp h₂ p
    simp only [Finset.mem_inter,Finset.mem_sdiff] at *
    tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,Finset.product_eq_sprod,card_product,Q,r] using hc

theorem omissionEnvelope_entropy {L k : ℕ} (hk : k ∈ Icc 1 L) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ τ₀ →
      ∀ (B : ℕ) (C : ℝ) (A : Finset ℕ) (d : ℕ), 0 < auxiliaryLogLength B →
        RegularPrimeSet B L τ C A →
        ((omissionEnvelope B L k τ A d).card : ℝ) ≤
          ((A.card : ℝ)+1)*Real.exp
            (((((k : ℝ)/L)/2)*Real.binEntropy
              (2*min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2))+
                ε+highOmissionExponent τ)*auxiliaryLogLength B) := by
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hg : 0 < (k : ℝ)/L := div_pos
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < k))
    (by exact_mod_cast (by omega : 0 < L))
  obtain ⟨τ₁,hτ₁,hwin⟩ := subset_card_window_entropy hg hε
  refine ⟨min τ₁ (1/100),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall B C A d hℓ hA
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hsmall : τ ≤ 1/100 := hτsmall.trans (min_le_right _ _)
  let Q := primePrefix B ((k : ℝ)/L) A
  let r := min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2)
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hP : |(Q.card : ℝ)/auxiliaryLogLength B-((k : ℝ)/L)/2| ≤ τ := by
    have hlo := (le_div_iff₀ hℓ).mpr (hA.1 k hk).1
    have hup := (div_le_iff₀ hℓ).mpr (hA.1 k hk).2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hpre := hwin Q (auxiliaryLogLength B) r τ hℓ hτ.le hτ₁' hr hr1 hP
  have hregion : ((A \ Q).card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B :=
    (show ((A \ Q).card : ℝ) ≤ A.card by exact_mod_cast card_le_card sdiff_subset).trans (hA.total_upper hL)
  have hhigh := high_omission_count_bound (A \ Q) hτ hsmall hℓ.le hregion
  have hc : ((omissionEnvelope B L k τ A d).card : ℝ) ≤
      (subsetCardWindow Q (auxiliaryLogLength B) ((k : ℝ)/L) r τ).card*
        (((A \ Q).powerset.filter (fun O => (O.card : ℝ) ≤ 4*τ*auxiliaryLogLength B)).card : ℝ) := by
    exact_mod_cast omissionEnvelope_count B L k τ A d
  have hQsub : Q ⊆ A := by
    dsimp only [Q,primePrefix]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hcA : (Q.card : ℝ)+1 ≤ (A.card : ℝ)+1 := by
    have hh : (Q.card : ℝ) ≤ A.card := by exact_mod_cast card_le_card hQsub
    linarith
  have hpre' := hpre.trans (mul_le_mul_of_nonneg_right hcA (Real.exp_pos _).le)
  refine hc.trans ((mul_le_mul hpre' hhigh (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)).trans_eq ?_)
  rw [mul_assoc,← Real.exp_add]
  congr 2
  dsimp [highOmissionExponent,r]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularPrefixChoices
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting prescribed-size additions inside a regular remainder -/

namespace JointDickman
open Finset Classical

theorem regularPrefixChoices_entropy {L k : ℕ} (hk : k ∈ Icc 1 L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ (τ : ℝ), 0 ≤ τ → τ ≤ τ₀ →
      ∀ (B : ℕ) (C : ℝ) (R : Finset ℕ) (d : ℕ), 0 < auxiliaryLogLength B →
        RegularPrimeSet B L τ C R →
        ((regularPrefixChoices B L k R d).card : ℝ) ≤
          ((R.card : ℝ)+1)*Real.exp
            (((((k : ℝ)/L)/2)*Real.binEntropy
              (2*min ((d : ℝ)/(((k : ℝ)/L)*auxiliaryLogLength B)) (1/2))+ε)*auxiliaryLogLength B) := by
  have hg : 0 < (k : ℝ)/L := div_pos
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < k))
    (by exact_mod_cast (by have := (mem_Icc.mp hk).1; have := (mem_Icc.mp hk).2; omega : 0 < L))
  obtain ⟨τ₀,hτ₀,hwin⟩ := subset_card_window_entropy hg hε
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτsmall B C R d hℓ hR
  let g := (k : ℝ)/L
  let Q := primePrefix B g R
  let r := min ((d : ℝ)/(g*auxiliaryLogLength B)) (1/2)
  have hQsub : Q ⊆ R := by
    dsimp only [Q,primePrefix]
    split_ifs
    · exact filter_subset _ _
    · exact subset_rfl
  have hQcard := hR.1 k hk
  have hQnorm : |(Q.card : ℝ)/auxiliaryLogLength B-g/2| ≤ τ := by
    have hl := (le_div_iff₀ hℓ).mpr hQcard.1
    have hu := (div_le_iff₀ hℓ).mpr hQcard.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hr : 0 ≤ r := le_min (div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le) (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hwindow : regularPrefixChoices B L k R d ⊆ subsetCardWindow Q (auxiliaryLogLength B) g r τ := by
    intro Y hY
    obtain ⟨hY,hcard⟩ := mem_filter.mp hY
    have hsub : Y ⊆ Q := mem_powerset.mp hY
    apply mem_filter.mpr
    refine ⟨hY,?_⟩
    rw [hcard]
    have hdc : (d : ℝ) ≤ Q.card := by exact_mod_cast (hcard ▸ card_le_card hsub)
    have hdu : (d : ℝ) ≤ (g/2+τ)*auxiliaryLogLength B := hdc.trans hQcard.2
    by_cases hd : (d : ℝ)/(g*auxiliaryLogLength B) ≤ 1/2
    · dsimp only [r]
      rw [min_eq_left hd]
      have he : (d : ℝ)/auxiliaryLogLength B-g*((d : ℝ)/(g*auxiliaryLogLength B)) = 0 := by
        field_simp [show g ≠ 0 from hg.ne',hℓ.ne']
        ring
      rw [he,abs_zero]
      linarith
    · dsimp only [r]
      rw [min_eq_right (le_of_not_ge hd)]
      have hlow := (le_div_iff₀ (mul_pos hg hℓ)).mp (le_of_not_ge hd)
      have hhigh := (div_le_iff₀ hℓ).mpr hdu
      rw [abs_of_nonneg (by
        have hh : g/2 ≤ (d : ℝ)/auxiliaryLogLength B :=
          (le_div_iff₀ hℓ).mpr (by nlinarith [hlow])
        nlinarith : 0 ≤ (d : ℝ)/auxiliaryLogLength B-g*(1/2))]
      linarith
  have hcount : ((regularPrefixChoices B L k R d).card : ℝ) ≤
      (subsetCardWindow Q (auxiliaryLogLength B) g r τ).card := by exact_mod_cast card_le_card hwindow
  have hh := hwin Q (auxiliaryLogLength B) r τ hℓ hτ hτsmall hr hr1 hQnorm
  have hcard : (Q.card : ℝ)+1 ≤ (R.card : ℝ)+1 := by
    have hc : (Q.card : ℝ) ≤ R.card := by exact_mod_cast card_le_card hQsub
    linarith
  exact hcount.trans (hh.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAlternativePairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual alternative coefficient pairs in a large-addition class -/

namespace JointDickman
open Finset Classical

theorem retained_addition_product (A X : Finset ℕ) :
    (∏ p ∈ X, p : ℕ) = (∏ p ∈ A \ (A \ X), p)*(∏ p ∈ X \ A, p) := by
  have he : A \ (A \ X) ∪ (X \ A) = X := by
    ext p
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hd : Disjoint (A \ (A \ X)) (X \ A) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_sdiff.mp hq).2 (mem_sdiff.mp hp).1
  rw [← prod_union hd,he]

theorem alternative_additions_subset_remainder {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hX : X ∈ regularSmallAlternatives B L k τ C A U) : X \ A ⊆ U := by
  intro p hp
  have h := (mem_powerset.mp (mem_filter.mp hX).1) (mem_sdiff.mp hp).1
  exact (mem_union.mp h).resolve_left (mem_sdiff.mp hp).2

/-- Every actual pair maps to a fixed old-prime choice, a fixed opposite
addition, and an element of the numerically sieved class. -/
theorem largeHighAlternativePairs_encoding {B L k j d f : ℕ} {τ C Δ : ℝ}
    {A U D V X Y : Finset ℕ} (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V)
    (hXY : (X,Y) ∈ largeHighAlternativePairs B L k j d f τ C Δ A U D V) :
    A \ X ∈ omissionEnvelope B L k τ A d ∧
    D \ Y ∈ omissionEnvelope B L k τ D f ∧
    Y \ D ∈ regularPrefixChoices B L k V f ∧
    X \ A ∈ (activeHighAdditionClass B L k τ C Δ A
      (∏ p ∈ A \ (A \ X), p) j
      ((∏ p ∈ D \ (D \ Y), p)*(∏ p ∈ Y \ D, p)) d).filter (fun Z => Z ⊆ U) := by
  obtain ⟨hXY,hd,hf,hlarge,hsize,hXsize,hYsize,c,hc,hrel,hcr⟩ := mem_filter.mp hXY
  obtain ⟨hX,hY⟩ := mem_product.mp hXY
  have hZA := alternative_additions_subset_remainder hX
  have hYV := alternative_additions_subset_remainder hY
  have hZP : X \ A ⊆ auxiliaryPrimes B := hZA.trans (hU.trans sdiff_subset)
  have hXP : X ⊆ auxiliaryPrimes B :=
    (mem_powerset.mp (mem_filter.mp hX).1).trans (union_subset hA (hU.trans sdiff_subset))
  have hepos : 0 < (∏ p ∈ A \ (A \ X), p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA ((mem_sdiff.mp hp).1))).pos)
  have her : (0 : ℝ) < (∏ p ∈ A \ (A \ X), p : ℕ) := by exact_mod_cast hepos
  have hzpos : 0 < (∏ p ∈ X \ A, p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hZP hp)).pos)
  have hdecomp := retained_addition_product A X
  have hydecomp := retained_addition_product D Y
  let e := (∏ p ∈ A \ (A \ X), p : ℕ)
  let b := (∏ p ∈ D \ (D \ Y), p : ℕ)*(∏ p ∈ Y \ D, p : ℕ)
  let z := (∏ p ∈ X \ A, p : ℕ)
  have heq : e*z = b+j*c := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hrel
  have hbound : (e*z : ℕ) ≤ 2*b := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hsize
  have hlo : highAdditionWindow e b ≤ (z : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*e)).mpr
    have hrelr : (b : ℝ) ≤ e*z := by exact_mod_cast (by omega : b ≤ e*z)
    change (b : ℝ) ≤ (z : ℝ)*(2*e)
    nlinarith [show (0 : ℝ) ≤ e*z by positivity]
  have hhi : (z : ℝ) ≤ 4*highAdditionWindow e b := by
    have hr : (e : ℝ)*z ≤ 2*b := by exact_mod_cast hbound
    calc
      _ ≤ (2*(b : ℝ))/(e : ℝ) := (le_div_iff₀ her).mpr (by nlinarith [hr])
      _ = _ := by unfold highAdditionWindow; ring
  have hactive : (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b := by
    refine ⟨?_,?_⟩
    · dsimp only [b]
      rwa [← hydecomp]
    · have hl : Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (z : ℝ) := hlarge
      linarith
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hd] using regular_omission_mem_envelope hk hτ hℓ hAr hUr hX
  · simpa only [hf] using regular_omission_mem_envelope hk hτ hℓ hDr hVr hY
  · exact mem_filter.mpr ⟨mem_powerset.mpr
      ((mem_filter.mp hY).2.2.trans (primePrefix_mono B _ hYV)),hf⟩
  · apply mem_filter.mpr
    refine ⟨?_,hZA⟩
    change X \ A ∈ activeHighAdditionClass B L k τ C Δ A e j b d
    rw [activeHighAdditionClass,ite_eq_left hactive]
    apply mem_filter.mpr
    refine ⟨mem_numericAdditionClass.mpr ⟨hZP,hd,hlo,hhi,c,hc,heq,hcr⟩,
      hZA.trans hU,?_,(mem_filter.mp hX).2.2⟩
    have hdiv : z ∣ ∏ p ∈ X, p := prod_dvd_prod_of_subset _ _ id sdiff_subset
    have hprodpos : 0 < ∏ p ∈ X, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hXP hp)).pos)
    exact (show (z : ℝ) ≤ (∏ p ∈ X, p : ℕ) by exact_mod_cast Nat.le_of_dvd hprodpos hdiv).trans hXsize

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAlternativeCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectively counting large alternative representations by numeric classes -/

namespace JointDickman
open Finset Classical

theorem largeHighAlternativePairs_count {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V) :
    (largeHighAlternativePairs B L k j d f τ C Δ A U D V).card ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            ((activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
              ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U)).card := by
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let target := E.sigma (fun Oa => F.sigma (fun Od => P.sigma (fun Y =>
    (activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
      ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U))))
  let enc : (Finset ℕ × Finset ℕ) → Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ :=
    fun XY => ⟨A \ XY.1,⟨D \ XY.2,⟨XY.2 \ D,XY.1 \ A⟩⟩⟩
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ largeHighAlternativePairs B L k j d f τ C Δ A U D V) : enc XY ∈ target := by
    have hh := largeHighAlternativePairs_encoding hk hτ hℓ hA hU hAr hUr hDr hVr hXY
    simpa only [target,enc,E,F,P,mem_sigma] using hh
  have hinj : Set.InjOn enc (largeHighAlternativePairs B L k j d f τ C Δ A U D V) := by
    intro XY _ ZW _ he
    have h₁ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.1) he
    have h₂ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.1) he
    have h₃ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.1) he
    have h₄ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.2) he
    change A \ XY.1 = A \ ZW.1 at h₁
    change D \ XY.2 = D \ ZW.2 at h₂
    change XY.2 \ D = ZW.2 \ D at h₃
    change XY.1 \ A = ZW.1 \ A at h₄
    apply Prod.ext
    · ext p
      have h₁ := Finset.ext_iff.mp h₁ p
      have h₄ := Finset.ext_iff.mp h₄ p
      simp only [Finset.mem_sdiff] at *
      tauto
    · ext p
      have h₂ := Finset.ext_iff.mp h₂ p
      have h₃ := Finset.ext_iff.mp h₃ p
      simp only [Finset.mem_sdiff] at *
      tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,card_sigma,E,F,P] using hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeCardinalityPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning all large high-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

theorem allLargeHighAlternativePairs_fiber (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) :
    (allLargeHighAlternativePairs B L k j τ C Δ A U D V).filter
      (fun XY => ((XY.1 \ A).card,(XY.2 \ D).card) = (d,f)) =
        largeHighAlternativePairs B L k j d f τ C Δ A U D V := by
  ext XY
  simp only [allLargeHighAlternativePairs,largeHighAlternativePairs,mem_filter,Prod.mk.injEq]
  tauto

theorem regular_addition_card_le_logLength {B L k : ℕ} {τ C : ℝ} {A U X : Finset ℕ}
    (hk : k ∈ Icc 1 L) (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hX : X ∈ regularSmallAlternatives B L k τ C A U) :
    ((X \ A).card : ℝ) ≤ auxiliaryLogLength B := by
  have hkL := (mem_Icc.mp hk).2
  have hL : (0 : ℝ) < L := by exact_mod_cast (by have := (mem_Icc.mp hk).1; omega : 0 < L)
  have hg : (k : ℝ)/L ≤ 1 := (div_le_one hL).mpr (by exact_mod_cast hkL)
  have hsub := (mem_filter.mp hX).2.2.trans
    (primePrefix_mono B _ (alternative_additions_subset_remainder hX))
  have hc : ((X \ A).card : ℝ) ≤ (primePrefix B ((k : ℝ)/L) U).card := by
    exact_mod_cast card_le_card hsub
  have hbound := (hU.1 k hk).2
  have hh := mul_le_mul_of_nonneg_right (show ((k : ℝ)/L)/2+τ ≤ 1 by linarith) hℓ
  linarith

theorem allLargeHighAlternativePairs_card {B L k j : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    (allLargeHighAlternativePairs B L k j τ C Δ A U D V).card =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        (largeHighAlternativePairs B L k j d f τ C Δ A U D V).card := by
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ allLargeHighAlternativePairs B L k j τ C Δ A U D V) :
      ((XY.1 \ A).card,(XY.2 \ D).card) ∈ (range N).product (range N) := by
    obtain ⟨hX,hY⟩ := mem_product.mp (mem_filter.mp hXY).1
    apply mem_product.mpr
    constructor
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hU hX)))
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hV hY)))
  have hh := card_eq_sum_card_fiberwise hmap
  rw [Finset.product_eq_sprod,sum_product] at hh
  simpa only [allLargeHighAlternativePairs_fiber] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AdditionScaleDichotomy
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite grid dichotomy for the two addition products -/

namespace JointDickman
open Finset Classical

theorem addition_product_large_of_not_prefix {B : ℕ} {g : ℝ} {Z : Finset ℕ}
    (hg : g < 1) (hZ : Z ⊆ auxiliaryPrimes B) (hnot : ¬ Z ⊆ primePrefix B g Z) :
    Real.exp ((B : ℝ)^g) ≤ (∏ p ∈ Z, p : ℕ) := by
  obtain ⟨p,hp,hout⟩ := Finset.not_subset.mp hnot
  have hprime := auxiliaryPrimes_prime B p (hZ hp)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hlog : (B : ℝ)^g < Real.log p := by
    apply lt_of_not_ge
    intro hh
    exact hout (by simpa only [primePrefix,ite_eq_left hg] using mem_filter.mpr ⟨hp,hh⟩)
  have hprodpos : 0 < (∏ q ∈ Z, q : ℕ) :=
    prod_pos (fun q hq => (auxiliaryPrimes_prime B q (hZ hq)).pos)
  have hpProd : p ≤ ∏ q ∈ Z, q := Nat.le_of_dvd hprodpos (dvd_prod_of_mem id hp)
  calc
    _ ≤ Real.exp (Real.log p) := (Real.exp_le_exp.mpr hlog.le)
    _ = (p : ℝ) := Real.exp_log hp0
    _ ≤ _ := by exact_mod_cast hpProd

/-- Either both additions stay in the first three grid cells, or at their
first common grid cell one of the products is at least exp(B^(g-1/L)). -/
theorem addition_scale_dichotomy {B L : ℕ} (hL : 3 ≤ L) {Z Y : Finset ℕ}
    (hZ : Z ⊆ auxiliaryPrimes B) (hY : Y ⊆ auxiliaryPrimes B) :
    (Z ⊆ primePrefix B ((3 : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((3 : ℝ)/L) Y) ∨
      ∃ k ∈ Icc 4 L,
        Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((k : ℝ)/L) Y ∧
          (Real.exp ((B : ℝ)^(((k : ℝ)-1)/L)) ≤ (∏ p ∈ Z, p : ℕ) ∨
            Real.exp ((B : ℝ)^(((k : ℝ)-1)/L)) ≤ (∏ p ∈ Y, p : ℕ)) := by
  by_cases hsmall : Z ⊆ primePrefix B ((3 : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((3 : ℝ)/L) Y
  · exact Or.inl hsmall
  · right
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
    let P := fun k : ℕ => 3 ≤ k ∧ k ≤ L ∧
      Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧ Y ⊆ primePrefix B ((k : ℝ)/L) Y
    have hex : ∃ k, P k := by
      refine ⟨L,hL,le_rfl,?_,?_⟩ <;> simp [primePrefix,div_self hL0]
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    change 3 ≤ k ∧ k ≤ L ∧ Z ⊆ primePrefix B ((k : ℝ)/L) Z ∧
      Y ⊆ primePrefix B ((k : ℝ)/L) Y at hk
    have hk4 : 4 ≤ k := by
      by_contra hn
      have hkeq : k = 3 := by omega
      rw [hkeq] at hk
      exact hsmall ⟨hk.2.2.1,hk.2.2.2⟩
    have hprev : ¬ (Z ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Z ∧
        Y ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Y) := by
      intro hh
      have hn := Nat.find_min hex (show k-1 < k by omega)
      apply hn
      exact ⟨by omega,by omega,hh⟩
    have hprevlt : (((k-1 : ℕ) : ℝ)/L) < 1 := by
      have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
      apply (div_lt_one hLpos).mpr
      exact_mod_cast (by omega : k-1 < L)
    refine ⟨k,mem_Icc.mpr ⟨hk4,hk.2.1⟩,hk.2.2.1,hk.2.2.2,?_⟩
    have heq : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    by_cases hz : Z ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Z
    · right
      have hy : ¬ Y ⊆ primePrefix B (((k-1 : ℕ) : ℝ)/L) Y := fun hh => hprev ⟨hz,hh⟩
      simpa only [heq] using addition_product_large_of_not_prefix hprevlt hY hy
    · left
      simpa only [heq] using addition_product_large_of_not_prefix hprevlt hZ hz

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAlternativeExpectation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the injective count before applying the numeric sieve -/

namespace JointDickman
open Finset Classical

theorem tiltedLargeHighPairCount_le_classes {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B)
    (hAr : RegularPrimeSet B L τ C A) (hDr : RegularPrimeSet B L τ C D)
    (hVr : RegularPrimeSet B L τ C V) :
    tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            tiltedRegularSubsetCount B L τ C A
              (activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
                ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) := by
  let μ := fun U => bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let G := fun Oa Od Y => activeHighAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
    ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d
  have hmass (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) : 0 ≤ μ U := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp hU)
    intro p hp
    have hprime := auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    constructor
    · apply div_nonneg (by norm_num)
      linarith
    · apply (div_le_one (by linarith : (0 : ℝ) < 2*p-1)).mpr
      linarith
  have hpoint (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) :
      μ U*(if RegularPrimeSet B L τ C U then
        ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0) ≤
      ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
        μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) := by
    by_cases hUr : RegularPrimeSet B L τ C U
    · simp only [hUr,ite_true, if_true]
      have hc : ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) ≤
          ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) := by
        exact_mod_cast largeHighAlternativePairs_count A U D V hk hτ hℓ hA (mem_powerset.mp hU) hAr hUr hDr hVr
      simpa only [mul_sum] using mul_le_mul_of_nonneg_left hc (hmass U hU)
    · simp [hUr]
  calc
    _ ≤ ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
          μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) :=
      sum_le_sum hpoint
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro Oa _
      rw [sum_comm]
      apply sum_congr rfl
      intro Od _
      rw [sum_comm]
      rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AllLargeHighExpectation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cardinality-class decomposition in the tilted expectation -/

namespace JointDickman
open Finset Classical

theorem tiltedAllLargeHighPairCount_eq_sum {B L k j : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hV : RegularPrimeSet B L τ C V) :
    tiltedAllLargeHighPairCount B L k j τ C Δ A D V =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        tiltedLargeHighPairCount B L k j d f τ C Δ A D V := by
  unfold tiltedAllLargeHighPairCount tiltedLargeHighPairCount
  calc
    _ = ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
            if RegularPrimeSet B L τ C U then
              ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0 := by
      apply sum_congr rfl
      intro U _
      by_cases hU : RegularPrimeSet B L τ C U
      · simp only [hU,ite_true, if_true,← mul_sum]
        have hc : ((allLargeHighAlternativePairs B L k j τ C Δ A U D V).card : ℝ) =
            ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
              ((largeHighAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) := by
          exact_mod_cast allLargeHighAlternativePairs_card A U D V hk hτ hℓ hU hV
        rw [hc]
      · simp [hU]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeMultiplicityExponent
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The combined entropy exponent in large representation classes -/

namespace JointDickman

theorem largeMultiplicityBase_bounds : 0 < largeMultiplicityBase ∧
    largeMultiplicityBase < (233/1000 : ℝ) := by
  unfold largeMultiplicityBase weightBaseExponent
  constructor <;> linarith [Real.log_two_lt_d9,Real.log_two_gt_d9]

/-- One old-coefficient choice at each endpoint and the opposite remainder's
addition choices account for all three combinatorial entropy factors. -/
theorem large_multiplicity_exponent_bound {g Δ δ τ ε ℓ : ℝ} {d f : ℕ}
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hδ : 0 ≤ δ) :
    largeAvailabilityExponent g Δ δ τ ε ℓ d+
      ((g/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ)+
      ((g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ)+
      ((g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε) ≤
        largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε := by
  have hd := Real.binEntropy_le_log_two (p := 2*min ((d : ℝ)/(g*ℓ)) (1/2))
  have hf := Real.binEntropy_le_log_two (p := 2*min ((f : ℝ)/(g*ℓ)) (1/2))
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hd hf) hg
  have hb := mul_le_mul_of_nonneg_right hg1 largeMultiplicityBase_bounds.1.le
  have hδg := mul_le_mul_of_nonneg_right hg1 hδ
  unfold largeAvailabilityExponent largeMultiplicityBase largeMultiplicityLoss at *
  nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeAlternativeBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The expected multiplicity of a large high-endpoint addition class -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem large_high_alternative_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
            K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
              Real.exp ((largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)*auxiliaryLogLength B) := by
  obtain ⟨τa,hτa,henv⟩ := omissionEnvelope_entropy hk hε
  obtain ⟨τb,hτb,hpre⟩ := regularPrefixChoices_entropy hk hε
  refine ⟨min τa (min τb 1),lt_min hτa (lt_min hτb (by norm_num)),?_⟩
  intro τ hτ hτsmall
  have hτa' : τ ≤ τa := hτsmall.trans (min_le_left _ _)
  have hτb' : τ ≤ τb := (hτsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hτ1 : τ ≤ 1 := (hτsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨K,hK,hactive⟩ := active_high_addition_class_bound_jd hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hτ.le hτ1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hactive,auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hB hℓ
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  let ℓ := auxiliaryLogLength B
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let S := K/(j : ℝ)*Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)
  have hS : 0 ≤ S := by dsimp only [S] <;> positivity
  have hpoint (Oa : Finset ℕ) (_hOa : Oa ∈ E) (Od : Finset ℕ) (_hOd : Od ∈ F)
      (Y : Finset ℕ) (hY : Y ∈ P) :
      tiltedRegularSubsetCount B L τ C A (activeHighAdditionClass B L k τ C Δ A
        (∏ p ∈ A \ Oa, p) j ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) ≤ S := by
    have hYsub : Y ⊆ auxiliaryPrimes B := by
      have hy := mem_powerset.mp (mem_filter.mp hY).1
      have hp : primePrefix B ((k : ℝ)/L) V ⊆ V := by
        unfold primePrefix
        split_ifs
        · exact filter_subset _ _
        · exact subset_rfl
      exact (hy.trans hp).trans hV
    have he0 : 0 < (∏ p ∈ A \ Oa, p : ℕ) :=
      prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA (mem_sdiff.mp hp).1)).pos)
    have hb0 : 0 < (∏ p ∈ D \ Od, p : ℕ)*(∏ p ∈ Y, p) := mul_pos
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD (mem_sdiff.mp hp).1)).pos))
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hYsub hp)).pos))
    have heA : (∏ p ∈ A \ Oa, p : ℕ) ≤ ∏ p ∈ A, p :=
      Nat.le_of_dvd (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA hp)).pos))
        (prod_dvd_prod_of_subset _ _ id sdiff_subset)
    exact hB C A _ j _ d hA hAsize he0 hb0 hj hcut
      (auxiliary_product_coprime_lag (sdiff_subset.trans hA) hj hcut)
      ((show ((∏ p ∈ A \ Oa, p : ℕ) : ℝ) ≤ (∏ p ∈ A, p : ℕ) by exact_mod_cast heA).trans hAsize) hjB
  have hcount := tiltedLargeHighPairCount_le_classes A D V hk hτ.le hℓ hA hAr hDr hVr
    (j := j) (d := d) (f := f) (Δ := Δ)
  have hcounts : tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
      (E.card : ℝ)*F.card*P.card*S := by
    refine hcount.trans ?_
    calc
      _ ≤ ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, S := by
        apply sum_le_sum
        intro Oa hOa
        apply sum_le_sum
        intro Od hOd
        exact sum_le_sum (fun Y hY => hpoint Oa hOa Od hOd Y hY)
      _ = _ := by simp only [sum_const,nsmul_eq_mul] <;> ring
  let ea := (g/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let eb := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let ec := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε
  have hca : (E.card : ℝ) ≤ ((A.card : ℝ)+1)*Real.exp (ea*ℓ) := by
    have hh := henv τ hτ hτa' B C A d hℓ hAr
    rwa [hkg] at hh
  have hcb : (F.card : ℝ) ≤ ((D.card : ℝ)+1)*Real.exp (eb*ℓ) := by
    have hh := henv τ hτ hτa' B C D f hℓ hDr
    rwa [hkg] at hh
  have hcc : (P.card : ℝ) ≤ ((V.card : ℝ)+1)*Real.exp (ec*ℓ) := by
    have hh := hpre τ hτ.le hτb' B C V f hℓ hVr
    rwa [hkg] at hh
  have hexp := large_multiplicity_exponent_bound (Δ := Δ) (τ := τ) (ε := ε)
    (ℓ := ℓ) (d := d) (f := f) hg.le hg1 hδ.le
  have hprod := mul_le_mul (mul_le_mul hca hcb (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)) hcc (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
        (mul_nonneg (by positivity) (Real.exp_pos _).le))
  refine hcounts.trans ((mul_le_mul_of_nonneg_right hprod hS).trans ?_)
  have heq : Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
      Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ) =
      Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  calc
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        (Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
          Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)) := by dsimp only [S] <;> ring
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by rw [heq]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hexp hℓ.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_SmallCandidateMultiplicity
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairs of representations with only small added primes -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem smallCandidateAlternatives_subset (B L T H : ℕ) (τ C : ℝ)
    {M : ℕ} (i k : Fin M) (A D U V : Finset ℕ) :
    smallCandidateAlternatives B L T H τ C i k A D U V ⊆
      (regularSmallAlternatives B L 3 τ C A U).product
        (regularSmallAlternatives B L 3 τ C D V) := by
  intro ab hab
  obtain ⟨hab,hadd⟩ := mem_filter.mp hab
  have hm := mem_product.mp (mem_filter.mp hab).1
  have ha := mem_endpointSplits.mp hm.1
  have hd := mem_endpointSplits.mp hm.2
  exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr ha.1,ha.2.1,hadd.1⟩,
    mem_filter.mpr ⟨mem_powerset.mpr hd.1,hd.2.1,hadd.2⟩⟩

theorem smallCandidateAlternatives_exp_bound {B L T H : ℕ} {τ C : ℝ}
    {M : ℕ} (i k : Fin M) (A D U V : Finset ℕ) (hL : 3 ≤ L)
    (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hA : RegularPrimeSet B L τ C A) (hD : RegularPrimeSet B L τ C D)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
      Real.exp (smallMultiplicityExponent L τ*auxiliaryLogLength B) := by
  have ha := regularSmallAlternatives_exp_bound (k := 3) A U (by omega) (by simp; omega) hτ hτsmall hℓ hA hU
  have hd := regularSmallAlternatives_exp_bound (k := 3) D V (by omega) (by simp; omega) hτ hτsmall hℓ hD hV
  have hc : ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
      (regularSmallAlternatives B L 3 τ C A U).card*
        (regularSmallAlternatives B L 3 τ C D V).card := by
    exact_mod_cast (card_le_card (smallCandidateAlternatives_subset B L T H τ C i k A D U V)).trans_eq
      (by rw [Finset.product_eq_sprod,card_product])
  refine hc.trans ((mul_le_mul ha hd (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold smallMultiplicityExponent
  ring

theorem smallMultiplicityExponent_nonneg {L : ℕ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ 1/100) : 0 ≤ smallMultiplicityExponent L τ := by
  unfold smallMultiplicityExponent
  exact add_nonneg (mul_nonneg (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (mul_nonneg (by norm_num) hτ)) (Real.log_nonneg (by norm_num)))
    (mul_nonneg (by norm_num) (highOmissionExponent_nonneg hτ hτsmall))

/-- The deterministic small-addition count has the same bound under every
probability law on the two remainders. -/
theorem smallCandidateAlternatives_rpow_bound {L : ℕ} (hL : 3 ≤ L)
    {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ 1/100) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i k : Fin M) (A D U V : Finset ℕ),
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
        (B : ℝ)^(smallMultiplicityExponent L τ) := by
  filter_upwards [auxiliaryLogLength_between, eventually_gt_atTop 0] with B hℓ hB
  intro T H M C i k A D U V hA hD hU hV
  have h := smallCandidateAlternatives_exp_bound (T := T) (H := H) i k A D U V hL hτ hτsmall hℓ.1 hA hD hU hV
  refine h.trans ?_
  rw [Real.rpow_def_of_pos (by exact_mod_cast hB : (0 : ℝ) < B)]
  exact Real.exp_le_exp.mpr (by
    nlinarith [mul_le_mul_of_nonneg_left hℓ.2 (smallMultiplicityExponent_nonneg hτ.le hτsmall (L := L))])

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicityParameters
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the grid and tolerance for the small-addition estimate -/

namespace JointDickman
open Filter
open scoped Topology

theorem smallMultiplicityExponent_tendsto (L : ℕ) :
    Tendsto (smallMultiplicityExponent L) (𝓝 0) (𝓝 ((6 : ℝ)/L*Real.log 2)) := by
  change Tendsto (fun τ : ℝ => ((6 : ℝ)/L+4*τ)*Real.log 2+2*highOmissionExponent τ) _ _
  have hh := (((tendsto_const_nhds (x := (6 : ℝ)/L)).add (tendsto_id.const_mul (4 : ℝ))).mul_const (Real.log 2)).add
    (highOmissionExponent_tendsto.const_mul (2 : ℝ))
  simpa [smallMultiplicityExponent] using hh

theorem smallCandidateAlternatives_power_bound {L : ℕ} (hL : 3 ≤ L)
    {τ : ℝ} (hτ : 0 < τ) (hτsmall : τ ≤ samplingTau)
    (he : smallMultiplicityExponent L τ ≤ 8/1000) :
    ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i k : Fin M) (A D U V : Finset ℕ),
      RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
      RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i k A D U V).card : ℝ) ≤
        (B : ℝ)^(8/1000 : ℝ) := by
  have hsmall : τ ≤ 1/100 := hτsmall.trans (by norm_num [samplingTau])
  filter_upwards [smallCandidateAlternatives_rpow_bound hL hτ hsmall, eventually_ge_atTop 1] with B hB hB1
  intro T H M C i k A D U V hA hD hU hV
  exact (hB T H M C i k A D U V hA hD hU hV).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB1) he)

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_MultiplicityMargins
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible small and large multiplicity parameters -/

namespace JointDickman
open Filter
open scoped Topology

theorem largeMultiplicityLoss_tendsto (Δ δ ε : ℝ) :
    Tendsto (fun τ : ℝ => largeMultiplicityLoss Δ δ τ ε) (𝓝 0) (𝓝 (3*Δ+2*δ+5*ε)) := by
  have h := (((tendsto_const_nhds (x := 3*Δ+2*δ)).add
    (tendsto_id.const_mul (Real.log 2-Real.log (2*δ)))).add_const (5*ε)).add
      (highOmissionExponent_tendsto.const_mul 2)
  simpa [largeMultiplicityLoss] using h

/-- A common arbitrarily small positive tolerance preserves both the
small-addition exponent and the large-addition margin. -/
theorem exists_common_multiplicity_tolerance {L : ℕ} (hL : 10000 ≤ L)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      smallMultiplicityExponent L τ < 8/1000 ∧
      largeMultiplicityLoss (1/(L : ℝ)) (1/200) τ (1/1000) < 4/100 := by
  have hLr : (10000 : ℝ) ≤ L := by exact_mod_cast hL
  have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsmall : (6 : ℝ)/L*Real.log 2 < 8/1000 := by
    have hd : (6 : ℝ)/L ≤ 6/10000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLr
    have hp : 0 ≤ (6 : ℝ)/L := div_nonneg (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hlog hp]
  have hlarge : 3*(1/(L : ℝ))+2*(1/200 : ℝ)+5*(1/1000) < 4/100 := by
    have hd : (1 : ℝ)/L ≤ 1/10000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLr
    linarith
  have hnear := ((smallMultiplicityExponent_tendsto L).eventually (Iio_mem_nhds hsmall)).and
    ((largeMultiplicityLoss_tendsto (1/(L : ℝ)) (1/200) (1/1000)).eventually (Iio_mem_nhds hlarge))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let τ := min (r/2) (min cap samplingTau)
  have hτ : 0 < τ := lt_min (by positivity) (lt_min hcap samplingTau_pos)
  have hτr : τ < r := (min_le_left _ _).trans_lt (by linarith)
  have hp := hball (show dist τ 0 < r by simpa only [Real.dist_eq,sub_zero,abs_of_pos hτ] using hτr)
  exact ⟨τ,hτ,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _),hp.1,hp.2⟩

/-- Every fixed logarithmic polynomial is negligible compared to the
strict power saving in the large-class estimate. -/
theorem log_add_one_cube_div_rpow_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun B : ℝ => (Real.log B+1)^3/B^c) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℝ => 8*(Real.log B)^3/B^c) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using
      (log_power_div_power_tendsto_zero (3 : ℕ) hc).const_mul 8
  apply squeeze_zero' _ _ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hB.le _)
    have hh : Real.log B+1 ≤ 2*Real.log B := by linarith
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B+1) hh 3
    nlinarith

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeHighVanishing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing contribution of each large high-endpoint class -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem largeMultiplicityLoss_nonneg {Δ δ τ ε : ℝ}
    (hΔ : 0 ≤ Δ) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2)
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/100) (hε : 0 ≤ ε) :
    0 ≤ largeMultiplicityLoss Δ δ τ ε := by
  have hlog : Real.log (2*δ) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have hdiff : 0 ≤ Real.log 2-Real.log (2*δ) := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hhigh := highOmissionExponent_nonneg hτ hτ1
  unfold largeMultiplicityLoss
  positivity

theorem largeClassError_tendsto {K η ν : ℝ} (hν : ν < 32/100) :
    Tendsto (largeClassError K η ν) atTop (𝓝 0) := by
  have hh := ((log_add_one_cube_div_rpow_tendsto (sub_pos.mpr hν)).comp
    tendsto_natCast_atTop_atTop).const_mul (K/η)
  unfold largeClassError
  simpa only [mul_zero,mul_div_assoc,Function.comp_apply] using hh

theorem large_high_class_error_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ K : ℝ, 0 < K ∧
        Tendsto (largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)) atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedLargeHighPairCount B L k j d f τ C Δ A D V ≤
            largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε) B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_high_alternative_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε
  refine ⟨min τ₁ (1/1000),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτsmall' : τ ≤ 1/1000 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,hestimate⟩ := hbound τ hτ hτ₁'
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  have hν0 : 0 ≤ ν := add_nonneg largeMultiplicityBase_bounds.1.le
    (largeMultiplicityLoss_nonneg hΔ.le hδ hδ1 hτ.le (by linarith) hε.le)
  refine ⟨K,hK,largeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hcard (R : Finset ℕ) (hR : RegularPrimeSet B L τ C R) : (R.card : ℝ)+1 ≤ Real.log B+1 := by
    have hh := hR.total_upper hL
    have hc : (1/2+τ)*auxiliaryLogLength B ≤ auxiliaryLogLength B := by
      have hm := mul_le_mul_of_nonneg_right (show 1/2+τ ≤ (1 : ℝ) by linarith) hℓB.1
      simpa only [one_mul] using hm
    linarith [hh.trans hc,hℓB.2]
  have hprod : ((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1) ≤ (Real.log B+1)^3 := by
    have hp := mul_le_mul (mul_le_mul (hcard A hAr) (hcard D hDr) (by positivity) (by positivity))
      (hcard V hVr) (by positivity) (by positivity)
    nlinarith
  have hexp : Real.exp (ν*auxiliaryLogLength B) ≤ (B : ℝ)^ν := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hℓB.2 hν0]
  have hjinv : K/(j : ℝ) ≤ K/(η*(B : ℝ)^(32/100 : ℝ)) :=
    div_le_div_of_nonneg_left hK.le (by positivity) hjlow
  have hh := hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  refine hh.trans ?_
  change K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
    Real.exp (ν*auxiliaryLogLength B) ≤ _
  calc
    _ = (K/(j : ℝ))*(((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1))*
        Real.exp (ν*auxiliaryLogLength B) := by ring
    _ ≤ (K/(η*(B : ℝ)^(32/100 : ℝ)))*(Real.log B+1)^3*(B : ℝ)^ν :=
      mul_le_mul (mul_le_mul hjinv hprod (by positivity) (by positivity)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      dsimp only [largeClassError,ν]
      rw [Real.rpow_sub hB0]
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AllLargeHighVanishing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing every cardinality class of a large high-endpoint addition -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem log_add_one_fifth_div_rpow_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun B : ℝ => (Real.log B+1)^5/B^c) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℝ => 32*(Real.log B)^5/B^c) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast,mul_zero,mul_div_assoc] using
      (log_power_div_power_tendsto_zero (5 : ℕ) hc).const_mul 32
  apply squeeze_zero' _ _ ht
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    positivity
  · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0 : ℝ)] with B hlog hB
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hB.le _)
    have hh : Real.log B+1 ≤ 2*Real.log B := by linarith
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log B+1) hh 5
    nlinarith

theorem allLargeClassError_tendsto {K η ν : ℝ} (hν : ν < 32/100) :
    Tendsto (allLargeClassError K η ν) atTop (𝓝 0) := by
  have hh := ((log_add_one_fifth_div_rpow_tendsto (sub_pos.mpr hν)).comp
    tendsto_natCast_atTop_atTop).const_mul (K/η)
  unfold allLargeClassError
  simpa only [mul_zero,mul_div_assoc,Function.comp_apply] using hh

/-- All cardinality classes together still have vanishing expected
multiplicity. The only loss from summing them is two logarithmic powers. -/
theorem all_large_high_class_vanishing
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeHighPairCount B L k j τ C Δ A D V ≤ E B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_high_class_error_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε hη
  refine ⟨min τ₁ (1/2),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτhalf : τ ≤ 1/2 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,_,hestimate⟩ := hbound τ hτ hτ₁' hloss
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  refine ⟨allLargeClassError K η ν,allLargeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  rw [tiltedAllLargeHighPairCount_eq_sum A D V hk hτhalf hℓB.1 hVr]
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hN : (N : ℝ) ≤ Real.log B+1 := by
    have hh := Nat.floor_le hℓB.1
    dsimp only [N]
    push_cast
    linarith [hℓB.2]
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hE : 0 ≤ largeClassError K η ν B := by
    unfold largeClassError
    positivity
  calc
    _ ≤ ∑ d ∈ range N, ∑ f ∈ range N, largeClassError K η ν B := by
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro f _
      exact hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
    _ = (N : ℝ)^2*largeClassError K η ν B := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ (Real.log B+1)^2*largeClassError K η ν B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) hE
    _ = _ := by unfold largeClassError allLargeClassError; ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowNumericAdditionClass
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAlternativePairs
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual pairs with a large addition at the low endpoint -/

namespace JointDickman
open Finset Classical

/-- Every actual pair maps to a fixed old-prime choice, a fixed opposite
addition, and an element of the numerically sieved class. -/
theorem largeLowAlternativePairs_encoding {B L k j d f : ℕ} {τ C Δ : ℝ}
    {A U D V X Y : Finset ℕ} (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V)
    (hXY : (X,Y) ∈ largeLowAlternativePairs B L k j d f τ C Δ A U D V) :
    A \ X ∈ omissionEnvelope B L k τ A d ∧
    D \ Y ∈ omissionEnvelope B L k τ D f ∧
    Y \ D ∈ regularPrefixChoices B L k V f ∧
    X \ A ∈ (activeLowAdditionClass B L k τ C Δ A
      (∏ p ∈ A \ (A \ X), p) j
      ((∏ p ∈ D \ (D \ Y), p)*(∏ p ∈ Y \ D, p)) d).filter (fun Z => Z ⊆ U) := by
  obtain ⟨hXY,hd,hf,hlarge,hsize,hXsize,hYsize,c,hc,hrel,hcr⟩ := mem_filter.mp hXY
  obtain ⟨hX,hY⟩ := mem_product.mp hXY
  have hZA := alternative_additions_subset_remainder hX
  have hYV := alternative_additions_subset_remainder hY
  have hZP : X \ A ⊆ auxiliaryPrimes B := hZA.trans (hU.trans sdiff_subset)
  have hXP : X ⊆ auxiliaryPrimes B :=
    (mem_powerset.mp (mem_filter.mp hX).1).trans (union_subset hA (hU.trans sdiff_subset))
  have hepos : 0 < (∏ p ∈ A \ (A \ X), p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA ((mem_sdiff.mp hp).1))).pos)
  have her : (0 : ℝ) < (∏ p ∈ A \ (A \ X), p : ℕ) := by exact_mod_cast hepos
  have hzpos : 0 < (∏ p ∈ X \ A, p : ℕ) :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hZP hp)).pos)
  have hdecomp := retained_addition_product A X
  have hydecomp := retained_addition_product D Y
  let e := (∏ p ∈ A \ (A \ X), p : ℕ)
  let b := (∏ p ∈ D \ (D \ Y), p : ℕ)*(∏ p ∈ Y \ D, p : ℕ)
  let z := (∏ p ∈ X \ A, p : ℕ)
  have heq : e*z+j*c = b := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hrel
  have hbound : b ≤ 2*(e*z : ℕ) := by
    dsimp only [e,b,z]
    rw [← hdecomp,← hydecomp]
    exact hsize
  have hlo : highAdditionWindow e b ≤ (z : ℝ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*e)).mpr
    have hr : (b : ℝ) ≤ 2*((e : ℝ)*z) := by exact_mod_cast hbound
    change (b : ℝ) ≤ (z : ℝ)*(2*e)
    nlinarith
  have hhi : (z : ℝ) ≤ 4*highAdditionWindow e b := by
    have hr : (e : ℝ)*z ≤ b := by exact_mod_cast (by omega : e*z ≤ b)
    calc
      _ ≤ (2*(b : ℝ))/(e : ℝ) := (le_div_iff₀ her).mpr (by nlinarith [hr, show (0 : ℝ) ≤ b from Nat.cast_nonneg b])
      _ = _ := by unfold highAdditionWindow; ring
  have hactive : (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) ∧
      Real.exp ((B : ℝ)^((k : ℝ)/L-Δ))/4 ≤ highAdditionWindow e b := by
    refine ⟨?_,?_⟩
    · dsimp only [b]
      rwa [← hydecomp]
    · have hl : Real.exp ((B : ℝ)^((k : ℝ)/L-Δ)) ≤ (z : ℝ) := hlarge
      linarith
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hd] using regular_omission_mem_envelope hk hτ hℓ hAr hUr hX
  · simpa only [hf] using regular_omission_mem_envelope hk hτ hℓ hDr hVr hY
  · exact mem_filter.mpr ⟨mem_powerset.mpr
      ((mem_filter.mp hY).2.2.trans (primePrefix_mono B _ hYV)),hf⟩
  · apply mem_filter.mpr
    refine ⟨?_,hZA⟩
    change X \ A ∈ activeLowAdditionClass B L k τ C Δ A e j b d
    rw [activeLowAdditionClass,ite_eq_left hactive]
    apply mem_filter.mpr
    refine ⟨mem_lowNumericAdditionClass.mpr ⟨hZP,hd,hlo,hhi,c,hc,heq,hcr⟩,
      hZA.trans hU,?_,(mem_filter.mp hX).2.2⟩
    have hdiv : z ∣ ∏ p ∈ X, p := prod_dvd_prod_of_subset _ _ id sdiff_subset
    have hprodpos : 0 < ∏ p ∈ X, p := prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hXP hp)).pos)
    exact (show (z : ℝ) ≤ (∏ p ∈ X, p : ℕ) by exact_mod_cast Nat.le_of_dvd hprodpos hdiv).trans hXsize

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAlternativeCount
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injectively counting large alternative representations by numeric classes -/

namespace JointDickman
open Finset Classical

theorem largeLowAlternativePairs_count {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B) (hU : U ⊆ auxiliaryPrimes B \ A)
    (hAr : RegularPrimeSet B L τ C A) (hUr : RegularPrimeSet B L τ C U)
    (hDr : RegularPrimeSet B L τ C D) (hVr : RegularPrimeSet B L τ C V) :
    (largeLowAlternativePairs B L k j d f τ C Δ A U D V).card ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            ((activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
              ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U)).card := by
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let target := E.sigma (fun Oa => F.sigma (fun Od => P.sigma (fun Y =>
    (activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
      ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d).filter (fun Z => Z ⊆ U))))
  let enc : (Finset ℕ × Finset ℕ) → Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ :=
    fun XY => ⟨A \ XY.1,⟨D \ XY.2,⟨XY.2 \ D,XY.1 \ A⟩⟩⟩
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ largeLowAlternativePairs B L k j d f τ C Δ A U D V) : enc XY ∈ target := by
    have hh := largeLowAlternativePairs_encoding hk hτ hℓ hA hU hAr hUr hDr hVr hXY
    simpa only [target,enc,E,F,P,mem_sigma] using hh
  have hinj : Set.InjOn enc (largeLowAlternativePairs B L k j d f τ C Δ A U D V) := by
    intro XY _ ZW _ he
    have h₁ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.1) he
    have h₂ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.1) he
    have h₃ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.1) he
    have h₄ := congrArg (fun t : Σ _ : Finset ℕ, Σ _ : Finset ℕ, Σ _ : Finset ℕ, Finset ℕ => t.2.2.2) he
    change A \ XY.1 = A \ ZW.1 at h₁
    change D \ XY.2 = D \ ZW.2 at h₂
    change XY.2 \ D = ZW.2 \ D at h₃
    change XY.1 \ A = ZW.1 \ A at h₄
    apply Prod.ext
    · ext p
      have h₁ := Finset.ext_iff.mp h₁ p
      have h₄ := Finset.ext_iff.mp h₄ p
      simp only [Finset.mem_sdiff] at *
      tauto
    · ext p
      have h₂ := Finset.ext_iff.mp h₂ p
      have h₃ := Finset.ext_iff.mp h₃ p
      simp only [Finset.mem_sdiff] at *
      tauto
  have hc := card_le_card_of_injOn enc hmap hinj
  simpa only [target,card_sigma,E,F,P] using hc

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAlternativeExpectation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaging the injective count before applying the numeric sieve -/

namespace JointDickman
open Finset Classical

theorem tiltedLargeLowPairCount_le_classes {B L k j d f : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : 0 ≤ τ) (hℓ : 0 < auxiliaryLogLength B)
    (hA : A ⊆ auxiliaryPrimes B)
    (hAr : RegularPrimeSet B L τ C A) (hDr : RegularPrimeSet B L τ C D)
    (hVr : RegularPrimeSet B L τ C V) :
    tiltedLargeLowPairCount B L k j d f τ C Δ A D V ≤
      ∑ Oa ∈ omissionEnvelope B L k τ A d,
        ∑ Od ∈ omissionEnvelope B L k τ D f,
          ∑ Y ∈ regularPrefixChoices B L k V f,
            tiltedRegularSubsetCount B L τ C A
              (activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
                ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) := by
  let μ := fun U => bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let G := fun Oa Od Y => activeLowAdditionClass B L k τ C Δ A (∏ p ∈ A \ Oa, p) j
    ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d
  have hmass (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) : 0 ≤ μ U := by
    apply bernoulliSubsetMass_nonneg (mem_powerset.mp hU)
    intro p hp
    have hprime := auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
    constructor
    · apply div_nonneg (by norm_num)
      linarith
    · apply (div_le_one (by linarith : (0 : ℝ) < 2*p-1)).mpr
      linarith
  have hpoint (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset) :
      μ U*(if RegularPrimeSet B L τ C U then
        ((largeLowAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0) ≤
      ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
        μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) := by
    by_cases hUr : RegularPrimeSet B L τ C U
    · simp only [hUr,ite_true, if_true]
      have hc : ((largeLowAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) ≤
          ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) := by
        exact_mod_cast largeLowAlternativePairs_count A U D V hk hτ hℓ hA (mem_powerset.mp hU) hAr hUr hDr hVr
      simpa only [mul_sum] using mul_le_mul_of_nonneg_left hc (hmass U hU)
    · simp [hUr]
  calc
    _ ≤ ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P,
          μ U*(if RegularPrimeSet B L τ C U then (((G Oa Od Y).filter (fun Z => Z ⊆ U)).card : ℝ) else 0) :=
      sum_le_sum hpoint
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro Oa _
      rw [sum_comm]
      apply sum_congr rfl
      intro Od _
      rw [sum_comm]
      rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowCardinalityPartition
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partitioning all large low-endpoint alternatives by cardinality -/

namespace JointDickman
open Finset Classical

theorem allLargeLowAlternativePairs_fiber (B L k j d f : ℕ) (τ C Δ : ℝ)
    (A U D V : Finset ℕ) :
    (allLargeLowAlternativePairs B L k j τ C Δ A U D V).filter
      (fun XY => ((XY.1 \ A).card,(XY.2 \ D).card) = (d,f)) =
        largeLowAlternativePairs B L k j d f τ C Δ A U D V := by
  ext XY
  simp only [allLargeLowAlternativePairs,largeLowAlternativePairs,mem_filter,Prod.mk.injEq]
  tauto

theorem allLargeLowAlternativePairs_card {B L k j : ℕ} {τ C Δ : ℝ}
    (A U D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hU : RegularPrimeSet B L τ C U) (hV : RegularPrimeSet B L τ C V) :
    (allLargeLowAlternativePairs B L k j τ C Δ A U D V).card =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        (largeLowAlternativePairs B L k j d f τ C Δ A U D V).card := by
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hmap (XY : Finset ℕ × Finset ℕ)
      (hXY : XY ∈ allLargeLowAlternativePairs B L k j τ C Δ A U D V) :
      ((XY.1 \ A).card,(XY.2 \ D).card) ∈ (range N).product (range N) := by
    obtain ⟨hX,hY⟩ := mem_product.mp (mem_filter.mp hXY).1
    apply mem_product.mpr
    constructor
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hU hX)))
    · exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor
        (regular_addition_card_le_logLength hk hτ hℓ hV hY)))
  have hh := card_eq_sum_card_fiberwise hmap
  rw [Finset.product_eq_sprod,sum_product] at hh
  simpa only [allLargeLowAlternativePairs_fiber] using hh

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AllLargeLowExpectation
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cardinality-class decomposition in the tilted expectation -/

namespace JointDickman
open Finset Classical

theorem tiltedAllLargeLowPairCount_eq_sum {B L k j : ℕ} {τ C Δ : ℝ}
    (A D V : Finset ℕ) (hk : k ∈ Icc 1 L)
    (hτ : τ ≤ 1/2) (hℓ : 0 ≤ auxiliaryLogLength B)
    (hV : RegularPrimeSet B L τ C V) :
    tiltedAllLargeLowPairCount B L k j τ C Δ A D V =
      ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
        tiltedLargeLowPairCount B L k j d f τ C Δ A D V := by
  unfold tiltedAllLargeLowPairCount tiltedLargeLowPairCount
  calc
    _ = ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
          bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
            if RegularPrimeSet B L τ C U then
              ((largeLowAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) else 0 := by
      apply sum_congr rfl
      intro U _
      by_cases hU : RegularPrimeSet B L τ C U
      · simp only [hU,ite_true, if_true,← mul_sum]
        have hc : ((allLargeLowAlternativePairs B L k j τ C Δ A U D V).card : ℝ) =
            ∑ d ∈ range (⌊auxiliaryLogLength B⌋₊+1), ∑ f ∈ range (⌊auxiliaryLogLength B⌋₊+1),
              ((largeLowAlternativePairs B L k j d f τ C Δ A U D V).card : ℝ) := by
          exact_mod_cast allLargeLowAlternativePairs_card A U D V hk hτ hℓ hU hV
        rw [hc]
      · simp [hU]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [sum_comm]

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LowAlternativeBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The expected multiplicity of a large low-endpoint addition class -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem large_low_alternative_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          tiltedLargeLowPairCount B L k j d f τ C Δ A D V ≤
            K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
              Real.exp ((largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)*auxiliaryLogLength B) := by
  obtain ⟨τa,hτa,henv⟩ := omissionEnvelope_entropy hk hε
  obtain ⟨τb,hτb,hpre⟩ := regularPrefixChoices_entropy hk hε
  refine ⟨min τa (min τb 1),lt_min hτa (lt_min hτb (by norm_num)),?_⟩
  intro τ hτ hτsmall
  have hτa' : τ ≤ τa := hτsmall.trans (min_le_left _ _)
  have hτb' : τ ≤ τb := (hτsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hτ1 : τ ≤ 1 := (hτsmall.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨K,hK,hactive⟩ := active_low_addition_class_bound_jd hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hτ.le hτ1 hε
  refine ⟨K,hK,?_⟩
  filter_upwards [hactive,auxiliaryLogLength_tendsto.eventually_gt_atTop 0] with B hB hℓ
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  let ℓ := auxiliaryLogLength B
  let E := omissionEnvelope B L k τ A d
  let F := omissionEnvelope B L k τ D f
  let P := regularPrefixChoices B L k V f
  let S := K/(j : ℝ)*Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)
  have hS : 0 ≤ S := by dsimp only [S] <;> positivity
  have hpoint (Oa : Finset ℕ) (_hOa : Oa ∈ E) (Od : Finset ℕ) (_hOd : Od ∈ F)
      (Y : Finset ℕ) (hY : Y ∈ P) :
      tiltedRegularSubsetCount B L τ C A (activeLowAdditionClass B L k τ C Δ A
        (∏ p ∈ A \ Oa, p) j ((∏ p ∈ D \ Od, p)*(∏ p ∈ Y, p)) d) ≤ S := by
    have hYsub : Y ⊆ auxiliaryPrimes B := by
      have hy := mem_powerset.mp (mem_filter.mp hY).1
      have hp : primePrefix B ((k : ℝ)/L) V ⊆ V := by
        unfold primePrefix
        split_ifs
        · exact filter_subset _ _
        · exact subset_rfl
      exact (hy.trans hp).trans hV
    have he0 : 0 < (∏ p ∈ A \ Oa, p : ℕ) :=
      prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA (mem_sdiff.mp hp).1)).pos)
    have hb0 : 0 < (∏ p ∈ D \ Od, p : ℕ)*(∏ p ∈ Y, p) := mul_pos
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD (mem_sdiff.mp hp).1)).pos))
      (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hYsub hp)).pos))
    have heA : (∏ p ∈ A \ Oa, p : ℕ) ≤ ∏ p ∈ A, p :=
      Nat.le_of_dvd (prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hA hp)).pos))
        (prod_dvd_prod_of_subset _ _ id sdiff_subset)
    exact hB C A _ j _ d hA hAsize he0 hb0 hj hcut
      (auxiliary_product_coprime_lag (sdiff_subset.trans hA) hj hcut)
      ((show ((∏ p ∈ A \ Oa, p : ℕ) : ℝ) ≤ (∏ p ∈ A, p : ℕ) by exact_mod_cast heA).trans hAsize) hjB
  have hcount := tiltedLargeLowPairCount_le_classes A D V hk hτ.le hℓ hA hAr hDr hVr
    (j := j) (d := d) (f := f) (Δ := Δ)
  have hcounts : tiltedLargeLowPairCount B L k j d f τ C Δ A D V ≤
      (E.card : ℝ)*F.card*P.card*S := by
    refine hcount.trans ?_
    calc
      _ ≤ ∑ Oa ∈ E, ∑ Od ∈ F, ∑ Y ∈ P, S := by
        apply sum_le_sum
        intro Oa hOa
        apply sum_le_sum
        intro Od hOd
        exact sum_le_sum (fun Y hY => hpoint Oa hOa Od hOd Y hY)
      _ = _ := by simp only [sum_const,nsmul_eq_mul] <;> ring
  let ea := (g/2)*Real.binEntropy (2*min ((d : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let eb := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε+highOmissionExponent τ
  let ec := (g/2)*Real.binEntropy (2*min ((f : ℝ)/(g*ℓ)) (1/2))+ε
  have hca : (E.card : ℝ) ≤ ((A.card : ℝ)+1)*Real.exp (ea*ℓ) := by
    have hh := henv τ hτ hτa' B C A d hℓ hAr
    rwa [hkg] at hh
  have hcb : (F.card : ℝ) ≤ ((D.card : ℝ)+1)*Real.exp (eb*ℓ) := by
    have hh := henv τ hτ hτa' B C D f hℓ hDr
    rwa [hkg] at hh
  have hcc : (P.card : ℝ) ≤ ((V.card : ℝ)+1)*Real.exp (ec*ℓ) := by
    have hh := hpre τ hτ.le hτb' B C V f hℓ hVr
    rwa [hkg] at hh
  have hexp := large_multiplicity_exponent_bound (Δ := Δ) (τ := τ) (ε := ε)
    (ℓ := ℓ) (d := d) (f := f) hg.le hg1 hδ.le
  have hprod := mul_le_mul (mul_le_mul hca hcb (Nat.cast_nonneg _)
    (mul_nonneg (by positivity) (Real.exp_pos _).le)) hcc (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
        (mul_nonneg (by positivity) (Real.exp_pos _).le))
  refine hcounts.trans ((mul_le_mul_of_nonneg_right hprod hS).trans ?_)
  have heq : Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
      Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ) =
      Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  calc
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        (Real.exp (ea*ℓ)*Real.exp (eb*ℓ)*Real.exp (ec*ℓ)*
          Real.exp (largeAvailabilityExponent g Δ δ τ ε ℓ d*ℓ)) := by dsimp only [S] <;> ring
    _ = K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
        Real.exp ((largeAvailabilityExponent g Δ δ τ ε ℓ d+ea+eb+ec)*ℓ) := by rw [heq]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hexp hℓ.le

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_LargeLowVanishing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing contribution of each large low-endpoint class -/

namespace JointDickman
open Filter Finset
open scoped Topology

theorem large_low_class_error_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ K : ℝ, 0 < K ∧
        Tendsto (largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε)) atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j d f : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedLargeLowPairCount B L k j d f τ C Δ A D V ≤
            largeClassError K η (largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε) B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_low_alternative_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε
  refine ⟨min τ₁ (1/1000),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτsmall' : τ ≤ 1/1000 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,hestimate⟩ := hbound τ hτ hτ₁'
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  have hν0 : 0 ≤ ν := add_nonneg largeMultiplicityBase_bounds.1.le
    (largeMultiplicityLoss_nonneg hΔ.le hδ hδ1 hτ.le (by linarith) hε.le)
  refine ⟨K,hK,largeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hL : 1 ≤ L := (mem_Icc.mp hk).1.trans (mem_Icc.mp hk).2
  have hcard (R : Finset ℕ) (hR : RegularPrimeSet B L τ C R) : (R.card : ℝ)+1 ≤ Real.log B+1 := by
    have hh := hR.total_upper hL
    have hc : (1/2+τ)*auxiliaryLogLength B ≤ auxiliaryLogLength B := by
      have hm := mul_le_mul_of_nonneg_right (show 1/2+τ ≤ (1 : ℝ) by linarith) hℓB.1
      simpa only [one_mul] using hm
    linarith [hh.trans hc,hℓB.2]
  have hprod : ((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1) ≤ (Real.log B+1)^3 := by
    have hp := mul_le_mul (mul_le_mul (hcard A hAr) (hcard D hDr) (by positivity) (by positivity))
      (hcard V hVr) (by positivity) (by positivity)
    nlinarith
  have hexp : Real.exp (ν*auxiliaryLogLength B) ≤ (B : ℝ)^ν := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hℓB.2 hν0]
  have hjinv : K/(j : ℝ) ≤ K/(η*(B : ℝ)^(32/100 : ℝ)) :=
    div_le_div_of_nonneg_left hK.le (by positivity) hjlow
  have hh := hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB
  refine hh.trans ?_
  change K/(j : ℝ)*((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1)*
    Real.exp (ν*auxiliaryLogLength B) ≤ _
  calc
    _ = (K/(j : ℝ))*(((A.card : ℝ)+1)*((D.card : ℝ)+1)*((V.card : ℝ)+1))*
        Real.exp (ν*auxiliaryLogLength B) := by ring
    _ ≤ (K/(η*(B : ℝ)^(32/100 : ℝ)))*(Real.log B+1)^3*(B : ℝ)^ν :=
      mul_le_mul (mul_le_mul hjinv hprod (by positivity) (by positivity)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      dsimp only [largeClassError,ν]
      rw [Real.rpow_sub hB0]
      field_simp

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_AllLargeLowVanishing
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing every cardinality class of a large low-endpoint addition -/

namespace JointDickman
open Finset Filter
open scoped Topology

/-- All cardinality classes together still have vanishing expected
multiplicity. The only loss from summing them is two logarithmic powers. -/
theorem all_large_low_class_vanishing
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L k : ℕ} (hk : k ∈ Icc 1 L) {g Δ δ ε η : ℝ}
    (hkg : (k : ℝ)/L = g) (hg : 0 < g) (hg1 : g ≤ 1)
    (hΔ : 0 < Δ) (hgap : 2*Δ < g)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) (hε : 0 < ε) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      largeMultiplicityLoss Δ δ τ ε < 4/100 →
      ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ᶠ B : ℕ in atTop,
        ∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeLowPairCount B L k j τ C Δ A D V ≤ E B := by
  obtain ⟨τ₁,hτ₁,hbound⟩ := large_low_class_error_bound hFord hM hk hkg hg hg1 hΔ hgap hδ hδ1 hε hη
  refine ⟨min τ₁ (1/2),lt_min hτ₁ (by norm_num),?_⟩
  intro τ hτ hτsmall hloss
  have hτ₁' : τ ≤ τ₁ := hτsmall.trans (min_le_left _ _)
  have hτhalf : τ ≤ 1/2 := hτsmall.trans (min_le_right _ _)
  obtain ⟨K,hK,_,hestimate⟩ := hbound τ hτ hτ₁' hloss
  let ν := largeMultiplicityBase+largeMultiplicityLoss Δ δ τ ε
  have hν : ν < 32/100 := by
    have hh := largeMultiplicityBase_bounds.2
    dsimp only [ν]
    linarith
  refine ⟨allLargeClassError K η ν,allLargeClassError_tendsto hν,?_⟩
  filter_upwards [hestimate,auxiliaryLogLength_between,eventually_gt_atTop 1] with B hB hℓB hB1
  intro C A D V j hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
  rw [tiltedAllLargeLowPairCount_eq_sum A D V hk hτhalf hℓB.1 hVr]
  let N := ⌊auxiliaryLogLength B⌋₊+1
  have hN : (N : ℝ) ≤ Real.log B+1 := by
    have hh := Nat.floor_le hℓB.1
    dsimp only [N]
    push_cast
    linarith [hℓB.2]
  have hlog : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB1.le)
  have hE : 0 ≤ largeClassError K η ν B := by
    unfold largeClassError
    positivity
  calc
    _ ≤ ∑ d ∈ range N, ∑ f ∈ range N, largeClassError K η ν B := by
      apply sum_le_sum
      intro d _
      apply sum_le_sum
      intro f _
      exact hB C A D V j d f hA hD hV hAr hDr hVr hAsize hj hcut hjB hjlow
    _ = (N : ℝ)^2*largeClassError K η ν B := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      ring
    _ ≤ (Real.log B+1)^2*largeClassError K η ν B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) hE
    _ = _ := by unfold largeClassError allLargeClassError; ring

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

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateAdditionClasses
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering the actual candidate representations by addition classes -/

namespace JointDickman
open Finset Classical

private theorem endpoint_box_exp_bound {B T c b : ℕ} (hB : 5 ≤ B)
    (hT : (T : ℝ) ≤ Real.exp B) (hc : (c : ℝ) ≤ Real.exp (2*B))
    (hb : b ≤ 2*T*c) : (b : ℝ) ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hB' : (5 : ℝ) ≤ B := by exact_mod_cast hB
  have htwo : (2 : ℝ) ≤ Real.exp ((B : ℝ)/5) := by
    linarith [Real.add_one_le_exp ((B : ℝ)/5)]
  calc
    (b : ℝ) ≤ 2*T*c := by exact_mod_cast hb
    _ ≤ 2*Real.exp (B : ℝ)*Real.exp (2*B) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hc
        (Nat.cast_nonneg _) (by positivity)
    _ = 2*Real.exp (3*(B : ℝ)) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ Real.exp ((B : ℝ)/5)*Real.exp (3*B) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Each actual representation is either small at both endpoints, or is
in a later grid class with a large addition at one of its endpoints. -/
theorem candidatePairRepresentations_addition_cover
    {B L T H M : ℕ} {τ C : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D U V : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hU : U ⊆ auxiliaryPrimes B) (hV : V ⊆ auxiliaryPrimes B)
    {ab : Finset ℕ × Finset ℕ}
    (hab : ab ∈ candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)) :
    ab ∈ smallCandidateAlternatives B L T H τ C i t A D U V ∨
      ∃ k ∈ Icc 4 L,
        ab ∈ allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V ∨
        ab.swap ∈ allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U := by
  obtain ⟨hm,he⟩ := mem_filter.mp hab
  obtain ⟨ha,hd⟩ := mem_product.mp hm
  have ha' := mem_endpointSplits.mp ha
  have hd' := mem_endpointSplits.mp hd
  have hZ : ab.1 \ A ⊆ auxiliaryPrimes B :=
    sdiff_subset.trans (ha'.1.trans (union_subset hA hU))
  have hY : ab.2 \ D ⊆ auxiliaryPrimes B :=
    sdiff_subset.trans (hd'.1.trans (union_subset hD hV))
  rcases addition_scale_dichotomy hL hZ hY with hs | ⟨k,hk,hz,hy,hl⟩
  · exact Or.inl (mem_filter.mpr ⟨hab,hs⟩)
  · right
    let e : BlockCandidateIndex M := ((i,t),ab)
    have he' : BlockCandidateAdmissible B L T H τ C e := he
    have hcsize := (candidate_quotient_exp_bounds he').2
    obtain ⟨_,_,_,hc,hrel,_,_,_,_,hcr,_,_,hlo,hhi,hdlo,hdhi⟩ := he'
    have hsizea := endpoint_box_exp_bound hB hT hcsize hhi
    have hsized := endpoint_box_exp_bound hB hT hcsize hdhi
    have hratiod : candidateHigh e ≤ 2*candidateLow e :=
      hdhi.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hlo)
    have hgeq : ((k : ℝ)-1)/L = (k : ℝ)/L-1/(L : ℝ) := by ring
    rw [hgeq] at hl
    have haReg : ab.1 ∈ regularSmallAlternatives B L k τ C A U :=
      mem_filter.mpr ⟨mem_powerset.mpr ha'.1,ha'.2.1,hz⟩
    have hdReg : ab.2 ∈ regularSmallAlternatives B L k τ C D V :=
      mem_filter.mpr ⟨mem_powerset.mpr hd'.1,hd'.2.1,hy⟩
    dsimp only [e,candidateLow,candidateHigh,candidateLag] at hrel hsizea hsized hratiod
    refine ⟨k,hk,?_⟩
    rcases hl with hl | hl
    · left
      exact mem_filter.mpr ⟨mem_product.mpr ⟨haReg,hdReg⟩,
        hl,hratiod,hsizea,hsized,candidateQuotient e,hc,hrel.symm,hcr⟩
    · right
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hdReg,haReg⟩,
        hl,hratiod,hsized,hsizea,candidateQuotient e,hc,hrel,hcr⟩

/-- A finite cardinal bound retaining every representation and both endpoint
orientations. No uniqueness of a coefficient pair is assumed. -/
theorem candidatePairRepresentations_card_le_addition_classes
    {B L T H M : ℕ} {τ C : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D U V : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B)
    (hU : U ⊆ auxiliaryPrimes B) (hV : V ⊆ auxiliaryPrimes B) :
    (candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)).card ≤
      (smallCandidateAlternatives B L T H τ C i t A D U V).card +
      ∑ k ∈ Icc 4 L,
        ((allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V).card +
         (allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U).card) := by
  let lo := fun k => allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V
  let hi := fun k => allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U
  have hsub : candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V) ⊆
      smallCandidateAlternatives B L T H τ C i t A D U V ∪
        (Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap) := by
    intro ab hab
    rcases candidatePairRepresentations_addition_cover hB hL hT i t A D U V hA hD hU hV hab with hs | ⟨k,hk,hh⟩
    · exact mem_union_left _ hs
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨k,hk,?_⟩
      rcases hh with hl | hh
      · exact mem_union_left _ hl
      · exact mem_union_right _ (mem_image.mpr ⟨ab.swap,hh,Prod.swap_swap ab⟩)
  calc
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V ∪
        (Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap)).card := card_le_card hsub
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V).card +
        ((Icc 4 L).biUnion (fun k => lo k ∪ (hi k).image Prod.swap)).card := card_union_le _ _
    _ ≤ (smallCandidateAlternatives B L T H τ C i t A D U V).card +
        ∑ k ∈ Icc 4 L, ((lo k).card+(hi k).card) := by
      apply Nat.add_le_add_left
      exact card_biUnion_le.trans (sum_le_sum (fun k _ => (card_union_le _ _).trans
        (Nat.add_le_add_left card_image_le _)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_RegularTiltAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tilted remainder averages with the regularity event retained -/

namespace JointDickman
open Finset Classical

theorem remainderTiltMass_nonneg (B : ℕ) (A U : Finset ℕ)
    (hU : U ∈ (auxiliaryPrimes B \ A).powerset) :
    0 ≤ bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U := by
  apply bernoulliSubsetMass_nonneg (mem_powerset.mp hU)
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by
    exact_mod_cast (auxiliaryPrimes_prime B p (mem_sdiff.mp hp).1).two_le
  exact ⟨div_nonneg (by norm_num) (by linarith), (div_le_one (by linarith : (0 : ℝ) < 2*p-1)).mpr (by linarith)⟩

theorem regularTiltAverage_mono {B L : ℕ} {τ C : ℝ} {A : Finset ℕ}
    {F G : Finset ℕ → ℝ}
    (h : ∀ U ∈ (auxiliaryPrimes B \ A).powerset,
      RegularPrimeSet B L τ C U → F U ≤ G U) :
    regularTiltAverage B L τ C A F ≤ regularTiltAverage B L τ C A G := by
  apply sum_le_sum
  intro U hU
  apply mul_le_mul_of_nonneg_left _ (remainderTiltMass_nonneg B A U hU)
  split_ifs with hr
  · exact h U hU hr
  · rfl

theorem regularTiltAverage_bound {B L : ℕ} {τ C K : ℝ} {A : Finset ℕ}
    (hK : 0 ≤ K) {F : Finset ℕ → ℝ}
    (h : ∀ U ∈ (auxiliaryPrimes B \ A).powerset,
      RegularPrimeSet B L τ C U → F U ≤ K) :
    regularTiltAverage B L τ C A F ≤ K := by
  calc
    _ ≤ ∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U*K := by
      apply sum_le_sum
      intro U hU
      apply mul_le_mul_of_nonneg_left _ (remainderTiltMass_nonneg B A U hU)
      split_ifs with hr
      · exact h U hU hr
      · exact hK
    _ = K := by rw [← sum_mul,bernoulliSubsetMass_sum,one_mul]

theorem regularTiltAverage_add (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (F G : Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => F U+G U) =
      regularTiltAverage B L τ C A F+regularTiltAverage B L τ C A G := by
  unfold regularTiltAverage
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro U _
  split_ifs <;> ring

theorem regularTiltAverage_sum {ι : Type*} (B L : ℕ) (τ C : ℝ) (A : Finset ℕ)
    (s : Finset ι) (F : ι → Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => ∑ i ∈ s, F i U) =
      ∑ i ∈ s, regularTiltAverage B L τ C A (F i) := by
  unfold regularTiltAverage
  rw [sum_comm]
  apply sum_congr rfl
  intro U _
  rw [← mul_sum]
  congr 1
  split_ifs <;> simp_all

theorem regularTiltAverage_comm (B L : ℕ) (τ C : ℝ) (A D : Finset ℕ)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (F U)) =
      regularTiltAverage B L τ C D (fun V => regularTiltAverage B L τ C A (fun U => F U V)) := by
  unfold regularTiltAverage
  have he (A D : Finset ℕ) (F : Finset ℕ → Finset ℕ → ℝ) :
      (∑ U ∈ (auxiliaryPrimes B \ A).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
          if RegularPrimeSet B L τ C U then
            ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
              bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V *
                if RegularPrimeSet B L τ C V then F U V else 0
          else 0) =
      ∑ U ∈ (auxiliaryPrimes B \ A).powerset, ∑ V ∈ (auxiliaryPrimes B \ D).powerset,
        bernoulliSubsetMass (auxiliaryPrimes B \ A) (fun p => 1/(2*(p : ℝ)-1)) U *
        bernoulliSubsetMass (auxiliaryPrimes B \ D) (fun p => 1/(2*(p : ℝ)-1)) V *
          if RegularPrimeSet B L τ C U ∧ RegularPrimeSet B L τ C V then F U V else 0 := by
    apply sum_congr rfl
    intro U _
    by_cases hU : RegularPrimeSet B L τ C U
    · simp only [hU,ite_true, if_true,true_and,mul_sum]
      apply sum_congr rfl
      intro V _
      ring
    · simp [hU]
  rw [he,he,sum_comm]
  apply sum_congr rfl
  intro V _
  apply sum_congr rfl
  intro U _
  simp only [and_comm]
  ring

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMultiplicityAverage
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual representation count under both tilted remainder laws -/

namespace JointDickman
open Finset Classical

/-- The finite grid cover can be averaged without dropping either regularity
indicator. The opposite orientation is averaged in the opposite order. -/
theorem tiltedCandidatePairCount_le_classes
    {B L T H M : ℕ} {τ C K : ℝ} (hB : 5 ≤ B) (hL : 3 ≤ L)
    (hT : (T : ℝ) ≤ Real.exp B) (i t : Fin M) (A D : Finset ℕ)
    (hA : A ⊆ auxiliaryPrimes B) (hD : D ⊆ auxiliaryPrimes B) (hK : 0 ≤ K)
    (hsmall : ∀ U V : Finset ℕ, RegularPrimeSet B L τ C U → RegularPrimeSet B L τ C V →
      ((smallCandidateAlternatives B L T H τ C i t A D U V).card : ℝ) ≤ K) :
    tiltedCandidatePairCount B L T H τ C i t A D ≤ K +
      ∑ k ∈ Icc 4 L,
        (regularTiltAverage B L τ C D (fun V =>
          tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) +
        regularTiltAverage B L τ C A (fun U =>
          tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U)) := by
  let small := fun U V => ((smallCandidateAlternatives B L T H τ C i t A D U V).card : ℝ)
  let lo := fun k U V => ((allLargeLowAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) A U D V).card : ℝ)
  let hi := fun k U V => ((allLargeHighAlternativePairs B L k (t.val-i.val) τ C (1/(L : ℝ)) D V A U).card : ℝ)
  have hpoint (U : Finset ℕ) (hU : U ∈ (auxiliaryPrimes B \ A).powerset)
      (V : Finset ℕ) (hV : V ∈ (auxiliaryPrimes B \ D).powerset) :
      ((candidatePairRepresentations B L T H τ C i t (A ∪ U) (D ∪ V)).card : ℝ) ≤
        small U V+∑ k ∈ Icc 4 L, (lo k U V+hi k U V) := by
    dsimp only [small,lo,hi]
    exact_mod_cast candidatePairRepresentations_card_le_addition_classes (H := H) (τ := τ) (C := C) hB hL hT i t A D U V
      hA hD ((mem_powerset.mp hU).trans sdiff_subset) ((mem_powerset.mp hV).trans sdiff_subset)
  calc
    _ ≤ regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D
        (fun V => small U V+∑ k ∈ Icc 4 L, (lo k U V+hi k U V))) := by
      apply regularTiltAverage_mono
      intro U hU _
      apply regularTiltAverage_mono
      intro V hV _
      exact hpoint U hU V hV
    _ = regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (small U)) +
        ∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (lo k U)) +
          regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (hi k U))) := by
      simp_rw [regularTiltAverage_add,regularTiltAverage_sum]
      simp_rw [regularTiltAverage_add]
    _ ≤ K+∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (lo k U)) +
          regularTiltAverage B L τ C A (fun U => regularTiltAverage B L τ C D (hi k U))) := by
      apply add_le_add _ le_rfl
      apply regularTiltAverage_bound hK
      intro U _ hUr
      apply regularTiltAverage_bound hK
      intro V _ hVr
      exact hsmall U V hUr hVr
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro k _
      rw [regularTiltAverage_comm B L τ C A D (lo k)]
      rfl

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_GridMultiplicityBounds
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One tolerance and vanishing errors for every grid cell -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

private theorem finite_positive_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) : ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t,ht,hbound⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi))
    refine ⟨min (f a) t,lt_min (hf a (mem_insert_self _ _)) ht,?_⟩
    intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound i hi)

/-- The actual sieve estimates at both endpoints hold for the same positive
tolerance, with a nonnegative vanishing majorant on every later grid cell. -/
theorem exists_grid_multiplicity_bounds
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      smallMultiplicityExponent L τ < 8/1000 ∧
      ∃ E : ℕ → ℕ → ℝ, (∀ k B, 0 ≤ E k B) ∧
        (∀ k ∈ Icc 4 L, Tendsto (E k) atTop (𝓝 0)) ∧
        ∀ᶠ B : ℕ in atTop, ∀ k ∈ Icc 4 L,
          ∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
            A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
            RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
            (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
            0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
            η*(B : ℝ)^(32/100 : ℝ) ≤ j →
            tiltedAllLargeLowPairCount B L k j τ C (1/(L : ℝ)) A D V ≤ E k B ∧
            tiltedAllLargeHighPairCount B L k j τ C (1/(L : ℝ)) A D V ≤ E k B := by
  let I := ↥(Icc 4 L)
  let : Fintype I := FinsetCoe.fintype _
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hg (k : I) : 0 < (k.val : ℝ)/L :=
    div_pos (by exact_mod_cast (show 0 < k.val from lt_of_lt_of_le (by norm_num) (mem_Icc.mp k.property).1)) hLpos
  have hg1 (k : I) : (k.val : ℝ)/L ≤ 1 :=
    (div_le_one hLpos).mpr (by exact_mod_cast (mem_Icc.mp k.property).2)
  have hgap (k : I) : 2*(1/(L : ℝ)) < (k.val : ℝ)/L := by
    rw [mul_one_div]
    exact (div_lt_div_iff_of_pos_right hLpos).mpr
      (by exact_mod_cast (show 2 < k.val from lt_of_lt_of_le (by norm_num) (mem_Icc.mp k.property).1))
  have hk (k : I) : k.val ∈ Icc 1 L := mem_Icc.mpr ⟨by have := (mem_Icc.mp k.property).1; omega,(mem_Icc.mp k.property).2⟩
  have hlo (k : I) := all_large_low_class_vanishing hFord hM (hk k) rfl (hg k) (hg1 k)
    (show 0 < 1/(L : ℝ) by positivity) (hgap k)
    (by norm_num : (0 : ℝ) < 1/200) (by norm_num) (by norm_num : (0 : ℝ) < 1/1000) hη
  have hhi (k : I) := all_large_high_class_vanishing hFord hM (hk k) rfl (hg k) (hg1 k)
    (show 0 < 1/(L : ℝ) by positivity) (hgap k)
    (by norm_num : (0 : ℝ) < 1/200) (by norm_num) (by norm_num : (0 : ℝ) < 1/1000) hη
  choose tlo htlo hlo using hlo
  choose thi hthi hhi using hhi
  obtain ⟨θ,hθ,hθle⟩ := finite_positive_bound (univ : Finset I)
    (fun k => min (tlo k) (thi k)) (fun k _ => lt_min (htlo k) (hthi k))
  obtain ⟨τ,hτ,hτbound,hτsampling,hsmall,hloss⟩ :=
    exists_common_multiplicity_tolerance hL (lt_min hcap hθ)
  have hτlo (k : I) : τ ≤ tlo k :=
    hτbound.trans ((min_le_right _ _).trans ((hθle k (mem_univ k)).trans (min_le_left _ _)))
  have hτhi (k : I) : τ ≤ thi k :=
    hτbound.trans ((min_le_right _ _).trans ((hθle k (mem_univ k)).trans (min_le_right _ _)))
  choose Elo hElolim hElobound using fun k => hlo k τ hτ (hτlo k) hloss
  choose Ehi hEhilim hEhibound using fun k => hhi k τ hτ (hτhi k) hloss
  let E := fun k B => if hk : k ∈ Icc 4 L then |Elo ⟨k,hk⟩ B|+|Ehi ⟨k,hk⟩ B| else 0
  refine ⟨τ,hτ,hτbound.trans (min_le_left _ _),hτsampling,hsmall,E,?_,?_,?_⟩
  · intro k B
    dsimp only [E]
    split_ifs <;> positivity
  · intro k hk
    have hh := (hElolim ⟨k,hk⟩).abs.add (hEhilim ⟨k,hk⟩).abs
    simpa only [E,dite_eq_left hk,abs_zero,add_zero] using hh
  · have hboth : ∀ᶠ B : ℕ in atTop, ∀ k : I,
        (∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeLowPairCount B L k.val j τ C (1/(L : ℝ)) A D V ≤ Elo k B) ∧
        (∀ (C : ℝ) (A D V : Finset ℕ) (j : ℕ),
          A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B → V ⊆ auxiliaryPrimes B →
          RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D → RegularPrimeSet B L τ C V →
          (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
          0 < j → j ≤ auxiliaryCutoff B → (j : ℝ) ≤ (B : ℝ)^2 →
          η*(B : ℝ)^(32/100 : ℝ) ≤ j →
          tiltedAllLargeHighPairCount B L k.val j τ C (1/(L : ℝ)) A D V ≤ Ehi k B) :=
      eventually_all.mpr (fun k => (hElobound k).and (hEhibound k))
    filter_upwards [hboth] with B hB
    intro k hk C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    have hlo := (hB ⟨k,hk⟩).1 C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    have hhi := (hB ⟨k,hk⟩).2 C A D V j hA hD hV hAr hDr hVr hsize hj hcut hjB hjlow
    dsimp only [E]
    rw [dite_eq_left hk]
    constructor
    · exact hlo.trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))
    · exact hhi.trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _)))

end JointDickman

end OAI
end

section
-- module Solutions.OAIQ083_JD.JointDickman_Amplification_CandidateMultiplicityBound
attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
attribute [-simp] _root_.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.ContinuousLinearEquiv.coe_toLinearEquiv_symm _root_.Erdos970.Function.support_abs _root_.Erdos970.Function.support_ofReal _root_.Erdos970.nnnorm_circle_smul _root_.Erdos970.nnnorm_eq_of_mem_circle _root_.Erdos970.preimage_equivRealProdCLM_reProdIm _root_.F_add _root_.F_mul _root_.F_neg _root_.F_sub _root_.OAI.LargePrimeGaps.append_ker_left _root_.OAI.LargePrimeGaps.append_ker_right _root_.deriv_ofReal _root_.nnnorm_circle_smul _root_.nnnorm_eq_of_mem_circle _root_.preimage_equivRealProdCLM_reProdIm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform expected multiplicity of actual coefficient representations -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

/-- The entire representation count, including both large-addition
orientations, is at most twice the small-addition power under the two
first-representation remainder laws. Only Ford's sieve and Mertens enter. -/
theorem tiltedCandidatePairCount_bound_jd_oai
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 10000 ≤ L) {η cap : ℝ} (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ᶠ B : ℕ in atTop, ∀ (T H M : ℕ) (C : ℝ) (i t : Fin M) (A D : Finset ℕ),
        (T : ℝ) ≤ Real.exp B →
        A ⊆ auxiliaryPrimes B → D ⊆ auxiliaryPrimes B →
        RegularPrimeSet B L τ C A → RegularPrimeSet B L τ C D →
        (∏ p ∈ A, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        (∏ p ∈ D, p : ℕ) ≤ Real.exp ((16/5 : ℝ)*B) →
        0 < t.val-i.val → t.val-i.val ≤ auxiliaryCutoff B →
        ((t.val-i.val : ℕ) : ℝ) ≤ (B : ℝ)^2 →
        η*(B : ℝ)^(32/100 : ℝ) ≤ ((t.val-i.val : ℕ) : ℝ) →
        tiltedCandidatePairCount B L T H τ C i t A D ≤ 2*(B : ℝ)^(8/1000 : ℝ) := by
  obtain ⟨τ,hτ,hτcap,hτsampling,hsmall,E,hEnn,hElim,hbound⟩ :=
    exists_grid_multiplicity_bounds hFord hM hL hη hcap
  let Etot := fun B => 2*∑ k ∈ Icc 4 L, E k B
  have hEtot : Tendsto Etot atTop (𝓝 0) := by
    have hh := (tendsto_finsetSum (Icc 4 L) hElim).const_mul 2
    simpa only [sum_const_zero,mul_zero] using hh
  have hL3 : 3 ≤ L := by omega
  refine ⟨τ,hτ,hτcap,hτsampling,?_⟩
  filter_upwards [hbound,smallCandidateAlternatives_power_bound hL3 hτ hτsampling hsmall.le,
    hEtot.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),eventually_ge_atTop 5]
    with B hB hsmallB hE hB5
  intro T H M C i t A D hT hA hD hAr hDr hAsize hDsize hj hcut hjB hjlow
  have hp : (1 : ℝ) ≤ (B : ℝ)^(8/1000 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ B)) (by norm_num)
  calc
    _ ≤ (B : ℝ)^(8/1000 : ℝ)+
        ∑ k ∈ Icc 4 L,
          (regularTiltAverage B L τ C D (fun V =>
            tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) +
          regularTiltAverage B L τ C A (fun U =>
            tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U)) :=
      tiltedCandidatePairCount_le_classes hB5 hL3 hT i t A D hA hD
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun U V hUr hVr => hsmallB T H M C i t A D U V hAr hDr hUr hVr)
    _ ≤ (B : ℝ)^(8/1000 : ℝ)+Etot B := by
      apply add_le_add le_rfl
      dsimp only [Etot]
      rw [mul_sum]
      apply sum_le_sum
      intro k hk
      have hlo : regularTiltAverage B L τ C D (fun V =>
          tiltedAllLargeLowPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) A D V) ≤ E k B := by
        apply regularTiltAverage_bound (hEnn k B)
        intro V hV hVr
        exact (hB k hk C A D V (t.val-i.val) hA hD
          ((mem_powerset.mp hV).trans sdiff_subset) hAr hDr hVr hAsize hj hcut hjB hjlow).1
      have hhi : regularTiltAverage B L τ C A (fun U =>
          tiltedAllLargeHighPairCount B L k (t.val-i.val) τ C (1/(L : ℝ)) D A U) ≤ E k B := by
        apply regularTiltAverage_bound (hEnn k B)
        intro U hU hUr
        exact (hB k hk C D A U (t.val-i.val) hD hA
          ((mem_powerset.mp hU).trans sdiff_subset) hDr hAr hUr hDsize hj hcut hjB hjlow).2
      linarith
    _ ≤ 2*(B : ℝ)^(8/1000 : ℝ) := by linarith

end JointDickman

end OAI
end

theorem solution : type_of% @OAI.JointDickman.tiltedCandidatePairCount_bound_jd_oai := @OAI.JointDickman.tiltedCandidatePairCount_bound_jd_oai
