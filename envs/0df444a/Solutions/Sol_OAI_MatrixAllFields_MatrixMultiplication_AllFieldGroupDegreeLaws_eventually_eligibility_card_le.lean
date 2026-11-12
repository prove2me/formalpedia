-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:14.94435+00:00
-- url     : https://prove2.me/submissions/eb3b1ea9-2187-4658-9789-d1b7c648c2e3

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldActiveCapacity_workCapacity_first
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupAmbientDegree_localAllowed_entropy_le

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

theorem conditionalWords_card_pos (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    0 < Fintype.card (ConditionalWords w counts) := by
  rw [conditionalWords_card w counts h]
  exact Finset.prod_pos fun a _ => Nat.multinomial_pos Finset.univ (counts a)

theorem conditionalWords_nonempty (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Nonempty (ConditionalWords w counts) :=
  Fintype.card_pos_iff.mp (conditionalWords_card_pos w counts h)

theorem conditionalWords_nonempty_iff (w : I → A) (counts : A → B → ℕ) :
    Nonempty (ConditionalWords w counts) ↔
      ∀ a, wordPopulation w a = ∑ b, counts a b := by
  constructor
  · rintro ⟨r⟩ a
    calc
      wordPopulation w a =
          ∑ b, wordPopulation (fun i : {i // w i = a} => r.val i.val) b :=
        (wordPopulation_sum _).symm
      _ = ∑ b, counts a b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [wordPopulation_fiber, r.property]
  · exact conditionalWords_nonempty w counts

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

end MatrixMultiplication.Foundation





noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

end MatrixMultiplication.Foundation






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointTypeCounts
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section CoarseFibers

variable {I A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [Fintype B] in
private theorem pushforwardCounts_eq_sum (counts : A → ℕ) (f : A → B) (b : B) :
    pushforwardCounts counts f b = ∑ a, if f a = b then counts a else 0 := by
  classical
  dsimp only [pushforwardCounts]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, if_true, ite_false, if_false]

theorem fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (FixedCoarseWords counts f k) =
      ∏ b, Nat.multinomial Finset.univ (fun a => if f a = b then counts a else 0) := by
  rw [Fintype.card_congr (fixedCoarseWordsEquiv counts f k)]
  apply conditionalWords_card
  intro b
  rw [← pushforwardCounts_eq_sum]
  exact hk b

theorem fixedCoarseWords_card_pos (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    0 < Fintype.card (FixedCoarseWords counts f k) := by
  rw [fixedCoarseWords_card counts f k hk]
  exact Finset.prod_pos fun b _ => Nat.multinomial_pos _ _

theorem exactWords_card_eq_coarse_mul_fixed (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (pushforwardCounts counts f)) *
        Fintype.card (FixedCoarseWords counts f k) := by
  classical
  have hgraph (b : B) (a : A) :
      pushforwardCounts counts (fun a => (f a, a)) (b, a) =
        if f a = b then counts a else 0 := by
    simp [pushforwardCounts, Prod.mk.injEq, and_comm, ite_and]
  have hinj : Function.Injective (fun a : A => (f a, a)) :=
    fun _ _ h => congrArg Prod.snd h
  have hmain := multinomial_prod_counts
    (pushforwardCounts counts (fun a => (f a, a)))
  rw [multinomial_pushforwardCounts_of_injective counts _ hinj] at hmain
  simp_rw [pushforwardCounts_sum_pair, hgraph] at hmain
  rw [exactWords_card, exactWords_card, fixedCoarseWords_card counts f k hk]
  exact hmain

theorem log_fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) := by
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ))
    (exactWords_card_eq_coarse_mul_fixed counts f k hk)
  rw [Nat.cast_mul, Real.log_mul] at h
  · simpa only [exactWords_card] using (eq_sub_iff_add_eq.mpr (by linarith :
      Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) +
        Real.log (Fintype.card (ExactWords (pushforwardCounts counts f)) : ℝ) =
          Real.log (Fintype.card (ExactWords counts) : ℝ)))
  · exact_mod_cast (Nat.ne_of_gt (exactWords_card_pos (pushforwardCounts counts f)))
  · exact_mod_cast (Nat.ne_of_gt (fixedCoarseWords_card_pos counts f k hk))

theorem abs_log_fixedCoarseWords_card_sub_entropy_le
    (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    |Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) -
      (∑ a, counts a : ℕ) *
        (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) -
          finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
            (∑ a, counts a : ℕ)))| ≤
      ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hA := abs_log_multinomial_sub_entropy_le counts
  have hB := abs_log_multinomial_sub_entropy_le (pushforwardCounts counts f)
  rw [pushforwardCounts_sum] at hB
  rw [log_fixedCoarseWords_card counts f k hk]
  have h := (abs_sub
    (Real.log (Nat.multinomial Finset.univ counts : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))
    (Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
          (∑ a, counts a : ℕ)))).trans (add_le_add hA hB)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> ring)

theorem card_allowed_over_coarse_le
    (f : A → B) (k : I → B) (allowed : (I → A) → Prop) [DecidablePred allowed]
    (H : ℝ)
    (hcoarse : ∀ w, allowed w → ∀ i, f (w i) = k i)
    (hentropy : ∀ w, allowed w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H) :
    (Fintype.card {w : I → A // allowed w} : ℝ) ≤
      ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) *
          (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
          ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  let S := {w : I → A // allowed w}
  let T := A → Fin (Fintype.card I + 1)
  let E : ℝ := (Fintype.card I : ℝ) *
    (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
    ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
      (1 + Real.log (Fintype.card I + 1 : ℕ))
  let profile : S → T := fun w a =>
    ⟨wordPopulation w.val a,
      Nat.lt_succ_of_le (Fintype.card_subtype_le (fun i : I => w.val i = a))⟩
  have hcap (p : T) :
      (Fintype.card {w : S // profile w = p} : ℝ) ≤ Real.exp E := by
    let Fiber := {w : S // profile w = p}
    by_cases hn : Nonempty Fiber
    · let : Nonempty Fiber := hn
      let w : Fiber := Classical.choice hn
      let counts : A → ℕ := wordPopulation w.val.val
      let encode : Fiber → FixedCoarseWords counts f k := fun v =>
        ⟨v.val.val, ⟨fun a => by
          change wordPopulation v.val.val a = wordPopulation w.val.val a
          exact congrArg Fin.val (congrFun (v.property.trans w.property.symm) a),
          hcoarse v.val.val v.val.property⟩⟩
      have hinj : Function.Injective encode := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : FixedCoarseWords counts f k => z.val) h
      have hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b := by
        have hh := (conditionalWords_nonempty_iff k
          (fun b a => if f a = b then counts a else 0)).mp
            ⟨fixedCoarseWordsEquiv counts f k (encode w)⟩
        intro b
        rw [pushforwardCounts_eq_sum]
        exact hh b
      have htotal : (∑ a, counts a) = Fintype.card I := wordPopulation_sum w.val.val
      have hbound := (abs_le.mp
        (abs_log_fixedCoarseWords_card_sub_entropy_le counts f k hk)).2
      rw [htotal] at hbound
      simp_rw [← hk] at hbound
      have hw := hentropy w.val.val w.val.property
      have hmain := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hw
          (finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)))
        (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I)
      have hfixed : Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) ≤ E := by
        dsimp only [E]
        change (Fintype.card I : ℝ) *
          (finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) -
            finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) ≤
          _ at hmain
        linarith
      have hpos : (0 : ℝ) < Fintype.card Fiber := Nat.cast_pos.mpr Fintype.card_pos
      have hlog : Real.log (Fintype.card Fiber : ℝ) ≤ E :=
        (Real.log_le_log hpos
          (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj))).trans hfixed
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
    · let : IsEmpty Fiber := ⟨fun w => hn ⟨w⟩⟩
      change (Fintype.card Fiber : ℝ) ≤ Real.exp E
      simpa only [Fintype.card_of_isEmpty, Nat.cast_zero] using (Real.exp_pos E).le
  have hdecomp : Fintype.card S = ∑ p : T, Fintype.card {w : S // profile w = p} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv profile)).symm
  calc
    (Fintype.card S : ℝ) =
        ∑ p : T, (Fintype.card {w : S // profile w = p} : ℝ) := by
      exact_mod_cast hdecomp
    _ ≤ ∑ _p : T, Real.exp E := Finset.sum_le_sum fun p _ => hcap p
    _ = (Fintype.card T : ℝ) * Real.exp E := by simp
    _ = _ := by simp [T, E]

end CoarseFibers

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMarginalSupport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientDegree

open MatrixMultiplication.Foundation JointPopulation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem localWord_injective : Function.Injective (localWord counts) := by
  intro t u he
  apply Prod.ext
  · funext p
    exact congrArg (fun w => (w p.1 p.2).1) he
  · apply Prod.ext
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.1) he
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.2) he

theorem localAllowed_of_mem_ambient (sum : H → ℕ)
    (t : JointCoarseHashing.Triple (Position counts))
    (ht : t ∈ ambientSet counts sum) (h : H) :
    localAllowed counts sum h (localWord counts t h) := by
  obtain ⟨hs, hm⟩ := (Finset.mem_filter.mp ht).2
  exact ⟨fun i => hs ⟨h, i⟩, fun s a => hm h s a⟩

omit [Fintype H] [DecidableEq H] in
theorem classBound_eq_exp (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (h : H) (entropyCap : ℝ) :
    classBound counts s e h entropyCap = Real.exp (classExponent counts s e h entropyCap) := by
  unfold classBound classExponent
  conv_rhs => rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_comm _ _

omit [Fintype H] [DecidableEq H] in
theorem classExponent_target_eq (s : Fin 3) (e : Target counts) (h : H)
    (entropyCap : ℝ) :
    classExponent counts s (triple counts e) h entropyCap =
      classExponent counts s (triple counts (canonicalTarget counts)) h entropyCap := by
  simp_rw [classExponent, marginal_population_eq counts e (canonicalTarget counts)]

theorem sharedAmbient_card_le (sum : H → ℕ) (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h) :
    ((sharedAmbient counts sum s e).card : ℝ) ≤
      ∏ h, classBound counts s e h (entropyCap h) := by
  classical
  let Allowed := fun h (w : Positions counts h → Shape) =>
    localAllowed counts sum h w ∧ ∀ i, shapeSide s (w i) = sideWord counts s e h i
  let Local := fun h => {w : Positions counts h → Shape // Allowed h w}
  let encode : {t // t ∈ sharedAmbient counts sum s e} → ∀ h, Local h := fun t h =>
    ⟨localWord counts t.val h, localAllowed_of_mem_ambient counts sum t.val
      (Finset.mem_filter.mp t.property).1 h,
      fun i => congrFun ((Finset.mem_filter.mp t.property).2 h) i⟩
  have hinj : Function.Injective encode := by
    intro t u he
    apply Subtype.ext
    apply localWord_injective counts
    funext h
    exact congrArg Subtype.val (congrFun he h)
  have hcard : (sharedAmbient counts sum s e).card ≤ ∏ h, Fintype.card (Local h) := by
    simpa only [Fintype.card_coe, Fintype.card_pi] using
      Fintype.card_le_of_injective encode hinj
  have hlocal (h : H) : (Fintype.card (Local h) : ℝ) ≤
      classBound counts s e h (entropyCap h) := by
    exact JointTypeCounts.card_allowed_over_coarse_le (shapeSide s)
      (sideWord counts s e h) (Allowed h) (entropyCap h)
      (fun w hw => hw.2) (fun w hw => hentropy h w hw.1)
  calc
    ((sharedAmbient counts sum s e).card : ℝ) ≤
        ∏ h, (Fintype.card (Local h) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun history _ => hlocal history)

end MatrixMultiplication.JointAmbientDegree






namespace MatrixMultiplication.AllFieldGroupDegrees

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData JointPopulation JointCanonicalization
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem tripleSide_eq_sideWord (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (t : JointCoarseHashing.Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s t ⟨h, i⟩ = sideWord (Counts (K := K) (tick := tick) allocation m sigma) s t h i := by
  fin_cases s <;> rfl

theorem eligibility_card_le_sharedAmbient (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    ((data allocation m ε sigma).eligibilityCompetitors e).card ≤
      (JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
        (fun h => 2 * activeHalfLength h.val) (sigma 0)
        (triple (Counts (K := K) (tick := tick) allocation m sigma) e)).card := by
  let a := JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
    (fun h => 2 * activeHalfLength h.val) (sigma 0)
    (triple (Counts (K := K) (tick := tick) allocation m sigma) e)
  have hs : (data allocation m ε sigma).eligibilityCompetitors e ⊆
      a.image (reorder sigma) := by
    intro f hf
    obtain ⟨ha, _, hx⟩ :=
      ((data allocation m ε sigma).mem_eligibilityCompetitors e f).1 hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, rfl⟩
    intro h
    funext i
    have hh := congrFun hx ⟨h, i⟩
    change tripleSide (sigma 0) t ⟨h, i⟩ =
      tripleSide (sigma 0) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ at hh
    simpa only [tripleSide_eq_sideWord] using hh
  exact (Finset.card_le_card hs).trans Finset.card_image_le

end MatrixMultiplication.AllFieldGroupDegrees






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientRateLimit
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientRateLimit

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

theorem tendsto_log_succ_div_nat_of_ratio {n : ℕ → ℕ} {mass : ℝ}
    (hsize : Tendsto (fun N => (n N : ℝ) / (N : ℝ)) atTop (𝓝 mass)) :
    Tendsto (fun N => Real.log (n N + 1 : ℕ) / (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := |mass| + 2
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hmC : mass < C := by dsimp [C] <;> linarith [le_abs_self mass]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log (C + 1) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ =>
      (Real.log (C + 1) + Real.log (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hc.add hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n N))))
        (Nat.cast_nonneg _)
  · filter_upwards [(tendsto_order.1 hsize).2 C hmC,
      eventually_ge_atTop (1 : ℕ)] with N hn hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
    have hsizeN := (div_lt_iff₀ hNp).mp hn
    have hbound : (n N + 1 : ℕ) ≤ (C + 1) * (N : ℝ) := by
      push_cast
      nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n N + 1 : ℕ)) hbound
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) hNp.ne'] at hl
    exact div_le_div_of_nonneg_right hl hNp.le

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem tendsto_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3) (h : H)
    (cap : ℕ → ℝ) (mass capRate marginalRate : ℝ)
    (hsize : Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 mass))
    (hcap : Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N)
      atTop (𝓝 capRate))
    (hmarginal : Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 marginalRate)) :
    Tendsto (fun N =>
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N) /
        (N : ℝ)) atTop (𝓝 (capRate - marginalRate)) := by
  let A : ℝ := (Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2
  have hlog := tendsto_log_succ_div_nat_of_ratio hsize
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal := (hcap.sub hmarginal).add
    (((hinv.add hlog).const_mul A).add (hlog.const_mul (Fintype.card Shape : ℝ)))
  simp only [add_zero, mul_zero] at htotal
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  dsimp only [classExponent, A, Positions]
  simp only [Fintype.card_fin, div_eq_mul_inv]
  ring

omit [DecidableEq H] in
theorem tendsto_sum_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3)
    (cap : ℕ → H → ℝ) (mass capRate marginalRate : H → ℝ)
    (hsize : ∀ h, Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 (mass h)))
    (hcap : ∀ h, Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N h)
      atTop (𝓝 (capRate h)))
    (hmarginal : ∀ h, Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 (marginalRate h))) :
    Tendsto (fun N => (∑ h,
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) /
        (N : ℝ)) atTop (𝓝 (∑ h, (capRate h - marginalRate h))) := by
  have hs := tendsto_finsetSum Finset.univ (fun h _ =>
    tendsto_classExponent_div_nat counts s h (fun N => cap N h)
      (mass h) (capRate h) (marginalRate h) (hsize h) (hcap h) (hmarginal h))
  simpa only [Finset.sum_div] using hs

end MatrixMultiplication.JointAmbientRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem tendsto_total_div_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ)) atTop (𝓝 mass) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum, hp, mul_one] using h

theorem finiteEntropy_scalar {A : Type*} [Fintype A]
    (p : A → ℝ) (mass : ℝ) (hp : ∑ a, p a = 1) :
    finiteEntropy (fun a => mass * p a) = entropyTerm mass + mass * finiteEntropy p := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, one_mul]

theorem weighted_empirical_entropy_eq {A : Type*} [Fintype A]
    (counts : A → ℕ) (scale : ℝ) :
    ((∑ a, counts a : ℕ) / scale) *
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
        finiteEntropy (fun a => (counts a : ℝ) / scale) -
          entropyTerm ((∑ a, counts a : ℕ) / scale) := by
  by_cases hzero : (∑ a, counts a) = 0
  · have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, finiteEntropy]
  have hD : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
  have hsum : (∑ a, (counts a : ℝ) / (∑ a, counts a : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hD]
  have hfac (a : A) : (counts a : ℝ) / scale =
      ((∑ a, counts a : ℕ) / scale) * ((counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    rw [div_mul_div_comm,
      mul_comm ((∑ a, counts a : ℕ) : ℝ) (counts a : ℝ), mul_div_mul_right _ _ hD]
  have h := finiteEntropy_scalar
    (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))
    ((∑ a, counts a : ℕ) / scale) hsum
  simp_rw [← hfac] at h
  linarith

theorem tendsto_weighted_empirical_entropy_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => ((∑ a, counts n a : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a => (counts n a : ℝ) / (∑ a, counts n a : ℕ)))
      atTop (𝓝 (mass * finiteEntropy p)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (tendsto_finiteEntropy_of_tendsto hcounts).sub (tendsto_entropyTerm htotal)
  rw [finiteEntropy_scalar p mass hp, add_sub_cancel_left] at h
  simpa only [weighted_empirical_entropy_eq] using h

theorem sideCounts_total (counts : Shape → ℕ) (s : Fin 3) :
    (∑ a, sideCounts counts s a) = ∑ u, counts u := by
  unfold sideCounts
  rw [Finset.sum_comm]
  simp

theorem sideMass_total (p : Shape → ℝ) (s : Fin 3) :
    (∑ a, sideMass p s a) = ∑ u, p u := by
  unfold sideMass
  rw [Finset.sum_comm]
  simp

theorem tendsto_sideCounts_div_of_coordinate_rates
    (counts : ℕ → Shape → ℕ) (mass : ℝ) (p : Shape → ℝ)
    (hcounts : ∀ u, Tendsto (fun n : ℕ => (counts n u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p u))) (s : Fin 3) (a : Fin 17) :
    Tendsto (fun n : ℕ => (sideCounts (counts n) s a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * sideMass p s a)) := by
  have hfun (n : ℕ) : (sideCounts (counts n) s a : ℝ) / (n : ℝ) =
      ∑ u, if shapeSide s u = a then (counts n u : ℝ) / (n : ℝ) else 0 := by
    unfold sideCounts
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : shapeSide s u = a <;> simp [h]
  simp_rw [hfun]
  rw [sideMass, Finset.mul_sum]
  apply tendsto_finsetSum
  intro u _
  by_cases h : shapeSide s u = a
  · simpa only [h, ite_true, if_true] using hcounts u
  · simp only [h, ite_false, if_false, mul_zero]
    exact tendsto_const_nhds

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem target_side_population (counts : H → Shape → ℕ)
    (e : Target counts) (h : H) (s : Fin 3) (a : Fin 17) :
    wordPopulation (sideWord counts s (triple counts e) h) a = sideCounts (counts h) s a := by
  let w : JointTypeCounts.FixedCoarseWords (counts h) (shapeSide s)
      (sideWord counts s (triple counts e) h) :=
    ⟨(e h).val, (e h).property, fun _ => rfl⟩
  exact ((conditionalWords_nonempty_iff
    (sideWord counts s (triple counts e) h)
    (fun b u => if shapeSide s u = b then counts h u else 0)).mp
      ⟨JointTypeCounts.fixedCoarseWordsEquiv _ _ _ w⟩) a

omit [Fintype H] [DecidableEq H] in
theorem tendsto_weighted_target_side_entropy
    (counts : ℕ → H → Shape → ℕ) (e : ∀ n, Target (counts n))
    (mass : H → ℝ) (p : H → Shape → ℝ) (hp : ∀ h, ∑ u, p h u = 1)
    (hcounts : ∀ h u, Tendsto (fun n : ℕ => (counts n h u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h u))) (h : H) (s : Fin 3) :
    Tendsto (fun n : ℕ => ((∑ u, counts n h u : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a =>
        (wordPopulation (sideWord (counts n) s (triple (counts n) (e n)) h) a : ℝ) /
          (∑ u, counts n h u : ℕ)))
      atTop (𝓝 (mass h * finiteEntropy (sideMass (p h) s))) := by
  have hside := tendsto_weighted_empirical_entropy_of_coordinate_rates
    (fun n => sideCounts (counts n h) s) (mass h) (sideMass (p h) s)
    ((sideMass_total (p h) s).trans (hp h))
    (tendsto_sideCounts_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hcounts h) s)
  simpa only [target_side_population, sideCounts_total] using hside

end MatrixMultiplication.JointPopulationRates






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem branchPopulation_cast_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℚ) =
      (population allocation dilation (w.1.source, w.2) : ℚ) *
        branchProbability w.1 b := by
  rcases w with ⟨w, phi⟩
  cases w <;>
    simp only [branchPopulation, Work.child, Work.source, population_cast,
      amount, canonicalAmount, aAmount, bAmount, cAmount, branchProbability] <;> ring

theorem branchPopulation_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (branchLaw w.1).mass b := by
  rw [branchLaw_mass]
  exact_mod_cast branchPopulation_cast_rat allocation dilation w b

theorem jointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (placedLaw w).mass u := by
  simp only [jointCounts, shapeCounts, Nat.cast_sum, placedLaw_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : branchShape w b = u
  · simp only [hb, ite_true, if_true, branchPopulation_cast, branchLaw_mass]
  · simp [hb]

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem jointCounts_source_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u) := by
  rw [jointCounts_cast, population_cast_real, mul_assoc]

theorem populationLength_dilation {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    populationLength (K := K) allocation dilation =
      dilation * populationLength (K := K) allocation 1 := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem jointCounts_dilation_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) / (dilation : ℝ) =
      ((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast, populationLength_dilation, Nat.cast_mul]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  field_simp [hd']

theorem jointCounts_dilation_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_dilation_ratio allocation hd w u).symm

theorem orderCounts_dilation_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
        (orderLaw h).mass u)) :=
  jointCounts_dilation_rate allocation h.val.val u

end MatrixMultiplication.AllFieldActiveLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem order_first_capacity {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) :
    workCapacity h.val.val.1 0 = finiteEntropy
      (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)) := by
  have hh := workCapacity_first h.val.val
  rw [h.property] at hh
  exact hh

end MatrixMultiplication.AllFieldActiveCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAmbientDegree
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem tendsto_firstExponent (allocation : Allocation) (sigma : Placement) :
    Tendsto (fun m : ℕ => (∑ h : ActiveOrder K tick sigma,
      classExponent (orderCounts allocation m) (sigma 0)
        (triple (orderCounts allocation m) (canonicalTarget (orderCounts allocation m))) h
        (finiteEntropy (orderLaw h).mass)) / (m : ℝ)) atTop
      (𝓝 (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)) := by
  have hsize (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_total_div_of_coordinate_rates
      (fun m => orderCounts allocation m h)
      ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (orderLaw h).mass (orderLaw h).total (orderCounts_dilation_rate allocation h)
  have hside (h : ActiveOrder K tick sigma) :=
    JointPopulationRates.tendsto_weighted_target_side_entropy
      (fun m => orderCounts allocation m)
      (fun m => canonicalTarget (orderCounts allocation m))
      (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
      (fun h => (orderLaw h).mass) (fun h => (orderLaw h).total)
      (orderCounts_dilation_rate allocation) h (sigma 0)
  have hr := JointAmbientRateLimit.tendsto_sum_classExponent_div_nat
    (fun m => orderCounts allocation m) (sigma 0)
    (fun _ h => finiteEntropy (orderLaw h).mass)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (orderLaw h).mass)
    (fun h => ((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
      finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)))
    hsize (fun h => (hsize h).mul_const (finiteEntropy (orderLaw h).mass))
    (fun h => by simpa only [Positions, Fintype.card_fin] using hside h)
  simpa only [orderNativeDegree, order_first_capacity, mul_sub] using hr

theorem eventually_sharedAmbient_first_card_le (allocation : Allocation)
    (sigma : Placement) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ e : Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m),
      ((sharedAmbient (orderCounts allocation m) orderTotal (sigma 0)
        (triple (orderCounts allocation m) e)).card : ℝ) ≤
      Real.exp ((m : ℝ) *
        (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)) := by
  filter_upwards [(tendsto_order.1
      (tendsto_firstExponent (K := K) (tick := tick) allocation sigma)).2
      (orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + ε)
      (lt_add_of_pos_right _ hε), eventually_gt_atTop (0 : ℕ)] with m hm hmp
  intro e
  have hmr : (0 : ℝ) < m := by exact_mod_cast hmp
  have hb := sharedAmbient_card_le (orderCounts allocation m) orderTotal (sigma 0)
    (triple (orderCounts allocation m) e) (fun h => finiteEntropy (orderLaw h).mass)
    (fun h word hw => localAllowed_entropy_le allocation m h word hw)
  apply hb.trans
  simp_rw [classBound_eq_exp]
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  simp_rw [classExponent_target_eq]
  simpa only [mul_comm] using (div_le_iff₀ hmr).mp hm.le

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupCountRate
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeLaws

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem eventually_eligibility_card_le_oai (allocation : Allocation) (sigma : Placement)
    (width : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
        Real.exp ((m : ℝ) *
          (AllFieldActiveCapacity.orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + δ)) := by
  filter_upwards [AllFieldGroupAmbientDegree.eventually_sharedAmbient_first_card_le
    (K := K) (tick := tick) allocation sigma hδ] with m hm
  intro e
  exact (Nat.cast_le.mpr (eligibility_card_le_sharedAmbient allocation m width sigma e)).trans (hm e)

end MatrixMultiplication.AllFieldGroupDegreeLaws

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le_oai
