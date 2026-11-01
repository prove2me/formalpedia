-- Prove2me | solution 1 for OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:34:36.213717+00:00
-- url     : https://prove2.me/submissions/ad8a01c3-f96e-4544-90a7-8f0bf18db58e

import Mathlib
import Definitions.Def_OAIQ053K037
import Definitions.Def_OAIQ053K049
import Theorems.Thm_OAI_MetricKMedian_CountStatistic_variance_bound_s53
import Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_count_variance_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Binary_BooleanMonomials
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem flag_zero_or_one (q : Fin n → Bool) (i : Fin n) : flag q i=0 ∨ flag q i=1 := by
  unfold flag
  split_ifs <;> simp

theorem flag_mul_self (q : Fin n → Bool) (i : Fin n) : flag q i*flag q i=flag q i := by
  rcases flag_zero_or_one q i with h | h <;> simp [h]

theorem flag_mul_product (q : Fin n → Bool) (S : Finset (Fin n)) (i : Fin n) (hi : i∈S) :
    flag q i*(∏ j∈S,flag q j)=∏ j∈S,flag q j := by
  conv_rhs => rw [← mul_prod_erase S (flag q) hi]
  rw [← mul_prod_erase S (flag q) hi,← mul_assoc,flag_mul_self]

theorem product_union (q : Fin n → Bool) (S T : Finset (Fin n)) :
    (∏ i∈S,flag q i)*(∏ i∈T,flag q i)=∏ i∈S∪T,flag q i := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,mul_assoc,ih,insert_union]
    by_cases hit : i∈T
    · have hum : i∈S∪T := mem_union_right S hit
      rw [insert_eq_of_mem hum]
      exact flag_mul_product q _ i hum
    · rw [prod_insert (by simp only [mem_union,not_or]; exact ⟨hi,hit⟩)]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem prob_congr (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω ↔ F ω) : μ.prob E = μ.prob F := by
  exact le_antisymm (μ.prob_mono fun ω => (hEF ω).mp) (μ.prob_mono fun ω => (hEF ω).mpr)

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliBatches
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem bernoulli_expect_prod (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (f : I → Bool → ℝ) :
    (bernoulli p hp hp1).expect (fun ω => ∏ i, f i (ω i)) =
       ∏ i, ((1-p i)*f i false+p i*f i true) := by
  unfold expect bernoulli
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => coinWeight (p i) b * f i b)]
  simp only [Fintype.sum_bool, coinWeight_true, coinWeight_false]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem bernoulli_cylinder (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset I) (c : I → Bool) :
    (bernoulli p hp hp1).prob (fun ω => ∀ i ∈ S, ω i = c i) =
      ∏ i ∈ S, coinWeight (p i) (c i) := by
  classical
  have hpoint : ∀ ω : I → Bool,
      (if ∀ i ∈ S, ω i = c i then (1:ℝ) else 0) =
      ∏ i, (if i ∈ S then if ω i = c i then (1:ℝ) else 0 else 1) := by
    intro ω
    by_cases h : ∀ i ∈ S, ω i = c i
    · rw [ite_eq_left h]
      symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S <;> simp [hi, h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i, hi, hne⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi, hne]
  unfold prob
  simp_rw [hpoint]
  rw [bernoulli_expect_prod p hp hp1 (fun i b => if i ∈ S then if b = c i then 1 else 0 else 1)]
  have hfactor : ∀ i,
      (1-p i)*(if i ∈ S then if false = c i then (1:ℝ) else 0 else 1)+
      p i*(if i ∈ S then if true = c i then (1:ℝ) else 0 else 1) =
      if i ∈ S then coinWeight (p i) (c i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · cases hc : c i <;> simp [hi]
    · simp [hi]
  simp_rw [hfactor]
  simp only [← Finset.prod_filter, Finset.filter_univ_mem]

theorem bernoulli_marginal (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : I) :
    (bernoulli p hp hp1).prob (fun ω => ω i = true) = p i := by
  simpa only [Finset.mem_singleton, forall_eq, Finset.prod_singleton, coinWeight_true] using
    bernoulli_cylinder p hp hp1 {i} (fun _ => true)

theorem bernoulli_pair (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i j : I} (hij : i ≠ j) :
    (bernoulli p hp hp1).prob (fun ω => ω i = true ∧ ω j = true) = p i*p j := by
  simpa [hij] using
    bernoulli_cylinder p hp hp1 {i,j} (fun _ => true)

end FiniteLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliPolynomial
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem polynomial_moment {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ d) :
    (run (d := d) p hp n).moment (polynomial S c)=∑ j, c j*∏ i ∈ S j, p i := by
  unfold SparseIntegerLaw.moment polynomial
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  have hh := subset_moment p hp (S j) (hS j)
  change (run (d := d) p hp n).moment (fun q => c j*∏ i∈S j,flag q i)=_
  rw [SparseIntegerLaw.moment_mul,hh]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
theorem chebyshev (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ |f ω-μ.expect f|) ≤ μ.variance f/t^2 := by
  classical
  have he : ∀ ω, (t ≤ |f ω-μ.expect f|) ↔ t^2 ≤ (f ω-μ.expect f)^2 := by
    intro ω
    exact (sq_le_sq₀ ht.le (abs_nonneg _)).symm.trans (by rw [sq_abs])
  rw [μ.prob_congr he]
  exact μ.prob_le_expect_div (fun ω => (f ω-μ.expect f)^2) (fun _ => sq_nonneg _) (sq_pos_of_pos ht)

omit [Fintype Ξ] in
                                                                                 
theorem prob_positive_le (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (hmean : μ.expect f ≤ -t) :
    μ.prob (fun ω => 0 < f ω) ≤ μ.variance f/t^2 := by
  classical
  apply (μ.prob_mono (E := fun ω => 0 < f ω)
    (F := fun ω => t ≤ |f ω-μ.expect f|) ?_).trans (μ.chebyshev f ht)
  intro ω hω
  have hh : t ≤ f ω-μ.expect f := by linarith only [hω, hmean]
  exact hh.trans (le_abs_self _)

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRealTransfer
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalSignedTerminal.point_state _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem product_indicator (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i)=(if ∀ i∈S, q i=true then (1:ℚ) else 0) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [prod_insert hi,ih]
    simp only [mem_insert,forall_eq_or_imp]
    cases hq : q i <;> simp [flag,hq]

theorem reference_subset (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Finset (Fin n)) :
    (reference p hp).expect (fun q => ((∏ i∈S,flag q i:ℚ):ℝ))=((∏ i∈S,p i:ℚ):ℝ) := by
  simp_rw [product_indicator]
  simp only [apply_ite,Rat.cast_one,Rat.cast_zero]
  change (reference p hp).prob (fun q => ∀ i∈S, q i=true)=_
  have hh := FiniteLaw.bernoulli_cylinder (fun i => (p i:ℝ))
      (fun i => by exact_mod_cast (hp i).1) (fun i => by exact_mod_cast (hp i).2) S (fun _ => true)
  simp only [FiniteLaw.coinWeight_true] at hh
  rw [Rat.cast_prod]
  apply Eq.trans ?_ hh
  unfold reference FiniteLaw.prob FiniteLaw.expect
  apply sum_congr rfl
  intro q _
  by_cases hq : ∀ i∈S, q i=true
  · simp only [ite_eq_left hq]
  · simp only [ite_eq_right hq]

theorem reference_polynomial {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) :
    (reference p hp).expect (fun q => (polynomial S c q:ℝ))=
      ((∑ j, c j*∏ i∈S j,p i:ℚ):ℝ) := by
  simp only [polynomial,Rat.cast_sum,Rat.cast_mul,FiniteLaw.expect_sum,
    FiniteLaw.expect_mul,reference_subset]

theorem real_polynomial {d m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ d) :
    (run (d := d) p hp n).real.expect (fun q => (polynomial S c q:ℝ))=
      (reference p hp).expect (fun q => (polynomial S c q:ℝ)) := by
  rw [SparseIntegerLaw.real_expect,polynomial_moment p hp S c hS,reference_polynomial]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_QuadraticCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.RationalLaw.real_expect _root_.OAI.MetricKMedian.SparseBernoulli.cast_flag _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem expectation (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : I → ℝ) (c : I → I → ℝ) (hdiag : ∀ i, c i i=0) :
    (FiniteLaw.bernoulli p hp0 hp1).expect (statistic b c)=
      (∑ i, b i*p i)+(1/2)*∑ i, ∑ j, c i j*p i*p j := by
  let μ := FiniteLaw.bernoulli p hp0 hp1
  have hm : ∀ i, μ.expect (fun ω => bit ω i)=p i := by
    intro i
    exact FiniteLaw.bernoulli_marginal p hp0 hp1 i
  have hpair : ∀ i j, μ.expect (fun ω => c i j*bit ω i*bit ω j)=c i j*p i*p j := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [hdiag, zero_mul, FiniteLaw.expect_const]
    · have hp := FiniteLaw.bernoulli_pair p hp0 hp1 hij
      have hpoint : ∀ ω, bit ω i*bit ω j=if ω i=true ∧ ω j=true then (1:ℝ) else 0 := by
        intro ω
        unfold bit
        cases ω i <;> cases ω j <;> norm_num
      simp only [mul_assoc, FiniteLaw.expect_mul]
      simp_rw [hpoint]
      change c i j*μ.prob (fun ω => ω i=true ∧ ω j=true)=_
      rw [hp]
  change μ.expect (statistic b c)=_
  unfold statistic
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_sum, FiniteLaw.expect_mul, hm, hpair]

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountVariance
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic

open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem expectation_bound (p a m : I → ℝ) (c : I → I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {P D L : ℝ} (hP : 0 ≤ P) (_hD : 1 ≤ D) (hpP : ∀ i, p i ≤ P)
    (_hm : ∀ i, 0 ≤ m i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i)
    (hlinear : (∑ i, (a i-m i)*p i) ≤ L) :
    (FiniteLaw.bernoulli p hp0 hp1).expect (statistic (fun i => a i-m i) c) ≤
      L+(1/2)*P^2*(D-1)*∑ i, m i := by
  rw [expectation p hp0 hp1 _ c hdiag]
  have hov : (∑ i, ∑ j, c i j*p i*p j) ≤ P^2*(D-1)*∑ i, m i := by
    calc
      _ ≤ ∑ i, ∑ j, P^2*c i j := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        have hprod := mul_le_mul (hpP i) (hpP j) (hp0 j) hP
        have hh := mul_le_mul_of_nonneg_left hprod (hc0 i j)
        nlinarith only [hh]
      _ = P^2*∑ i, ∑ j, c i j := by simp only [mul_sum]
      _ ≤ P^2*∑ i, (D-1)*m i :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hrow i)) (sq_nonneg _)
      _ = _ := by rw [← mul_sum]; ring
  nlinarith only [hlinear, hov]

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_CountTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem overlap_budget {p φ g A D M : ℝ}
    (hp : 0 ≤ p) (hg : 0 < g) (hA : 0 ≤ A) (hD : 1 ≤ D) (hM : 0 ≤ M)
    (hmass : M ≤ 2*A/g) (hsmall : 8*p*D ≤ φ*g) :
    (1/2)*(2*p)^2*(D-1)*M ≤ p*φ*A/2 := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hmg : M*g ≤ 2*A := (le_div_iff₀ hg).mp hmass
  have h1 := mul_le_mul_of_nonneg_left hmg (show 0 ≤ 2*p^2*D by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ p*A by positivity)
  have h3 : 0 ≤ p^2*M*g := by positivity
  apply (mul_le_mul_iff_right₀ hg).mp
  nlinarith only [h1,h2,h3]

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCountStatistic
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem countSets_card (a : Fin (n+n*n)) : (countSets a).card ≤ 2 := by
  unfold countSets
  cases finSumFinEquiv.symm a with
  | inl i => simp
  | inr ij => exact (card_union_le _ _).trans (by simp)

theorem count_polynomial (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (q : Fin n → Bool) :
    polynomial countSets (countCoefficients b c) q=
      (∑ i,b i*flag q i)+(1/2)*∑ i, ∑ j, c i j*flag q i*flag q j := by
  unfold polynomial
  rw [← (finSumFinEquiv : Fin n ⊕ Fin (n*n) ≃ Fin (n+n*n)).sum_comp]
  simp only [countSets,countCoefficients,Equiv.symm_apply_apply,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,prod_singleton]
  congr 1
  rw [← (finProdFinEquiv : Fin n × Fin n ≃ Fin (n*n)).sum_comp]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,← product_union,prod_singleton,mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem cast_count_polynomial (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) (q : Fin n → Bool) :
    (polynomial countSets (countCoefficients b c) q:ℝ)=
      CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)) q := by
  rw [count_polynomial]
  simp only [Rat.cast_add,Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_one,
    Rat.cast_ofNat,cast_flag,CountStatistic.statistic]

theorem count_mean (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
    (run (d := 4) p hp n).real.expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
      (reference p hp).expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ))) := by
  have he := real_polynomial (d := 4) p hp countSets (countCoefficients b c)
    (fun a => (countSets_card a).trans (by omega))
  simpa only [cast_count_polynomial] using he

theorem count_failure (p a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
    (hpP : ∀ i, (p i:ℝ) ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(p i:ℝ)) ≤
      -t-(1/2)*P^2*(D-1)*∑ i, (m i:ℝ)) :
    (run (d := 4) p hp n).real.prob (fun q => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) q) ≤
      (P*D^2*B*(∑ i, ((a i:ℝ)+(m i:ℝ))))/t^2 := by
  let pR := fun i => (p i:ℝ)
  let aR := fun i => (a i:ℝ)
  let mR := fun i => (m i:ℝ)
  let cR := fun i j => (c i j:ℝ)
  have hp0 : ∀ i, 0 ≤ pR i := fun i => by dsimp only [pR]; exact_mod_cast (hp i).1
  have hp1 : ∀ i, pR i ≤ 1 := fun i => by dsimp only [pR]; exact_mod_cast (hp i).2
  have haR : ∀ i, 0 ≤ aR i := fun i => by dsimp only [aR]; exact_mod_cast ha i
  have hmR : ∀ i, 0 ≤ mR i := fun i => by dsimp only [mR]; exact_mod_cast hm i
  have hcR : ∀ i j, cR i j=cR j i := fun i j => congrArg (fun z : ℚ => (z:ℝ)) (hc i j)
  have hdR : ∀ i, cR i i=0 := fun i => by dsimp only [cR]; exact_mod_cast hdiag i
  have hc0R : ∀ i j, 0 ≤ cR i j := fun i j => by dsimp only [cR]; exact_mod_cast hc0 i j
  have hmean := CountStatistic.expectation_bound pR aR mR cR hp0 hp1 hP hD hpP hmR hdR hc0R hrow hlinear
  have hvar := CountStatistic.variance_bound_s53 pR aR mR cR hp0 hp1 hD hP hpP haR hmR hsize hcR hdR hc0R hrow
  have eqmean := count_mean p hp (fun i => a i-m i) c
  have eqvar := count_variance_s53 p hp (fun i => a i-m i) c
  simp only [Rat.cast_sub] at eqmean eqvar
  change _=(FiniteLaw.bernoulli pR hp0 hp1).expect _ at eqmean
  change _=(FiniteLaw.bernoulli pR hp0 hp1).variance _ at eqvar
  apply (FiniteLaw.prob_positive_le _ _ ht ?_).trans
    (div_le_div_of_nonneg_right (eqvar.le.trans hvar) (sq_nonneg t))
  rw [eqmean]
  linarith only [hmean]

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseConditionalCount
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Amplifier.bitsFintype _root_.OAI.MetricKMedian.PCP.Amplifier.edgeSampleFintype _root_.OAI.MetricKMedian.PCP.Amplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.FlexibleAmplifier.nodeFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem conditional_count_tail_s53_oai (q a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {D p φ g A b : ℝ}
    (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
    (hlarge : 1 < b*A) (hqP : ∀ i, (q i:ℝ) ≤ 2*p)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, (a i:ℝ)+(m i:ℝ) ≤ b*A+2)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, (c i j:ℝ) ≤ (D-1)*(m i:ℝ))
    (hmass : (∑ i, (m i:ℝ)) ≤ 2*A/g)
    (htotal : (∑ i, ((a i:ℝ)+(m i:ℝ))) ≤ 4*A/g)
    (hsmall : 8*p*D ≤ φ*g)
    (hlinear : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤ -p*φ*A) :
    (run (d := 4) q hq n).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  have hA : 0 < A := (mul_pos_iff_of_pos_left hb).mp (lt_trans (by norm_num) hlarge)
  have ht : 0 < p*φ*A/2 := by positivity
  have hM : 0 ≤ ∑ i, (m i:ℝ) := sum_nonneg (fun i _ => by exact_mod_cast hm i)
  have hov := CountStatistic.overlap_budget hp.le hg hA.le hD hM hmass hsmall
  have hlin : (∑ i, ((a i:ℝ)-(m i:ℝ))*(q i:ℝ)) ≤
      -(p*φ*A/2)-(1/2)*(2*p)^2*(D-1)*∑ i, (m i:ℝ) := by
    linarith only [hlinear,hov]
  have hprob := count_failure q a m c hq hD (by positivity) ht hqP ha hm
    hsize hc hdiag hc0 hrow hlin
  apply hprob.trans
  have hsum : 0 ≤ ∑ i, ((a i:ℝ)+(m i:ℝ)) := by
    apply sum_nonneg
    intro i _
    exact add_nonneg (by exact_mod_cast ha i) (by exact_mod_cast hm i)
  have hB : b*A+2 ≤ 3*b*A := by linarith only [hlarge]
  calc
    (2*p)*D^2*(b*A+2)*(∑ i, ((a i:ℝ)+(m i:ℝ)))/(p*φ*A/2)^2 ≤
        (2*p)*D^2*(3*b*A)*(4*A/g)/(p*φ*A/2)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) htotal hsum (by positivity)
    _ = 96*D^2*b/(p*φ^2*g) := by
      field_simp
      ring

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53_oai := @OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53_oai
