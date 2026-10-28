-- Prove2me | solution 1 for OAI.MetricKMedian.SparseBernoulli.count_mean_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:30:55.834069+00:00
-- url     : https://prove2.me/submissions/7b4d8914-39fa-41cb-b22e-dab78e199a9d

import Mathlib
import Definitions.Def_OAIQ035K026
import Definitions.Def_OAIQ035K062

section
-- module Solutions.OAIQ035_KM.KMedian_Binary_BooleanMonomials
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliBatches
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

end FiniteLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliPolynomial
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRealTransfer
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseCountStatistic
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

theorem count_mean_s35_oai (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (b : Fin n → ℚ) (c : Fin n → Fin n → ℚ) :
    (run (d := 4) p hp n).real.expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ)))=
      (reference p hp).expect
        (CountStatistic.statistic (fun i => (b i:ℝ)) (fun i j => (c i j:ℝ))) := by
  have he := real_polynomial (d := 4) p hp countSets (countCoefficients b c)
    (fun a => (countSets_card a).trans (by omega))
  simpa only [cast_count_polynomial] using he

end MetricKMedian.SparseBernoulli
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseBernoulli.count_mean_s35_oai := @OAI.MetricKMedian.SparseBernoulli.count_mean_s35_oai
