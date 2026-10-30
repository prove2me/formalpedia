-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:51:25.55023+00:00
-- url     : https://prove2.me/submissions/71809e91-63e7-41f5-b790-79762a493d8e

import Mathlib
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K049
import Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_count_failure

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountTail
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseConditionalCount
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

theorem conditional_count_tail (q a m : Fin n → ℚ) (c : Fin n → Fin n → ℚ)
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

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseRealExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem expectation_def (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.expectation f=∑ i : Fin μ.length, (μ.law.rational.weight i:ℝ)*f μ.states[i.val] := rfl

theorem expectation_map (μ : SparseIntegerLaw α) (g : α → β) (f : β → ℝ) :
    (μ.map g).expectation f=μ.expectation (fun a => f (g a)) := by
  simp only [expectation_def,map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

theorem real_expect_all [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℝ) :
    μ.real.expect f=μ.expectation f := by
  rw [real,FiniteLaw.expect_map]
  rfl

theorem prob_map [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : SparseIntegerLaw α) (f : α → β) (P : β → Prop) [DecidablePred P] :
    (μ.map f).real.prob P=μ.real.prob (fun a => P (f a)) := by
  simp only [FiniteLaw.prob,real_expect_all,expectation_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBernoulli
open Finset
variable {E : Type} [Fintype E] [DecidableEq E] {n : ℕ}

omit [DecidableEq E] in
theorem statistic_reindex (enum : Fin n ≃ E) (a : E → ℝ) (c : E → E → ℝ)
    (ω : Fin n → Bool) :
    CountStatistic.statistic a c (fun e => ω (enum.symm e))=
      CountStatistic.statistic (fun i => a (enum i)) (fun i j => c (enum i) (enum j)) ω := by
  unfold CountStatistic.statistic
  rw [← enum.sum_comp (fun e => a e * CountStatistic.bit (fun e => ω (enum.symm e)) e)]
  simp only [CountStatistic.bit,Equiv.symm_apply_apply]
  congr 1
  congr 1
  rw [← enum.sum_comp]
  apply sum_congr rfl
  intro i _
  rw [← enum.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem conditional_count_tail_oai (enum : Fin n ≃ E) (q a m : E → ℚ) (c : E → E → ℚ)
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
    (law enum q hq).real.prob (fun ω => 0 <
      CountStatistic.statistic (fun i => (a i:ℝ)-(m i:ℝ)) (fun i j => (c i j:ℝ)) ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  rw [law,SparseIntegerLaw.prob_map]
  simp only [statistic_reindex]
  apply SparseBernoulli.conditional_count_tail (fun i => q (enum i))
    (fun i => a (enum i)) (fun i => m (enum i)) (fun i j => c (enum i) (enum j))
    (fun i => hq (enum i)) hD hp hφ hg hb hlarge (fun i => hqP (enum i))
    (fun i => ha (enum i)) (fun i => hm (enum i)) (fun i => hsize (enum i))
    (fun i j => hc (enum i) (enum j)) (fun i => hdiag (enum i))
    (fun i j => hc0 (enum i) (enum j))
  · intro i
    rw [enum.sum_comp (fun j => (c (enum i) j:ℝ))]
    exact hrow (enum i)
  · rw [enum.sum_comp (fun i => (m i:ℝ))]
    exact hmass
  · rw [enum.sum_comp (fun i => (a i:ℝ)+(m i:ℝ))]
    exact htotal
  · exact hsmall
  · rw [enum.sum_comp (fun i => ((a i:ℝ)-(m i:ℝ))*(q i:ℝ))]
    exact hlinear

end MetricKMedian.SparseEnumeratedBernoulli
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_oai := @OAI.MetricKMedian.SparseEnumeratedBernoulli.conditional_count_tail_oai
