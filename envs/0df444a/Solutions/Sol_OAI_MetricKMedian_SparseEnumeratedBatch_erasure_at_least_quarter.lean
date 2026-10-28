-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:44:08.52212+00:00
-- url     : https://prove2.me/submissions/55216c7d-c2e0-4042-9971-3c4be7515177

import Mathlib
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_lower
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_pair_le

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
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

namespace BatchRemainder

theorem expect_selected_sum {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) :
    μ.expect (fun ω => ∑ e ∈ A ω, b e) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) * b e := by
  have hsum : ∀ ω, (∑ e ∈ A ω, b e) = ∑ e, (if e ∈ A ω then (1:ℝ) else 0) * b e := by
    intro ω
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
    simp only [Finset.filter_univ_mem]
  simp_rw [hsum, FiniteLaw.expect_sum, FiniteLaw.expect_mul_right]
  rfl

theorem expect_pair_count {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) :
    μ.expect (fun ω => (Finset.card (A ω).offDiag : ℝ)) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have hset : ∀ ω, (A ω).offDiag =
      (Finset.univ : Finset E).offDiag.filter (fun p => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
    intro ω
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hsum : ∀ ω, (Finset.card (A ω).offDiag : ℝ) =
      ∑ p ∈ (Finset.univ : Finset E).offDiag, if p.1 ∈ A ω ∧ p.2 ∈ A ω then (1:ℝ) else 0 := by
    intro ω
    rw [hset, ← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hsum, FiniteLaw.expect_sum]
  rfl

end BatchRemainder
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SurvivalProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset

theorem prob_nonempty_ge {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) :
    (∑ e, μ.prob (fun ω => e ∈ A ω)) -
      (1/2)*∑ p ∈ (univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) ≤
      μ.prob (fun ω => (A ω).Nonempty) := by
  have hpoint : ∀ ω, ((A ω).card:ℝ)-(1/2)*((A ω).offDiag.card:ℝ) ≤
      if (A ω).Nonempty then (1:ℝ) else 0 := by
    intro ω
    by_cases ha : (A ω).Nonempty
    · rw [ite_eq_left ha]
      have hn : 1 ≤ (A ω).card := card_pos.mpr ha
      have hcard : ((A ω).offDiag.card:ℝ) = ((A ω).card:ℝ)*(((A ω).card:ℝ)-1) := by
        rw [offDiag_card, show (A ω).card*(A ω).card-(A ω).card =
          (A ω).card*((A ω).card-1) by simp only [Nat.mul_sub_left_distrib, mul_one]]
        rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
      rw [hcard]
      rcases eq_or_lt_of_le hn with h | h
      · have hc : ((A ω).card:ℝ)=1 := by exact_mod_cast h.symm
        rw [hc]; norm_num
      · have hc : (2:ℝ) ≤ (A ω).card := by exact_mod_cast h
        nlinarith only [hc, sq_nonneg (((A ω).card:ℝ)-2)]
    · have he := not_nonempty_iff_eq_empty.mp ha
      simp only [he, card_empty, offDiag_empty, Nat.cast_zero, mul_zero,
        sub_zero, Finset.not_nonempty_empty, ite_false, le_refl]
  have h := μ.expect_mono hpoint
  have hcard : μ.expect (fun ω => ((A ω).card:ℝ)) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) := by
    have hc := BatchRemainder.expect_selected_sum μ A (fun _ => (1:ℝ))
    simpa only [sum_const, nsmul_eq_mul, mul_one] using hc
  simpa only [expect_sub, expect_mul, hcard, BatchRemainder.expect_pair_count, prob] using h

theorem prob_exists_ge {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (P : E → Ω → Prop) [∀ e, DecidablePred (P e)] :
    (∑ e, μ.prob (P e)) -
      (1/2)*∑ p ∈ (univ : Finset E).offDiag,
        μ.prob (fun ω => P p.1 ω ∧ P p.2 ω) ≤
      μ.prob (fun ω => ∃ e, P e ω) := by
  classical
  have h := prob_nonempty_ge μ (fun ω => univ.filter (fun e => P e ω))
  simpa only [mem_filter, mem_univ, true_and, filter_nonempty_iff,
    exists_prop, true_and] using h

end MetricKMedian.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem erasure_lower (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) :
    (R.card:ℝ)*(p:ℝ)/2-(R.card:ℝ)*(N:ℝ)*(p:ℝ)^2/2-2*(R.card:ℝ)^2*(p:ℝ)^2 ≤
      (law enum Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A) := by
  have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  let μ := (law enum Z C p q hp hq0).real
  have hfirst : (R.card:ℝ)*((p:ℝ)/2-(N:ℝ)*(p:ℝ)^2/2) ≤
      ∑ e : R, μ.prob (fun A => e.val ∈ A) := by
    have h := sum_le_sum (fun e (_ : e ∈ (univ : Finset R)) =>
      marginal_lower enum Z C p q hp hq0 (fun e => (hq e).1) hC hself e.val)
    simpa only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe] using h
  have hpair : ∀ e f : R, e ≠ f → μ.prob (fun A => e.val ∈ A ∧ f.val ∈ A) ≤ 4*(p:ℝ)^2 := by
    intro e f hef
    have h := pair_le enum Z C p q hp hq0 e.val f.val
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hm := mul_le_mul (hq e.val).2 (hq f.val).2 (show (0:ℝ) ≤ q f.val by exact_mod_cast (hq0 f.val).1) (by positivity : 0 ≤ 2*(p:ℝ))
    nlinarith only [h, hm, sq_nonneg (p:ℝ)]
  have hpairSum : (∑ ef ∈ (univ : Finset R).offDiag,
        μ.prob (fun A => ef.1.val ∈ A ∧ ef.2.val ∈ A)) ≤ 4*(R.card:ℝ)^2*(p:ℝ)^2 := by
    have h := sum_le_sum (fun ef (hef : ef ∈ (univ : Finset R).offDiag) =>
      hpair ef.1 ef.2 (mem_offDiag.mp hef).2.2)
    simp only [sum_const, nsmul_eq_mul] at h
    have hc : ((univ : Finset R).offDiag.card:ℝ) ≤ (R.card:ℝ)^2 := by
      have hn : (univ : Finset R).offDiag.card ≤ R.card*R.card := by
        rw [offDiag_card, card_univ, Fintype.card_coe]
        exact Nat.sub_le _ _
      exact_mod_cast (show (univ : Finset R).offDiag.card ≤ R.card^2 by simpa only [pow_two] using hn)
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 4*(p:ℝ)^2)
    nlinarith only [h, hm]
  have h := FiniteLaw.prob_exists_ge μ (fun e : R => fun A => e.val ∈ A)
  have heq : μ.prob (fun A => ∃ e : R, e.val ∈ A) = μ.prob (fun A => ∃ e ∈ R, e ∈ A) := by
    apply FiniteLaw.prob_congr
    intro A
    exact ⟨fun ⟨e, he⟩ => ⟨e.val, e.property, he⟩,
      fun ⟨e, he, ha⟩ => ⟨⟨e, he⟩, ha⟩⟩
  rw [heq] at h
  nlinarith only [h, hfirst, hpairSum]

theorem erasure_at_least_quarter_oai (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (hstep : (p:ℝ)*(2*(N:ℝ)+8*(R.card:ℝ)) ≤ 1) :
    (R.card:ℝ)*(p:ℝ)/4 ≤
      (law enum Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A) := by
  have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  have h := erasure_lower enum Z R C p q hp hq0 hq hC hself
  have hm := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ (R.card:ℝ)*(p:ℝ))
  nlinarith only [h, hm]

end MetricKMedian.SparseEnumeratedBatch
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter_oai := @OAI.MetricKMedian.SparseEnumeratedBatch.erasure_at_least_quarter_oai
