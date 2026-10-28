-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:44:30.798862+00:00
-- url     : https://prove2.me/submissions/b7fdc784-5343-4a4f-acf6-e6a4fa370d13

import Mathlib
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_marginal_error
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_pair_le

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace BatchRemainder

theorem pointwise {E : Type*} [DecidableEq E] (A : Finset E)
    (b : E → ℝ) {D K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ e ∈ A, -K ≤ b e) (hD : D ≤ K)
    (hzero : A = ∅ → D ≤ 0) (hone : ∀ e, A = {e} → D ≤ b e) :
    D ≤ (∑ e ∈ A, b e) + 2 * K * (A.offDiag.card : ℝ) := by
  rcases lt_or_ge A.card 2 with hsmall | hlarge
  · have hc : A.card ≤ 1 := by omega
    by_cases h : A = ∅
    · simpa only [h, Finset.sum_empty, Finset.offDiag_empty, Finset.card_empty,
        Nat.cast_zero, mul_zero, add_zero] using hzero h
    · have hpos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
      obtain ⟨e, ha⟩ := Finset.card_eq_one.mp (show A.card = 1 by omega)
      simpa only [ha, Finset.sum_singleton, Finset.offDiag_singleton,
        Finset.card_empty, Nat.cast_zero, mul_zero, add_zero] using hone e ha
  · have hsum := Finset.sum_le_sum hb
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hn : (2:ℝ) ≤ A.card := by exact_mod_cast hlarge
    have hcard : (A.offDiag.card : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      rw [Finset.offDiag_card]
      have hrewrite : A.card * A.card - A.card = A.card * (A.card - 1) := by
        simp only [Nat.mul_sub_left_distrib, mul_one]
      rw [hrewrite, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard]
    have hquad : (A.card : ℝ) + 1 ≤ 2 * (A.card : ℝ) * ((A.card : ℝ) - 1) := by
      nlinarith only [hn, sq_nonneg ((A.card : ℝ) - 2)]
    have hmul := mul_le_mul_of_nonneg_left hquad hK
    nlinarith only [hsum, hD, hmul]

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

theorem expectation_le {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ) (D : Ω → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ e, -K ≤ b e) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω = ∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω = {e} → D ω ≤ b e) :
    μ.expect D ≤ (∑ e, μ.prob (fun ω => e ∈ A ω) * b e) +
      2 * K * ∑ p ∈ (Finset.univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) := by
  have h := μ.expect_mono (fun ω => pointwise (A ω) b hK (fun e _ => hb e)
    (hD ω) (hzero ω) (hone ω))
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_mul,
    expect_selected_sum, expect_pair_count] at h
  exact h

end BatchRemainder
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.BatchRemainder
open Finset

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]

theorem generator_estimate (μ : FiniteLaw Ω) (A : Ω → Finset E) (b : E → ℝ)
    (D : Ω → ℝ) {K lam δ J : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hb : ∀ e, |b e| ≤ K) (hD : ∀ ω, D ω ≤ K)
    (hzero : ∀ ω, A ω=∅ → D ω ≤ 0)
    (hone : ∀ ω e, A ω={e} → D ω ≤ b e)
    (hfirst : ∀ e, |μ.prob (fun ω => e ∈ A ω)-lam| ≤ δ)
    (hpair : ∀ e f, e ≠ f → μ.prob (fun ω => e ∈ A ω ∧ f ∈ A ω) ≤ J) :
    μ.expect D ≤ lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ+
      2*K*((univ : Finset E).offDiag.card:ℝ)*J := by
  have hfirstsum : (∑ e, μ.prob (fun ω => e ∈ A ω)*b e) ≤
      lam*(∑ e, b e)+(Fintype.card E:ℝ)*K*δ := by
    have hpoint : ∀ e, μ.prob (fun ω => e ∈ A ω)*b e ≤ lam*b e+K*δ := by
      intro e
      have habs : |(μ.prob (fun ω => e ∈ A ω)-lam)*b e| ≤ δ*K := by
        rw [abs_mul]
        exact mul_le_mul (hfirst e) (hb e) (abs_nonneg _) hδ
      have hle := (le_abs_self ((μ.prob (fun ω => e ∈ A ω)-lam)*b e)).trans habs
      nlinarith only [hle]
    have hsum := sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) => hpoint e)
    simpa only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      using hsum
  have hpairSum : (∑ p ∈ (univ : Finset E).offDiag,
      μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω)) ≤ ((univ : Finset E).offDiag.card:ℝ)*J := by
    calc
      _ ≤ ∑ _p ∈ (univ : Finset E).offDiag, J :=
        sum_le_sum (fun p hp => hpair p.1 p.2 (mem_offDiag.mp hp).2.2)
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hbase := expectation_le μ A b D hK (fun e => (abs_le.mp (hb e)).1) hD hzero hone
  have hj := mul_le_mul_of_nonneg_left hpairSum (by positivity : 0 ≤ 2*K)
  nlinarith only [hbase, hfirstsum, hj]

end MetricKMedian.BatchRemainder

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseEnumeratedBatch
open Finset
variable {E : Type} [DecidableEq E] [Fintype E] {n : ℕ}

theorem relevant_generator_estimate_oai (enum : Fin n ≃ E) (Z R : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (b : E → ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ K Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    (D : Finset E → ℝ)
    (hb : ∀ e ∈ R, |b e| ≤ K) (hD : ∀ A, D A ≤ K)
    (hzero : ∀ A, A ∩ R=∅ → D A ≤ 0)
    (hone : ∀ A e, A ∩ R={e} → D A ≤ b e) :
    (law enum Z C p q hp hq0).real.expect D ≤
      ((p:ℝ)/2)*(∑ e ∈ R, b e)+(R.card:ℝ)*K*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*K*((univ : Finset R).offDiag.card:ℝ)*Q^2 := by
  let A' : Finset E → Finset R := fun A => univ.filter (fun e : R => e.val ∈ A)
  have hzero' : ∀ A, A' A=∅ → A ∩ R=∅ := by
    intro A ha
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have he' : (⟨e, (mem_inter.mp he).2⟩ : R) ∈ A' A := by
      simp only [A', mem_filter, mem_univ, true_and]
      exact (mem_inter.mp he).1
    rw [ha] at he'
    exact notMem_empty _ he'
  have hone' : ∀ A (e : R), A' A={e} → A ∩ R={e.val} := by
    intro A e ha
    ext f
    constructor
    · intro hf
      have hf' : (⟨f, (mem_inter.mp hf).2⟩ : R) ∈ A' A := by
        simp only [A', mem_filter, mem_univ, true_and]
        exact (mem_inter.mp hf).1
      rw [ha, mem_singleton] at hf'
      simpa only [mem_singleton] using congrArg Subtype.val hf'
    · intro hf
      have hfval : f=e.val := mem_singleton.mp hf
      subst f
      have he : e ∈ A' A := by rw [ha]; exact mem_singleton_self _
      exact mem_inter.mpr ⟨(mem_filter.mp he).2, e.property⟩
  have hfirst : ∀ e : R,
      |(law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A)-(p:ℝ)/2| ≤
        (N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2 := by
    intro e
    simpa only [A', mem_filter, mem_univ, true_and] using
      marginal_error enum Z C p q hp hq0 hφ hq hC hself e.val
  have hpair : ∀ e f : R, e ≠ f →
      (law enum Z C p q hp hq0).real.prob (fun A => e ∈ A' A ∧ f ∈ A' A) ≤ Q^2 := by
    intro e f hef
    have h2 := pair_le enum Z C p q hp hq0 e.val f.val
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hpp : (p:ℝ)^2 ≤ Q^2 := (sq_le_sq₀ (by exact_mod_cast hp.1) hQ).mpr hpQ
    have hqq := mul_le_mul (hqQ e.val) (hqQ f.val) (show (0:ℝ) ≤ q f.val by exact_mod_cast (hq0 f.val).1) hQ
    simp only [A', mem_filter, mem_univ, true_and]
    nlinarith only [h2, hpp, hqq]
  have h := BatchRemainder.generator_estimate (law enum Z C p q hp hq0).real A'
    (fun e : R => b e.val) D hK (by
      have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
      positivity)
    (fun e => hb e.val e.property) hD (fun A ha => hzero A (hzero' A ha))
    (fun A e ha => hone A e.val (hone' A e ha)) hfirst hpair
  simpa only [Fintype.card_coe, sum_coe_sort] using h

end MetricKMedian.SparseEnumeratedBatch

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_oai := @OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_oai
