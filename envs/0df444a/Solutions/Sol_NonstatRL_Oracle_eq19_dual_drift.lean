-- Prove2me | solution 1 for NonstatRL.Oracle.eq19_dual_drift
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:51:02.329171+00:00
-- url     : https://prove2.me/submissions/14e3cdea-6c46-4282-81f6-8ca4c1a1d079

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal

namespace NonstatRL.Oracle

theorem eq19_helper_r_le {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    |(M (q + 1)).r s a - (M q).r s a| ≤ rewardDrift M As q := by
  unfold rewardDrift
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro d ⟨s', a', -, rfl⟩
    have h1 := (M (q+1)).r_mem_Icc s' a'
    have h2 := (M q).r_mem_Icc s' a'
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · exact ⟨s, a, ha, rfl⟩

theorem eq19_helper_P_le {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    ∑ s' : Fin S, |((M (q + 1)).P s a s' : ℝ) - ((M q).P s a s' : ℝ)| ≤ transDrift M As q := by
  unfold transDrift
  apply le_csSup
  · refine ⟨2, ?_⟩
    rintro d ⟨s₀, a₀, -, rfl⟩
    calc ∑ s' : Fin S, |((M (q + 1)).P s₀ a₀ s' : ℝ) - ((M q).P s₀ a₀ s' : ℝ)|
        ≤ ∑ s' : Fin S, (((M (q + 1)).P s₀ a₀ s' : ℝ) + ((M q).P s₀ a₀ s' : ℝ)) := by
          apply Finset.sum_le_sum; intro s' _
          have h1 : (0:ℝ) ≤ ((M (q + 1)).P s₀ a₀ s' : ℝ) := NNReal.coe_nonneg _
          have h2 : (0:ℝ) ≤ ((M q).P s₀ a₀ s' : ℝ) := NNReal.coe_nonneg _
          rw [abs_le]; constructor <;> linarith
      _ = 2 := by
          rw [Finset.sum_add_distrib]
          have e1 := (M (q+1)).P_sum_one s₀ a₀
          have e2 := (M q).P_sum_one s₀ a₀
          have f1 : (∑ s', ((M (q+1)).P s₀ a₀ s' : ℝ)) = 1 := by
            rw [← NNReal.coe_sum, e1]; simp
          have f2 : (∑ s', ((M q).P s₀ a₀ s' : ℝ)) = 1 := by
            rw [← NNReal.coe_sum, e2]; simp
          rw [f1, f2]; norm_num
  · exact ⟨s, a, ha, rfl⟩

theorem eq19_helper_r_tel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (t τ : ℕ) (htτ : t ≤ τ) :
    |(M τ).r s a - (M t).r s a| ≤ ∑ q ∈ Finset.Ico t τ, rewardDrift M As q := by
  induction τ, htτ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have := eq19_helper_r_le M As n s a ha
    calc |(M (n+1)).r s a - (M t).r s a|
        = |((M (n+1)).r s a - (M n).r s a) + ((M n).r s a - (M t).r s a)| := by ring_nf
      _ ≤ |(M (n+1)).r s a - (M n).r s a| + |(M n).r s a - (M t).r s a| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem eq19_helper_P_tel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (t τ : ℕ) (htτ : t ≤ τ) :
    ∑ s' : Fin S, |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| ≤
      ∑ q ∈ Finset.Ico t τ, transDrift M As q := by
  induction τ, htτ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have := eq19_helper_P_le M As n s a ha
    calc ∑ s' : Fin S, |((M (n+1)).P s a s' : ℝ) - ((M t).P s a s' : ℝ)|
        ≤ ∑ s' : Fin S, (|((M (n+1)).P s a s' : ℝ) - ((M n).P s a s' : ℝ)| +
            |((M n).P s a s' : ℝ) - ((M t).P s a s' : ℝ)|) := by
          apply Finset.sum_le_sum; intro s' _
          calc |((M (n+1)).P s a s' : ℝ) - ((M t).P s a s' : ℝ)|
              = |(((M (n+1)).P s a s' : ℝ) - ((M n).P s a s' : ℝ)) +
                  (((M n).P s a s' : ℝ) - ((M t).P s a s' : ℝ))| := by ring_nf
            _ ≤ _ := abs_add_le _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by linarith

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (t τ : ℕ) (htτ : t ≤ τ) (hτ : τ < T)
    (γ : Fin S → ℝ)
    (hγ : DualFeasible (M t).r (fun s a s' => ((M t).P s a s' : ℝ))
      As (optGain (M t) As) γ)
    (hγbounds : ∀ s, 0 ≤ γ s ∧ γ s ≤ 2 * Dmax)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    (M τ).r s a +
      ((∑ s' : Fin S, ((M τ).P s a s' : ℝ) * γ s') - γ s) -
      (∑ q ∈ Finset.Ico t τ,
        (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      optGain (M t) As := by
  have hfeas := hγ s a ha
  have hr := eq19_helper_r_tel M As s a ha t τ htτ
  have hP := eq19_helper_P_tel M As s a ha t τ htτ
  have hDnn : 0 ≤ Dmax := by linarith [(hγbounds s).1, (hγbounds s).2]
  have hdiff : (∑ s' : Fin S, ((M τ).P s a s' : ℝ) * γ s') -
      (∑ s' : Fin S, ((M t).P s a s' : ℝ) * γ s') ≤
      2 * Dmax * ∑ q ∈ Finset.Ico t τ, transDrift M As q := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ s' : Fin S, (((M τ).P s a s' : ℝ) * γ s' - ((M t).P s a s' : ℝ) * γ s')
        ≤ ∑ s' : Fin S, (2 * Dmax) * |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| := by
          apply Finset.sum_le_sum; intro s' _
          have hb := hγbounds s'
          rw [← sub_mul]
          calc (((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)) * γ s'
              ≤ |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| * γ s' :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hb.1
            _ ≤ |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| * (2 * Dmax) :=
                mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
            _ = _ := by ring
      _ = 2 * Dmax * ∑ s' : Fin S, |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by linarith)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have := (abs_le.mp hr).2
  linarith
