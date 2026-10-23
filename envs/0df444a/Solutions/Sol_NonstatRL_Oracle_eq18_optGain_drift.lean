-- Prove2me | solution 1 for NonstatRL.Oracle.eq18_optGain_drift
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:53:19.239997+00:00
-- url     : https://prove2.me/submissions/5938f660-cfdd-4d61-b303-be33bfa30425

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Theorems.Thm_NonstatRL_Oracle_exists_bounded_optimal_dual

open BanditAlgorithm ENNReal

namespace NonstatRL.Oracle

theorem eq18_helper_r_le {S A : ℕ} (M : ℕ → FiniteMDP S A)
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

theorem eq18_helper_P_le {S A : ℕ} (M : ℕ → FiniteMDP S A)
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

theorem eq18_helper_r_tel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (t τ : ℕ) (htτ : t ≤ τ) :
    |(M τ).r s a - (M t).r s a| ≤ ∑ q ∈ Finset.Ico t τ, rewardDrift M As q := by
  induction τ, htτ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have := eq18_helper_r_le M As n s a ha
    calc |(M (n+1)).r s a - (M t).r s a|
        = |((M (n+1)).r s a - (M n).r s a) + ((M n).r s a - (M t).r s a)| := by ring_nf
      _ ≤ |(M (n+1)).r s a - (M n).r s a| + |(M n).r s a - (M t).r s a| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem eq18_helper_P_tel {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (s : Fin S) (a : Fin A) (ha : a ∈ As s)
    (t τ : ℕ) (htτ : t ≤ τ) :
    ∑ s' : Fin S, |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| ≤
      ∑ q ∈ Finset.Ico t τ, transDrift M As q := by
  induction τ, htτ using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn]
    have := eq18_helper_P_le M As n s a ha
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


theorem eq18_weak_duality {S A : ℕ} (r : Fin S → Fin A → ℝ)
    (P : Fin S → Fin A → Fin S → ℝ) (As : Fin S → Finset (Fin A))
    (ρ : ℝ) (γ : Fin S → ℝ) (hfeas : DualFeasible r P As ρ γ) (hρ : 0 ≤ ρ) :
    lpValue r P As ≤ ρ := by
  unfold lpValue
  apply Real.sSup_le _ hρ
  rintro v ⟨x, hx0, -, hflow, hsum, rfl⟩
  calc ∑ s : Fin S, ∑ a ∈ As s, r s a * x s a
      ≤ ∑ s : Fin S, ∑ a ∈ As s, (ρ + γ s - ∑ s' : Fin S, P s a s' * γ s') * x s a := by
        apply Finset.sum_le_sum; intro s _
        apply Finset.sum_le_sum; intro a ha
        apply mul_le_mul_of_nonneg_right _ (hx0 s a)
        have := hfeas s a ha; linarith
    _ = ρ * (∑ s : Fin S, ∑ a ∈ As s, x s a) + (∑ s : Fin S, γ s * ∑ a ∈ As s, x s a)
          - ∑ s : Fin S, ∑ a ∈ As s, (∑ s' : Fin S, P s a s' * γ s') * x s a := by
        simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
    _ = ρ := by
        have key : ∑ s : Fin S, ∑ a ∈ As s, (∑ s' : Fin S, P s a s' * γ s') * x s a =
            ∑ s : Fin S, γ s * ∑ a ∈ As s, x s a := by
          calc ∑ s : Fin S, ∑ a ∈ As s, (∑ s' : Fin S, P s a s' * γ s') * x s a
              = ∑ s : Fin S, ∑ a ∈ As s, ∑ s' : Fin S, P s a s' * γ s' * x s a := by
                simp_rw [Finset.sum_mul]
            _ = ∑ s : Fin S, ∑ s' : Fin S, ∑ a ∈ As s, P s a s' * γ s' * x s a := by
                apply Finset.sum_congr rfl; intro s _; exact Finset.sum_comm
            _ = ∑ s' : Fin S, ∑ s : Fin S, ∑ a ∈ As s, P s a s' * γ s' * x s a :=
                Finset.sum_comm
            _ = ∑ s' : Fin S, γ s' * ∑ s : Fin S, ∑ a ∈ As s, P s a s' * x s a := by
                apply Finset.sum_congr rfl; intro s' _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro s _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro a _
                ring
            _ = _ := by
                apply Finset.sum_congr rfl; intro s' _
                rw [hflow s']
        rw [key, hsum]; ring

theorem eq18_optGain_nonneg {S A : ℕ} (M : FiniteMDP S A) (As : Fin S → Finset (Fin A)) :
    0 ≤ optGain M As := by
  unfold optGain lpValue
  apply Real.sSup_nonneg
  rintro v ⟨x, hx0, -, -, -, rfl⟩
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro a _
  exact mul_nonneg (M.r_mem_Icc s a).1 (hx0 s a)

theorem eq18_rewardDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ rewardDrift M As q := by
  unfold rewardDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact abs_nonneg _

theorem eq18_transDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ transDrift M As q := by
  unfold transDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (t τ : ℕ) (htτ : t ≤ τ) (hτ : τ < T) :
    optGain (M t) As -
      (∑ q ∈ Finset.Ico t τ,
        (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      optGain (M τ) As := by
  obtain ⟨γ, hγ, hγb⟩ := exists_bounded_optimal_dual (M τ) As hS hAs Dmax (hD τ hτ)
  have hDnn : 0 ≤ Dmax := by
    have := hγb ⟨0, hS⟩; linarith [this.1, this.2]
  have hsumnn : 0 ≤ ∑ q ∈ Finset.Ico t τ,
      (rewardDrift M As q + 2 * Dmax * transDrift M As q) := by
    apply Finset.sum_nonneg; intro q _
    have := eq18_rewardDrift_nonneg M As q
    have := eq18_transDrift_nonneg M As q
    positivity
  have hfeas : DualFeasible (M t).r (fun s a s' => ((M t).P s a s' : ℝ)) As
      (optGain (M τ) As + ∑ q ∈ Finset.Ico t τ,
        (rewardDrift M As q + 2 * Dmax * transDrift M As q)) γ := by
    intro s a ha
    have hf := hγ s a ha
    have hr := eq18_helper_r_tel M As s a ha t τ htτ
    have hP := eq18_helper_P_tel M As s a ha t τ htτ
    have hdiff : (∑ s' : Fin S, ((M t).P s a s' : ℝ) * γ s') -
        (∑ s' : Fin S, ((M τ).P s a s' : ℝ) * γ s') ≤
        2 * Dmax * ∑ q ∈ Finset.Ico t τ, transDrift M As q := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ s' : Fin S, (((M t).P s a s' : ℝ) * γ s' - ((M τ).P s a s' : ℝ) * γ s')
          ≤ ∑ s' : Fin S, (2 * Dmax) * |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| := by
            apply Finset.sum_le_sum; intro s' _
            have hb := hγb s'
            rw [← sub_mul]
            calc (((M t).P s a s' : ℝ) - ((M τ).P s a s' : ℝ)) * γ s'
                ≤ |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| * γ s' := by
                  apply mul_le_mul_of_nonneg_right _ hb.1
                  rw [abs_sub_comm]; exact le_abs_self _
              _ ≤ |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| * (2 * Dmax) :=
                  mul_le_mul_of_nonneg_left hb.2 (abs_nonneg _)
              _ = _ := by ring
        _ = 2 * Dmax * ∑ s' : Fin S, |((M τ).P s a s' : ℝ) - ((M t).P s a s' : ℝ)| := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hP (by linarith)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have := (abs_le.mp hr).1
    simp only at hf ⊢
    linarith
  have := eq18_weak_duality _ _ As _ γ hfeas
    (add_nonneg (eq18_optGain_nonneg (M τ) As) hsumnn)
  have : optGain (M t) As ≤ _ := this
  linarith
