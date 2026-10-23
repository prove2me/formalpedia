-- Prove2me | solution 1 for NonstatRL.Oracle.exists_bounded_optimal_dual
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T18:15:43.227859+00:00
-- url     : https://prove2.me/submissions/7d23e071-3f15-46c1-8256-95fd36e584e1

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Theorems.Thm_NonstatRL_Oracle_lemma2_dual_span
import Theorems.Thm_NonstatRL_Oracle_lp_dual_attained

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

theorem bdual_optGain_le_one {S A : ℕ} (M : FiniteMDP S A) (As : Fin S → Finset (Fin A)) :
    optGain M As ≤ 1 := by
  unfold optGain lpValue
  apply Real.sSup_le _ zero_le_one
  rintro v ⟨x, hx0, -, -, hsum, rfl⟩
  calc ∑ s : Fin S, ∑ a ∈ As s, M.r s a * x s a ≤ ∑ s : Fin S, ∑ a ∈ As s, x s a := by
        apply Finset.sum_le_sum; intro s _
        apply Finset.sum_le_sum; intro a _
        have := (M.r_mem_Icc s a).2
        nlinarith [hx0 s a]
    _ = 1 := hsum

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (D : ℝ)
    (hD : diameter M As ≤ ENNReal.ofReal D) :
    ∃ γ : Fin S → ℝ,
      DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As (optGain M As) γ ∧
      ∀ s, 0 ≤ γ s ∧ γ s ≤ 2 * D := by
  obtain ⟨γ₀, hγ₀⟩ := lp_dual_attained M As
  have hne : (Finset.univ : Finset (Fin S)).Nonempty := ⟨⟨0, hS⟩, Finset.mem_univ _⟩
  obtain ⟨smin, -, hmin⟩ := Finset.exists_min_image Finset.univ γ₀ hne
  refine ⟨fun s => γ₀ s - γ₀ smin, ?_, ?_⟩
  · intro s a ha
    have h := hγ₀ s a ha
    have hP : (∑ s' : Fin S, ((M.P s a s' : ℝ)) * (γ₀ s' - γ₀ smin)) =
        (∑ s' : Fin S, ((M.P s a s' : ℝ)) * γ₀ s') - γ₀ smin := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      have : (∑ s' : Fin S, (M.P s a s' : ℝ)) = 1 := by
        rw [← NNReal.coe_sum, M.P_sum_one s a]; simp
      rw [this, one_mul]
    simp only at h ⊢
    rw [hP]
    linarith
  · intro s
    refine ⟨by linarith [hmin s (Finset.mem_univ _)], ?_⟩
    exact lemma2_dual_span M As D hD (optGain M As) γ₀ hγ₀ (bdual_optGain_le_one M As) s smin
