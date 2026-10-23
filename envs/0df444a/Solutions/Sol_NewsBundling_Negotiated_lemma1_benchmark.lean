-- Prove2me | solution 1 for NewsBundling.Negotiated.lemma1_benchmark
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:26:55.483043+00:00
-- url     : https://prove2.me/submissions/94ae1d0b-a02a-49cc-8748-5d040513f893

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting
import Theorems.Thm_NewsBundling_Unilateral_lemma2_attention

open NewsBundling.Unilateral

theorem solution (β φ0 φ1 c Λ : ℝ) (h : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ) ∧
      ∀ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ → σ.quality = β / c ∧ NewsBundling.Unilateral.eqProfit β φ1 c σ = β ^ 2 / (2 * c) := by
  obtain ⟨_, ⟨hφ1, _⟩, hφβ, hc, _⟩ := h
  have hβ : 0 < β := by linarith
  have hc0 : 0 < c := by linarith
  have hq0 : β / c ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hβ.le hc0.le, by rw [div_le_one hc0]; linarith⟩
  -- profit at cap 0 equals βq - cq²/2 whenever the consumer plays a best response at λ = 0
  have key : ∀ σ : Profile, IsSPE β φ0 φ1 c 0 σ → ∀ q ∈ Set.Icc (0 : ℝ) 1,
      publisherProfit β φ1 c σ q = β * q - c * q ^ 2 / 2 := by
    intro σ hσ q hq
    have hp : σ.platform q = 0 := by
      have := (hσ.2.1 q hq).1
      exact le_antisymm this.2 this.1
    have hT : σ.consumer q 0 = q := by
      have := (lemma2_attention q hq 0 le_rfl (by norm_num) _).1
        (hσ.1 q hq 0 ⟨le_rfl, le_rfl⟩)
      rw [this]; simp [hq.1]
    unfold publisherProfit publisherRevenue
    rw [hp, hT]; ring
  refine ⟨⟨⟨fun q lam => max ((q - lam) / (1 - lam)) 0, fun _ => 0, β / c⟩, ?_, ?_, hq0, ?_⟩, ?_⟩
  · intro q hq lam hlam
    exact (lemma2_attention q hq lam hlam.1 (by linarith [hlam.2]) _).2 rfl
  · intro q _
    refine ⟨⟨le_rfl, le_rfl⟩, ?_⟩
    intro lam hlam
    have : lam = 0 := le_antisymm hlam.2 hlam.1
    subst this; exact le_rfl
  · intro q hq
    unfold publisherProfit publisherRevenue
    simp only
    have e : ∀ x : ℝ, 0 ≤ x → max ((x - 0) / (1 - 0)) 0 = x := by
      intro x hx; simp [hx]
    rw [e q hq.1, e (β / c) hq0.1]
    have hx : c * (β / c) = β := by field_simp
    generalize β / c = x at hx ⊢
    subst hx
    nlinarith [mul_nonneg hc0.le (sq_nonneg (q - x))]
  · intro σ hσ
    have hQ := hσ.2.2.1
    have hopt := hσ.2.2.2 (β / c) hq0
    rw [key σ hσ _ hq0, key σ hσ _ hQ] at hopt
    have hsq : c * (σ.quality - β / c) ^ 2 ≤ 0 := by
      have hx : c * (β / c) = β := by field_simp
      generalize β / c = x at hx hopt ⊢
      subst hx
      nlinarith
    have hsq' : (σ.quality - β / c) ^ 2 = 0 := by
      have := mul_nonneg hc0.le (sq_nonneg (σ.quality - β / c))
      have h0 : c * (σ.quality - β / c) ^ 2 = 0 := le_antisymm hsq this
      rcases mul_eq_zero.1 h0 with h1 | h1
      · exact absurd h1 hc0.ne'
      · exact h1
    have hq : σ.quality = β / c := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq'
      linarith
    refine ⟨hq, ?_⟩
    unfold eqProfit
    rw [key σ hσ _ hQ, hq]
    field_simp
    ring
