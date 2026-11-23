-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.power_four_padding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:49:35.882449+00:00
-- url     : https://prove2.me/submissions/6a39e093-cddf-489e-980e-208431c90aae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ITPIRPreproc_MatchVec_padded_scheme_adapter
import Theorems.Thm_ITPIRPreproc_MatchVec_power_four_padding_asymptotics

open scoped ENNReal
open Filter Topology
open ITPIRPreproc.MatchVec

theorem solution
    (hSquare :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
        ∃ (K : ℝ) (c : ℕ), ∀ h lam : ℕ, 3 ≤ h → 1 ≤ lam →
          PerfectlyPrivate S (4^h) lam ∧
          Correct S (4^h) lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞)^lam) ∧
          MeetsBudget S (4^h) lam
            { preWork := K * ((4^h : ℕ) : ℝ)^(1+η h) * (lam:ℝ)^c
              preSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              online := K * lam * ((4^h : ℕ) : ℝ)^(η h)
              offline := K * Real.sqrt (4^h : ℕ)
              clientWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              clientSpace := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c
              serverWork := K * ((4^h : ℕ) : ℝ)^((1:ℝ)/2+η h) * (lam:ℝ)^c }) :
    ∃ S : Scheme, S.WellFormed ∧
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
        ∃ (C : ℝ) (c : ℕ), ∀ n lam : ℕ, 1 ≤ n → 1 ≤ lam →
          PerfectlyPrivate S n lam ∧
          Correct S n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
          MeetsBudget S n lam
            { preWork := C * (n : ℝ) ^ (1 + ε n) * (lam : ℝ) ^ c
              preSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              online := C * lam * (n : ℝ) ^ (ε n)
              offline := C * Real.sqrt n
              clientWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              clientSpace := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c
              serverWork := C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε n) * (lam : ℝ) ^ c } := by
  rcases hSquare with ⟨S, hS, η, hη, K, c, hsquare⟩
  rcases padded_scheme_adapter S hS with ⟨A, hA, T, hT, hadapter⟩
  rcases power_four_padding_asymptotics η hη K c A hA with ⟨ε, hε, C, hbounds⟩
  refine ⟨T, hT, ε, hε, C, c, ?_⟩
  intro n lam hn hlam
  have hn4 : padLength n = 4 ^ padHeight n := rfl
  have hs := hsquare (padHeight n) lam (le_max_left _ _) hlam
  rw [← hn4] at hs
  have hcostS : MeetsBudget S (padLength n) lam
      (powerFourBudget K c η (padHeight n) lam) := hs.2.2
  rcases hadapter n lam (powerFourBudget K c η (padHeight n) lam) hn hs.1 hs.2.1 hcostS with
    ⟨hprivate, hcorrect, hcost⟩
  exact ⟨hprivate, hcorrect, meetsBudget_mono (hbounds n lam hn hlam) hcost⟩