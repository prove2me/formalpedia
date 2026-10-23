-- Prove2me | solution 1 for NewsBundling.Negotiated.proposition5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:25:04.808525+00:00
-- url     : https://prove2.me/submissions/9ddf4052-fe42-472d-8039-f19c0a240efb

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting
import Theorems.Thm_NewsBundling_Negotiated_lemma5_negotiated_quality
import Theorems.Thm_NewsBundling_Negotiated_lemma1_benchmark
import Theorems.Thm_NewsBundling_Negotiated_lemma4_equilibrium_quality
import Theorems.Thm_NewsBundling_Negotiated_prop5_preamble

open NewsBundling.Negotiated

theorem solution (β φ0 φ1 c Λ : ℝ) (hN : NegAssumptions β c Λ)
    (hU : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    ((∃ σ, IsNegotiatedSPE β c Λ σ) ∧ (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ) ∧
        (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σ)) ∧
      ∀ σN σb σU, IsNegotiatedSPE β c Λ σN → NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σb → NewsBundling.Unilateral.IsSPE β φ0 φ1 c Λ σU →
        (β < 1 → (σb.quality < σN.quality ↔ β / Λ < c)) ∧
          (c ≠ NewsBundling.Unilateral.cdagger β φ1 Λ → (σU.quality < σN.quality ↔ NewsBundling.Unilateral.cdagger β φ1 Λ < c)) := by
  have L5 := lemma5_negotiated_quality β c Λ hN
  have L1 := lemma1_benchmark β φ0 φ1 c Λ hU
  have L4 := lemma4_equilibrium_quality β φ0 φ1 c Λ hU
  refine ⟨⟨L5.1, L1.1, L4.1⟩, ?_⟩
  intro σN σb σU hσN hσb hσU
  have hqN := L5.2 σN hσN
  have hqb := (L1.2 σb hσb).1
  obtain ⟨hU1, hU2, _⟩ := L4.2.1 σU hσU
  obtain ⟨⟨hβ1, hβ2⟩, hc, hΛ0, hΛ1⟩ := hN
  obtain ⟨_, ⟨hφ0, hφ1⟩, hφβ, _, _⟩ := hU
  have hc0 : 0 < c := by linarith
  have hΛ' : 0 < 1 - Λ := by linarith
  have hcΛ : 0 < c * Λ := mul_pos hc0 hΛ0
  have hcΛ' : 0 < c * (1 - Λ) := mul_pos hc0 hΛ'
  -- threshold facts
  have ha : ∀ x : ℝ, x < (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * Λ) ↔
      x * (2 * (1 - Λ) * Λ) < β * (2 - Λ) - Λ := fun x => lt_div_iff₀ (by positivity)
  have hb : ∀ x : ℝ, x ≤ (1 + β) / (2 * Λ) ↔ x * (2 * Λ) ≤ 1 + β :=
    fun x => le_div_iff₀ (by positivity)
  have hcd : ∀ x : ℝ, x < NewsBundling.Unilateral.cdagger β φ1 Λ ↔
      x * (2 * Λ * (1 - Λ)) < β + φ1 * (1 - 2 * Λ) := by
    intro x; unfold NewsBundling.Unilateral.cdagger; exact lt_div_iff₀ (by positivity)
  have hcd' : ∀ x : ℝ, NewsBundling.Unilateral.cdagger β φ1 Λ < x ↔
      β + φ1 * (1 - 2 * Λ) < x * (2 * Λ * (1 - Λ)) := by
    intro x; unfold NewsBundling.Unilateral.cdagger; exact div_lt_iff₀ (by positivity)
  have hβΛ : β / Λ < c ↔ β < c * Λ := div_lt_iff₀ hΛ0
  -- quality comparisons as cross-multiplied facts
  have q2e : q2 β c Λ = (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * c) := rfl
  have q1e : q1 β c = (1 + β) / (2 * c) := rfl
  constructor
  · intro hβ
    have hpre := prop5_preamble β c Λ ⟨⟨hβ1, hβ2⟩, hc, hΛ0, hΛ1⟩ hβ
    rw [hqb, hqN, hβΛ]
    split_ifs with h1 h2
    · constructor
      · intro h; linarith [hpre.1]
      · intro h
        exfalso
        rw [ha] at h1
        nlinarith [mul_pos hΛ0 (sub_pos.2 hβ)]
    · constructor
      · intro h; rwa [div_lt_iff₀ hc0, mul_comm] at h
      · intro h; rw [div_lt_iff₀ hc0]; linarith
    · constructor
      · intro _
        push Not at h2
        rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Λ)] at h2
        nlinarith
      · intro _; exact hpre.2
  · intro hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- c < c†: q* = qH
      have hq := hU2 hlt
      rw [hq, hqN]
      have hlt' := (hcd c).1 hlt
      constructor
      · intro h
        exfalso
        unfold NewsBundling.Unilateral.qH at h
        split_ifs at h with h1 h2
        · rw [q2e, div_lt_div_iff₀ hcΛ' (by positivity)] at h
          nlinarith [mul_pos (mul_pos hcΛ' hΛ0) (by linarith : (0:ℝ) < β + 1 - 2 * φ1)]
        · rw [div_lt_iff₀ hcΛ'] at h
          nlinarith [mul_pos hΛ0 hΛ']
        · push Not at h2
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Λ)] at h2
          rw [q1e, div_lt_div_iff₀ hcΛ' (by positivity)] at h
          nlinarith [mul_pos hΛ0 hΛ', mul_pos hc0 hΛ0]
      · intro h; exact absurd h (not_lt.2 hlt.le)
    · -- c > c†: q* = qL
      have hq := hU1 hgt
      rw [hq, hqN]
      have hgt' := (hcd' c).1 hgt
      constructor
      · intro _; exact hgt
      · intro _
        unfold NewsBundling.Unilateral.qL
        split_ifs with h1 h2
        · rw [q2e, div_lt_div_iff₀ hc0 (by positivity)]
          rw [ha] at h1
          nlinarith [mul_pos hΛ0 hΛ', mul_pos hc0 hΛ0]
        · rw [div_lt_iff₀ hc0]
          nlinarith [mul_pos hΛ0 hΛ', mul_pos hc0 hΛ0, mul_pos hΛ0 (sub_pos.2 hφβ)]
        · rw [q1e, div_lt_div_iff₀ hc0 (by positivity)]
          nlinarith
