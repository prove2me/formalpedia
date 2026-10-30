-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:58:30.316901+00:00
-- url     : https://prove2.me/submissions/a9f68646-25ce-48b4-a882-1e3148e09c9c

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_1
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_claim_2
import Theorems.Thm_NoisyPrototyping_ReservationPolicy_weitzman_pandora_rule

open MeasureTheory
open NoisyPrototyping.ReservationPolicy

theorem solution {N : ℕ} (M : Model N) (f : Fin N → ℝ × ℝ → ℝ)
    (hf_nonneg : ∀ i z, 0 ≤ f i z) (hf_meas : ∀ i, Measurable (f i))
    (hlaw : ∀ i, M.law i =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z => ENNReal.ofReal (f i z)))
    (R : Fin N → ℝ)
    (hR : ∀ i, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂(g M.toSearchProblem (fun j => Q (f j)) i)
      = M.cost i} (R i))
    (σ : Fin N ≃ Fin N) (hσ : ∀ a b, a ≤ b → R (σ b) ≤ R (σ a)) :
    Admissible M.toSearchProblem (fidelityPolicy (fun j => Q (f j)) σ R) ∧
    ∀ ρ : Policy N, Admissible M.toSearchProblem ρ →
      value M.toSearchProblem ρ ≤
        value M.toSearchProblem (fidelityPolicy (fun j => Q (f j)) σ R) := by
  obtain ⟨hG, h2, h3, -⟩ := claim_2 M f hf_nonneg hf_meas hlaw
  haveI : ∀ i, IsProbabilityMeasure (g M.toSearchProblem (fun j => Q (f j)) i) :=
    fun i => (hG i).1
  obtain ⟨hWadm, hWopt⟩ := weitzman_pandora_rule
    (fun i => g M.toSearchProblem (fun j => Q (f j)) i) (fun i => (hG i).2)
    M.cost M.cost_pos R hR σ hσ
  obtain ⟨h2adm, h2val⟩ := h2 σ R
  have hP2 := h2adm hWadm
  obtain ⟨h1iff, h1val⟩ := claim_1 M f hf_nonneg hf_meas hlaw
    (fidelityPolicy (fun j => Q (f j)) σ R)
  have hP : Admissible M.toSearchProblem (fidelityPolicy (fun j => Q (f j)) σ R) :=
    h1iff.2 hP2
  refine ⟨hP, fun ρ hρ => ?_⟩
  obtain ⟨hρiff, hρval⟩ := claim_1 M f hf_nonneg hf_meas hlaw ρ
  obtain ⟨ρ', hρ'adm, hρ'le⟩ := h3 ρ (hρiff.1 hρ)
  rw [hρval hρ, h1val hP, h2val]
  exact hρ'le.trans (hWopt ρ' hρ'adm)
