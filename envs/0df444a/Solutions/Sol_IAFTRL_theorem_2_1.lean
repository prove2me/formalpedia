-- Prove2me | solution 1 for IAFTRL.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T07:43:52.015244+00:00
-- url     : https://prove2.me/submissions/5f8847e7-2edb-4103-9f6d-983502d26fb0

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Theorems.Thm_IAFTRL_proposition_2_1
import Theorems.Thm_IAFTRL_lemma_C_3

open Matrix MeasureTheory IAFTRL

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : Run d K Ω), 1 ≤ T → IsIAFTRLRun P arms T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K))) ∧
      (∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * (BanditAlgorithm.linearBanditAllocationValue arms (-θ) * Real.log K *
                Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M) := by
  obtain ⟨c₀, hc₀, hP⟩ := proposition_2_1
  refine ⟨2 * c₀, by positivity, ?_⟩
  intro d K hd arms hA
  obtain ⟨hadv, hsto⟩ := hP hd arms hA
  refine ⟨?_, ?_⟩
  · -- adversarial regime: the bound of Proposition 2.1 with the larger constant `2 c₀`
    intro Ω _ P _ T R hT hR u
    have hK : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
      exact_mod_cast this
    have hX : 0 ≤ (d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K) :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hK)) (Real.sqrt_nonneg _)
    calc regretVs P arms T R u
        ≤ c₀ * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K)) :=
          hadv P T R hT hR u
      _ ≤ 2 * c₀ * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K)) := by
          nlinarith
  · -- corrupted stochastic regime: Proposition 2.1 at the allocation of Lemma C.3
    intro θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap
    obtain ⟨⟨n, hn, hcost, -⟩, -⟩ := lemma_C_3 hd arms hA θ jstar huniq Δ₀ hΔ₀ hgap
    obtain ⟨M, hM⟩ := hsto θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
    refine ⟨M, ?_⟩
    intro Ω _ P _ T C R hT hC hR hcorr u
    have hK : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
      exact_mod_cast this
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hL : 0 ≤ Real.log K * Real.log T :=
      mul_nonneg (Real.log_nonneg hK) (Real.log_nonneg hT')
    have hJ : 0 ≤ Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hΔ₀.le _))
        (Real.sqrt_nonneg _)
    set cstar := BanditAlgorithm.linearBanditAllocationValue arms (-θ)
    set J := Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C
    set L := Real.log K * Real.log T
    have h1 := hM P T C R hT hC hR hcorr u
    have h2 : allocCost arms θ jstar n * L ≤ 2 * cstar * L :=
      mul_le_mul_of_nonneg_right hcost hL
    calc regretVs P arms T R u
        ≤ c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T + J) + M := h1
      _ = c₀ * (allocCost arms θ jstar n * L + J) + M := by simp only [L, mul_assoc]
      _ ≤ c₀ * (2 * cstar * L + J) + M := by gcongr
      _ ≤ 2 * c₀ * (cstar * L + J) + M := by nlinarith
      _ = 2 * c₀ * (cstar * Real.log K * Real.log T + J) + M := by simp only [L, mul_assoc]
