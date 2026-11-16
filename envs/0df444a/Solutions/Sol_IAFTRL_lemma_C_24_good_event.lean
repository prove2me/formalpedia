-- Prove2me | solution 1 for IAFTRL.lemma_C_24_good_event
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:11:14.501086+00:00
-- url     : https://prove2.me/submissions/3aaa9f6e-6c33-4acb-9d7d-8a122cfa8505

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_proxyC
import Definitions.Def_IAFTRL_cR
import Definitions.Def_IAFTRL_Run_cumEst
import Theorems.Thm_IAFTRL_lemma_C_13_good_event

open Matrix IAFTRL MeasureTheory

theorem solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d K : ℕ}, 1 ≤ d → ∀ (arms : Fin K → Fin d → ℝ), IsActionSet arms →
      ∀ (θ : Fin d → ℝ) (jstar : Fin K) (Δ₀ : ℝ),
        actionNorm arms θ ≤ 1 → IsUniqueMin arms θ jstar → 0 < Δ₀ → Δ₀ ≤ 1 →
        (∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ) →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∃ G : ℕ → Set Ω, (∀ t, MeasurableSet (G t)) ∧
            (∀ t < T, ∀ ω ∈ G t, ∀ a, a ≠ jstar →
              4 * (t + 1 : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ R.cumEst arms t ω) ∧
            cR d K * ∑ t ∈ Finset.range T, (P (G t)ᶜ).toReal / Real.sqrt (t + 1) ≤
              c₀ * (Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) +
                M := by
  obtain ⟨c₀, hc₀, h⟩ := lemma_C_13_good_event
  refine ⟨c₀, hc₀, ?_⟩
  intro d K hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  obtain ⟨M, hM⟩ := h hd arms hA θ jstar Δ₀ hθ hu hΔ₀ hΔ₀1 hgap
  refine ⟨M, ?_⟩
  intro Ω _ P _ T C R hT hC hR hcor
  obtain ⟨G, L, U, hGm, hsep, hfail, -⟩ := hM P T C R hT hC hR hcor
  exact ⟨G, hGm, hsep, hfail⟩
