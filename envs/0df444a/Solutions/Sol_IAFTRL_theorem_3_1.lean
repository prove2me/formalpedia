-- Prove2me | solution 1 for IAFTRL.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:40:10.414788+00:00
-- url     : https://prove2.me/submissions/d8ca353c-b359-4377-88b8-a61753c762b1

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Theorems.Thm_IAFTRL_proposition_3_1
import Theorems.Thm_IAFTRL_lemma_J_10
import Theorems.Thm_IAFTRL_theorem_3_1_alloc

namespace IAFTRL

open MeasureTheory

theorem _root_.solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d : ℕ}, 1 ≤ d → ∀ (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ),
      IsCompact 𝒜 → IsCompact ℬ → IsGenerator 𝒜 ℬ → (∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) →
      Submodule.span ℝ 𝒜 = ⊤ → 1 ≤ kdim ℬ → Function.Surjective e →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : GRun d Ω), 2 ≤ T → IsGIAFTRLRun P 𝒜 ℬ e T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤ c₀ * ((d : ℝ) * Real.sqrt T * Real.log T)) ∧
      (∀ (θ astar : Fin d → ℝ), setNorm 𝒜 θ ≤ 1 → astar ∈ 𝒜 →
        (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) → IsSharp 𝒜 θ astar →
        ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
          IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤
            c₀ * (cstarCtr 𝒜 θ astar * d * Real.log T) + M +
              J * Real.sqrt C * Real.log (max (Real.exp 1) C)) := by
  obtain ⟨c₀, hc₀, hP⟩ := proposition_3_1
  refine ⟨2 * c₀, by positivity, ?_⟩
  intro d hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he
  obtain ⟨hadv, hsto⟩ := hP hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he
  constructor
  · intro Ω _ P _ T R hT hR u hu
    have h := hadv P T R hT hR u hu
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
    have hnn : 0 ≤ (d : ℝ) * Real.sqrt T * Real.log T :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)) (Real.log_nonneg hT1)
    nlinarith
  · intro θ astar hθ hastar huniq hsharp
    obtain ⟨J, hJ⟩ := hsto θ astar hθ hastar huniq hsharp
    obtain ⟨n, hn, hcost⟩ :=
      theorem_3_1_alloc hd 𝒜 ℬ h𝒜 hℬ hgen hball hspan θ astar hastar huniq hsharp
    obtain ⟨M, hM⟩ := hJ n hn
    have hJ10 := (lemma_J_10.{0} 𝒜 ℬ h𝒜 hℬ hgen).2.1 θ astar hastar huniq
    refine ⟨M, J, ?_⟩
    intro Ω _ P _ T C R hT hC hR hcor u hu
    have h := hM P T C R hT hC hR hcor u hu
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hdl : 0 ≤ (d : ℝ) * Real.log T := mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg hT1)
    have hc : ctrCost θ astar n * d * Real.log T ≤ 2 * (cstarCtr 𝒜 θ astar * d * Real.log T) := by
      rw [hJ10, mul_assoc, mul_assoc, ← mul_assoc 2]
      exact mul_le_mul_of_nonneg_right hcost hdl
    have := mul_le_mul_of_nonneg_left hc hc₀.le
    linarith

end IAFTRL
