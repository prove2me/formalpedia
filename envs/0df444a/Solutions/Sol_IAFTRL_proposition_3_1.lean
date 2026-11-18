-- Prove2me | solution 1 for IAFTRL.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-17T09:17:23.567762+00:00
-- url     : https://prove2.me/submissions/2220c22b-26cf-441a-a517-a45cdddd62d4

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Theorems.Thm_IAFTRL_proposition_G_2
import Theorems.Thm_IAFTRL_proposition_G_1

namespace IAFTRL

open MeasureTheory

lemma p31_log_eT {T : ℕ} (hT : 1 ≤ T) : Real.log (Real.exp 1 * T) = 1 + Real.log T := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]

lemma p31_log_max (C : ℝ) (hC : 0 ≤ C) :
    Real.log (Real.exp 1 + C) ≤ 2 * Real.log (max (Real.exp 1) C) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  set m := max (Real.exp 1) C with hm
  have hm1 : Real.exp 1 ≤ m := le_max_left _ _
  have hm2 : C ≤ m := le_max_right _ _
  have hmpos : 0 < m := by linarith
  have h1 : Real.exp 1 + C ≤ m ^ 2 := by nlinarith
  calc Real.log (Real.exp 1 + C) ≤ Real.log (m ^ 2) :=
        Real.log_le_log (by linarith [Real.exp_pos 1]) h1
    _ = 2 * Real.log m := by rw [Real.log_pow]; norm_num

theorem _root_.solution : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {d : ℕ}, 1 ≤ d → ∀ (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ),
      IsCompact 𝒜 → IsCompact ℬ → IsGenerator 𝒜 ℬ → (∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) →
      Submodule.span ℝ 𝒜 = ⊤ → 1 ≤ kdim ℬ → Function.Surjective e →
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
          (R : GRun d Ω), 2 ≤ T → IsGIAFTRLRun P 𝒜 ℬ e T R →
          ∀ u ∈ 𝒜, gRegretVs P T R u ≤ c₀ * ((d : ℝ) * Real.sqrt T * Real.log T)) ∧
      (∀ (θ astar : Fin d → ℝ), setNorm 𝒜 θ ≤ 1 → astar ∈ 𝒜 →
        (∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ) → IsSharp 𝒜 θ astar →
        ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
          ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
            IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
            ∀ u ∈ 𝒜, gRegretVs P T R u ≤
              c₀ * (ctrCost θ astar n * d * Real.log T) + M +
                J * Real.sqrt C * Real.log (max (Real.exp 1) C)) := by
  refine ⟨2 ^ 65, by positivity, ?_⟩
  intro d hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨?_, ?_⟩
  · intro Ω _ P _ T R hT hR u hu
    have hT1 : 1 ≤ T := by omega
    have h := proposition_G_2 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he P T R hT1 hR u (hgen.2 hu)
    rw [p31_log_eT hT1] at h
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log T := by
      have h2 : Real.log 2 ≤ Real.log T :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hT)
      have := Real.log_two_gt_d9
      linarith
    have hsq : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    refine h.trans ?_
    have hA : 320 * ((d : ℝ) + 1) * Real.sqrt T * (1 + Real.log T) ≤
        1920 * ((d : ℝ) * Real.sqrt T * Real.log T) := by
      have h3 : (1 : ℝ) + Real.log T ≤ 3 * Real.log T := by linarith
      have h4 : (d : ℝ) + 1 ≤ 2 * d := by linarith
      calc 320 * ((d : ℝ) + 1) * Real.sqrt T * (1 + Real.log T)
          ≤ 320 * (2 * d) * Real.sqrt T * (3 * Real.log T) := by
            gcongr
      _ = 1920 * ((d : ℝ) * Real.sqrt T * Real.log T) := by ring
    have hB : 0 ≤ (d : ℝ) * Real.sqrt T * Real.log T := by
      have : 0 ≤ Real.log T := by linarith
      positivity
    nlinarith
  · intro θ astar hθ hastar huniq hsharp
    obtain ⟨J, hJ⟩ := proposition_G_1 hd 𝒜 ℬ e h𝒜 hℬ hgen hball hspan hk he θ astar hθ hastar
      huniq hsharp
    refine ⟨2 * |J|, fun n hn => ?_⟩
    obtain ⟨M, hM⟩ := hJ n hn
    -- the cost is nonnegative
    have hcost : 0 ≤ ctrCost θ astar n := by
      obtain ⟨_, hsupp, _, _⟩ := hn
      refine integral_nonneg_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with a ha
      have ha' : a ∈ 𝒜 := hgen.1 (by simpa using ha)
      show (0 : ℝ) ≤ (a - astar) ⬝ᵥ θ
      rw [sub_dotProduct]
      by_cases h : a = astar
      · simp [h]
      · linarith [huniq a ha' h]
    refine ⟨M + 16 * gB d * 64 ^ 4 * ctrCost θ astar n, ?_⟩
    intro Ω _ P _ T C R hT hC hR hcor u hu
    have h := hM P T C R hT hC hR hcor u hu
    rw [p31_log_eT hT] at h
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
    have hgB : 16 * gB d * 64 ^ 4 ≤ 2 ^ 65 * d := by
      simp only [gB]; nlinarith
    have h1 : 16 * gB d * 64 ^ 4 * ctrCost θ astar n * (1 + Real.log T) ≤
        2 ^ 65 * (ctrCost θ astar n * d * Real.log T) + 16 * gB d * 64 ^ 4 * ctrCost θ astar n := by
      have : 16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log T ≤
          2 ^ 65 * d * ctrCost θ astar n * Real.log T := by
        have hcl : 0 ≤ ctrCost θ astar n * Real.log T := mul_nonneg hcost hlogT
        have := mul_le_mul_of_nonneg_right hgB hcl
        linarith
      nlinarith
    have hlogC := p31_log_max C hC
    have hlogpos : 0 ≤ Real.log (Real.exp 1 + C) :=
      Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hsC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    have h2 : J * Real.sqrt C * Real.log (Real.exp 1 + C) ≤
        2 * |J| * Real.sqrt C * Real.log (max (Real.exp 1) C) := by
      calc J * Real.sqrt C * Real.log (Real.exp 1 + C)
          ≤ |J| * Real.sqrt C * Real.log (Real.exp 1 + C) := by
            have := le_abs_self J
            have hx : 0 ≤ Real.sqrt C * Real.log (Real.exp 1 + C) := mul_nonneg hsC hlogpos
            nlinarith
        _ ≤ |J| * Real.sqrt C * (2 * Real.log (max (Real.exp 1) C)) := by
            have : 0 ≤ |J| * Real.sqrt C := mul_nonneg (abs_nonneg _) hsC
            exact mul_le_mul_of_nonneg_left hlogC this
        _ = 2 * |J| * Real.sqrt C * Real.log (max (Real.exp 1) C) := by ring
    linarith

end IAFTRL
