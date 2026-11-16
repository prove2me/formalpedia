-- Prove2me | solution 1 for IAFTRL.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:24:32.006206+00:00
-- url     : https://prove2.me/submissions/b4edb340-3e8a-4ab1-804f-fb28c636f3c3

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsCorrupted
import Definitions.Def_IAFTRL_regretVs
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocCost

import Theorems.Thm_IAFTRL_proposition_D_2
import Theorems.Thm_IAFTRL_proposition_2_1_stochastic

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
        ∀ n : Fin K → ℝ, IsFeasibleAlloc arms θ jstar n →
        ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (T : ℕ) (C : ℝ) (R : Run d K Ω), 1 ≤ T → 0 ≤ C →
          IsIAFTRLRun P arms T R → IsCorrupted P arms θ C T R →
          ∀ u : Fin K, regretVs P arms T R u ≤
            c₀ * (allocCost arms θ jstar n * Real.log K * Real.log T +
              Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M) := by
  obtain ⟨cs, hcs, hS⟩ := proposition_2_1_stochastic
  refine ⟨max 48 cs, lt_max_of_lt_left (by norm_num), ?_⟩
  intro d K hd arms hA
  refine ⟨?_, ?_⟩
  · -- adversarial regime (2.4) from Proposition D.2
    intro Ω _ P _ T R hT hR u
    have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKr
    have hX : 0 ≤ (d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K) :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogK) (Real.sqrt_nonneg _)
    have hmono : 48 * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K)) ≤
        max 48 cs * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hX
    refine le_trans ?_ hmono
    rcases Nat.lt_or_ge K 2 with hK | hK
    · -- a single action: the regret is zero
      have hK' : K = 1 := by omega
      subst hK'
      have h0 : regretVs P arms T R u = 0 := by
        unfold regretVs
        have : ∀ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω = 0 := by
          intro ω
          refine Finset.sum_eq_zero fun t _ => ?_
          rw [Subsingleton.elim (R.A t ω) u, sub_self, zero_dotProduct]
        simp only [this, integral_zero]
      rw [h0]
      positivity
    · -- `K ≥ 2`: `log (e K) = 1 + log K ≤ 3 log K`
      have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
      have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      have hlogK2 : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK2
      have heK : Real.log (Real.exp 1 * K) = 1 + Real.log K := by
        rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      have hle3 : Real.log (Real.exp 1 * K) ≤ 3 * Real.log K := by rw [heK]; linarith
      have hD2 := min_le_right _ _ |>.trans' (proposition_D_2 hd arms hA P T hT R hR u)
      have hdT : (0 : ℝ) ≤ (d : ℝ) * T := by positivity
      have hsqrt3 : Real.sqrt 3 ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hs : Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K)) ≤
          2 * Real.sqrt ((d : ℝ) * T * Real.log K) := by
        calc Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K))
            ≤ Real.sqrt (3 * ((d : ℝ) * T * Real.log K)) := by
              apply Real.sqrt_le_sqrt
              nlinarith [mul_le_mul_of_nonneg_left hle3 hdT]
          _ = Real.sqrt 3 * Real.sqrt ((d : ℝ) * T * Real.log K) :=
              Real.sqrt_mul (by norm_num) _
          _ ≤ 2 * Real.sqrt ((d : ℝ) * T * Real.log K) :=
              mul_le_mul_of_nonneg_right hsqrt3 (Real.sqrt_nonneg _)
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      have h1 : 16 * (d : ℝ) * Real.log (Real.exp 1 * K) ≤ 48 * ((d : ℝ) * Real.log K) := by
        nlinarith [mul_le_mul_of_nonneg_left hle3 hd0]
      have hsq0 := Real.sqrt_nonneg ((d : ℝ) * T * Real.log K)
      calc regretVs P arms T R u
          ≤ 16 * (d : ℝ) * Real.log (Real.exp 1 * K) +
              21 * Real.sqrt ((d : ℝ) * T * Real.log (Real.exp 1 * K)) := hD2
        _ ≤ 48 * ((d : ℝ) * Real.log K + Real.sqrt ((d : ℝ) * T * Real.log K)) := by
            nlinarith
  · -- corrupted stochastic regime (2.5) from the stochastic child
    intro θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
    obtain ⟨M, hM⟩ := (hS hd arms hA) θ jstar Δ₀ hθ huniq hΔ₀ hΔ₀1 hgap n hn
    refine ⟨M, ?_⟩
    intro Ω _ P _ T C R hT hC hR hcorr u
    have hK : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ u).elim0)
      exact_mod_cast this
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have hcost : 0 ≤ allocCost arms θ jstar n := by
      unfold allocCost
      refine Finset.sum_nonneg fun j _ => mul_nonneg (hn.1 j) ?_
      by_cases hj : j = jstar
      · simp [hj]
      · have := huniq j hj
        rw [sub_dotProduct]; linarith
    have hY : 0 ≤ allocCost arms θ jstar n * Real.log K * Real.log T +
        Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C := by
      have := Real.log_nonneg hK
      have := Real.log_nonneg hT'
      have := Real.rpow_nonneg hΔ₀.le (-(128 : ℝ) / 255)
      positivity
    calc regretVs P arms T R u
        ≤ cs * (allocCost arms θ jstar n * Real.log K * Real.log T +
            Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M :=
          hM P T C R hT hC hR hcorr u
      _ ≤ max 48 cs * (allocCost arms θ jstar n * Real.log K * Real.log T +
            Real.sqrt ((d : ℝ) * Real.log K) * Δ₀ ^ (-(128 : ℝ) / 255) * Real.sqrt C) + M := by
          gcongr
          exact le_max_right _ _
