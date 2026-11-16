-- Prove2me | solution 1 for IAFTRL.proposition_D_2_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:26:40.907194+00:00
-- url     : https://prove2.me/submissions/cb4c5689-38df-4fec-a21f-26137eace898

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_IAFTRL_regretVs


open Matrix MeasureTheory IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (hT : 1 ≤ T) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R)
    (u : Fin K) :
    regretVs P arms T R u ≤ 2 * (T : ℝ) := by
  -- every action has loss in `[-1, 1]` under an adversary with `‖θ_t‖_𝒜 ≤ 1`
  have hbd : ∀ t < T, ∀ ω, ∀ j : Fin K, |arms j ⬝ᵥ R.θs t ω| ≤ 1 := by
    intro t ht ω j
    have hnorm := (hR t ht).2.2.2.2 ω
    exact (le_ciSup (f := fun j => |arms j ⬝ᵥ R.θs t ω|) (Set.finite_range _).bddAbove j).trans
      hnorm
  -- hence the realized regret is at most `2T` on every outcome
  have hpt : ∀ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω ≤ 2 * (T : ℝ) := by
    intro ω
    calc ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω
        ≤ ∑ t ∈ Finset.range T, (2 : ℝ) := by
          refine Finset.sum_le_sum fun t ht => ?_
          have ht' := Finset.mem_range.mp ht
          have h1 := abs_le.mp (hbd t ht' ω (R.A t ω))
          have h2 := abs_le.mp (hbd t ht' ω u)
          rw [sub_dotProduct]
          linarith [h1.2, h2.1]
      _ = 2 * (T : ℝ) := by simp [mul_comm]
  unfold regretVs
  by_cases hint : Integrable (fun ω => ∑ t ∈ Finset.range T,
      (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω) P
  · calc ∫ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - arms u) ⬝ᵥ R.θs t ω ∂P
        ≤ ∫ _ω, 2 * (T : ℝ) ∂P := integral_mono hint (integrable_const _) hpt
      _ = 2 * (T : ℝ) := by simp
  · rw [integral_undef hint]
    positivity
