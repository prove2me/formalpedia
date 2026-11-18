-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_large_count_ae_finite_of_integrable_truncated
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:12:05.885998+00:00
-- url     : https://prove2.me/submissions/fb0cb8a8-8dc3-451e-a559-81a44f87bc9f

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (htrunc : Integrable (fun x => min (1 : ℝ) |f x|) m) :
    ∀ᵐ ω ∂P,
      ProbabilityTheory.poissonRandomMeasure K Y ω {x | 1 < |f x|} < ⊤ := by
  have hA : MeasurableSet {x | 1 < |f x|} := measurableSet_lt measurable_const hf.abs
  have hfin : m {x | 1 < |f x|} < ⊤ := by
    have hle : {x | 1 < |f x|}.indicator (fun _ => (1 : ℝ≥0∞)) ≤
        fun x => ENNReal.ofReal (min (1 : ℝ) |f x|) := by
      intro x
      by_cases hx : x ∈ {x | 1 < |f x|}
      · simp only [Set.indicator_of_mem hx]
        have : min (1 : ℝ) |f x| = 1 := min_eq_left (le_of_lt hx)
        rw [this, ENNReal.ofReal_one]
      · simp [Set.indicator_of_notMem hx]
    calc m {x | 1 < |f x|} = ∫⁻ x, {x | 1 < |f x|}.indicator (fun _ => (1 : ℝ≥0∞)) x ∂m := by
          rw [lintegral_indicator_const hA, one_mul]
      _ ≤ ∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |f x|) ∂m := lintegral_mono hle
      _ < ⊤ := htrunc.lintegral_lt_top
  exact ProbabilityTheory.ae_poissonRandomMeasure_apply_lt_top hd hA hfin
