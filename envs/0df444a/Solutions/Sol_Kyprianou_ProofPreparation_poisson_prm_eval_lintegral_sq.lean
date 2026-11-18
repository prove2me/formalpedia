-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_eval_lintegral_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:02:36.254871+00:00
-- url     : https://prove2.me/submissions/1b4c216f-4051-4d8a-a9cf-290fe02e7207

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_map_poissonRandomMeasure_apply
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_lintegral_sq_nat_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Transfer the Poisson count-square identity along the exact evaluation law. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    (∫⁻ ω, ENNReal.ofReal
      (((ProbabilityTheory.poissonRandomMeasure K Y ω A).toReal) ^ 2) ∂P) =
      ENNReal.ofReal ((m A).toReal ^ 2 + (m A).toReal) := by
  let Z : Ω → ℝ≥0∞ := fun ω => poissonRandomMeasure K Y ω A
  let g : ℝ≥0∞ → ℝ≥0∞ := fun z => ENNReal.ofReal (z.toReal ^ 2)
  have hZ : Measurable Z :=
    measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.pow_const 2)
  have hNat : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := measurable_from_top
  have hLaw : P.map Z =
      (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) :=
    map_poissonRandomMeasure_apply hd hA hfin
  change (∫⁻ ω, g (Z ω) ∂P) =
    ENNReal.ofReal ((m A).toReal ^ 2 + (m A).toReal)
  calc
    (∫⁻ ω, g (Z ω) ∂P) =
        ∫⁻ z, g z ∂(P.map Z) :=
      (lintegral_map (f := g) hg hZ).symm
    _ = ∫⁻ z, g z ∂
        ((poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) := by
      rw [hLaw]
    _ = ∫⁻ n : ℕ, g (n : ℝ≥0∞) ∂(poissonMeasure (m A).toNNReal) :=
      lintegral_map (f := g) hg hNat
    _ = ∫⁻ n : ℕ, ENNReal.ofReal ((n : ℝ) ^ 2) ∂
        (poissonMeasure (m A).toNNReal) := by
      simp [g, ENNReal.toReal_natCast]
    _ = ENNReal.ofReal (((m A).toNNReal : ℝ) ^ 2 + (m A).toNNReal) :=
      Kyprianou.ProofPreparation.poisson_lintegral_sq_nat_count _
    _ = ENNReal.ofReal ((m A).toReal ^ 2 + (m A).toReal) := rfl
