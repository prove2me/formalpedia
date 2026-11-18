-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_charfun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:14:46.351123+00:00
-- url     : https://prove2.me/submissions/320c6a92-a6dc-4c3a-94f6-64348c1e7b28

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_integral_ae_eq
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_prm_two_cell_charfun

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two-cell count exponent is the exponent of the actual Poisson integral. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) (a b ξ : ℝ) :
    charFun (P.map (fun ω =>
      ∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
        b * B.indicator (fun _ => (1 : ℝ)) x) ∂
        (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp ((((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) +
        (((m B).toReal : ℂ) *
        (Complex.exp ((((b * ξ : ℝ) : ℂ)) * Complex.I) - 1))) := by
  have hAE := Kyprianou.ProofPreparation.poisson_prm_two_cell_integral_ae_eq
    P m K Y hd A B hA hB hfinA hfinB a b
  have hm : P.map (fun ω =>
      ∫ x, (a * A.indicator (fun _ => (1 : ℝ)) x +
        b * B.indicator (fun _ => (1 : ℝ)) x) ∂
        (poissonRandomMeasure K Y ω)) =
      P.map (fun ω => a * (poissonRandomMeasure K Y ω A).toReal +
        b * (poissonRandomMeasure K Y ω B).toReal) :=
    Measure.map_congr hAE
  rw [hm]
  exact Kyprianou.ProofPreparation.poisson_prm_two_cell_charfun
    P m K Y hd A B hA hB hfinA hfinB hAB a b ξ
