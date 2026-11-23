-- Prove2me | solution 1 for Kyprianou.Ch02.levyFiniteVariationMonotoneJordanRepresentationV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:45:53.319139+00:00
-- url     : https://prove2.me/submissions/a7f2d78c-e0bb-475a-b132-b9343d031e6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyActualFiniteVariationSignedJumpSeriesV1
import Theorems.Thm_Kyprianou_Ch02_absSummableJumpSeriesMonotonePairV1
open MeasureTheory ProbabilityTheory Complex Kyprianou Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) :
    (σ = 0 ∧ Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) →
    ∀ᵐ ω ∂P,
      ∃ (p q : ℝ≥0 → ℝ), Monotone p ∧ Monotone q ∧
        ∀ t : ℝ≥0, X t ω = p t - q t := by
  intro hfin
  obtain ⟨drift, hseries⟩ :=
    Kyprianou.Ch02.levyActualFiniteVariationSignedJumpSeriesV1
      a σ levyMeasure hlevyMeasure P X hX hchar hfin
  filter_upwards [hseries] with ω hω
  obtain ⟨g, hsum, hpath⟩ := hω
  obtain ⟨p, q, hp, hq, heq⟩ :=
    Kyprianou.Ch02.absSummableJumpSeriesMonotonePairV1 g hsum
  let dpos : ℝ := max drift 0
  let dneg : ℝ := max (-drift) 0
  have hdp : 0 ≤ dpos := by
    dsimp only [dpos]
    exact le_max_right _ _
  have hdn : 0 ≤ dneg := by
    dsimp only [dneg]
    exact le_max_right _ _
  let p' : ℝ≥0 → ℝ := fun t => p t + dpos * (t : ℝ)
  let q' : ℝ≥0 → ℝ := fun t => q t + dneg * (t : ℝ)
  have hpm : Monotone p' := by
    intro t u htu
    have hu : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast htu
    exact add_le_add (hp htu) (mul_le_mul_of_nonneg_left hu hdp)
  have hqm : Monotone q' := by
    intro t u htu
    have hu : (t : ℝ) ≤ (u : ℝ) := by exact_mod_cast htu
    exact add_le_add (hq htu) (mul_le_mul_of_nonneg_left hu hdn)
  have hd : dpos - dneg = drift := by
    dsimp only [dpos, dneg]
    rcases le_total (0 : ℝ) drift with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
  refine ⟨p', q', hpm, hqm, ?_⟩
  intro T
  dsimp only [p', q']
  rw [hpath T, heq T, ← hd]
  ring
