-- Prove2me | solution 1 for Kyprianou.Ch04.compensatedTimeBoxSplitAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:30:25.451927+00:00
-- url     : https://prove2.me/submissions/c7036826-a879-466b-8059-62957c5e8129

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_compensatedDisjointUnionAE
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Split a compensated time-mark box at an intermediate deterministic time. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (a b t : NNReal) (hab : a ≤ b) (hbt : b ≤ t)
    (A : Set E) (hA : MeasurableSet A)
    (hFin : referenceIntensity ν (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ≠ ⊤) :
    (fun ω => N.compensated (Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A) ω) =ᵐ[P]
      (fun ω => N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω +
        N.compensated (Set.Ioc (b : ℝ) (t : ℝ) ×ˢ A) ω) := by
  let U := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A
  let V := Set.Ioc (b : ℝ) (t : ℝ) ×ˢ A
  let W := Set.Ioc (a : ℝ) (t : ℝ) ×ˢ A
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbt' : (b : ℝ) ≤ t := by exact_mod_cast hbt
  have hU : U ⊆ W := fun z hz => ⟨⟨hz.1.1, hz.1.2.trans hbt'⟩, hz.2⟩
  have hV : V ⊆ W := fun z hz => ⟨⟨hab'.trans_lt hz.1.1, hz.1.2⟩, hz.2⟩
  have hd : Disjoint U V := Set.disjoint_left.mpr
    (fun z hz hz' => (not_lt_of_ge hz.1.2) hz'.1.1)
  have hu : U ∪ V = W := by
    ext z
    constructor
    · intro hz
      exact hz.elim (fun h => hU h) (fun h => hV h)
    · intro hz
      by_cases h : z.1 ≤ (b : ℝ)
      · exact Or.inl ⟨⟨hz.1.1, h⟩, hz.2⟩
      · exact Or.inr ⟨⟨lt_of_not_ge h, hz.1.2⟩, hz.2⟩
  have hUf := ne_top_of_le_ne_top hFin (measure_mono hU)
  have hVf := ne_top_of_le_ne_top hFin (measure_mono hV)
  simpa only [hu, W, U, V] using
    Kyprianou.Ch04.compensatedDisjointUnionAE N
      (A := U) (B := V) (measurableSet_Ioc.prod hA)
      (measurableSet_Ioc.prod hA) hd hUf hVf
