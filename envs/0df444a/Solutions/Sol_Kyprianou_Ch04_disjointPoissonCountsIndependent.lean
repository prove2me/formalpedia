-- Prove2me | solution 1 for Kyprianou.Ch04.disjointPoissonCountsIndependent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:35:16.12764+00:00
-- url     : https://prove2.me/submissions/0b5bafa7-c485-4250-826e-67bc2136fb4f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- Independence of counts on two disjoint measurable marked-time regions. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hdisj : Disjoint B B') :
    IndepFun (fun ω => N.N ω B) (fun ω => N.N ω B') P := by
  set G : ULift (Fin 2) → Set (ℝ × E) := fun i => ![B, B'] i.down with hG
  have hm : ∀ i, MeasurableSet (G i) := by
    rintro ⟨i⟩; fin_cases i <;> first | exact hB | exact hB'
  have hp : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    rintro ⟨i⟩ ⟨j⟩ hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hdisj | exact hdisj.symm
  have hne : (ULift.up (0 : Fin 2)) ≠ ULift.up (1 : Fin 2) := by simp
  simpa [hG] using (N.independent_disjoint G hm hp).indepFun hne
