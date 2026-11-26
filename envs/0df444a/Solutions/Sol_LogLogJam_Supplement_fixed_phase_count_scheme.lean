-- Prove2me | solution 1 for LogLogJam.Supplement.fixed_phase_count_scheme
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:28:47.718934+00:00
-- url     : https://prove2.me/submissions/e20ad8d8-2e58-43f7-ab01-a5d5897b925f

import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Theorems.Thm_LogLogJam_Supplement_even_phase_povm
import Theorems.Thm_LogLogJam_Supplement_photon_number_povm

open MeasureTheory ProbabilityTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Classical

open LogLogJam LogLogJam.Supplement

/-- The preassigned phase and count detectors can be run on two disjoint sets of
fresh copies for every integer sample count, with their exact Fock-space Born laws. -/
theorem solution (m : ℕ) :
    ∃ S : AdaptiveScheme 1 m ℝ, phaseCountReadouts S := by
  classical
  obtain ⟨P, hP⟩ := even_phase_povm
  obtain ⟨C, hC⟩ := photon_number_povm
  let M := fun t : Fin m => if t.val < m / 2 then P else C
  let L := fun (ρ : Matrix (Occupation (Fin 1)) (Occupation (Fin 1)) ℂ) (t : Fin m) =>
    if IsDensity ρ then (M t).law ρ else Measure.dirac (0 : ℝ)
  have hL (ρ) (t) : IsProbabilityMeasure (L ρ t) := by
    dsimp only [L]
    split
    · exact (M t).law_prob _ ‹_›
    · infer_instance
  let S : AdaptiveScheme 1 m ℝ := {
    povm := fun t _ => M t
    round := fun ρ t => Kernel.const _ (L ρ t)
    round_markov := fun ρ t => by let := hL ρ t; infer_instance
    round_born := fun ρ hρ t x => by simp [L, hρ] }
  refine ⟨S, fun _ _ _ => rfl, ?_, ?_⟩
  · intro t ht h B hB k l
    simpa only [S, M, if_pos ht] using hP B hB k l
  · intro t ht h B _ i j
    simpa only [S, M, if_neg (not_lt.mpr ht)] using hC B i j
