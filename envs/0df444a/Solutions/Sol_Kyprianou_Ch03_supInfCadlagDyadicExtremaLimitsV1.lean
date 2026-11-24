-- Prove2me | solution 1 for Kyprianou.Ch03.supInfCadlagDyadicExtremaLimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:01:09.924405+00:00
-- url     : https://prove2.me/submissions/e56a6477-0aa3-4c72-b62d-35e645c98688

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_supInfCadlagFullRangeBoundsV1
import Theorems.Thm_Kyprianou_Ch03_supInfDyadicGridArithmeticV1
import Theorems.Thm_Kyprianou_Ch03_supInfDyadicRightApproximantsV1
import Theorems.Thm_Kyprianou_Ch03_supInfFiniteExtremaLimitOfApproximantsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f : NNReal → Real) (hf : IsCadlag f) (t : NNReal) (ht : 0 < t) :
    Tendsto (fun n : ℕ => sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))))) atTop
      (𝓝 (LevyExtrema.SBA.runSup f t)) ∧
    Tendsto (fun n : ℕ => sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
      f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal)))))) atTop
      (𝓝 (sInf (f '' Set.Icc 0 t))) := by
  let A := f '' Set.Icc (0 : NNReal) t
  let B (n : ℕ) := Set.range (fun i : Fin (2 ^ n + 1) =>
    f ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))))
  have hA : A.Nonempty := ⟨f 0, 0, ⟨le_rfl, by positivity⟩, rfl⟩
  obtain ⟨hAb, hAl⟩ := Kyprianou.Ch03.supInfCadlagFullRangeBoundsV1 f hf t
  have hB (n : ℕ) : (B n).Nonempty := Set.range_nonempty _
  have hsub (n : ℕ) : B n ⊆ A := by
    rintro y ⟨i, rfl⟩
    have hqt := (Kyprianou.Ch03.supInfDyadicGridArithmeticV1 t n).2.2.2.1 i
    exact ⟨_, ⟨by positivity, hqt⟩, rfl⟩
  have happrox : ∀ a ∈ A, ∃ u : ℕ → Real,
      (∀ n, u n ∈ B n) ∧ Tendsto u atTop (𝓝 a) := by
    rintro a ⟨s, hs, rfl⟩
    obtain ⟨u, hu, hut⟩ := Kyprianou.Ch03.supInfDyadicRightApproximantsV1 s t ht hs.2
    refine ⟨fun n => f (u n), ?_, ?_⟩
    · intro n
      obtain ⟨i, hi⟩ := (hu n).2
      exact ⟨i, congrArg f hi.symm⟩
    · have hwithin : Tendsto u atTop (𝓝[≥] s) :=
        tendsto_nhdsWithin_iff.mpr ⟨hut, Eventually.of_forall fun n => (hu n).1⟩
      have hc : Tendsto f (𝓝[≥] s) (𝓝 (f s)) := (hf s).1
      exact hc.comp hwithin
  exact Kyprianou.Ch03.supInfFiniteExtremaLimitOfApproximantsV1 A hA hAb hAl
    B hB hsub happrox
