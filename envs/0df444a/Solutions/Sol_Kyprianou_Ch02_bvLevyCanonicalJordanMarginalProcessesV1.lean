-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:27:47.23973+00:00
-- url     : https://prove2.me/submissions/2b91cdac-0b9e-4668-bc7f-9d1064bb104b

import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPairStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanCadlagV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ProbabilityTheory.IsLevyProcess Spos P ∧
    ProbabilityTheory.IsLevyProcess Sneg P := by
  dsimp only
  let V : ℝ≥0 → Ω → ℝ := fun t ω =>
    variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
  let A : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
  let B : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
  let Y : ℝ≥0 → Ω → ℝ × ℝ := fun t ω => (A t ω, B t ω)
  have hi : HasIndependentIncrements Y P :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPairIndependentIncrementsV1 P X hX hBV
  have hs : HasStationaryIncrements Y P :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPairStationaryIncrementsV1 P X hX hBV
  obtain ⟨hcA, hcB⟩ := Kyprianou.Ch02.bvLevyCanonicalJordanCadlagV1 P X hX hBV
  have hz : ∀ ω, X 0 ω = 0 := congrFun hX.start_zero
  change IsLevyProcess A P ∧ IsLevyProcess B P
  constructor
  · refine ⟨?_, ?_, ?_, hcA⟩
    · funext ω
      simp [A, V, variationOnFromTo.self, hz]
    · intro n t ht
      exact (hi n t ht).comp (fun _ => Prod.fst) (fun _ => measurable_fst)
    · intro s u
      exact (hs s u).comp measurable_fst
  · refine ⟨?_, ?_, ?_, hcB⟩
    · funext ω
      simp [B, V, variationOnFromTo.self, hz]
    · intro n t ht
      exact (hi n t ht).comp (fun _ => Prod.snd) (fun _ => measurable_snd)
    · intro s u
      exact (hs s u).comp measurable_snd
