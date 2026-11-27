-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45StrictBandRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:40:00.42831+00:00
-- url     : https://prove2.me/submissions/7d6ccda6-a2f7-4cce-b743-e5b19f03109a

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_smallJumpBandMeasureFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmCompensatedFiniteRegionCadlagAEV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false
/-- Use finite-region cadlag regularity, and eliminate the time-zero slice with the null-origin assumption. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hZero : ∀ᵐ w ∂P, N.N w ({0} ×ˢ (univ : Set ℝ)) = 0)
    (e : ℝ) (he : 0 < e) :
    ∀ᵐ w ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun s : NNReal =>
        (∫ z in Icc (0:ℝ) (s:ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
          z.2 ∂(N.N w)) - (s:ℝ)*∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν)
        (Ici t) t := by
  let B : Set ℝ := {x | e < |x| ∧ |x| < 1}
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const)
  have hsub : B ⊆ {x : ℝ | e ≤ |x| ∧ |x| < 1} := by
    intro x hx
    exact ⟨hx.1.le,hx.2⟩
  have hfin : ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub)
      (Kyprianou.Ch02.smallJumpBandMeasureFiniteV1 ν hν e he)
  have hc := Kyprianou.Ch02.prmCompensatedFiniteRegionCadlagAEV1 P ν N B hB hfin
    (∫ x in B, x ∂ν)
  filter_upwards [hc,hZero] with w hw hz
  have heq (s : NNReal) :
      (N.N w).restrict (Icc (0:ℝ) (s:ℝ) ×ˢ B) =
      (N.N w).restrict (Ioc (0:ℝ) (s:ℝ) ×ˢ B) := by
    apply Measure.restrict_congr_set
    have h : ∀ᵐ z : ℝ × ℝ ∂N.N w, z ∉ ({0} ×ˢ (univ : Set ℝ)) :=
      compl_mem_ae_iff.mpr hz
    filter_upwards [h] with z hnot
    have hn : z.1 ≠ 0 := fun h => hnot ⟨h,mem_univ _⟩
    apply propext
    change ((0 ≤ z.1 ∧ z.1 ≤ (s:ℝ)) ∧ z.2 ∈ B) ↔
      ((0 < z.1 ∧ z.1 ≤ (s:ℝ)) ∧ z.2 ∈ B)
    exact ⟨fun h => ⟨⟨lt_of_le_of_ne h.1.1 (Ne.symm hn),h.1.2⟩,h.2⟩,
      fun h => ⟨⟨h.1.1.le,h.1.2⟩,h.2⟩⟩
  intro t
  have hfun : (fun s : NNReal =>
        (∫ z in Icc (0:ℝ) (s:ℝ) ×ˢ B, z.2 ∂(N.N w)) -
          (s:ℝ)*∫ x in B, x ∂ν) =
      (fun s : NNReal =>
        (∫ z in Ioc (0:ℝ) (s:ℝ) ×ˢ B, z.2 ∂(N.N w)) -
          (s:ℝ)*∫ x in B, x ∂ν) := by
    funext s
    rw [heq]
  change ContinuousWithinAt (fun s : NNReal =>
    (∫ z in Icc (0:ℝ) (s:ℝ) ×ˢ B, z.2 ∂(N.N w)) -
      (s:ℝ)*∫ x in B, x ∂ν) (Ici t) t
  rw [hfun]
  exact (hw t).1
