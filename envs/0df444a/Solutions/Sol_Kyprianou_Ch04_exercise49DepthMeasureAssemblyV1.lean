-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DepthMeasureAssemblyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:47:59.490015+00:00
-- url     : https://prove2.me/submissions/abf283cb-2d17-4e41-818b-dabe90910edb

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A stopped product law and depth splitting give the defective measure renewal equation. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Set Ω) (hD : MeasurableSet D) (I V W : Ω → ℝ)
    (hI : Measurable I) (hV : Measurable V) (hW : Measurable W)
    (hZero : ∀ᵐ ω ∂P.restrict Dᶜ, V ω = 0)
    (hSplit : ∀ᵐ ω ∂P.restrict D, V ω = I ω + W ω)
    (hJoint : Measure.map (fun ω => (I ω, W ω)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod (Measure.map V P)) :
    Measure.map V P = P Dᶜ • Measure.dirac 0 +
      (Measure.map V P).conv (Measure.map I (P.restrict D)) := by
  have hsum : P.restrict D + P.restrict Dᶜ = P :=
    Measure.restrict_add_restrict_compl hD
  have hzero : Measure.map V (P.restrict Dᶜ) = P Dᶜ • Measure.dirac 0 := by
    rw [Measure.map_congr hZero, Measure.map_const, Measure.restrict_apply_univ]
  have hsplit : Measure.map V (P.restrict D) =
      (Measure.map I (P.restrict D)).conv (Measure.map V P) := by
    rw [Measure.map_congr hSplit]
    change Measure.map (fun ω => I ω + W ω) (P.restrict D) =
      Measure.map (fun z : ℝ × ℝ => z.1 + z.2)
        ((Measure.map I (P.restrict D)).prod (Measure.map V P))
    rw [← hJoint]
    have hm : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
    rw [Measure.map_map hm (hI.prodMk hW)]
    rfl
  calc
    Measure.map V P = Measure.map V (P.restrict D + P.restrict Dᶜ) := by rw [hsum]
    _ = Measure.map V (P.restrict D) + Measure.map V (P.restrict Dᶜ) :=
      Measure.map_add _ _ hV
    _ = P Dᶜ • Measure.dirac 0 +
        (Measure.map V P).conv (Measure.map I (P.restrict D)) := by
      rw [hzero, hsplit, Measure.conv_comm, add_comm]
