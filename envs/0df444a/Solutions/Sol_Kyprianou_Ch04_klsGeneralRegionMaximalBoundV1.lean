-- Prove2me | solution 1 for Kyprianou.Ch04.klsGeneralRegionMaximalBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:47:15.781384+00:00
-- url     : https://prove2.me/submissions/5023bdbc-7825-4466-9b15-28ae2a96f46d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
import Theorems.Thm_Kyprianou_Ch04_klsGeneralRegionVarianceBoundV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleL2MaximalV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The compensated finite-region real-mark integral satisfies the maximal L2 estimate. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (T : ℝ≥0) (hT : 0 < T) :
    let D := fun (t : ℝ≥0) ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν
    Integrable (fun ω => sSup ((fun t : ℝ≥0 => |D t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : ℝ≥0 => |D t ω|^2) '' Iic T) ∂P) ≤
        4 * (T : ℝ) * ∫ x in B, x^2 ∂ν := by
  dsimp only
  have : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hfinite.ne
  let D : ℝ≥0 → Ω → ℝ := fun t ω =>
    (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν
  obtain ⟨F,hF,hM,hLp⟩ := Kyprianou.compensatedGeneralRegionMartingaleCh02V3
    P ν N B hB hfinite (hsecond.integrable (by norm_num))
  have hr : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto (fun s => D s ω)
      (nhdsWithin t (Ioi t)) (𝓝 (D t ω)) := by
    filter_upwards [Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N B hB hfinite] with ω hω
    intro t
    have hc : Continuous (fun s : ℝ≥0 => (s : ℝ) * ∫ x in B, x ∂ν) :=
      continuous_subtype_val.mul continuous_const
    exact (continuousWithinAt_Ioi_iff_Ici.mpr (hω t).1).sub
      ((hc.tendsto t).mono_left nhdsWithin_le_nhds)
  have hv := Kyprianou.Ch04.klsGeneralRegionVarianceBoundV1 P ν N B hB hfinite hsecond T
  have hm := Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1 P F D hM T hT hr hv.1
  refine ⟨hm.1, hm.2.trans ?_⟩
  calc
    _ ≤ 4 * ((T : ℝ) * ∫ x in B, x^2 ∂ν) := mul_le_mul_of_nonneg_left hv.2 (by norm_num)
    _ = _ := by ring
