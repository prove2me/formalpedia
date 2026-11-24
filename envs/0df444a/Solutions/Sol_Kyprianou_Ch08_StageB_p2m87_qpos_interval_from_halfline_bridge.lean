-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_interval_from_halfline_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:46:24.676204+00:00
-- url     : https://prove2.me/submissions/752359f4-5123-41ea-a2cb-9a8e8a53d63d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_density_halfline_add_split
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_occupation_halfline_add_split
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exp_clock_normalization
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) x y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X x) 0 ω ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) a y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              tauMinus (shifted D.X a) 0 ω ∧
              shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue →
        ((volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedIntervalDensity (W q) a x y))) A =
        ∫⁻ t : ℝ≥0,
          ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
            P {ω | (t : WithTop ℝ≥0) <
              min (tauMinus (shifted D.X x) 0 ω)
                (tauPlus (shifted D.X x) a ω) ∧
              shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA hxHalf haHalf
  letI : IsProbabilityMeasure (expMeasure q) := isProbabilityMeasure_expMeasure hq
  let Ox : ℝ≥0∞ := ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
    P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
      shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
  let Oa : ℝ≥0∞ := ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
    P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
      shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue
  let T : ℝ≥0∞ := ENNReal.ofReal (W q x / W q a) * Oa
  have hOa_le : Oa ≤ (ENNReal.ofReal q)⁻¹ := by
    dsimp [Oa]
    calc
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
          P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
            shifted D.X a t ω ∈ A} ∂positiveTimeLebesgue)
          ≤ ∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) * 1 ∂positiveTimeLebesgue := by
            apply lintegral_mono
            intro t
            have hprob : P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
                shifted D.X a t ω ∈ A} ≤ 1 := by
              calc
                P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X a) 0 ω ∧
                    shifted D.X a t ω ∈ A} ≤
                    P (Set.univ : Set Ω) :=
                  measure_mono (μ := P) (Set.subset_univ _)
                _ = 1 := measure_univ
            simpa [mul_comm] using
              (mul_le_mul_left hprob (ENNReal.ofReal (Real.exp (-q * (t : ℝ)))))
      _ = (ENNReal.ofReal q)⁻¹ := by
            simpa using (p2m88_exp_clock_normalization q hq
              (fun _ : ℝ≥0 => (1 : ℝ≥0∞)) measurable_const)
  have hinv_ne : (ENNReal.ofReal q)⁻¹ ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hq).ne'
  have hOa_ne : Oa ≠ ∞ := ne_top_of_le_ne_top hinv_ne hOa_le
  have hT_ne : T ≠ ∞ := by
    dsimp [T]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOa_ne
  have hDens := p2m87_qpos_interval_density_halfline_add_split
    Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
  have hOcc := p2m87_qpos_interval_occupation_halfline_add_split
    Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
  rw [haHalf, hxHalf] at hDens
  change Ox = _ at hDens
  change Ox = _ at hOcc
  have hsum :
      (∫⁻ t : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (t : ℝ))) *
        P {ω | (t : WithTop ℝ≥0) <
          min (tauMinus (shifted D.X x) 0 ω)
            (tauPlus (shifted D.X x) a ω) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue) + T =
      ((volume.restrict (Set.Icc 0 a)).withDensity
        (fun y : ℝ => ENNReal.ofReal
          (killedIntervalDensity (W q) a x y))) A + T := by
    exact hOcc.symm.trans hDens
  exact ((ENNReal.add_left_inj hT_ne).mp hsum).symm
