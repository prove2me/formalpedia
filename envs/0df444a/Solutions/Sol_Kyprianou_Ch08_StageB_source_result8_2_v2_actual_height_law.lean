-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_actual_height_law
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:09:02.666962+00:00
-- url     : https://prove2.me/submissions/18615cc2-c0f3-4d4c-afcd-ca25406a496e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_exists_pos_tail_measure_of_log_stieltjes_link
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_regularity
import Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_tail_multiplicative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Exact survival functional S from the original no-drawdown event. -/
noncomputable def survivalS_b2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (q : ℝ) (a h : ℝ) : ℝ :=
  ∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω},
    Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P

/-- Actual tail F = -log S(1,·) from the process law. -/
noncomputable def tailF_b2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  fun h => -Real.log (survivalS_b2 P D ψ q 1 h)

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ n : Measure ℝ, HasActualQExcursionHeightLaw P D ψ q n := by
  have hPhi : PhiIsLargestRoot ψ q := (hW q hq).1
  have hB := Kyprianou.Ch08.StageB.actual_height_tail_bounds P D ψ W hψ hW q hq
  have hR := Kyprianou.Ch08.StageB.actual_height_tail_regularity P D ψ W hψ hW q hq
  have hM := Kyprianou.Ch08.StageB.actual_height_tail_multiplicative P D ψ W hψ hW q hq
  obtain ⟨hGanti, hGcont, hGtop, hlink⟩ := hR
  have hGanti' : AntitoneOn (tailF_b2 P D ψ q) (Set.Ioi 0) := hGanti
  have hGcont' : ∀ h₀ : ℝ, 0 < h₀ → ContinuousWithinAt (tailF_b2 P D ψ q) (Set.Ici h₀) h₀ := hGcont
  have hGtop' : Tendsto (tailF_b2 P D ψ q) atTop (nhds 0) := hGtop
  have hlink' : ∀ y : ℝ, 0 < y → Tendsto (fun s => -(tailF_b2 P D ψ q s)) (nhdsWithin y (Set.Iio y)) (nhds (-(tailF_b2 P D ψ q y))) := hlink
  obtain ⟨mu, htail, hfin⟩ := Kyprianou.Ch08.StageB.exists_pos_tail_measure_of_log_stieltjes_link
    (tailF_b2 P D ψ q) (tailF_b2 P D ψ q) hGanti' hGcont' hGtop' hlink'
  refine ⟨mu, hPhi, ?_⟩
  intro a h ha hh
  have hnn : 0 ≤ tailF_b2 P D ψ q h := by
    have hb := hB h hh
    have hlog : Real.log (survivalS_b2 P D ψ q 1 h) ≤ 0 := Real.log_nonpos hb.1.le hb.2
    simp only [tailF_b2]
    linarith
  have hTR : (mu (Set.Ici h)).toReal = tailF_b2 P D ψ q h := by
    rw [htail h hh]
    exact ENNReal.toReal_ofReal hnn
  constructor
  · exact hfin h hh
  · have hEq : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X a h ω},
        Real.exp (Phi ψ q * a) * discountedAt q (tauPlus D.X a ω) ∂P) =
        survivalS_b2 P D ψ q a h := rfl
    have hm := hM a h ha hh
    have hm' : survivalS_b2 P D ψ q a h = Real.exp (-a * tailF_b2 P D ψ q h) := hm
    rw [hEq, hm', hTR]
