-- Prove2me | solution 1 for Kyprianou.Ch03.rawEsscherUnitFromMomentsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T22:55:46.713547+00:00
-- url     : https://prove2.me/submissions/4c4a5a4c-6b9b-414b-9769-dc6fd6136e5d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_stableLevyLogMomentTimeScalingV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ)
    (hi : ∀ t, Integrable (fun w => Real.exp (beta * X t w)) P) :
    let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
    ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1 := by
  let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
  have hmoment (u : NNReal) :
      (∫ w, Real.exp (beta * X u w) ∂P) = Real.exp ((u : ℝ) * k) := by
    let G := ∫⁻ w, ENNReal.ofReal (Real.exp (beta * X u w)) ∂P
    have hG : G ≠ 0 := by
      intro hz
      have hme := ENNReal.measurable_ofReal.comp_aemeasurable (hi u).aestronglyMeasurable.aemeasurable
      obtain ⟨w, hw⟩ := ((lintegral_eq_zero_iff' hme).1 hz).exists
      exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hw
    have hfin : G ≠ ⊤ := (hi u).lintegral_lt_top.ne
    have hR : (∫ w, Real.exp (beta * X u w) ∂P) = G.toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun w => (Real.exp_pos _).le) (hi u).aestronglyMeasurable
    have hpos : 0 < (∫ w, Real.exp (beta * X u w) ∂P) := by
      rw [hR]
      exact ENNReal.toReal_pos hG hfin
    have hlog := Kyprianou.Ch03.stableLevyLogMomentTimeScalingV1 P X hX beta hi u
    change _ = (u : ℝ) * k at hlog
    rw [← hlog, Real.exp_log hpos]
  have hunit (u : NNReal) : Integrable (esscherDensity X beta k u) P ∧
      (∫ w, esscherDensity X beta k u w ∂P) = 1 := by
    have he : esscherDensity X beta k u =
        fun w => Real.exp (-(k * (u : ℝ))) * Real.exp (beta * X u w) := by
      funext w
      dsimp only [esscherDensity]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    refine ⟨(hi u).const_mul _, ?_⟩
    rw [integral_const_mul, hmoment u, ← Real.exp_add]
    have hzero : -(k * (u : ℝ)) + (u : ℝ) * k = 0 := by ring
    rw [hzero, Real.exp_zero]
  exact hunit
