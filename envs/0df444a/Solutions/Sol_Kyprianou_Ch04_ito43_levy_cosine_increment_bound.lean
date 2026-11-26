-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_cosine_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:10:10.765105+00:00
-- url     : https://prove2.me/submissions/4b9ee2b0-6e6c-47d3-a273-9239f2b108f7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_ProbabilityTheory_leanlevy_chat24_re_one_sub_charFun_eq_integral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A small deterministic Levy increment has a cosine deficit of order its duration.
No second-moment hypothesis on the Levy process is required. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (tr : LevyKhintchineTriple)
    (hc : ∀ (t : NNReal) (ξ : ℝ), charFun (P.map (X t)) ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ))
    (s h : NNReal) (ξ : ℝ)
    (hh : (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ ≤ 1) :
    let F : Ω → ℝ := fun w => 1 - Real.cos (ξ * (X (s+h) w - X s w))
    Integrable F P ∧
      (∀ w, 0 ≤ F w) ∧
      (∫ w, F w ∂P) ≤ 2 * (h : ℝ) * ‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by
  intro F
  let U : Ω → ℝ := fun w => X (s+h) w - X s w
  let g : ℝ → ℝ := fun x => 1 - Real.cos (ξ*x)
  have hm (t : NNReal) := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX t
  have hU : AEMeasurable U P := (hm _).sub (hm _)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hpos (w : Ω) : 0 ≤ F w := sub_nonneg.mpr (Real.cos_le_one _)
  have hF : Integrable F P := by
    apply (integrable_const (2 : ℝ)).mono
      (hg.measurable.comp_aemeasurable hU).aestronglyMeasurable
    filter_upwards [] with w
    change ‖F w‖ ≤ ‖(2 : ℝ)‖
    rw [Real.norm_of_nonneg (hpos w),Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    dsimp [F]
    linarith [Real.neg_one_le_cos (ξ * (X (s+h) w - X s w))]
  have hLaw : P.map U = P.map (X h) := by
    have H := (hX.stationary_increments s h).map_eq
    change P.map (fun w => X (s+h) w - X s w) = P.map (fun w => X h w - X 0 w) at H
    simpa only [U,hX.start_zero,sub_zero] using H
  haveI : IsProbabilityMeasure (P.map (X h)) := Measure.isProbabilityMeasure_map (hm h)
  have hInt : (∫ w, F w ∂P) = (1 - charFun (P.map (X h)) ξ).re := by
    rw [ProbabilityTheory.leanlevy_chat24_re_one_sub_charFun_eq_integral]
    change (∫ w, g (U w) ∂P) = ∫ x, g x ∂(P.map (X h))
    rw [← hLaw,integral_map hU hg.measurable.aestronglyMeasurable]
  refine ⟨hF,hpos,?_⟩
  rw [hInt,hc]
  let z : ℂ := ((h : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent tr ξ
  have hz : ‖z‖ = (h : ℝ)*‖Kyprianou.Ch01.levyTripleExponent tr ξ‖ := by
    simp [z,norm_mul,Real.norm_of_nonneg h.coe_nonneg]
  calc
    (1 - Complex.exp z).re ≤ |(1 - Complex.exp z).re| := le_abs_self _
    _ ≤ ‖1 - Complex.exp z‖ := Complex.abs_re_le_norm _
    _ = ‖Complex.exp z - 1‖ := norm_sub_rev _ _
    _ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le (hz ▸ hh)
    _ = _ := by rw [hz]; ring
