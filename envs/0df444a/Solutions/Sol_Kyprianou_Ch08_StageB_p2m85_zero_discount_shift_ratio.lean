-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_zero_discount_shift_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:46:16.466726+00:00
-- url     : https://prove2.me/submissions/6a2016f9-1a7b-4da1-b1ae-25a53f579032
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_height_tail_shift_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m85_excursion_quotient
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (hW : HasSourceScaleFamily ψ W) (x : ℝ) :
    Tendsto (fun a : ℝ => W 0 (a-x) / W 0 a)
      atTop (𝓝 (Real.exp (-Phi ψ 0 * x))) := by
  obtain ⟨n, hn, hr, _, _⟩ := source_result8_2_v2 Ω P D ψ W hψ hW 0 le_rfl
  have hf := (hn.2 1 1 zero_lt_one zero_lt_one).1
  have ht := p2m85_height_tail_shift_integral n hf x
  have he := Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := -Phi ψ 0*x)).sub ht)
  simp only [sub_zero] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop (max 1 (x+1))] with a ha
  have hA : 0 < a := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ha)
  have hB : 0 < a-x := by linarith [le_max_right (1:ℝ) (x+1)]
  exact p2m85_excursion_quotient ψ (W 0) n hr a x hA hB
