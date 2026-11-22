-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_upper_positive_discount
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:20:47.185938+00:00
-- url     : https://prove2.me/submissions/76a5930e-d166-491a-b71a-699665dcd99b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_scale_transfer_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_bridge_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_bv_exit_ratio_no_standing_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_exit_ratio_unbounded_public
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_negative_start_payoff_zero_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open AvramDividend.Classical Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (q x a : ℝ) (hq : 0 < q) (ha : 0 < a) (hxa : x ≤ a) :
    upBeforeDownExpectation P D.X q x a = W q x / W q a := by
  classical
  obtain ⟨F, A, hpaths, hexp⟩ := source_result81_filtered_avram_model Ω P D ψ hψ
  have hnotneg : ¬ (∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω)) := by
    intro h
    apply D.excludesNegativeSubordinator
    filter_upwards [hpaths, h] with ω heq hant
    intro s t hst
    simpa only [heq] using hant hst
  have hqscale := hW q hq.le
  have hscale := source_result81_upper_scale_transfer_public A ψ hexp hnotneg q hq (W q) hqscale
  have hpayoff := source_result81_upper_payoff_bridge_public D A hpaths q x a
  have hψ0 : ψ 0 = 0 := by
    simpa only [SpectrallyNegativeModel.toData, zero_mul, Real.exp_zero, integral_const,
      probReal_univ, one_smul, Real.log_one, zero_div] using (hψ 0 1 le_rfl zero_lt_one).2
  have hφ0 : 0 ≤ Phi ψ q := hqscale.1.2.1.1
  have hrootψ : ψ (Phi ψ q) = q := hqscale.1.2.1.2
  have hφpos : 0 < Phi ψ q := by
    by_contra! hn
    have hh : Phi ψ q = 0 := le_antisymm hn hφ0
    rw [hh, hψ0] at hrootψ
    linarith
  have hrootA : A.ψ (Phi ψ q) = q := (hexp (Phi ψ q) hφ0).trans hrootψ
  have hnonratio : 0 ≤ W q x / W q a :=
    div_nonneg (hqscale.2.2.1 x) (hqscale.2.2.1 a)
  by_cases hx0 : 0 ≤ x
  · by_cases hBV : A.BoundedVariation
    · rw [hpayoff, source_result81_bv_exit_ratio_no_standing_public A q (Phi ψ q)
        hq hφpos hrootA (W q) hscale hBV a x ha hx0 hxa]
      exact ENNReal.toReal_ofReal hnonratio
    · rw [hpayoff, source_result81_upper_exit_ratio_unbounded_public A q hq
        (W q) hscale hBV a x ha hx0 hxa]
      exact ENNReal.toReal_ofReal hnonratio
  · have hxneg : x < 0 := lt_of_not_ge hx0
    unfold upBeforeDownExpectation
    rw [integral_congr_ae
      (source_result81_upper_negative_start_payoff_zero_public D A hpaths q x a hxneg)]
    simp only [Pi.zero_apply, integral_zero, hqscale.2.1 x hxneg, zero_div]
