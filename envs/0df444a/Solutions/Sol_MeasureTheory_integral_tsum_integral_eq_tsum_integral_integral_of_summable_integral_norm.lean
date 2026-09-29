-- Prove2me | solution 1 for MeasureTheory.integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3004fe50-c451-5322-af86-8ff367e684c5

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm

set_option autoImplicit false

open MeasureTheory

namespace Interchange21

open Filter Topology ENNReal

theorem integrable_tsum_of_summable_integral_norm {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {ι : Type*} [Countable ι] {F : ι → α → ℂ}
    (hF_int : ∀ i : ι, Integrable (F i) μ) (hF_sum : Summable fun i => ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a => ∑' i, F i a) μ := by
  have hmeas : ∀ i, AEMeasurable (fun a => ‖F i a‖ₑ) μ := fun i => (hF_int i).1.enorm
  have hfin : ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ < ∞ := by
    have heq : ∀ i, ∫⁻ a, ‖F i a‖ₑ ∂μ = ENNReal.ofReal (∫ a, ‖F i a‖ ∂μ) := fun i =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF_int i)).symm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun a => norm_nonneg _) hF_sum]
    exact ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · exact (AEMeasurable.tsum fun i => (hF_int i).1.aemeasurable).aestronglyMeasurable
  · show ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ < ∞
    calc ∫⁻ a, ‖∑' i, F i a‖ₑ ∂μ ≤ ∫⁻ a, ∑' i, ‖F i a‖ₑ ∂μ := lintegral_mono fun a => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ a, ‖F i a‖ₑ ∂μ := lintegral_tsum hmeas
      _ < ∞ := hfin

end Interchange21

theorem solution
    {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [Countable ι]
    (H : ι → X × Y → ℂ) (hH : ∀ i, Integrable (H i) (μ.prod ν))
    (hS : Summable fun i => ∫ p, ‖H i p‖ ∂(μ.prod ν)) :
    (∀ i, Integrable (fun x => ∫ y, H i (x, y) ∂ν) μ) ∧
    (∀ i, Integrable (fun y => ∫ x, H i (x, y) ∂μ) ν) ∧
    (Summable fun i => ∫ x, ‖∫ y, H i (x, y) ∂ν‖ ∂μ) ∧
    (Summable fun i => ∫ y, ‖∫ x, H i (x, y) ∂μ‖ ∂ν) ∧
    Integrable (fun y => ∑' i, ∫ x, H i (x, y) ∂μ) ν ∧
    ∫ y, ∑' i, ∫ x, H i (x, y) ∂μ ∂ν = ∑' i, ∫ x, ∫ y, H i (x, y) ∂ν ∂μ := by

  have hF : ∀ i, Integrable (fun x => ∫ y, H i (x, y) ∂ν) μ := fun i => (hH i).integral_prod_left
  have hG : ∀ i, Integrable (fun y => ∫ x, H i (x, y) ∂μ) ν := fun i => (hH i).integral_prod_right

  have hFb : ∀ i, ∫ x, ‖∫ y, H i (x, y) ∂ν‖ ∂μ ≤ ∫ p, ‖H i p‖ ∂(μ.prod ν) := by
    intro i
    rw [integral_prod (fun p => ‖H i p‖) (hH i).norm]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) (hH i).norm.integral_prod_left
      (Filter.Eventually.of_forall fun x => norm_integral_le_integral_norm _)
  have hGb : ∀ i, ∫ y, ‖∫ x, H i (x, y) ∂μ‖ ∂ν ≤ ∫ p, ‖H i p‖ ∂(μ.prod ν) := by
    intro i
    rw [integral_prod_symm (fun p => ‖H i p‖) (hH i).norm]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) (hH i).norm.integral_prod_right
      (Filter.Eventually.of_forall fun y => norm_integral_le_integral_norm _)
  have hSF : Summable fun i => ∫ x, ‖∫ y, H i (x, y) ∂ν‖ ∂μ :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) hFb hS
  have hSG : Summable fun i => ∫ y, ‖∫ x, H i (x, y) ∂μ‖ ∂ν :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _) hGb hS
  refine ⟨hF, hG, hSF, hSG, Interchange21.integrable_tsum_of_summable_integral_norm hG hSG, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hG hSG]
  congr 1
  funext i
  rw [← integral_prod_symm (H i) (hH i), integral_prod (H i) (hH i)]

end S_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm
end P2MW
export P2MW.S_MeasureTheory_integral_tsum_integral_eq_tsum_integral_integral_of_summable_integral_norm (solution)
