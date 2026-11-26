-- Prove2me | solution 1 for LowerSemicontinuous.lintegral_le_liminf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:54.68135+00:00
-- url     : https://prove2.me/submissions/1fd8ae17-8d56-4468-b193-ff0d414aea03

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LintegralLsc
import Theorems.Thm_LowerSemicontinuous_lintegral_le_liminf_of_ne_top
section
open MeasureTheory Filter Set Topology
open scoped ENNReal
private lemma ennreal_iSup_min_natCast' (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  rcases eq_or_ne a ∞ with rfl | ha
  · have hmin : ∀ n : ℕ, min (∞ : ℝ≥0∞) (n : ℝ≥0∞) = (n : ℝ≥0∞) := fun n =>
      min_eq_right le_top
    simp only [hmin]
    exact ENNReal.iSup_natCast.ge
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (min_eq_left hn.le).ge
section SequentialBound
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]
end SequentialBound
end

set_option autoImplicit false
open MeasureTheory Filter Set Topology
open scoped ENNReal
variable {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [OpensMeasurableSpace W]
namespace LowerSemicontinuous
theorem _root_.solution
    {μ : Measure W} {μs : ℕ → Measure W} {f : W → ℝ≥0∞}
    (hf : LowerSemicontinuous f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf fun i => μs i G) :
    ∫⁻ x, f x ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := by
  -- the truncations are again lower semicontinuous
  have h_trunc_lsc : ∀ n : ℕ, LowerSemicontinuous fun x => min (f x) (n : ℝ≥0∞) := by
    intro n x y hy
    filter_upwards [hf x y (hy.trans_le (min_le_left _ _))] with z hz
    exact lt_min hz (hy.trans_le (min_le_right _ _))
  -- each truncation satisfies the liminf bound for the untruncated integrals
  have h_bound : ∀ n : ℕ,
      ∫⁻ x, min (f x) (n : ℝ≥0∞) ∂μ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := fun n =>
    ((h_trunc_lsc n).lintegral_le_liminf_of_ne_top
        (fun x => ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _))
        h_opens).trans
      (liminf_le_liminf
        (Eventually.of_forall fun i => lintegral_mono fun x => min_le_left _ _))
  -- monotone convergence for the truncations
  calc ∫⁻ x, f x ∂μ
      = ⨆ n : ℕ, ∫⁻ x, min (f x) (n : ℝ≥0∞) ∂μ := by
        rw [← lintegral_iSup (fun n => hf.measurable.min measurable_const)
            (fun n m hnm x => min_le_min le_rfl (by exact_mod_cast hnm))]
        exact lintegral_congr fun x => (ennreal_iSup_min_natCast' (f x)).symm
    _ ≤ atTop.liminf fun i => ∫⁻ x, f x ∂(μs i) := iSup_le h_bound
end LowerSemicontinuous
