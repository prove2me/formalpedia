-- Prove2me | solution 1 for GraphonMF.DenseLLN.lusin_approx
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:48:06.072148+00:00
-- url     : https://prove2.me/submissions/1780f168-d298-4bb7-80c4-e130e3ab1b93

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GMF2Lusin
open GraphonMF.Stability

lemma opNorm_le_L1 (W : I → I → ℝ) (hW : Measurable (Function.uncurry W))
    (hb : ∀ u v, |W u v| ≤ 1) :
    opNorm W ≤ ∫ p : I × I, |W p.1 p.2| := by
  have hint : Integrable (fun p : I × I => |W p.1 p.2|) (volume : Measure (I × I)) := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (hW.abs).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by simpa using hb p.1 p.2
  have h0 : 0 ≤ ∫ p : I × I, |W p.1 p.2| := integral_nonneg fun _ => abs_nonneg _
  unfold opNorm
  refine Real.iSup_le (fun g => Real.iSup_le (fun hg => ?_) h0) h0
  have hprod : ∫ p : I × I, |W p.1 p.2| = ∫ u, ∫ v, |W u v| := by
    rw [show (volume : Measure (I × I)) = (volume : Measure I).prod volume from rfl]
    exact integral_prod _ hint
  rw [hprod]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
  · exact hint.integral_prod_left
  · refine Filter.Eventually.of_forall fun u => ?_
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
    · refine Integrable.of_bound (C := 1) ?_ ?_
      · exact (hW.comp (measurable_const.prodMk measurable_id)).abs.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun v => by simpa using hb u v
    · refine Filter.Eventually.of_forall fun v => ?_
      simp only [abs_mul]
      have := hg.2 v
      calc |W u v| * |g v| ≤ |W u v| * 1 := by gcongr
        _ = |W u v| := mul_one _

end GMF2Lusin

open GraphonMF.Stability GMF2Lusin in
theorem solution (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ G' : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ, GraphonMF.Stability.IsGraphon G' ∧ Continuous (Function.uncurry G') ∧
      GraphonMF.Stability.opNorm (fun u v => G' u v - G u v) < η := by
  obtain ⟨hGm, hGs, hGr⟩ := hG
  have hFint : Integrable (fun p : I × I => G p.1 p.2) (volume : Measure (I × I)) := by
    refine Integrable.of_bound (C := 1) hGm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun p => ?_
    have := hGr p.1 p.2
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  obtain ⟨h, hh, -⟩ := hFint.exists_boundedContinuous_integral_sub_le (half_pos hη)
  set c : I × I → ℝ := fun p => max 0 (min 1 (h p)) with hc
  have hcc : Continuous c := by
    exact continuous_const.max (continuous_const.min h.continuous)
  have hcr : ∀ p, c p ∈ Set.Icc (0 : ℝ) 1 := fun p =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcF : ∀ p, |G p.1 p.2 - c p| ≤ |G p.1 p.2 - h p| := by
    intro p
    have hr := hGr p.1 p.2
    have e : G p.1 p.2 = max 0 (min 1 (G p.1 p.2)) := by
      rw [min_eq_right hr.2, max_eq_right hr.1]
    rw [e]
    calc |max 0 (min 1 (G p.1 p.2)) - c p| = |min 1 (G p.1 p.2) ⊔ 0 - min 1 (h p) ⊔ 0| := by
            simp [c, max_comm]
      _ ≤ |min 1 (G p.1 p.2) - min 1 (h p)| := abs_max_sub_max_le_abs _ _ _
      _ ≤ |G p.1 p.2 - h p| := by
            have := abs_min_sub_min_le_max (1:ℝ) (G p.1 p.2) 1 (h p)
            simpa using this
      _ = |max 0 (min 1 (G p.1 p.2)) - h p| := by rw [← e]
  set G' : I → I → ℝ := fun u v => (c (u, v) + c (v, u)) / 2 with hG'
  have hG'c : Continuous (Function.uncurry G') := by
    have h1 : Continuous fun p : I × I => c p := hcc
    have h2 : Continuous fun p : I × I => c p.swap := hcc.comp continuous_swap
    exact (h1.add h2).div_const 2
  refine ⟨G', ⟨hG'c.measurable, fun u v => by simp [G', add_comm], fun u v => ?_⟩, hG'c, ?_⟩
  · have a := hcr (u, v); have b := hcr (v, u)
    constructor <;> simp only [G'] <;> linarith [a.1, a.2, b.1, b.2]
  · have hcint : Integrable (fun p : I × I => |G p.1 p.2 - c p|) (volume : Measure (I × I)) := by
      refine Integrable.of_bound (C := 2) ((hGm.sub hcc.measurable).abs).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun p => ?_
      have := hcr p; have hr := hGr p.1 p.2
      rw [Real.norm_eq_abs, abs_abs, abs_le]; constructor <;> linarith [this.1, this.2, hr.1, hr.2]
    have hbound : ∀ u v, |G' u v - G u v| ≤ 1 := by
      intro u v
      have a := hcr (u, v); have b := hcr (v, u); have hr := hGr u v
      rw [abs_le]; constructor <;> simp only [G'] <;> linarith [a.1, a.2, b.1, b.2, hr.1, hr.2]
    have hmeas : Measurable (Function.uncurry fun u v => G' u v - G u v) :=
      hG'c.measurable.sub hGm
    refine (opNorm_le_L1 _ hmeas hbound).trans_lt ?_
    have hpt : ∀ p : I × I, |G' p.1 p.2 - G p.1 p.2| ≤
        (|G p.1 p.2 - c p| + |G p.2 p.1 - c p.swap|) / 2 := by
      intro p
      have hs : G p.1 p.2 = G p.2 p.1 := hGs p.1 p.2
      simp only [G']
      rw [show (c (p.1, p.2) + c (p.2, p.1)) / 2 - G p.1 p.2 =
        -(((G p.1 p.2 - c p) + (G p.2 p.1 - c p.swap)) / 2) by
          rw [show ((p.1, p.2) : I × I) = p from rfl]
          have : (p.2, p.1) = p.swap := rfl
          rw [this]; linarith]
      rw [abs_neg, abs_div, abs_two]
      gcongr
      exact abs_add_le _ _
    have hswap : ∫ p : I × I, |G p.2 p.1 - c p.swap| = ∫ p : I × I, |G p.1 p.2 - c p| := by
      rw [show (volume : Measure (I × I)) = (volume : Measure I).prod volume from rfl]
      exact integral_prod_swap (fun p : I × I => |G p.1 p.2 - c p|)
    calc ∫ p : I × I, |G' p.1 p.2 - G p.1 p.2|
        ≤ ∫ p : I × I, (|G p.1 p.2 - c p| + |G p.2 p.1 - c p.swap|) / 2 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_
            (Filter.Eventually.of_forall hpt)
          refine (hcint.add ?_).div_const 2
          rw [show (volume : Measure (I × I)) = (volume : Measure I).prod volume from rfl]
          exact hcint.swap
      _ = ∫ p : I × I, |G p.1 p.2 - c p| := by
          rw [integral_div, integral_add hcint, hswap]
          · ring
          · rw [show (volume : Measure (I × I)) = (volume : Measure I).prod volume from rfl]
            exact hcint.swap
      _ ≤ ∫ p : I × I, ‖G p.1 p.2 - h p‖ := by
          refine integral_mono hcint ?_ fun p => ?_
          · exact (hFint.sub (h.integrable _)).norm
          · simpa [Real.norm_eq_abs] using hcF p
      _ ≤ η / 2 := hh
      _ < η := half_lt_self hη
