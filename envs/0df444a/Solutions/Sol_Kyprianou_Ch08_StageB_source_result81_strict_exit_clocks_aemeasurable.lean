-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_strict_exit_clocks_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T14:16:59.780626+00:00
-- url     : https://prove2.me/submissions/34c4f0e0-4e0f-40ac-afe8-c429d2d9fe2b

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem lower_clock_eq_rational_iInf
    (f : ℝ≥0 → ℝ) (hright : ∀ t, ContinuousWithinAt f (Ici t) t) :
    tauMinus (fun s (_ : Unit) => f s) 0 () =
      ⨅ r : ℚ, if 0 < (r : ℝ).toNNReal ∧ f (r : ℝ).toNNReal < 0 then
        ((r : ℝ).toNNReal : ℝ≥0∞) else ⊤ := by
  let k : ℚ → ℝ≥0 := fun r => (r : ℝ).toNNReal
  let C : ℚ → ℝ≥0∞ := fun r => if 0 < k r ∧ f (k r) < 0 then k r else ⊤
  let S : Set ℝ≥0∞ := {y | ∃ u : ℝ≥0, 0 < u ∧ (u : ℝ≥0∞) = y ∧ f u < 0}
  change sInf S = ⨅ r, C r
  apply le_antisymm
  · apply le_iInf
    intro r
    by_cases h : 0 < k r ∧ f (k r) < 0
    · rw [show C r = (k r : ℝ≥0∞) from if_pos h]
      exact sInf_le ⟨k r, h.1, rfl, h.2⟩
    · simp [C, h]
  · apply le_sInf
    rintro _ ⟨u, hu, rfl, hfu⟩
    by_contra! hlt
    obtain ⟨w, huw, hw⟩ := exists_between hlt
    obtain ⟨v, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hw.trans_le le_top))
    obtain ⟨b, hub, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.mp ((hright u) (Iio_mem_nhds hfu))
    obtain ⟨r, hur, hrm⟩ := exists_rat_btwn
      (show (u : ℝ) < (min v b : ℝ≥0) by exact_mod_cast lt_min (WithTop.coe_lt_coe.mp huw) hub)
    have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ (by linarith [u.coe_nonneg])
    have huk : u < k r := by exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkm : k r < min v b := by
      exact_mod_cast (show (k r : ℝ) < (min v b : ℝ≥0) by rwa [hcoe])
    have hneg : f (k r) < 0 := hsub ⟨huk.le, hkm.trans_le (min_le_right _ _)⟩
    have hkv : C r < (v : ℝ≥0∞) := by
      rw [show C r = (k r : ℝ≥0∞) from if_pos ⟨hu.trans huk, hneg⟩]
      exact WithTop.coe_lt_coe.mpr (hkm.trans_le (min_le_left _ _))
    exact (not_le_of_gt (hkv.trans hw)) (iInf_le C r)

private theorem lower_clock_aemeasurable
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℝ≥0 → Ω → ℝ) (hm : ∀ t, AEMeasurable (f t) P)
    (hr : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun s => f s ω) (Ici t) t) :
    AEMeasurable (fun ω => (tauMinus f 0 ω : ℝ≥0∞)) P := by
  let k : ℚ → ℝ≥0 := fun r => (r : ℝ).toNNReal
  have hparts (r : ℚ) : AEMeasurable (fun ω =>
      if 0 < k r ∧ f (k r) ω < 0 then (k r : ℝ≥0∞) else ⊤) P := by
    by_cases h : 0 < k r
    · simp only [h, true_and]
      have hg : Measurable (fun z : ℝ => if z < 0 then (k r : ℝ≥0∞) else ⊤) :=
        Measurable.ite (measurableSet_lt measurable_id measurable_const)
          measurable_const measurable_const
      exact hg.comp_aemeasurable (hm (k r))
    · simpa only [h, false_and, if_false] using
        (aemeasurable_const : AEMeasurable (fun _ : Ω => (⊤ : ℝ≥0∞)) P)
  refine (AEMeasurable.iInf hparts).congr ?_
  filter_upwards [hr] with ω hc
  exact (lower_clock_eq_rational_iInf (fun t => f t ω) hc).symm

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (x a : ℝ) :
    AEMeasurable (fun ω => (tauPlus (shifted D.X x) a ω : ℝ≥0∞)) P ∧
      AEMeasurable (fun ω => (tauMinus (shifted D.X x) 0 ω : ℝ≥0∞)) P := by
  have hX (t : ℝ≥0) : AEMeasurable (D.X t) P := by
    have hi := (D.levy.stationary_increments 0 t).aemeasurable_snd
    change AEMeasurable (fun ω => D.X t ω - D.X 0 ω) P at hi
    simpa only [D.levy.start_zero, sub_zero] using hi
  have hshift (t : ℝ≥0) : AEMeasurable (shifted D.X x t) P :=
    aemeasurable_const.add (hX t)
  have hright : ∀ᵐ ω ∂P, ∀ t,
      ContinuousWithinAt (fun s => shifted D.X x s ω) (Ici t) t := by
    filter_upwards [D.levy.cadlag_ae] with ω h
    exact fun t => continuous_const.continuousWithinAt.add (h t).1
  refine ⟨?_, lower_clock_aemeasurable (shifted D.X x) hshift hright⟩
  have H := lower_clock_aemeasurable (fun t ω => a - shifted D.X x t ω)
    (fun t => aemeasurable_const.sub (hshift t)) (by
      filter_upwards [hright] with ω h
      exact fun t => continuous_const.continuousWithinAt.sub (h t))
  simpa only [tauPlus, tauMinus, sub_lt_zero] using H
