-- Prove2me | solution 1 for Kyprianou.Ch04.pathTimeWeightDCTV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:16.103875+00:00
-- url     : https://prove2.me/submissions/5d460808-b292-4afd-95fe-9de2ddab11ad

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A bounded continuous time-state weight passes through a pointwise path limit on a compact clock. -/
theorem solution (Y : ℕ → NNReal → ℝ) (X : NNReal → ℝ)
    (g : ℝ → ℝ → ℝ) (K : ℝ) (T : NNReal)
    (hY : ∀ n, Measurable (Y n)) (hX : Measurable X)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hK : ∀ s x, 0 ≤ s → |g s x| ≤ K)
    (h : ∀ t : NNReal, 0 < t → t ≤ T →
      Tendsto (fun n => Y n t) atTop (𝓝 (X t))) :
    Tendsto (fun n => ∫ s in Icc (0 : ℝ) (T : ℝ), g s (Y n s.toNNReal)) atTop
      (𝓝 (∫ s in Icc (0 : ℝ) (T : ℝ), g s (X s.toNNReal))) := by
  let A := Icc (0 : ℝ) (T : ℝ)
  let μ := volume.restrict A
  haveI : IsFiniteMeasure μ := ⟨by simp [μ,A,Real.volume_Icc]⟩
  have hmeas (Z : NNReal → ℝ) (hZ : Measurable Z) :
      AEStronglyMeasurable (fun s : ℝ => g s (Z s.toNNReal)) μ := by
    have hgc : Continuous (fun p : ℝ × ℝ => g (max 0 p.1) p.2) := by
      exact hg.comp_continuous ((continuous_const.max continuous_fst).prodMk continuous_snd)
        (fun p => ⟨(show (max 0 p.1) ∈ Ici (0 : ℝ) by simp),mem_univ _⟩)
    have hm : Measurable (fun s : ℝ => g (max 0 s) (Z s.toNNReal)) :=
      hgc.measurable.comp (measurable_id.prodMk (hZ.comp measurable_real_toNNReal))
    apply hm.aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := volume) (show MeasurableSet A from measurableSet_Icc)] with s hs
    simp [max_eq_right hs.1]
  have hpos : ∀ᵐ s ∂μ, 0 < s ∧ s ≤ (T : ℝ) := by
    have hmem : ∀ᵐ s ∂μ, s ∈ A := ae_restrict_mem measurableSet_Icc
    have hzero : ∀ᵐ s ∂μ, s ≠ 0 :=
      ae_restrict_of_ae (by simpa using (show ∀ᵐ s : ℝ ∂volume, s ∉ ({0} : Set ℝ) from
        ae_iff.mpr (by simp)))
    filter_upwards [hmem,hzero] with s hs hz
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hz),hs.2⟩
  apply tendsto_integral_of_dominated_convergence (fun _ => K)
    (fun n => hmeas (Y n) (hY n)) (integrable_const K)
  · intro n
    filter_upwards [hpos] with s hs
    simpa [Real.norm_eq_abs] using hK s (Y n s.toNNReal) hs.1.le
  · filter_upwards [hpos] with s hs
    have hp : Tendsto (fun n => (s,Y n s.toNNReal)) atTop
        (𝓝[Ici (0 : ℝ) ×ˢ (univ : Set ℝ)] (s,X s.toNNReal)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_const_nhds.prodMk_nhds (h _ (Real.toNNReal_pos.mpr hs.1)
          (Real.toNNReal_le_iff_le_coe.mpr hs.2)),Eventually.of_forall fun _ => ⟨(show s ∈ Ici (0 : ℝ) from hs.1.le),mem_univ _⟩⟩
    exact (hg (s,X s.toNNReal) ⟨hs.1.le,mem_univ _⟩).tendsto.comp hp
