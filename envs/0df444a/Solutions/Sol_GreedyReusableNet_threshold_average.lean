-- Prove2me | solution 1 for GreedyReusableNet.threshold_average
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:43:45.450871+00:00
-- url     : https://prove2.me/submissions/5a3f3caf-f1a8-4356-b202-5717c2b526c5

import Mathlib
import Definitions.Def_GreedyReusableNet_thresholdLaw

open MeasureTheory

open GreedyReusableNet in
theorem solution (a b x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hax : a ≤ x) (hxb : x ≤ b) :
    ∫ r, (if r ≤ x then r else 0) ∂(thresholdLaw a b) = x / (1 + Real.log (b / a)) := by
  set L := Real.log (b / a) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  set K := 1 + L with hK
  have hK0 : 0 < K := by linarith
  set f : ℝ → ℝ := fun r => if r ≤ x then r else 0 with hf
  set g : ℝ → ENNReal := fun r => ENNReal.ofReal (1 / (K * r)) with hg
  have hgm : Measurable g := by
    apply Measurable.ennreal_ofReal
    exact measurable_const.div (measurable_const.mul measurable_id)
  have hglt : ∀ᵐ r ∂(volume.restrict (Set.Ioc a b)), g r < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  -- the density part as an indicator
  set c : ℝ := 1 / K with hc
  have hpt : ∀ r ∈ Set.Ioc a b, (g r).toReal • f r = (Set.Iic x).indicator (fun _ => c) r := by
    intro r hr
    have hr0 : 0 < r := lt_trans ha hr.1
    simp only [hg, hf, smul_eq_mul, Set.indicator_apply, Set.mem_Iic]
    rw [ENNReal.toReal_ofReal (by positivity)]
    split_ifs with h
    · rw [hc]; field_simp
    · ring
  have hae : (fun r => (g r).toReal • f r) =ᵐ[volume.restrict (Set.Ioc a b)]
      (Set.Iic x).indicator (fun _ => c) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt)
  have hfin : (volume.restrict (Set.Ioc a b)) (Set.Iic x) ≠ ⊤ := by
    rw [Measure.restrict_apply measurableSet_Iic]
    apply ne_top_of_le_ne_top (b := volume (Set.Ioc a b))
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    · exact measure_mono Set.inter_subset_right
  have hind_int : Integrable ((Set.Iic x).indicator (fun _ => c)) (volume.restrict (Set.Ioc a b)) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact integrableOn_const hfin
  have h2 : Integrable f ((volume.restrict (Set.Ioc a b)).withDensity g) := by
    rw [integrable_withDensity_iff_integrable_smul' hgm hglt]
    exact hind_int.congr hae.symm
  have h1 : Integrable f (ENNReal.ofReal (1 / K) • Measure.dirac a) := by
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact integrable_dirac (by simp)
  have hthr : thresholdLaw a b = ENNReal.ofReal (1 / K) • Measure.dirac a +
      (volume.restrict (Set.Ioc a b)).withDensity g := rfl
  show ∫ r, f r ∂(thresholdLaw a b) = x / K
  rw [hthr, integral_add_measure h1 h2, integral_smul_measure, integral_dirac,
    integral_withDensity_eq_integral_toReal_smul hgm hglt, integral_congr_ae hae,
    integral_indicator measurableSet_Iic, setIntegral_const, Measure.real,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic x ∩ Set.Ioc a b = Set.Ioc a x := by
    ext r; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, le_trans h2 hxb⟩
  have hxa : (0 : ℝ) ≤ x - a := by linarith
  have hKi : (0 : ℝ) ≤ 1 / K := by positivity
  rw [hset, Real.volume_Ioc, ENNReal.toReal_ofReal hxa, ENNReal.toReal_ofReal hKi]
  simp only [hf, if_pos hax, smul_eq_mul, hc]
  field_simp
  ring
