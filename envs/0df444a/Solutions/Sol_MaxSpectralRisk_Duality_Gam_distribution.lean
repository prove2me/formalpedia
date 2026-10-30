-- Prove2me | solution 1 for MaxSpectralRisk.Duality.Gam_distribution
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:41:20.528225+00:00
-- url     : https://prove2.me/submissions/b46f719e-e5e6-4515-9ea0-ea2fefd4a7a1

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRGamAux

instance gam_finite (sig : SpectralFunction) : IsFiniteMeasure (gam sig) := by
  refine ⟨?_⟩
  unfold gam
  rw [Measure.restrict_apply_univ]
  exact measure_Ico_lt_top

lemma sig_nonneg (sig : SpectralFunction) (v : ℝ) : 0 ≤ sig v := by
  rcases lt_or_ge v 0 with h | h
  · exact (sig.eq_zero_of_neg v h).ge
  · have := sig.toStieltjes.mono (show (-1 : ℝ) ≤ v by linarith)
    have h0 := sig.eq_zero_of_neg (-1) (by norm_num)
    show 0 ≤ sig.toStieltjes v
    linarith

lemma leftLim_zero (sig : SpectralFunction) : Function.leftLim sig.toStieltjes 0 = 0 := by
  apply leftLim_eq_of_tendsto
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact (sig.eq_zero_of_neg v hv).symm

lemma gam_Iic_of_mem (sig : SpectralFunction) {v : ℝ} (hv : v ∈ Set.Ico (0 : ℝ) 1) :
    gam sig (Set.Iic v) = ENNReal.ofReal (sig v) := by
  unfold gam
  rw [Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic v ∩ Set.Ico 0 1 = Set.Icc 0 v := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hv.2]⟩
  rw [this, StieltjesFunction.measure_Icc, leftLim_zero, sub_zero]

lemma gam_Iic_of_neg (sig : SpectralFunction) {v : ℝ} (hv : v < 0) :
    gam sig (Set.Iic v) = 0 := by
  unfold gam
  rw [Measure.restrict_apply measurableSet_Iic]
  have : Set.Iic v ∩ Set.Ico 0 1 = ∅ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ico, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2; linarith
  rw [this, measure_empty]

/-- Tonelli: `∫ (u - t)₊ dγσ(t) = ∫_{v ≤ u} γσ((-∞, v]) dv`. -/
lemma fub (sig : SpectralFunction) (u : ℝ) :
    ∫⁻ t, ENNReal.ofReal (u - t) ∂(gam sig) = ∫⁻ v in Set.Iic u, gam sig (Set.Iic v) := by
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ u} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have h1 := Measure.prod_apply (μ := gam sig) (ν := (volume : Measure ℝ)) hS
  have h2 := Measure.prod_apply_symm (μ := gam sig) (ν := (volume : Measure ℝ)) hS
  rw [h1] at h2
  have e1 : ∀ t, Prod.mk t ⁻¹' S = Set.Icc t u := by
    intro t; ext v; simp [S]
  simp only [e1, Real.volume_Icc] at h2
  rw [h2, ← lintegral_indicator measurableSet_Iic]
  congr 1
  funext v
  by_cases hv : v ≤ u
  · rw [Set.indicator_of_mem (show v ∈ Set.Iic u from hv)]
    congr 1
    ext t; simp [S, hv]
  · rw [Set.indicator_of_notMem (show v ∉ Set.Iic u from hv)]
    have : (fun x => (x, v)) ⁻¹' S = ∅ := by
      ext t; simp [S, hv]
    rw [this, measure_empty]

lemma lint_Iic (sig : SpectralFunction) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∫⁻ v in Set.Iic u, gam sig (Set.Iic v) = ENNReal.ofReal (∫ v in (0 : ℝ)..u, sig v) := by
  rw [← Set.Iic_union_Ioc_eq_Iic hu0, lintegral_union measurableSet_Ioc
    (Set.disjoint_left.2 fun x hx hx' => by
      simp only [Set.mem_Iic, Set.mem_Ioc] at hx hx'; linarith)]
  have hA : ∫⁻ v in Set.Iic 0, gam sig (Set.Iic v) = 0 := by
    rw [← setLIntegral_congr (Iio_ae_eq_Iic (μ := (volume : Measure ℝ)))]
    rw [setLIntegral_congr_fun measurableSet_Iio (fun v hv => gam_Iic_of_neg sig hv)]
    simp
  have hB : ∫⁻ v in Set.Ioc 0 u, gam sig (Set.Iic v) =
      ∫⁻ v in Set.Ioc 0 u, ENNReal.ofReal (sig v) := by
    rw [← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ))),
      ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
    refine setLIntegral_congr_fun measurableSet_Ioo (fun v hv => ?_)
    exact gam_Iic_of_mem sig ⟨hv.1.le, by linarith [hv.2]⟩
  rw [hA, zero_add, hB, intervalIntegral.integral_of_le hu0]
  have hint : IntegrableOn (fun v => sig v) (Set.Ioc 0 u) := by
    have := (sig.toStieltjes.mono.intervalIntegrable (μ := volume) (a := 0) (b := u))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hu0).1 this
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun v => sig_nonneg sig v)]

lemma integral_nonneg' (sig : SpectralFunction) {u : ℝ} (hu0 : 0 ≤ u) :
    0 ≤ ∫ v in (0 : ℝ)..u, sig v :=
  intervalIntegral.integral_nonneg hu0 fun v _ => sig_nonneg sig v

end MSRGamAux

open MSRGamAux in
theorem solution (sig : SpectralFunction) :
    (∀ u ∈ Set.Ico (0 : ℝ) 1, (gam sig).real (Set.Iic u) = sig u) ∧
    IsProbabilityMeasure (Gam sig) ∧
    ∀ u ∈ Set.Ico (0 : ℝ) 1,
      (Gam sig).real (Set.Iic u) = (1 - u) * sig u + ∫ v in (0 : ℝ)..u, sig v := by
  refine ⟨fun u hu => ?_, ⟨?_⟩, fun u hu => ?_⟩
  · rw [measureReal_def, gam_Iic_of_mem sig hu, ENNReal.toReal_ofReal (sig_nonneg sig u)]
  · unfold Gam
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, fub sig 1,
      lint_Iic sig zero_le_one le_rfl, sig.integral_eq_one, ENNReal.ofReal_one]
  · have hGam : Gam sig (Set.Iic u) =
        ENNReal.ofReal ((1 - u) * sig u + ∫ v in (0 : ℝ)..u, sig v) := by
      unfold Gam
      rw [withDensity_apply _ measurableSet_Iic]
      have hsplit : ∀ t ∈ Set.Iic u, ENNReal.ofReal (1 - t) =
          ENNReal.ofReal (1 - u) + ENNReal.ofReal (u - t) := by
        intro t ht
        rw [← ENNReal.ofReal_add (by linarith [hu.2]) (by linarith [show t ≤ u from ht])]
        congr 1; ring
      rw [setLIntegral_congr_fun measurableSet_Iic hsplit,
        lintegral_add_left measurable_const, setLIntegral_const,
        gam_Iic_of_mem sig hu]
      have hsupp : (fun t => ENNReal.ofReal (u - t)).support ⊆ Set.Iic u := by
        intro t ht
        simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at ht
        simp only [Set.mem_Iic]; linarith
      rw [setLIntegral_eq_of_support_subset hsupp, fub sig u, lint_Iic sig hu.1 (le_of_lt hu.2),
        ← ENNReal.ofReal_mul (by linarith [hu.2]),
        ← ENNReal.ofReal_add (mul_nonneg (by linarith [hu.2]) (sig_nonneg sig u))
          (integral_nonneg' sig hu.1)]
    rw [measureReal_def, hGam, ENNReal.toReal_ofReal
      (add_nonneg (mul_nonneg (by linarith [hu.2]) (sig_nonneg sig u)) (integral_nonneg' sig hu.1))]
