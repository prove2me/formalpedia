-- Prove2me | solution 1 for MaxSpectralRisk.Duality.es_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:47:33.744791+00:00
-- url     : https://prove2.me/submissions/6a5f4d8d-7a6a-427f-b8a6-4d4b8102d316

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

open MeasureTheory Filter Topology MaxSpectralRisk.Duality

namespace MSRQuant

variable {W : Type*} [MeasurableSpace W]

lemma F_eq (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L) (x : ℝ) :
    π.real {p | L p ≤ x} = ProbabilityTheory.cdf (π.map L) x := by
  haveI : IsProbabilityMeasure (π.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, map_measureReal_apply hL measurableSet_Iic]
  rfl

lemma quantile_le_iff (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) 1) (x : ℝ) :
    quantile π L u ≤ x ↔ u ≤ π.real {p | L p ≤ x} := by
  haveI : IsProbabilityMeasure (π.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  set F := ProbabilityTheory.cdf (π.map L) with hF
  unfold quantile
  simp_rw [F_eq π hL]
  set S := {y | u ≤ F y} with hS
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atTop
      (μ := π.map L))).1 u hu.2).exists
    exact ⟨y, hy.le⟩
  have hbdd : BddBelow S := by
    obtain ⟨y0, hy0⟩ := ((tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atBot
      (μ := π.map L))).2 u hu.1).exists
    refine ⟨y0, fun y hy => ?_⟩
    by_contra h
    push_neg at h
    have := F.mono h.le
    have hy' : u ≤ F y := hy
    linarith
  have hmem : u ≤ F (sInf S) := by
    have hrc := F.right_continuous (sInf S)
    have ht : Tendsto F (𝓝[>] (sInf S)) (𝓝 (F (sInf S))) :=
      hrc.tendsto.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨s, hs, hsy⟩ := exists_lt_of_csInf_lt hne hy
    exact (show u ≤ F s from hs).trans (F.mono hsy.le)
  constructor
  · intro h; exact hmem.trans (F.mono h)
  · intro h; exact csInf_le hbdd h

lemma quantile_monoOn (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L) :
    MonotoneOn (quantile π L) (Set.Ioo 0 1) := fun u hu v hv huv =>
  (quantile_le_iff π hL hu _).2 (huv.trans ((quantile_le_iff π hL hv _).1 le_rfl))

lemma quantile_aemeas (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L) :
    AEMeasurable (quantile π L) (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monoOn π hL)

lemma quantile_map (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).map (quantile π L) = π.map L := by
  haveI : IsProbabilityMeasure (π.map L) := Measure.isProbabilityMeasure_map hL.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply_of_aemeasurable (quantile_aemeas π hL) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ProbabilityTheory.ofReal_cdf, ← F_eq π hL]
  set c := π.real {p | L p ≤ x}
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c ≤ 1 := by
    have := measureReal_mono (μ := π) (Set.subset_univ {p | L p ≤ x})
    simpa [c] using this
  have hset : quantile π L ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic c := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff π hL h2 x).1 h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨(quantile_le_iff π hL h1 x).2 h2, h1⟩
  rw [hset]
  apply le_antisymm
  · calc volume (Set.Ioo 0 1 ∩ Set.Iic c) ≤ volume (Set.Ioc 0 c) :=
          measure_mono fun u hu => ⟨hu.1.1, hu.2⟩
      _ = ENNReal.ofReal c := by rw [Real.volume_Ioc, sub_zero]
  · calc ENNReal.ofReal c = volume (Set.Ioo 0 c) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume (Set.Ioo 0 1 ∩ Set.Iic c) :=
          measure_mono fun u hu => ⟨⟨hu.1, by linarith [hu.2]⟩, hu.2.le⟩

lemma integral_quantile (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ} (hL : Measurable L)
    {h : ℝ → ℝ} (hh : Continuous h) :
    ∫ u in Set.Ioo (0 : ℝ) 1, h (quantile π L u) = ∫ p, h (L p) ∂π := by
  rw [← integral_map (quantile_aemeas π hL) hh.aestronglyMeasurable, quantile_map π hL,
    integral_map hL.aemeasurable hh.aestronglyMeasurable]

lemma integrable_quantile (π : Measure W) [IsProbabilityMeasure π] {L : W → ℝ}
    (hL : Measurable L) {h : ℝ → ℝ} (hh : Continuous h) (hi : Integrable (fun p => h (L p)) π) :
    Integrable (fun u => h (quantile π L u)) (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have h1 : Integrable h (π.map L) :=
    (integrable_map_measure hh.aestronglyMeasurable hL.aemeasurable).2 hi
  rw [← quantile_map π hL] at h1
  exact (integrable_map_measure hh.aestronglyMeasurable (quantile_aemeas π hL)).1 h1

end MSRQuant

namespace MSRESAux

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

lemma gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ico

lemma Gam_ac_gam (sig : SpectralFunction) : Gam sig ≪ gam sig :=
  withDensity_absolutelyContinuous _ _

lemma gam_ac_Gam (sig : SpectralFunction) : gam sig ≪ Gam sig := by
  unfold Gam
  refine withDensity_absolutelyContinuous' (by fun_prop) ?_
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith [hu.2]

lemma Gam_ae_Ico (sig : SpectralFunction) : ∀ᵐ u ∂(Gam sig), u ∈ Set.Ico (0 : ℝ) 1 :=
  (Gam_ac_gam sig).ae_le (gam_ae_Ico sig)

lemma int_Gam_iff (sig : SpectralFunction) (f : ℝ → ℝ) :
    Integrable f (Gam sig) ↔ Integrable (fun u => (1 - u) * f u) (gam sig) := by
  unfold Gam
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]

lemma integral_Gam (sig : SpectralFunction) (f : ℝ → ℝ) :
    ∫ u, f u ∂(Gam sig) = ∫ u, (1 - u) * f u ∂(gam sig) := by
  unfold Gam
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [gam_ae_Ico sig] with u hu
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by linarith [hu.2])]


end MSRESAux

open MSRQuant MSRESAux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (sig : SpectralFunction) (π : Measure (X × Y)) [IsProbabilityMeasure π] (L : X × Y → ℝ)
    (hLm : Measurable L) (hL : Integrable L π) :
    Integrable (fun u => ES u π L) (Gam sig) ∧
    specRisk sig π L = ∫ u, ES u π L ∂(Gam sig) := by
  set q := quantile π L with hq
  have hqi : Integrable q (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    integrable_quantile π hLm continuous_id hL
  set Q : ℝ → ℝ := (Set.Ioo (0 : ℝ) 1).indicator q with hQdef
  have hQ : Integrable Q volume := (integrable_indicator_iff measurableSet_Ioo).2 hqi
  set Slt : Set (ℝ × ℝ) := {p | p.1 < p.2}
  set Sle : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}
  have hSlt : MeasurableSet Slt := measurableSet_lt measurable_fst measurable_snd
  have hSle : MeasurableSet Sle := measurableSet_le measurable_fst measurable_snd
  set f1 : ℝ × ℝ → ℝ := Slt.indicator (fun p => Q p.2)
  set f2 : ℝ × ℝ → ℝ := Sle.indicator (fun p => Q p.2)
  have hQ2 : Integrable (fun p : ℝ × ℝ => Q p.2) ((gam sig).prod volume) := hQ.comp_snd _
  have hf1 : Integrable f1 ((gam sig).prod volume) := hQ2.indicator hSlt
  have hf2 : Integrable f2 ((gam sig).prod volume) := hQ2.indicator hSle
  -- the diagonal is null, so `f1 = f2` a.e.
  have hdiag : ((gam sig).prod volume) {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have : ∀ u : ℝ, Prod.mk u ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {u} := by
      intro u; ext v; simp [eq_comm]
    simp [this]
  have hf12 : f1 =ᵐ[(gam sig).prod volume] f2 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hdiag] with p hp
    have : p ∈ Slt ↔ p ∈ Sle := by
      simp only [Slt, Sle, Set.mem_setOf_eq]
      constructor
      · exact le_of_lt
      · exact fun h => lt_of_le_of_ne h hp
    simp only [f1, f2, Set.indicator, this]
  -- inner integrals
  have hin1 : ∀ u ∈ Set.Ico (0 : ℝ) 1, ∫ v, f1 (u, v) = ∫ v in Set.Ioo u 1, q v := by
    intro u hu
    have : (fun v => f1 (u, v)) = (Set.Ioi u).indicator Q := by
      funext v; simp [f1, Slt, Set.indicator]
    rw [this, integral_indicator measurableSet_Ioi, hQdef,
      setIntegral_indicator measurableSet_Ioo]
    rw [show Set.Ioi u ∩ Set.Ioo 0 1 = Set.Ioo u 1 from ?_]
    ext v; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, lt_of_le_of_lt hu.1 h1, h3⟩
  have hin2 : ∀ v, ∫ u, f2 (u, v) ∂(gam sig) = (gam sig).real (Set.Iic v) * Q v := by
    intro v
    have : (fun u => f2 (u, v)) = (Set.Iic v).indicator (fun _ => Q v) := by
      funext u; simp [f2, Sle, Set.indicator]
    rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul]
  -- `(1 - u) ES_u = ∫_u^1 q` on `[0, 1)`
  have hESu : ∀ u ∈ Set.Ico (0 : ℝ) 1, (1 - u) * ES u π L = ∫ v in Set.Ioo u 1, q v := by
    intro u hu
    unfold ES
    have h1 : (1 - u) ≠ 0 := by linarith [hu.2]
    rw [← mul_assoc, mul_inv_cancel₀ h1, one_mul, intervalIntegral.integral_of_le hu.2.le,
      integral_Ioc_eq_integral_Ioo]
  have hint1 : Integrable (fun u => ∫ v, f1 (u, v)) (gam sig) := hf1.integral_prod_left
  have hcongr : (fun u => (1 - u) * ES u π L) =ᵐ[gam sig] (fun u => ∫ v, f1 (u, v)) := by
    filter_upwards [gam_ae_Ico sig] with u hu
    rw [hESu u hu, hin1 u hu]
  refine ⟨(int_Gam_iff sig _).2 (hint1.congr hcongr.symm), ?_⟩
  rw [integral_Gam, integral_congr_ae hcongr, ← integral_prod _ hf1, integral_congr_ae hf12,
    integral_prod_symm _ hf2]
  simp_rw [hin2]
  unfold specRisk
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_indicator measurableSet_Ioo]
  congr 1
  funext v
  by_cases hv : v ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hv, hQdef, Set.indicator_of_mem hv, measureReal_def,
      gam_Iic_of_mem sig ⟨hv.1.le, hv.2⟩, ENNReal.toReal_ofReal (sig_nonneg sig v), mul_comm]
  · rw [Set.indicator_of_notMem hv, hQdef, Set.indicator_of_notMem hv, mul_zero]
