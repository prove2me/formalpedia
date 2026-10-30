-- Prove2me | solution 1 for MaxSpectralRisk.Duality.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:53:05.98786+00:00
-- url     : https://prove2.me/submissions/35de6c25-97aa-455d-b042-437216d32ec5

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting
import Theorems.Thm_MaxSpectralRisk_Duality_eq_2
import Theorems.Thm_MaxSpectralRisk_Duality_es_representation

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

namespace MSRL4Aux

open MSRQuant

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



section Coupling

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma aerect_ae {μ : Measure X} {ν : Measure Y} {P : X → Y → Prop}
    (h : AERect μ ν P) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    ∀ᵐ p ∂π, P p.1 p.2 := by
  obtain ⟨N, hN, N', hN', hP⟩ := h
  have h1 : π (Prod.fst ⁻¹' toMeasurable μ N) = 0 := by
    rw [← Measure.map_apply measurable_fst (measurableSet_toMeasurable _ _), hπ.2.1,
      measure_toMeasurable, hN]
  have h2 : π (Prod.snd ⁻¹' toMeasurable ν N') = 0 := by
    rw [← Measure.map_apply measurable_snd (measurableSet_toMeasurable _ _), hπ.2.2,
      measure_toMeasurable, hN']
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1, measure_eq_zero_iff_ae_notMem.1 h2]
    with p hp1 hp2
  exact hP p.1 (fun h => hp1 (subset_toMeasurable _ _ h)) p.2
    (fun h => hp2 (subset_toMeasurable _ _ h))

lemma int_fst {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun p : X × Y => f p.1) π := by
  have : Integrable f (π.map Prod.fst) := by rw [hπ.2.1]; exact hf
  exact (integrable_map_measure this.1 measurable_fst.aemeasurable).1 this

lemma int_snd {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun p : X × Y => f p.2) π := by
  have : Integrable f (π.map Prod.snd) := by rw [hπ.2.2]; exact hf
  exact (integrable_map_measure this.1 measurable_snd.aemeasurable).1 this

end Coupling

section Main

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {sig : SpectralFunction} {L : X × Y → ℝ}

lemma L_meas (hA : Assumptions L μ ν) : Measurable L := hA.usc.measurable

lemma L_int (hA : Assumptions L μ ν) {π : Measure (X × Y)}
    (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) : Integrable L π := by
  obtain ⟨A, B, -, hAi, -, hBi, hub⟩ := hA.upper_bound
  obtain ⟨a, b, -, hai, -, hbi, hlb⟩ := hA.lower_bound
  refine Integrable.mono' (((int_fst hπ hai).add (int_snd hπ hbi)).abs.add
    ((int_fst hπ hAi).add (int_snd hπ hBi)).abs) (L_meas hA).aestronglyMeasurable ?_
  filter_upwards [aerect_ae hub hπ, aerect_ae hlb hπ] with p h1 h2
  simp only [Prod.mk.eta] at h1 h2
  rw [Real.norm_eq_abs]
  exact (abs_le_max_abs_abs h2 h1).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))


end Main

lemma int_pos {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ}
    (hL : Integrable L π)
    (b : ℝ) : Integrable (fun p => max (L p - b) 0) π :=
  (hL.sub (integrable_const b)).pos_part

lemma g_convex {W : Type*} [MeasurableSpace W] {π : Measure W} [IsFiniteMeasure π] {L : W → ℝ} (hL : Integrable L π)
    {α : ℝ} (hα : α < 1) : ConvexOn ℝ Set.univ (fun b => g α b π L) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hc : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  have key : ∫ p, max (L p - (a * x + b * y)) 0 ∂π ≤
      a * ∫ p, max (L p - x) 0 ∂π + b * ∫ p, max (L p - y) 0 ∂π := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((int_pos hL x).const_mul a) ((int_pos hL y).const_mul b)]
    refine integral_mono (int_pos hL _) (((int_pos hL x).const_mul a).add
      ((int_pos hL y).const_mul b)) fun p => ?_
    have e : L p - (a * x + b * y) = a * (L p - x) + b * (L p - y) := by
      linear_combination (-(L p)) * hab
    show max (L p - (a * x + b * y)) 0 ≤ a * max (L p - x) 0 + b * max (L p - y) 0
    rw [e]
    exact max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  simp only [g, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left key hc
  nlinarith

lemma Φcont {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π]
    {L : W → ℝ} (hL : Integrable L π) : Continuous (fun b => ∫ p, max (L p - b) 0 ∂π) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, ← integral_sub (int_pos hL s) (int_pos hL t)]
  have := norm_integral_le_of_norm_le_const (μ := π)
    (f := fun p => max (L p - s) 0 - max (L p - t) 0) (C := |s - t|)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      have := abs_max_sub_max_le_abs (L p - s) (L p - t) 0
      rwa [show L p - s - (L p - t) = -(s - t) by ring, abs_neg] at this)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
  simpa using this

lemma g_meas {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π]
    {L : W → ℝ} (hL : Integrable L π) {β : ℝ → ℝ} (hβ : Measurable β) :
    Measurable (fun u => g u (β u) π L) :=
  hβ.add (((measurable_const.sub measurable_id).inv).mul ((Φcont hL).measurable.comp hβ))

lemma g0_mono {W : Type*} [MeasurableSpace W] {π : Measure W} [IsProbabilityMeasure π]
    {L : W → ℝ} (hL : Integrable L π) {b b' : ℝ} (h : b ≤ b') : g 0 b π L ≤ g 0 b' π L := by
  have hg0 : ∀ b, g 0 b π L = ∫ p, L p ∂π + ∫ p, max (b - L p) 0 ∂π := by
    intro b
    unfold g
    rw [sub_zero, inv_one, one_mul]
    have hneg : Integrable (fun p => max (b - L p) 0) π :=
      ((integrable_const b).sub hL).pos_part
    have : ∀ p, max (L p - b) 0 = (L p - b) + max (b - L p) 0 := by
      intro p
      rcases le_total (L p) b with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    simp_rw [this]
    have hsub : Integrable (fun p => L p - b) π := hL.sub (integrable_const b)
    rw [integral_add hsub hneg, integral_sub hL (integrable_const b)]
    simp
    ring
  rw [hg0, hg0]
  have : ∫ p, max (b - L p) 0 ∂π ≤ ∫ p, max (b' - L p) 0 ∂π :=
    integral_mono ((integrable_const b).sub hL).pos_part ((integrable_const b').sub hL).pos_part
      fun p => max_le_max (by linarith) le_rfl
  linarith

lemma g_quantile_eq {W : Type*} [MeasurableSpace W] (π : Measure W) [IsProbabilityMeasure π]
    {L : W → ℝ} (hLm : Measurable L) (hL : Integrable L π) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    g α (quantile π L α) π L = ES α π L := by
  set q := quantile π L with hq
  have hqi : Integrable q (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    integrable_quantile π hLm continuous_id hL
  have hqi' : IntegrableOn q (Set.Ioo (0 : ℝ) 1) := hqi
  have hP : ∀ b, ∫ p, max (L p - b) 0 ∂π = ∫ u in Set.Ioo (0 : ℝ) 1, max (q u - b) 0 := fun b =>
    (integral_quantile π hLm (h := fun t => max (t - b) 0) (by fun_prop)).symm
  have hqpos : ∀ b, IntegrableOn (fun u => max (q u - b) 0) (Set.Ioo (0 : ℝ) 1) := fun b =>
    (hqi.sub (integrable_const b)).pos_part
  have h1α : 0 < 1 - α := by linarith [hα.2]
  have hESα : ES α π L = (1 - α)⁻¹ * ∫ u in Set.Ioo α 1, q u := by
    unfold ES
    rw [intervalIntegral.integral_of_le hα.2.le, integral_Ioc_eq_integral_Ioo]
  have hqIoo : IntegrableOn q (Set.Ioo α 1) :=
    hqi'.mono_set (Set.Ioo_subset_Ioo_left hα.1.le)
  have hvol : volume.real (Set.Ioo α 1) = 1 - α := Real.volume_real_Ioo_of_le hα.2.le
  rw [hESα]
  show q α + (1 - α)⁻¹ * ∫ p, max (L p - q α) 0 ∂π = _
  rw [hP, ← Set.Ioc_union_Ioo_eq_Ioo hα.1.le hα.2,
    setIntegral_union (Set.disjoint_left.2 fun x hx hx' => by
      linarith [hx.2, hx'.1]) measurableSet_Ioo
      ((hqpos _).mono_set (Set.Ioc_subset_Ioo_right hα.2))
      ((hqpos _).mono_set (Set.Ioo_subset_Ioo_left hα.1.le))]
  have hz : ∫ u in Set.Ioc 0 α, max (q u - q α) 0 = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) (fun u hu => ?_)]
    · simp
    · have := quantile_monoOn π hLm ⟨hu.1, lt_of_le_of_lt hu.2 hα.2⟩ hα hu.2
      simp only [max_eq_right (by linarith : q u - q α ≤ 0)]
  have hpart : ∫ u in Set.Ioo α 1, max (q u - q α) 0 = ∫ u in Set.Ioo α 1, (q u - q α) := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun u hu => ?_)
    have := quantile_monoOn π hLm hα ⟨lt_trans hα.1 hu.1, hu.2⟩ hu.1.le
    simp only [max_eq_left (by linarith : 0 ≤ q u - q α)]
  rw [hz, zero_add, hpart, integral_sub hqIoo (integrable_const _), setIntegral_const,
    hvol, smul_eq_mul]
  field_simp
  ring

end MSRL4Aux

open MSRQuant MSRL4Aux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) (π : Measure (X × Y)) (hπ : π ∈ MongeKantorovichYao.transferencePlans μ ν) :
    K sig L π = extIntegral (fun u => ⨅ b : ℝ, g u b π L) (Gam sig) ∧
    K sig L π = (((Gam sig).real {0} * ∫ p, L p ∂π +
      ∫ u, ES u π L ∂((Gam sig).restrict (Set.Ioo 0 1)) : ℝ) : EReal) ∧
    (∀ β : ℝ → ℝ, Measurable β →
      (extIntegral (fun u => g u (β u) π L) (Gam sig) = K sig L π ↔
        ∀ᵐ u ∂(Gam sig), ∀ b : ℝ, g u (β u) π L ≤ g u b π L)) ∧
    K sig L π = ⨅ (β : ℝ → ℝ) (_ : MemLp β ⊤ (Gam sig)),
      extIntegral (fun u => g u (β u) π L) (Gam sig) := by
  haveI : IsProbabilityMeasure π := hπ.1
  have hLm : Measurable L := hA.usc.measurable
  have hL : Integrable L π := by
    obtain ⟨A, B, -, hAi, -, hBi, hub⟩ := hA.upper_bound
    obtain ⟨a, b, -, hai, -, hbi, hlb⟩ := hA.lower_bound
    refine Integrable.mono' (((int_fst hπ hai).add (int_snd hπ hbi)).abs.add
      ((int_fst hπ hAi).add (int_snd hπ hBi)).abs) hLm.aestronglyMeasurable ?_
    filter_upwards [aerect_ae hub hπ, aerect_ae hlb hπ] with p h1 h2
    simp only [Prod.mk.eta] at h1 h2
    rw [Real.norm_eq_abs]
    exact (abs_le_max_abs_abs h2 h1).trans (max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _))
  obtain ⟨hmin, hES0, hglb, htend⟩ := eq_2 π L hLm hL
  obtain ⟨hESi, -⟩ := es_representation sig π L hLm hL
  set Ki := ∫ u, ES u π L ∂(Gam sig) with hKi
  -- pointwise facts on `[0, 1)`
  have hlow : ∀ u ∈ Set.Ico (0 : ℝ) 1, ∀ b, ES u π L ≤ g u b π L := by
    intro u hu b
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      rw [hES0]; exact hglb.1 ⟨b, rfl⟩
    · exact (hmin u ⟨hpos, hu.2⟩).2 ⟨b, rfl⟩
  have hinf : ∀ u ∈ Set.Ico (0 : ℝ) 1, ⨅ b : ℝ, g u b π L = ES u π L := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      rw [hES0]
      exact hglb.csInf_eq (Set.range_nonempty _)
    · exact (hmin u ⟨hpos, hu.2⟩).csInf_eq
  have hmeq : (fun u => ⨅ b : ℝ, g u b π L) =ᵐ[Gam sig] (fun u => ES u π L) := by
    filter_upwards [Gam_ae_Ico sig] with u hu using hinf u hu
  have hA_eq : extIntegral (fun u => ⨅ b : ℝ, g u b π L) (Gam sig) = (Ki : EReal) := by
    unfold extIntegral
    rw [if_pos ((integrable_congr hmeq).2 hESi), integral_congr_ae hmeq]
  have hge : ∀ β : ℝ → ℝ, (Ki : EReal) ≤ extIntegral (fun u => g u (β u) π L) (Gam sig) := by
    intro β
    unfold extIntegral
    split_ifs with h
    · exact EReal.coe_le_coe_iff.2 (integral_mono_ae hESi h (by
        filter_upwards [Gam_ae_Ico sig] with u hu using hlow u hu (β u)))
    · exact le_top
  -- the approximating sequence `βₙ`
  have hqae : AEMeasurable (quantile π L) ((Gam sig).restrict (Set.Ioo 0 1)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (quantile_monoOn π hLm)
  have hqt_m : Measurable (hqae.mk _) := hqae.measurable_mk
  have hqt_ae : ∀ᵐ u ∂(Gam sig), u ∈ Set.Ioo (0 : ℝ) 1 → quantile π L u = hqae.mk _ u :=
    (ae_restrict_iff' measurableSet_Ioo).1 hqae.ae_eq_mk
  set qt := hqae.mk _ with hqt
  set βn : ℕ → ℝ → ℝ := fun n u =>
    if u = 0 then -(n : ℝ) else max (-(n : ℝ)) (min (qt u) n) with hβn
  have hβn_meas : ∀ n, Measurable (βn n) := fun n =>
    Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const
      (measurable_const.max (hqt_m.min measurable_const))
  have hβn_bd : ∀ n u, ‖βn n u‖ ≤ n := by
    intro n u
    rw [Real.norm_eq_abs, abs_le]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [βn]
    split_ifs
    · constructor <;> linarith
    · exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hβn_Lp : ∀ n, MemLp (βn n) ⊤ (Gam sig) := fun n =>
    memLp_top_of_bound (hβn_meas n).aestronglyMeasurable n (ae_of_all _ (hβn_bd n))
  -- domination
  set G : ℝ → ℝ := fun u => |ES u π L| + |g u 0 π L| with hG
  have hg0i : Integrable (fun u => g u 0 π L) (Gam sig) := by
    rw [int_Gam_iff]
    refine (integrable_const (∫ p, max (L p - 0) 0 ∂π)).congr ?_
    filter_upwards [gam_ae_Ico sig] with u hu
    have : (1 - u) ≠ 0 := by linarith [hu.2]
    simp only [g]
    rw [zero_add, ← mul_assoc, mul_inv_cancel₀ this, one_mul]
  have hGi : Integrable G (Gam sig) := hESi.abs.add hg0i.abs
  have hdom : ∀ n : ℕ, ∀ᵐ u ∂(Gam sig), ‖g u (βn n u) π L‖ ≤ G u := by
    intro n
    filter_upwards [Gam_ae_Ico sig, hqt_ae] with u hu hqu
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlo := hlow u hu (βn n u)
    have hup : g u (βn n u) π L ≤ max (ES u π L) (g u 0 π L) := by
      rcases eq_or_lt_of_le hu.1 with h0 | hpos
      · subst h0
        have : βn n 0 = -(n : ℝ) := by simp [βn]
        rw [this]
        exact (g0_mono hL (by linarith)).trans (le_max_right _ _)
      · have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hpos, hu.2⟩
        have hne : u ≠ 0 := hpos.ne'
        have hb : βn n u = max (-(n : ℝ)) (min (quantile π L u) n) := by
          simp only [βn, if_neg hne, hqu hu']
        rw [← g_quantile_eq π hLm hL hu']
        refine (g_convex hL hu.2).le_max_of_mem_segment (Set.mem_univ _) (Set.mem_univ _) ?_
        rw [segment_eq_uIcc, hb, Set.mem_uIcc]
        rcases le_total 0 (quantile π L u) with hq | hq
        · right
          exact ⟨le_max_of_le_right (le_min hq hn), max_le (by linarith) (min_le_left _ _)⟩
        · left
          exact ⟨le_max_of_le_right (le_min le_rfl (by linarith)),
            max_le (by linarith) ((min_le_left _ _).trans hq)⟩
    rw [Real.norm_eq_abs, abs_le]
    have h1 := neg_abs_le (ES u π L)
    have h2 := le_abs_self (ES u π L)
    have h3 := le_abs_self (g u 0 π L)
    have h4 := abs_nonneg (g u 0 π L)
    have h5 := abs_nonneg (ES u π L)
    constructor
    · show -(|ES u π L| + |g u 0 π L|) ≤ _
      linarith
    · show _ ≤ |ES u π L| + |g u 0 π L|
      have := max_le_iff.1 (le_refl (max (ES u π L) (g u 0 π L)))
      rcases le_total (ES u π L) (g u 0 π L) with h | h
      · rw [max_eq_right h] at hup; linarith
      · rw [max_eq_left h] at hup; linarith
  have hlim : ∀ᵐ u ∂(Gam sig), Tendsto (fun n : ℕ => g u (βn n u) π L) atTop (𝓝 (ES u π L)) := by
    filter_upwards [Gam_ae_Ico sig, hqt_ae] with u hu hqu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      have : (fun n : ℕ => g 0 (βn n 0) π L) = fun n : ℕ => g 0 (-(n : ℝ)) π L := by
        funext n; simp [βn]
      rw [this, hES0]
      exact htend.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    · have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hpos, hu.2⟩
      rw [← g_quantile_eq π hLm hL hu']
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop |quantile π L u|] with n hn
      have hb : βn n u = quantile π L u := by
        simp only [βn, if_neg hpos.ne', ← hqu hu']
        rw [min_eq_left ((le_abs_self _).trans hn),
          max_eq_right (by linarith [neg_abs_le (quantile π L u)])]
      rw [hb]
  have hmeasn : ∀ n, AEStronglyMeasurable (fun u => g u (βn n u) π L) (Gam sig) := fun n =>
    (g_meas hL (hβn_meas n)).aestronglyMeasurable
  have hconv : Tendsto (fun n : ℕ => ∫ u, g u (βn n u) π L ∂(Gam sig)) atTop (𝓝 Ki) :=
    tendsto_integral_of_dominated_convergence G hmeasn hGi hdom hlim
  have hβn_int : ∀ n, Integrable (fun u => g u (βn n u) π L) (Gam sig) := fun n =>
    Integrable.mono' hGi (hmeasn n) (hdom n)
  have hext : ∀ n, extIntegral (fun u => g u (βn n u) π L) (Gam sig) =
      ((∫ u, g u (βn n u) π L ∂(Gam sig) : ℝ) : EReal) := fun n => by
    unfold extIntegral; rw [if_pos (hβn_int n)]
  have hconvE : Tendsto (fun n : ℕ => ((∫ u, g u (βn n u) π L ∂(Gam sig) : ℝ) : EReal)) atTop
      (𝓝 (Ki : EReal)) := (continuous_coe_real_ereal.tendsto _).comp hconv
  have hK : K sig L π = (Ki : EReal) := by
    apply le_antisymm
    · unfold K
      refine ge_of_tendsto' hconvE fun n => ?_
      rw [← hext n]
      exact iInf₂_le_of_le (βn n) (hβn_meas n) le_rfl
    · unfold K
      exact le_iInf₂ fun β _ => hge β
  have hKinf : ⨅ (β : ℝ → ℝ) (_ : MemLp β ⊤ (Gam sig)),
      extIntegral (fun u => g u (β u) π L) (Gam sig) = (Ki : EReal) := by
    apply le_antisymm
    · refine ge_of_tendsto' hconvE fun n => ?_
      rw [← hext n]
      exact iInf₂_le_of_le (βn n) (hβn_Lp n) le_rfl
    · exact le_iInf₂ fun β _ => hge β
  refine ⟨by rw [hK, hA_eq], ?_, fun β hβ => ?_, by rw [hK, hKinf]⟩
  · rw [hK]
    congr 1
    have hIco : (Gam sig).restrict (Set.Ico 0 1) = Gam sig :=
      Measure.restrict_eq_self_of_ae_mem (Gam_ae_Ico sig)
    have h1 : ∫ u, ES u π L ∂(Gam sig) = ∫ u in Set.Ico (0 : ℝ) 1, ES u π L ∂(Gam sig) := by
      rw [hIco]
    rw [hKi, h1, ← Set.Ioo_insert_left zero_lt_one, Set.insert_eq,
      setIntegral_union (Set.disjoint_singleton_left.2 (fun h => (lt_irrefl _ h.1)))
        measurableSet_Ioo hESi.integrableOn hESi.integrableOn,
      integral_singleton, hES0, smul_eq_mul]
  · rw [hK]
    constructor
    · intro h
      unfold extIntegral at h
      split_ifs at h with hi
      · have hEq : ∫ u, g u (β u) π L ∂(Gam sig) = Ki := EReal.coe_eq_coe_iff.1 h
        have hnn : 0 ≤ᵐ[Gam sig] (fun u => g u (β u) π L - ES u π L) := by
          filter_upwards [Gam_ae_Ico sig] with u hu
          exact sub_nonneg.2 (hlow u hu (β u))
        have h0 : ∫ u, (g u (β u) π L - ES u π L) ∂(Gam sig) = 0 := by
          rw [integral_sub hi hESi, hEq, hKi, sub_self]
        have hz := (integral_eq_zero_iff_of_nonneg_ae hnn (hi.sub hESi)).1 h0
        filter_upwards [hz, Gam_ae_Ico sig] with u hu hIco b
        have : g u (β u) π L = ES u π L := by
          have := hu; simp only [Pi.zero_apply] at this; linarith
        rw [this]; exact hlow u hIco b
      · exact absurd h.symm (EReal.coe_ne_top _)
    · intro h
      have heq : (fun u => g u (β u) π L) =ᵐ[Gam sig] (fun u => ES u π L) := by
        filter_upwards [h, Gam_ae_Ico sig] with u hu hIco
        refine le_antisymm ?_ (hlow u hIco (β u))
        rcases eq_or_lt_of_le hIco.1 with h0 | hpos
        · subst h0
          rw [hES0]
          exact hglb.2 (fun _ ⟨b, hb⟩ => hb ▸ hu b)
        · obtain ⟨b0, hb0⟩ := (hmin u ⟨hpos, hIco.2⟩).1
          rw [← hb0]
          exact hu b0
      unfold extIntegral
      rw [if_pos ((integrable_congr heq).2 hESi), integral_congr_ae heq]
