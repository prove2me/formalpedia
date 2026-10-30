-- Prove2me | solution 1 for MaxSpectralRisk.Duality.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:45:22.80665+00:00
-- url     : https://prove2.me/submissions/ad37955a-b5bb-4d5b-8c46-ec1d3fb21e3f

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

open MSRQuant in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (L : X × Y → ℝ) (hLm : Measurable L)
    (hL : Integrable L π) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, IsLeast (Set.range fun b => g α b π L) (ES α π L)) ∧
    ES 0 π L = ∫ p, L p ∂π ∧
    IsGLB (Set.range fun b => g 0 b π L) (∫ p, L p ∂π) ∧
    Tendsto (fun b => g 0 b π L) atBot (𝓝 (∫ p, L p ∂π)) := by
  set q := quantile π L with hq
  have hqi : Integrable q (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    integrable_quantile π hLm continuous_id hL
  have hqi' : IntegrableOn q (Set.Ioo (0 : ℝ) 1) := hqi
  have hpos : ∀ b, Integrable (fun p => max (L p - b) 0) π := fun b =>
    (hL.sub (integrable_const b)).pos_part
  have hP : ∀ b, ∫ p, max (L p - b) 0 ∂π = ∫ u in Set.Ioo (0 : ℝ) 1, max (q u - b) 0 := fun b =>
    (integral_quantile π hLm (h := fun t => max (t - b) 0) (by fun_prop)).symm
  have hqpos : ∀ b, IntegrableOn (fun u => max (q u - b) 0) (Set.Ioo (0 : ℝ) 1) := fun b =>
    (hqi.sub (integrable_const b)).pos_part
  have hES0 : ES 0 π L = ∫ p, L p ∂π := by
    unfold ES
    rw [sub_zero, inv_one, one_mul, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    exact integral_quantile π hLm (h := id) continuous_id
  -- the decomposition `g₀(b) = E[L] + E[(b - L)₊]`
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
  have hnn : ∀ b, 0 ≤ ∫ p, max (b - L p) 0 ∂π := fun b =>
    integral_nonneg fun p => le_max_right _ _
  have htend : Tendsto (fun b => g 0 b π L) atBot (𝓝 (∫ p, L p ∂π)) := by
    simp_rw [hg0]
    have : Tendsto (fun b : ℝ => ∫ p, max (b - L p) 0 ∂π) atBot (𝓝 0) := by
      have h := tendsto_integral_filter_of_dominated_convergence (μ := π) (l := atBot)
        (F := fun b p => max (b - L p) 0) (f := fun _ => (0 : ℝ)) (fun p => |L p|) ?_ ?_ hL.abs ?_
      · simpa using h
      · exact Eventually.of_forall fun b =>
          ((continuous_const.sub continuous_id).max continuous_const).comp_aestronglyMeasurable
            hL.1
      · filter_upwards [eventually_le_atBot (0 : ℝ)] with b hb
        refine Eventually.of_forall fun p => ?_
        rw [Real.norm_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [neg_abs_le (L p)]) (abs_nonneg _)
      · refine Eventually.of_forall fun p => ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_lt_atBot (L p)] with b hb
        rw [max_eq_right (by linarith)]
    simpa using tendsto_const_nhds.add this
  refine ⟨fun α hα => ?_, hES0, ⟨?_, fun c hc => ?_⟩, htend⟩
  · have h1α : 0 < 1 - α := by linarith [hα.2]
    have hESα : ES α π L = (1 - α)⁻¹ * ∫ u in Set.Ioo α 1, q u := by
      unfold ES
      rw [intervalIntegral.integral_of_le hα.2.le, integral_Ioc_eq_integral_Ioo]
    have hqIoo : IntegrableOn q (Set.Ioo α 1) :=
      hqi'.mono_set (Set.Ioo_subset_Ioo_left hα.1.le)
    have hvol : volume.real (Set.Ioo α 1) = 1 - α := Real.volume_real_Ioo_of_le hα.2.le
    rw [hESα]
    refine ⟨⟨q α, ?_⟩, ?_⟩
    · -- attainment at `b = q(α)`
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
    · rintro _ ⟨b, rfl⟩
      show (1 - α)⁻¹ * ∫ u in Set.Ioo α 1, q u ≤ b + (1 - α)⁻¹ * ∫ p, max (L p - b) 0 ∂π
      rw [hP]
      have hle1 : ∫ u in Set.Ioo α 1, q u ≤ ∫ u in Set.Ioo α 1, (b + max (q u - b) 0) :=
        setIntegral_mono_on hqIoo ((integrable_const b).add
          ((hqpos b).mono_set (Set.Ioo_subset_Ioo_left hα.1.le))) measurableSet_Ioo
          (fun u _ => by linarith [le_max_left (q u - b) 0])
      have hle2 : ∫ u in Set.Ioo α 1, max (q u - b) 0 ≤ ∫ u in Set.Ioo 0 1, max (q u - b) 0 :=
        setIntegral_mono_set (hqpos b) (Eventually.of_forall fun u => le_max_right _ _)
          (Eventually.of_forall (Set.Ioo_subset_Ioo_left hα.1.le))
      rw [integral_add (integrable_const b)
        ((hqpos b).mono_set (Set.Ioo_subset_Ioo_left hα.1.le)), setIntegral_const, hvol,
        smul_eq_mul] at hle1
      have key : ∫ u in Set.Ioo α 1, q u ≤ (1 - α) * b + ∫ u in Set.Ioo 0 1, max (q u - b) 0 := by
        linarith
      have hinv : 0 < (1 - α)⁻¹ := inv_pos.2 h1α
      calc (1 - α)⁻¹ * ∫ u in Set.Ioo α 1, q u
          ≤ (1 - α)⁻¹ * ((1 - α) * b + ∫ u in Set.Ioo 0 1, max (q u - b) 0) :=
            mul_le_mul_of_nonneg_left key hinv.le
        _ = b + (1 - α)⁻¹ * ∫ u in Set.Ioo 0 1, max (q u - b) 0 := by
            field_simp
  · rintro _ ⟨b, rfl⟩
    show ∫ p, L p ∂π ≤ g 0 b π L
    rw [hg0]; linarith [hnn b]
  · exact ge_of_tendsto' htend fun b => hc (Set.mem_range_self b)
