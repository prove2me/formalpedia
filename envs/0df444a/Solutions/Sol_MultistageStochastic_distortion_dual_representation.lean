-- Prove2me | solution 1 for MultistageStochastic.distortion_dual_representation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T02:47:25.337005+00:00
-- url     : https://prove2.me/submissions/6687ab16-3f71-42d1-bbb1-97482a0719b6

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def msDD_Q (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

theorem msDD_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem msDD_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem msDD_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (msDD_Q P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (msDD_Q P u)) (msDD_Q P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (msDD_Q P u)) (𝓝 (cdf P (msDD_Q P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (msDD_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

theorem msDD_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : msDD_Q P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (msDD_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (msDD_bdd P hu0) h

theorem msDD_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (msDD_Q P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [msDD_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (msDD_le_cdf_Q P hv.2)

instance msDD_U_prob : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

theorem msDD_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (msDD_Q P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (msDD_Q_mono P)

theorem msDD_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (msDD_Q P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (msDD_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : msDD_Q P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (msDD_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(msDD_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
  rw [hset]
  apply le_antisymm
  · calc volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} ≤ volume (Icc 0 (cdf P x)) :=
          measure_mono (fun u hu => ⟨hu.1.1.le, hu.2⟩)
      _ = ENNReal.ofReal (cdf P x) := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal (cdf P x) = volume (Ioo 0 (cdf P x)) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
          apply measure_mono
          intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 (cdf_le_one P x)⟩, hu.2.le⟩

theorem msDD_integral_Q (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hφ : Measurable φ) :
    ∫ u in Ioo (0:ℝ) 1, φ (msDD_Q μ u) = ∫ x, φ x ∂μ := by
  conv_rhs => rw [← msDD_map_Q μ]
  rw [integral_map (msDD_Q_ae μ) hφ.aestronglyMeasurable]

theorem msDD_integrableOn_Q (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hφ : Measurable φ) (hi : Integrable φ μ) :
    IntegrableOn (fun u => φ (msDD_Q μ u)) (Ioo (0:ℝ) 1) := by
  rw [← msDD_map_Q μ] at hi
  exact (integrable_map_measure hφ.aestronglyMeasurable (msDD_Q_ae μ)).mp hi

theorem msDD_var_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) :
    MultistageStochastic.valueAtRisk P Z = msDD_Q (P.map Z) := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ
  funext u
  unfold MultistageStochastic.valueAtRisk msDD_Q
  congr 1
  ext y
  simp only [mem_ofPred_eq]
  have h1 : P {ω | Z ω ≤ y} = ENNReal.ofReal (cdf (P.map Z) y) := by
    rw [ofReal_cdf, Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]; rfl
  rw [h1, ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)]

theorem msDD_pos_part {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : AEMeasurable Z P) (t : ℝ) :
    ∫ ω, max (Z ω - t) 0 ∂P = ∫ u in Ioo (0:ℝ) 1, max (msDD_Q (P.map Z) u - t) 0 := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ
  have hm : Measurable (fun x : ℝ => max (x - t) 0) :=
    ((continuous_id.sub continuous_const).max continuous_const).measurable
  have h := msDD_integral_Q (P.map Z) (fun x => max (x - t) 0) hm
  rw [h, integral_map hZ hm.aestronglyMeasurable]

theorem msDD_Q_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Integrable Z P) :
    IntegrableOn (msDD_Q (P.map Z)) (Ioo (0:ℝ) 1) := by
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have := msDD_integrableOn_Q (P.map Z) id measurable_id
    ((integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).mpr hZ)
  exact this

theorem msDD_avar_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable Z P) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (t : ℝ) :
    ∫ u in Ioo α 1, MultistageStochastic.valueAtRisk P Z u
      ≤ ∫ ω, max (Z ω - t) 0 ∂P + t * (1 - α) := by
  have hZm : AEMeasurable Z P := hZ.aemeasurable
  have hqi := msDD_Q_integrable P Z hZ
  rw [msDD_var_eq P Z hZm, msDD_pos_part P Z hZm t]
  have hsub : Ioo α 1 ⊆ Ioo (0:ℝ) 1 := Ioo_subset_Ioo_left hα0
  have hci : IntegrableOn (fun _ : ℝ => t) (Ioo (0:ℝ) 1) := integrable_const t
  have hpi : IntegrableOn (fun u => max (msDD_Q (P.map Z) u - t) 0) (Ioo (0:ℝ) 1) :=
    (hqi.sub hci).pos_part
  have e1 : ∫ u in Ioo α 1, msDD_Q (P.map Z) u
      = (∫ u in Ioo α 1, (msDD_Q (P.map Z) u - t)) + t * (1 - α) := by
    rw [integral_sub (hqi.mono_set hsub) (hci.mono_set hsub), setIntegral_const,
      Real.volume_real_Ioo_of_le hα1.le, smul_eq_mul]
    ring
  rw [e1]
  gcongr ?_ + _
  calc ∫ u in Ioo α 1, (msDD_Q (P.map Z) u - t)
      ≤ ∫ u in Ioo α 1, max (msDD_Q (P.map Z) u - t) 0 :=
        setIntegral_mono_on ((hqi.sub hci).mono_set hsub) (hpi.mono_set hsub) measurableSet_Ioo
          (fun u _ => le_max_left _ _)
    _ ≤ ∫ u in Ioo (0:ℝ) 1, max (msDD_Q (P.map Z) u - t) 0 :=
        setIntegral_mono_set hpi (Eventually.of_forall (fun u => le_max_right _ _))
          hsub.eventuallyLE

theorem msDD_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable Z P) (A : Set Ω) (hA : MeasurableSet A)
    (hp0 : 0 < P.real A) (hp1 : P.real A < 1) :
    ∫ ω in A, Z ω ∂P ≤ ∫ u in Ioo (1 - P.real A) 1, MultistageStochastic.valueAtRisk P Z u := by
  have hZm : AEMeasurable Z P := hZ.aemeasurable
  have : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZm
  have hqi := msDD_Q_integrable P Z hZ
  have hα0 : 0 < 1 - P.real A := by linarith
  have hα1 : 1 - P.real A < 1 := by linarith
  rw [msDD_var_eq P Z hZm]
  set p := P.real A with hpdef
  set α := 1 - p with hαdef
  set q := msDD_Q (P.map Z) with hq
  set t := q α with ht
  have hαI : α ∈ Ioo (0:ℝ) 1 := ⟨hα0, hα1⟩
  have hsub : Ioo α 1 ⊆ Ioo (0:ℝ) 1 := Ioo_subset_Ioo_left hα0.le
  have hci : IntegrableOn (fun _ : ℝ => t) (Ioo (0:ℝ) 1) := integrable_const t
  have hZt : Integrable (fun ω => Z ω - t) P := hZ.sub (integrable_const t)
  have h1 : ∫ ω in A, Z ω ∂P ≤ ∫ ω, max (Z ω - t) 0 ∂P + t * p := by
    have e : ∫ ω in A, Z ω ∂P = ∫ ω in A, (Z ω - t) ∂P + t * p := by
      rw [integral_sub hZ.integrableOn (integrable_const t).integrableOn, setIntegral_const,
        smul_eq_mul]
      ring
    rw [e]
    gcongr ?_ + _
    calc ∫ ω in A, (Z ω - t) ∂P ≤ ∫ ω in A, max (Z ω - t) 0 ∂P :=
          setIntegral_mono_on hZt.integrableOn hZt.pos_part.integrableOn hA
            (fun ω _ => le_max_left _ _)
      _ ≤ ∫ ω, max (Z ω - t) 0 ∂P :=
          setIntegral_le_integral hZt.pos_part (Eventually.of_forall (fun ω => le_max_right _ _))
  have h2 : ∫ ω, max (Z ω - t) 0 ∂P = (∫ u in Ioo α 1, q u) - t * (1 - α) := by
    rw [msDD_pos_part P Z hZm t]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub]
    · rw [setIntegral_congr_fun measurableSet_Ioo (g := fun u => q u - t)]
      · rw [integral_sub (hqi.mono_set hsub) (hci.mono_set hsub), setIntegral_const,
          Real.volume_real_Ioo_of_le hα1.le, smul_eq_mul]
        ring
      · intro u hu
        have : q α ≤ q u := msDD_Q_mono (P.map Z) hαI (hsub hu) hu.1.le
        simp only
        rw [max_eq_left (by rw [ht]; linarith)]
    · intro u hu
      have hu1 : u ∈ Ioo (0:ℝ) 1 := hu.1
      have hle : u ≤ α := by
        by_contra hc
        exact hu.2 ⟨lt_of_not_ge hc, hu1.2⟩
      have : q u ≤ q α := msDD_Q_mono (P.map Z) hu1 hαI hle
      rw [max_eq_right (by rw [ht]; linarith)]
  rw [h2] at h1
  have : 1 - α = p := by rw [hαdef]; ring
  rw [this] at h1
  linarith

theorem msDD_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W Y : Ω → ℝ) (hW : Integrable W P) (hY : Measurable Y) (C : ℝ)
    (hC : ∀ᵐ ω ∂P, |Y ω| ≤ C) :
    IntegrableOn (fun s => ∫ ω, W ω * (Ioi s).indicator 1 (Y ω) ∂P) (Ioo (-C) C) ∧
    ∫ ω, W ω * (Y ω + C) ∂P
      = ∫ s in Ioo (-C) C, ∫ ω, W ω * (Ioi s).indicator 1 (Y ω) ∂P := by
  set ν : Measure ℝ := volume.restrict (Ioo (-C) C) with hν
  have : IsFiniteMeasure ν := by
    rw [hν]
    exact isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
  set f : Ω × ℝ → ℝ := fun p => W p.1 * (Ioi p.2).indicator 1 (Y p.1) with hf
  have hS : MeasurableSet {p : Ω × ℝ | p.2 < Y p.1} :=
    measurableSet_lt measurable_snd (hY.comp measurable_fst)
  have hfeq : f = {p : Ω × ℝ | p.2 < Y p.1}.indicator (fun p => W p.1) := by
    funext p
    simp only [hf, Set.indicator, mem_Ioi, mem_ofPred_eq, Pi.one_apply]
    split_ifs <;> simp
  have hfi : Integrable f (P.prod ν) := by
    rw [hfeq]
    exact (hW.comp_fst ν).indicator hS
  refine ⟨hfi.integral_prod_right, ?_⟩
  calc ∫ ω, W ω * (Y ω + C) ∂P = ∫ ω, ∫ s, f (ω, s) ∂ν ∂P := by
        apply integral_congr_ae
        filter_upwards [hC] with ω hω
        have hω' := abs_le.mp hω
        have hfun : (fun s => f (ω, s)) = (Iio (Y ω)).indicator (fun _ => W ω) := by
          funext s
          simp only [hf, Set.indicator, mem_Ioi, mem_Iio, Pi.one_apply]
          split_ifs <;> simp
        show W ω * (Y ω + C) = ∫ s, (fun s => f (ω, s)) s ∂ν
        rw [hfun, integral_indicator_const _ measurableSet_Iio, smul_eq_mul, hν,
          measureReal_restrict_apply measurableSet_Iio]
        have hset : Iio (Y ω) ∩ Ioo (-C) C = Ioo (-C) (Y ω) := by
          ext x
          simp only [mem_inter_iff, mem_Iio, mem_Ioo]
          constructor
          · rintro ⟨h1, h2, _⟩
            exact ⟨h2, h1⟩
          · rintro ⟨h2, h1⟩
            exact ⟨h1, h2, lt_of_lt_of_le h1 hω'.2⟩
        rw [hset, Real.volume_real_Ioo_of_le hω'.1]
        ring
    _ = ∫ z, f z ∂(P.prod ν) := (integral_prod f hfi).symm
    _ = ∫ s, ∫ ω, f (ω, s) ∂P ∂ν := integral_prod_symm f hfi
    _ = _ := rfl

theorem msDD_sigma {σ : ℝ → ℝ} (hσ : MultistageStochastic.IsDistortionFunction σ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ u in Ioo (0:ℝ) 1, max (σ u - σ α) 0) + σ α * (1 - α) = ∫ u in Ioo α 1, σ u := by
  obtain ⟨_, hσm, hσi, _⟩ := hσ
  have hsub : Ioo α 1 ⊆ Ioo (0:ℝ) 1 := Ioo_subset_Ioo_left hα0
  have hαI : α ∈ Ico (0:ℝ) 1 := ⟨hα0, hα1⟩
  have hci : IntegrableOn (fun _ : ℝ => σ α) (Ioo (0:ℝ) 1) := integrable_const _
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub]
  · rw [setIntegral_congr_fun measurableSet_Ioo (g := fun u => σ u - σ α)]
    · rw [integral_sub (hσi.mono_set hsub) (hci.mono_set hsub), setIntegral_const,
        Real.volume_real_Ioo_of_le hα1.le, smul_eq_mul]
      ring
    · intro u hu
      have : σ α ≤ σ u := hσm hαI ⟨(hα0.trans hu.1.le), hu.2⟩ hu.1.le
      simp only
      rw [max_eq_left (by linarith)]
  · intro u hu
    have hu1 : u ∈ Ioo (0:ℝ) 1 := hu.1
    have hle : u ≤ α := by
      by_contra hc
      exact hu.2 ⟨lt_of_not_ge hc, hu1.2⟩
    have : σ u ≤ σ α := hσm ⟨hu1.1.le, hu1.2⟩ hαI hle
    rw [max_eq_right (by linarith)]

theorem msDD_exists {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ → ℝ) (hσ : MultistageStochastic.IsDistortionFunction σ) (Y : Ω → ℝ)
    (hY : Measurable Y) :
    ∃ Zs : Ω → ℝ, MultistageStochastic.DominatedByDistortion P σ Zs ∧
      (∫ ω, Y ω * Zs ω ∂P = MultistageStochastic.distortionFunctional P σ Y) ∧
      ∀ s : ℝ, ∫ ω, Zs ω * (Ioi s).indicator 1 (Y ω) ∂P
        = ∫ u in Ioo (cdf (P.map Y) s) 1, σ u := by
  have hσ' := hσ
  obtain ⟨hσ0, hσm, hσi, hσ1⟩ := hσ'
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hvar : MultistageStochastic.valueAtRisk P Y = msDD_Q (P.map Y) :=
    msDD_var_eq P Y hY.aemeasurable
  set μY := P.map Y with hμY
  set q := msDD_Q μY with hq
  set L : Measure ℝ :=
    (volume.restrict (Ioo (0:ℝ) 1)).withDensity (fun u => ENNReal.ofReal (σ u)) with hL
  have : IsFiniteMeasure L := isFiniteMeasure_withDensity_ofReal hσi.2
  have hqL : AEMeasurable q L := (msDD_Q_ae μY).mono_ac (withDensity_absolutelyContinuous _ _)
  set ν : Measure ℝ := L.map q with hν
  have hac : ν ≪ μY := by
    refine Measure.AbsolutelyContinuous.mk (fun B hB h0 => ?_)
    rw [hν, Measure.map_apply_of_aemeasurable hqL hB]
    apply withDensity_absolutelyContinuous
    rw [← Measure.map_apply_of_aemeasurable (msDD_Q_ae μY) hB, msDD_map_Q]
    exact h0
  set g : ℝ → ℝ := fun y => (ν.rnDeriv μY y).toReal with hg
  have hgm : Measurable g := (Measure.measurable_rnDeriv ν μY).ennreal_toReal
  have hσmeas : AEMeasurable (fun u => ENNReal.ofReal (σ u)) (volume.restrict (Ioo (0:ℝ) 1)) :=
    hσi.aemeasurable.ennreal_ofReal
  have key : ∀ h : ℝ → ℝ, Measurable h →
      ∫ ω, g (Y ω) * h (Y ω) ∂P = ∫ u in Ioo (0:ℝ) 1, σ u * h (q u) := by
    intro h hh
    calc ∫ ω, g (Y ω) * h (Y ω) ∂P = ∫ y, g y * h y ∂μY := by
          rw [hμY, integral_map (f := fun y => g y * h y) hY.aemeasurable
            (hgm.mul hh).aestronglyMeasurable]
      _ = ∫ y, h y ∂ν := by
          rw [← integral_rnDeriv_smul hac]
          simp only [smul_eq_mul, hg]
      _ = ∫ u, h (q u) ∂L := by rw [hν, integral_map hqL hh.aestronglyMeasurable]
      _ = ∫ u in Ioo (0:ℝ) 1, (ENNReal.ofReal (σ u)).toReal • h (q u) := by
          rw [hL, integral_withDensity_eq_integral_toReal_smul₀ hσmeas
            (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      _ = ∫ u in Ioo (0:ℝ) 1, σ u * h (q u) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro u hu
          simp only [smul_eq_mul]
          rw [ENNReal.toReal_ofReal (hσ0 u ⟨hu.1.le, hu.2⟩)]
  have hZi : Integrable (fun ω => g (Y ω)) P := by
    have : Integrable g μY := Measure.integrable_toReal_rnDeriv
    exact (integrable_map_measure hgm.aestronglyMeasurable hY.aemeasurable).mp this
  have hZ1 : ∫ ω, g (Y ω) ∂P = 1 := by
    have := key (fun _ => 1) measurable_const
    simp only [mul_one] at this
    rw [this, hσ1]
  -- convex dominance
  have hconv : ∀ t : ℝ, ∫ ω, max (g (Y ω) - t) 0 ∂P ≤ ∫ u in Ioo (0:ℝ) 1, max (σ u - t) 0 := by
    intro t
    set B : Set ℝ := {y | t < g y} with hB
    have hBm : MeasurableSet B := measurableSet_lt measurable_const hgm
    have hind : Measurable (B.indicator (1 : ℝ → ℝ)) := measurable_one.indicator hBm
    have hbd : ∀ y, ‖B.indicator (1 : ℝ → ℝ) y‖ ≤ 1 := by
      intro y
      by_cases hy : y ∈ B <;> simp [Set.indicator, hy]
    have hpt : ∀ ω, max (g (Y ω) - t) 0
        = g (Y ω) * B.indicator 1 (Y ω) - t * B.indicator 1 (Y ω) := by
      intro ω
      by_cases hy : Y ω ∈ B
      · have : t < g (Y ω) := hy
        simp only [Set.indicator, hy, if_true, Pi.one_apply, mul_one]
        rw [max_eq_left (by linarith)]
      · have : ¬ t < g (Y ω) := hy
        simp only [Set.indicator, hy, if_false, mul_zero, sub_zero]
        rw [max_eq_right (by linarith)]
    have hI1 : Integrable (fun ω => g (Y ω) * B.indicator 1 (Y ω)) P :=
      hZi.mul_bdd (hind.comp hY).aestronglyMeasurable (Eventually.of_forall (fun ω => hbd _))
    have hI2 : Integrable (fun ω => B.indicator (1 : ℝ → ℝ) (Y ω)) P :=
      Integrable.of_bound (hind.comp hY).aestronglyMeasurable 1
        (Eventually.of_forall (fun ω => hbd _))
    have hqind : AEStronglyMeasurable (fun u => B.indicator (1 : ℝ → ℝ) (q u))
        (volume.restrict (Ioo (0:ℝ) 1)) :=
      (hind.comp_aemeasurable (msDD_Q_ae μY)).aestronglyMeasurable
    have hJ1 : IntegrableOn (fun u => σ u * B.indicator 1 (q u)) (Ioo (0:ℝ) 1) :=
      hσi.mul_bdd hqind (Eventually.of_forall (fun u => hbd _))
    have hJ2 : IntegrableOn (fun u => B.indicator (1 : ℝ → ℝ) (q u)) (Ioo (0:ℝ) 1) :=
      Integrable.of_bound hqind 1 (Eventually.of_forall (fun u => hbd _))
    have hlaw : ∫ ω, B.indicator (1 : ℝ → ℝ) (Y ω) ∂P
        = ∫ u in Ioo (0:ℝ) 1, B.indicator (1 : ℝ → ℝ) (q u) := by
      rw [msDD_integral_Q μY _ hind, hμY, integral_map hY.aemeasurable hind.aestronglyMeasurable]
    have hci : IntegrableOn (fun _ : ℝ => t) (Ioo (0:ℝ) 1) := integrable_const t
    calc ∫ ω, max (g (Y ω) - t) 0 ∂P
        = ∫ ω, (g (Y ω) * B.indicator 1 (Y ω) - t * B.indicator 1 (Y ω)) ∂P := by
          congr 1; funext ω; exact hpt ω
      _ = ∫ u in Ioo (0:ℝ) 1, (σ u * B.indicator 1 (q u) - t * B.indicator 1 (q u)) := by
          rw [integral_sub hI1 (hI2.const_mul t), integral_const_mul, key _ hind, hlaw,
            integral_sub hJ1 (hJ2.const_mul t), integral_const_mul]
      _ ≤ ∫ u in Ioo (0:ℝ) 1, max (σ u - t) 0 := by
          apply integral_mono (hJ1.sub (hJ2.const_mul t)) ((hσi.sub hci).pos_part)
          intro u
          show σ u * B.indicator 1 (q u) - t * B.indicator 1 (q u) ≤ max (σ u - t) 0
          by_cases hu : q u ∈ B
          · simp only [Set.indicator, hu, if_true, Pi.one_apply, mul_one]
            exact le_max_left _ _
          · simp only [Set.indicator, hu, if_false, mul_zero, sub_zero]
            exact le_max_right _ _
  refine ⟨fun ω => g (Y ω), ⟨hZi, hZ1, ?_⟩, ?_, ?_⟩
  · intro α hα0 hα1
    unfold MultistageStochastic.averageValueAtRisk
    rw [if_neg hα1.ne]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
    calc ∫ p in Ioo α 1, MultistageStochastic.valueAtRisk P (fun ω => g (Y ω)) p
        ≤ ∫ ω, max (g (Y ω) - σ α) 0 ∂P + σ α * (1 - α) :=
          msDD_avar_le P (fun ω => g (Y ω)) hZi hα0 hα1 (σ α)
      _ ≤ (∫ u in Ioo (0:ℝ) 1, max (σ u - σ α) 0) + σ α * (1 - α) := by
          gcongr ?_ + _
          exact hconv (σ α)
      _ = ∫ u in Ioo α 1, σ u := msDD_sigma hσ hα0 hα1
  · have := key id measurable_id
    unfold MultistageStochastic.distortionFunctional
    rw [hvar]
    simp only [id] at this
    rw [← this]
    congr 1
    funext ω
    ring
  · intro s
    rw [key _ (measurable_one.indicator measurableSet_Ioi)]
    set F := cdf μY s with hF
    have hF0 : 0 ≤ F := cdf_nonneg _ _
    rw [setIntegral_congr_fun measurableSet_Ioo (g := (Ioo F 1).indicator σ)]
    · rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
      congr 2
      ext u
      simp only [mem_inter_iff, mem_Ioo]
      constructor
      · rintro ⟨⟨h1, h2⟩, _⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2⟩, lt_of_le_of_lt hF0 h1, h2⟩
    · intro u hu
      have hiff : s < q u ↔ F < u := by
        rw [← not_le, ← not_le, msDD_Q_le_iff μY hu.1 hu.2]
      by_cases hFu : F < u
      · have h1 : q u ∈ Ioi s := hiff.mpr hFu
        have h2 : u ∈ Ioo F 1 := ⟨hFu, hu.2⟩
        simp only [Set.indicator, h1, h2, if_true, Pi.one_apply, mul_one]
      · have h1 : q u ∉ Ioi s := fun h => hFu (hiff.mp h)
        have h2 : u ∉ Ioo F 1 := fun h => hFu h.1
        simp only [Set.indicator, h1, h2, if_false, mul_zero]

theorem msDD_point {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σ : ℝ → ℝ) (hσ : MultistageStochastic.IsDistortionFunction σ) (Y : Ω → ℝ)
    (hY : Measurable Y) (Z : Ω → ℝ) (hZ : MultistageStochastic.DominatedByDistortion P σ Z)
    (s : ℝ) :
    ∫ ω, Z ω * (Ioi s).indicator 1 (Y ω) ∂P ≤ ∫ u in Ioo (cdf (P.map Y) s) 1, σ u := by
  obtain ⟨hZi, hZ1, hZc⟩ := hZ
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set A : Set Ω := Y ⁻¹' Ioi s with hAdef
  have hA : MeasurableSet A := hY measurableSet_Ioi
  have hfun : (fun ω => Z ω * (Ioi s).indicator 1 (Y ω)) = A.indicator Z := by
    funext ω
    by_cases h : Y ω ∈ Ioi s
    · have h' : ω ∈ A := h
      simp only [Set.indicator, h, h', if_true, Pi.one_apply, mul_one]
    · have h' : ω ∉ A := h
      simp only [Set.indicator, h, h', if_false, mul_zero]
  rw [hfun, integral_indicator hA]
  set F := cdf (P.map Y) s with hF
  have hF0 : 0 ≤ F := cdf_nonneg _ _
  have hF1 : F ≤ 1 := cdf_le_one _ _
  have hpA : P.real A = 1 - F := by
    have hc : A = (Y ⁻¹' Iic s)ᶜ := by
      rw [hAdef]; ext ω; simp
    rw [hc, measureReal_compl (hY measurableSet_Iic), probReal_univ, hF, cdf_eq_real,
      map_measureReal_apply hY measurableSet_Iic]
  have hσi := hσ.2.2.1
  have hσ1 := hσ.2.2.2
  rcases eq_or_lt_of_le hF1 with hFe | hFl
  · -- F = 1 : A is null
    have hA0 : P A = 0 := by
      have : P.real A = 0 := by rw [hpA, hFe]; ring
      rw [measureReal_eq_zero_iff] at this
      exact this
    rw [Measure.restrict_eq_zero.mpr hA0, integral_zero_measure, hFe, Ioo_self,
      Measure.restrict_empty, integral_zero_measure]
  rcases eq_or_lt_of_le hF0 with hFe0 | hFp
  · -- F = 0 : A has full measure
    rw [← hFe0, hσ1]
    have hAc : P Aᶜ = 0 := by
      have : P.real Aᶜ = 0 := by
        rw [measureReal_compl hA, probReal_univ, hpA, ← hFe0]; ring
      rw [measureReal_eq_zero_iff] at this
      exact this
    have h := integral_add_compl hA hZi
    rw [Measure.restrict_eq_zero.mpr hAc, integral_zero_measure, add_zero, hZ1] at h
    rw [h]
  · have hp0 : 0 < P.real A := by rw [hpA]; linarith
    have hp1 : P.real A < 1 := by rw [hpA]; linarith
    have ht := msDD_tail P Z hZi A hA hp0 hp1
    have e : 1 - P.real A = F := by rw [hpA]; ring
    rw [e] at ht
    have hc := hZc F hF0 hFl
    unfold MultistageStochastic.averageValueAtRisk at hc
    rw [if_neg hFl.ne] at hc
    have hpos : 0 < (1 - F)⁻¹ := inv_pos.mpr (by linarith)
    exact le_trans ht (le_of_mul_le_mul_left hc hpos)

open MeasureTheory MultistageStochastic in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ)
    (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    distortionFunctional P σ Y
      = ⨆ Z : {Z : Ω → ℝ // DominatedByDistortion P σ Z},
          ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by
  obtain ⟨hYm, C, hC⟩ := hY
  obtain ⟨Zs, hZsD, hZsY, hZst⟩ := msDD_exists P σ hσ Y hYm
  have hYW : ∀ W : Ω → ℝ, Integrable W P → ∫ ω, W ω ∂P = 1 →
      ∫ ω, Y ω * W ω ∂P = ∫ ω, W ω * (Y ω + C) ∂P - C := by
    intro W hW hW1
    have hWY : Integrable (fun ω => W ω * Y ω) P :=
      hW.mul_bdd hYm.aestronglyMeasurable (by
        filter_upwards [hC] with ω hω
        rw [Real.norm_eq_abs]; exact hω)
    have e : (fun ω => W ω * (Y ω + C)) = fun ω => W ω * Y ω + C * W ω := by
      funext ω; ring
    rw [e, integral_add hWY (hW.const_mul C), integral_const_mul, hW1]
    have e2 : (fun ω => Y ω * W ω) = fun ω => W ω * Y ω := by funext ω; ring
    rw [e2]
    ring
  have hbound : ∀ Z : {Z : Ω → ℝ // DominatedByDistortion P σ Z},
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P ≤ distortionFunctional P σ Y := by
    rintro ⟨Z, hZ⟩
    rw [← hZsY]
    show ∫ ω, Y ω * Z ω ∂P ≤ ∫ ω, Y ω * Zs ω ∂P
    obtain ⟨hIZ, hLZ⟩ := msDD_layer P Z Y hZ.1 hYm C hC
    obtain ⟨hIZs, hLZs⟩ := msDD_layer P Zs Y hZsD.1 hYm C hC
    rw [hYW Z hZ.1 hZ.2.1, hYW Zs hZsD.1 hZsD.2.1, hLZ, hLZs]
    gcongr ?_ - _
    apply setIntegral_mono_on hIZ hIZs measurableSet_Ioo
    intro s _
    rw [hZst s]
    exact msDD_point P σ hσ Y hYm Z hZ s
  have hbdd : BddAbove (Set.range fun Z : {Z : Ω → ℝ // DominatedByDistortion P σ Z} =>
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) := by
    refine ⟨distortionFunctional P σ Y, ?_⟩
    rintro _ ⟨Z, rfl⟩
    exact hbound Z
  have : Nonempty {Z : Ω → ℝ // DominatedByDistortion P σ Z} := ⟨⟨Zs, hZsD⟩⟩
  apply le_antisymm
  · have h := le_ciSup hbdd ⟨Zs, hZsD⟩
    rw [hZsY] at h
    exact h
  · exact ciSup_le hbound
