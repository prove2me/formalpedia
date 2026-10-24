-- Prove2me | solution 1 for MultistageStochastic.avar_dual_representation_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:50:57.288003+00:00
-- url     : https://prove2.me/submissions/e14b235c-571e-44c4-9dad-b7b672ce3d92

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory

namespace AV88
noncomputable def g79q_F (μ : Measure ℝ) (u : ℝ) : ℝ := μ.real (Set.Iic u)

noncomputable def g79q_q (μ : Measure ℝ) (p : ℝ) : ℝ := sInf {u : ℝ | p ≤ g79q_F μ u}

theorem g79q_cdf_eq_real (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    ProbabilityTheory.cdf μ v = g79q_F μ v := ProbabilityTheory.cdf_eq_real μ v

theorem g79q_qle (μ : Measure ℝ) [IsProbabilityMeasure μ] (p u : ℝ)
    (hp : 0 < p) (hfin : ∃ v : ℝ, p ≤ g79q_F μ v) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := by
  have hF : ∀ v, g79q_F μ v = ProbabilityTheory.cdf μ v := fun v =>
    (g79q_cdf_eq_real μ v).symm
  set S := {u : ℝ | p ≤ g79q_F μ u} with hS
  have hne : S.Nonempty := hfin
  have hbdd : BddBelow S := by
    have h := (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (gt_mem_nhds hp)
    obtain ⟨L, hL⟩ := Filter.eventually_atBot.1 h
    refine ⟨L, fun v hv => ?_⟩
    by_contra hlt
    have := hL v (le_of_lt (lt_of_not_ge hlt))
    have hv' : p ≤ g79q_F μ v := hv
    rw [hF] at hv'
    linarith
  have hmono : Monotone (g79q_F μ) := fun a b hab => by
    rw [hF, hF]; exact (ProbabilityTheory.cdf μ).mono hab
  constructor
  · intro hq
    have hQ : p ≤ g79q_F μ (g79q_q μ p) := by
      have hev : ∀ᶠ v in nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)),
          p ≤ ProbabilityTheory.cdf μ v := by
        filter_upwards [self_mem_nhdsWithin] with v hv
        obtain ⟨w, hwS, hwv⟩ := exists_lt_of_csInf_lt hne hv
        have : p ≤ g79q_F μ w := hwS
        rw [← hF]; exact this.trans (hmono hwv.le)
      have ht : Filter.Tendsto (ProbabilityTheory.cdf μ)
          (nhdsWithin (g79q_q μ p) (Set.Ioi (g79q_q μ p)))
          (nhds (ProbabilityTheory.cdf μ (g79q_q μ p))) :=
        ((ProbabilityTheory.cdf μ).right_continuous _).tendsto.mono_left
          (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
      rw [hF]
      exact ge_of_tendsto ht hev
    exact hQ.trans (hmono hq)
  · intro hu
    exact csInf_le hbdd hu

theorem g79q_q_nonpos (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ) (hp : p ≤ 0) :
    g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    refine le_trans hp ?_
    unfold g79q_F; exact measureReal_nonneg
  rw [this]
  exact Real.sInf_of_not_bddBelow not_bddBelow_univ

theorem g79q_q_nowit (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : ℝ)
    (h : ¬ ∃ v, p ≤ g79q_F μ v) : g79q_q μ p = 0 := by
  unfold g79q_q
  have : {u : ℝ | p ≤ g79q_F μ u} = ∅ := by
    ext u; simp only [Set.mem_empty_iff_false, iff_false]; exact fun hu => h ⟨u, hu⟩
  rw [this, Real.sInf_empty]

theorem g79q_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] : Monotone (g79q_F μ) := by
  intro a b hab
  unfold g79q_F
  exact measureReal_mono (Set.Iic_subset_Iic.2 hab)

theorem g79q_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (g79q_q μ) := by
  set A : Set ℝ := Set.Ioi 0 ∩ ⋃ n : ℕ, Set.Iic (g79q_F μ n) with hA
  have hAm : MeasurableSet A :=
    measurableSet_Ioi.inter (MeasurableSet.iUnion (fun _ => measurableSet_Iic))
  have hAiff : ∀ p, p ∈ A ↔ 0 < p ∧ ∃ v, p ≤ g79q_F μ v := by
    intro p
    simp only [hA, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · rintro ⟨h0, n, hn⟩; exact ⟨h0, n, hn⟩
    · rintro ⟨h0, v, hv⟩
      obtain ⟨n, hn⟩ := exists_nat_ge v
      exact ⟨h0, n, hv.trans (g79q_mono μ hn)⟩
  refine measurable_of_Iic (fun x => ?_)
  have : g79q_q μ ⁻¹' Set.Iic x =
      (A ∩ Set.Iic (g79q_F μ x)) ∪ (Aᶜ ∩ {_p | 0 ≤ x}) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq]
    by_cases hp : p ∈ A
    · have := (hAiff p).1 hp
      rw [g79q_qle μ p x this.1 this.2]
      simp [hp]
    · have h0 : g79q_q μ p = 0 := by
        by_cases hp0 : p ≤ 0
        · exact g79q_q_nonpos μ p hp0
        · exact g79q_q_nowit μ p (fun hw => hp ((hAiff p).2 ⟨lt_of_not_ge hp0, hw⟩))
      simp [hp, h0]
  rw [this]
  exact (hAm.inter measurableSet_Iic).union (hAm.compl.inter (MeasurableSet.const _))

theorem g79q_transform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → ℝ) (hU : Measurable U) (hunif : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)) :
    P.map (fun ω => g79q_q μ (U ω)) = μ := by
  have hf := g79q_meas μ
  have hcomp : P.map (fun ω => g79q_q μ (U ω)) =
      (P.map U).map (g79q_q μ) := by
    rw [Measure.map_map hf hU]; rfl
  rw [hcomp, hunif]
  have hrestr : (volume.restrict (Set.Icc (0 : ℝ) 1)) = volume.restrict (Set.Ioo (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [hrestr]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    constructor; rw [Measure.restrict_apply_univ]; simp
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hf measurableSet_Iic,
    Measure.restrict_apply (hf measurableSet_Iic)]
  set g := g79q_F μ x with hg
  have hset : g79q_q μ ⁻¹' Set.Iic x ∩ Set.Ioo 0 1 = Set.Iic g ∩ Set.Ioo 0 1 := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h0, h1'⟩
      refine ⟨?_, h0, h1'⟩
      have hw : ∃ v, p ≤ g79q_F μ v := by
        have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) := by
          have := ProbabilityTheory.tendsto_cdf_atTop μ
          refine this.congr (fun v => ?_)
          exact g79q_cdf_eq_real μ v
        obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds h1')).exists
        exact ⟨v, hv.le⟩
      exact (g79q_qle μ p x h0 hw).1 h1
    · rintro ⟨h1, h0, h1'⟩
      exact ⟨(g79q_qle μ p x h0 ⟨x, h1⟩).2 h1, h0, h1'⟩
  rw [hset]
  have hg0 : 0 ≤ g := measureReal_nonneg
  have hg1 : g ≤ 1 := by
    rw [hg]; unfold g79q_F; exact measureReal_le_one
  have hμx : μ (Set.Iic x) = ENNReal.ofReal g := by
    rw [hg]; unfold g79q_F
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hμx]
  apply le_antisymm
  · calc volume (Set.Iic g ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc 0 g) := by
          apply measure_mono
          rintro p ⟨h1, h0, -⟩; exact ⟨h0, h1⟩
      _ = ENNReal.ofReal g := by simp
  · calc ENNReal.ofReal g = volume (Set.Ioo 0 g) := by simp
      _ ≤ volume (Set.Iic g ∩ Set.Ioo 0 1) := by
          apply measure_mono
          rintro p ⟨h0, h1⟩; exact ⟨h1.le, h0, lt_of_lt_of_le h1 hg1⟩

theorem g79q_wit (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp : p < 1) :
    ∃ v, p ≤ g79q_F μ v := by
  have hlim : Filter.Tendsto (g79q_F μ) Filter.atTop (nhds 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).congr (fun v => g79q_cdf_eq_real μ v)
  obtain ⟨v, hv⟩ := (hlim.eventually (lt_mem_nhds hp)).exists
  exact ⟨v, hv.le⟩

theorem g79q_qle' (μ : Measure ℝ) [IsProbabilityMeasure μ] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (u : ℝ) :
    g79q_q μ p ≤ u ↔ p ≤ g79q_F μ u := g79q_qle μ p u hp0 (g79q_wit μ hp1)


theorem g79q_Iio_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ)
    (h : ∀ y < a, g79q_F μ y ≤ t) : μ.real (Set.Iio a) ≤ t := by
  have hU : Set.Iio a = ⋃ n : ℕ, Set.Iic (a - 1 / ((n : ℝ) + 1)) := by
    ext v; simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hv
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hv)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone (fun n : ℕ => Set.Iic (a - 1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    apply Set.Iic_subset_Iic.mpr
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have ht : 0 ≤ t := le_trans measureReal_nonneg (h (a - 1) (by linarith))
  have hE : μ (Set.Iio a) ≤ ENNReal.ofReal t := by
    rw [hU, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have := h (a - 1 / ((n : ℝ) + 1)) (by linarith)
    unfold g79q_F at this
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal this
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal ht hE
theorem g79c_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] {u v : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hv : v < 1) : g79q_q μ u ≤ g79q_q μ v := by
  rw [g79q_qle' μ hu (lt_of_le_of_lt huv hv)]
  exact huv.trans ((g79q_qle' μ (lt_of_lt_of_le hu huv) hv _).1 le_rfl)

/-- integrals against the law as integrals of the quantile function -/
theorem g79n_E (μ : Measure ℝ) [IsProbabilityMeasure μ] (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable g μ) :
    IntegrableOn (fun u => g (g79q_q μ u)) (Set.Icc 0 1) ∧
    ∫ y, g y ∂μ = ∫ u in (0:ℝ)..1, g (g79q_q μ u) := by
  have hP : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have htr' : (volume.restrict (Set.Icc (0 : ℝ) 1)).map (g79q_q μ) = μ :=
    g79q_transform μ (volume.restrict (Set.Icc (0 : ℝ) 1)) id measurable_id Measure.map_id
  have hmeas := g79q_meas μ
  constructor
  · have h := hgi
    rw [← htr'] at h
    exact (integrable_map_measure hg.aestronglyMeasurable hmeas.aemeasurable).1 h
  · conv_lhs => rw [← htr']
    rw [integral_map hmeas.aemeasurable hg.aestronglyMeasurable,
      intervalIntegral.integral_of_le zero_le_one]
    exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm

/-- Rockafellar–Uryasev in quantile form, 0 < α < 1 -/
theorem g79n_RU (μ : Measure ℝ) [IsProbabilityMeasure μ] (hI : Integrable (fun y : ℝ => y) μ)
    {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    (∀ x : ℝ, α * x - ∫ y, max (x - y) 0 ∂μ ≤ ∫ u in (0:ℝ)..α, g79q_q μ u) ∧
    α * g79q_q μ α - ∫ y, max (g79q_q μ α - y) 0 ∂μ = ∫ u in (0:ℝ)..α, g79q_q μ u := by
  set q := g79q_q μ with hqdef
  have hqI : IntegrableOn q (Set.Icc 0 1) := by
    simpa using (g79n_E μ (fun y => y) measurable_id hI).1
  have hpI : ∀ x : ℝ, IntegrableOn (fun u => max (x - q u) 0) (Set.Icc 0 1) ∧
      ∫ y, max (x - y) 0 ∂μ = ∫ u in (0:ℝ)..1, max (x - q u) 0 := by
    intro x
    exact g79n_E μ (fun y => max (x - y) 0) (by fun_prop) ((integrable_const x).sub hI).pos_part
  have hII : ∀ (f : ℝ → ℝ), IntegrableOn f (Set.Icc 0 1) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable f volume a b := by
    intro f hf a b ha hab hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb))
  have hsplit : ∀ x : ℝ, ∫ u in (0:ℝ)..1, max (x - q u) 0 =
      (∫ u in (0:ℝ)..α, max (x - q u) 0) + ∫ u in α..1, max (x - q u) 0 := fun x =>
    (intervalIntegral.integral_add_adjacent_intervals (hII _ (hpI x).1 0 α le_rfl h0.le h1.le)
      (hII _ (hpI x).1 α 1 h0.le h1.le le_rfl)).symm
  constructor
  · intro x
    rw [(hpI x).2, hsplit x]
    have hnn : 0 ≤ ∫ u in α..(1:ℝ), max (x - q u) 0 :=
      intervalIntegral.integral_nonneg h1.le (fun u _ => le_max_right _ _)
    -- ∫_0^α (q - x + (x - q)^+) ≥ 0
    have hA : ∫ u in (0:ℝ)..α, (q u - x + max (x - q u) 0) =
        (∫ u in (0:ℝ)..α, q u) - α * x + ∫ u in (0:ℝ)..α, max (x - q u) 0 := by
      rw [intervalIntegral.integral_add ((hII q hqI 0 α le_rfl h0.le h1.le).sub
          intervalIntegrable_const) (hII _ (hpI x).1 0 α le_rfl h0.le h1.le),
        intervalIntegral.integral_sub (hII q hqI 0 α le_rfl h0.le h1.le) intervalIntegrable_const]
      simp
      try ring
    have hB : 0 ≤ ∫ u in (0:ℝ)..α, (q u - x + max (x - q u) 0) :=
      intervalIntegral.integral_nonneg h0.le (fun u _ => by
        rcases le_total (x - q u) 0 with h | h
        · rw [max_eq_right h]; linarith
        · rw [max_eq_left h]; linarith)
    linarith
  · rw [(hpI (q α)).2, hsplit (q α)]
    have hz : ∫ u in α..(1:ℝ), max (q α - q u) 0 = 0 := by
      rw [intervalIntegral.integral_of_le h1.le, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
      refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
      exact max_eq_right (by linarith [g79c_mono μ h0 hu.1.le hu.2])
    have he : ∫ u in (0:ℝ)..α, max (q α - q u) 0 = ∫ u in (0:ℝ)..α, (q α - q u) := by
      rw [intervalIntegral.integral_of_le h0.le, intervalIntegral.integral_of_le h0.le]
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      exact max_eq_left (by linarith [g79c_mono μ hu.1 hu.2 h1])
    rw [hz, he, intervalIntegral.integral_sub intervalIntegrable_const
      (hII q hqI 0 α le_rfl h0.le h1.le)]
    simp

end AV88

open MeasureTheory

namespace AV88
open MultistageStochastic

theorem var_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (u : ℝ) :
    valueAtRisk P Z u = g79q_q (P.map Z) u := by
  unfold valueAtRisk g79q_q g79q_F
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [measureReal_def, Measure.map_apply hZ measurableSet_Iic,
    ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  exact Iff.rfl

theorem F_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (y : ℝ) :
    g79q_F (P.map Z) y = P.real {ω | Z ω ≤ y} := by
  unfold g79q_F
  rw [measureReal_def, measureReal_def, Measure.map_apply hZ measurableSet_Iic]
  rfl

theorem ae_one {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : Ω → Prop) (hs : MeasurableSet {ω | p ω}) (h : ∀ᵐ ω ∂P, p ω) :
    P.real {ω | p ω} = 1 := by
  have h0 : P {ω | p ω}ᶜ = 0 := by
    rw [show ({ω | p ω}ᶜ) = {ω | ¬ p ω} from rfl]
    exact ae_iff.1 h
  rw [measureReal_def, (prob_compl_eq_zero_iff hs).1 h0]
  simp

theorem ru {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) :
    ∃ q : ℝ, P.real {ω | q < Y ω} ≤ 1 - α ∧ 1 - α ≤ P.real {ω | q ≤ Y ω} ∧
      averageValueAtRisk P Y α = q + (1 - α)⁻¹ * ∫ ω, max (Y ω - q) 0 ∂P := by
  obtain ⟨hYm, C, hC⟩ := hY
  have hYi : Integrable Y P :=
    Integrable.of_bound hYm.aestronglyMeasurable C (by simpa [Real.norm_eq_abs] using hC)
  set μ := P.map Y with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hYm.aemeasurable
  have hI : Integrable (fun y : ℝ => y) μ :=
    (integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).2 hYi
  have hne : α ≠ 1 := h1.ne
  have hAV : averageValueAtRisk P Y α = (1 - α)⁻¹ * ∫ p in Set.Ioo α 1, g79q_q μ p := by
    unfold averageValueAtRisk; rw [if_neg hne]; simp_rw [var_eq P Y hYm]; rfl
  have hqI : IntegrableOn (g79q_q μ) (Set.Icc 0 1) := by
    simpa using (g79n_E μ (fun y => y) measurable_id hI).1
  have hEY : ∫ u in (0:ℝ)..1, g79q_q μ u = ∫ ω, Y ω ∂P := by
    have := (g79n_E μ (fun y => y) measurable_id hI).2
    rw [← this]
    exact integral_map hYm.aemeasurable aestronglyMeasurable_id
  have hIoo : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      ∫ p in Set.Ioo a 1, g79q_q μ p = (∫ u in (0:ℝ)..1, g79q_q μ u) - ∫ u in (0:ℝ)..a, g79q_q μ u := by
    intro a ha0 ha1
    have hII : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable (g79q_q μ) volume a b := by
      intro a b ha hab hb
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      exact hqI.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc ha hb))
    have h := intervalIntegral.integral_add_adjacent_intervals (hII 0 a le_rfl ha0 ha1)
      (hII a 1 ha0 ha1 le_rfl)
    have h2 : ∫ u in a..1, g79q_q μ u = ∫ p in Set.Ioo a 1, g79q_q μ p := by
      rw [intervalIntegral.integral_of_le ha1]; exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm
    linarith
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · -- α = 0
    subst h0'
    refine ⟨-C - 1, ?_, ?_, ?_⟩
    · simpa using (measureReal_le_one (μ := P) (s := {ω | -C - 1 < Y ω}))
    · have hae : ∀ᵐ ω ∂P, -C - 1 ≤ Y ω := by
        filter_upwards [hC] with ω hω
        linarith [(abs_le.1 hω).1]
      rw [ae_one P _ (measurableSet_le measurable_const hYm) hae]
      simp
    · have h00 : ∫ u in (0:ℝ)..0, g79q_q μ u = 0 := intervalIntegral.integral_same
      have hA0 : averageValueAtRisk P Y 0 = ∫ ω, Y ω ∂P := by
        rw [hAV, hIoo 0 le_rfl zero_le_one]; simp only [sub_zero, inv_one, one_mul]; linarith
      rw [hA0]
      have hae : ∀ᵐ ω ∂P, max (Y ω - (-C - 1)) 0 = Y ω - (-C - 1) := by
        filter_upwards [hC] with ω hω
        exact max_eq_left (by linarith [(abs_le.1 hω).1])
      rw [integral_congr_ae hae, integral_sub hYi (integrable_const _)]
      simp
  · set q := g79q_q μ α with hq
    have hF : α ≤ P.real {ω | Y ω ≤ q} := by
      rw [← F_eq P Y hYm]; exact (g79q_qle' μ h0' h1 q).1 le_rfl
    have hlt : P.real {ω | Y ω < q} ≤ α := by
      have := g79q_Iio_le μ q α (fun y hy => by
        by_contra h
        push_neg at h
        have := (g79q_qle' μ h0' h1 y).2 h.le
        linarith)
      rw [measureReal_def, hμ, Measure.map_apply hYm measurableSet_Iio] at this
      exact this
    have hc1 : P.real {ω | q < Y ω} = 1 - P.real {ω | Y ω ≤ q} := by
      rw [← probReal_compl_eq_one_sub (measurableSet_le hYm measurable_const)]
      congr 1; ext ω; simp
    have hc2 : P.real {ω | q ≤ Y ω} = 1 - P.real {ω | Y ω < q} := by
      rw [← probReal_compl_eq_one_sub (measurableSet_lt hYm measurable_const)]
      congr 1; ext ω; simp
    refine ⟨q, by linarith, by linarith, ?_⟩
    obtain ⟨-, hRU2⟩ := g79n_RU μ hI h0' h1
    have hmap : ∫ y, max (q - y) 0 ∂μ = ∫ ω, max (q - Y ω) 0 ∂P :=
      integral_map hYm.aemeasurable (by fun_prop)
    have hpt : ∀ ω, max (Y ω - q) 0 = (Y ω - q) + max (q - Y ω) 0 := by
      intro ω
      rcases le_total (Y ω) q with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have hint : ∫ ω, max (Y ω - q) 0 ∂P = (∫ ω, Y ω ∂P) - q + ∫ ω, max (q - Y ω) 0 ∂P := by
      simp_rw [hpt]
      rw [integral_add (f := fun ω => Y ω - q) (g := fun ω => max (q - Y ω) 0)
        (hYi.sub (integrable_const q)) ((integrable_const q).sub hYi).pos_part,
        integral_sub hYi (integrable_const q)]
      simp
    rw [hAV, hIoo α h0 h1.le, hEY, ← hRU2, hmap, hint]
    have : (1 - α) ≠ 0 := by linarith
    field_simp
    ring

theorem upper {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLinfty P Y) (q c : ℝ) (Z : Ω → ℝ) (hZi : Integrable Z P)
    (hZ1 : ∫ ω, Z ω ∂P = 1) (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ c) :
    ∫ ω, Y ω * Z ω ∂P ≤ q + c * ∫ ω, max (Y ω - q) 0 ∂P := by
  obtain ⟨hYm, C, hC⟩ := hY
  have hC' : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ C := by simpa [Real.norm_eq_abs] using hC
  have hYi : Integrable Y P := Integrable.of_bound hYm.aestronglyMeasurable C hC'
  have hYZ : Integrable (fun ω => Y ω * Z ω) P := hZi.bdd_mul hYm.aestronglyMeasurable hC'
  have key : ∀ᵐ ω ∂P, Y ω * Z ω ≤ q * Z ω + c * max (Y ω - q) 0 := by
    filter_upwards [hZ] with ω ⟨h1, h2⟩
    rcases le_total (Y ω - q) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hI1 : Integrable (fun ω => q * Z ω) P := hZi.const_mul q
  have hI2 : Integrable (fun ω => c * max (Y ω - q) 0) P :=
    (hYi.sub (integrable_const q)).pos_part.const_mul c
  have := integral_mono_ae (g := fun ω => q * Z ω + c * max (Y ω - q) 0) hYZ (hI1.add hI2) key
  rw [integral_add (f := fun ω => q * Z ω) (g := fun ω => c * max (Y ω - q) 0) hI1 hI2,
    integral_const_mul, integral_const_mul, hZ1] at this
  simpa using this

/-- the optimal density -/
theorem opt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hYm : Measurable Y) (hYi : Integrable Y P) (α : ℝ) (h1 : α < 1) (q : ℝ)
    (ha : P.real {ω | q < Y ω} ≤ 1 - α) (hb : 1 - α ≤ P.real {ω | q ≤ Y ω}) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ ω, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹) ∧
      ∫ ω, Y ω * Z ω ∂P = q + (1 - α)⁻¹ * ∫ ω, max (Y ω - q) 0 ∂P := by
  set c := (1 - α)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (by linarith)
  set A := {ω | q < Y ω} with hA
  set B := {ω | Y ω = q} with hB
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hYm
  have hBm : MeasurableSet B := measurableSet_eq_fun hYm measurable_const
  have hdis : Disjoint A B := Set.disjoint_left.2 (fun ω h1 h2 => by
    simp only [hA, hB, Set.mem_setOf_eq] at h1 h2; linarith)
  have hAB : {ω | q ≤ Y ω} = A ∪ B := by
    ext ω; simp only [hA, hB, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact h.le
      · exact h.ge
  rw [hAB, measureReal_union hdis hBm] at hb
  set a := P.real A
  set b := P.real B
  have hb0 : 0 ≤ b := measureReal_nonneg
  set θ := ((1 - α) - a) / b with hθ
  have hθb : θ * b = (1 - α) - a := by
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h] at hb ⊢; simp only [mul_zero]; linarith
    · rw [hθ]; field_simp
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hb0
  have hθ1 : θ ≤ 1 := div_le_one_of_le₀ (by linarith) hb0
  have hIA : Integrable (fun ω => c * A.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1:ℝ)).indicator hAm).const_mul c
  have hIB : Integrable (fun ω => (c * θ) * B.indicator (1 : Ω → ℝ) ω) P :=
    ((integrable_const (1:ℝ)).indicator hBm).const_mul (c * θ)
  have hIZ : Integrable (fun ω => c * A.indicator (1 : Ω → ℝ) ω + (c * θ) * B.indicator 1 ω) P :=
    hIA.add hIB
  have hEZ : ∫ ω, (c * A.indicator (1 : Ω → ℝ) ω + (c * θ) * B.indicator 1 ω) ∂P = 1 := by
    rw [integral_add (f := fun ω => c * A.indicator 1 ω) (g := fun ω => (c * θ) * B.indicator 1 ω)
      hIA hIB,
      integral_const_mul, integral_const_mul, integral_indicator_one hAm,
      integral_indicator_one hBm]
    have : c * a + c * θ * b = c * (θ * b + a) := by ring
    rw [this, hθb, sub_add_cancel, hc]
    exact inv_mul_cancel₀ (by linarith)
  refine ⟨fun ω => c * A.indicator 1 ω + (c * θ) * B.indicator 1 ω, hIZ, hEZ, ?_, ?_⟩
  · intro ω
    by_cases h1 : ω ∈ A
    · have h2 : ω ∉ B := Set.disjoint_left.1 hdis h1
      simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, hc0.le]
    · by_cases h2 : ω ∈ B
      · simp only [Set.indicator_of_mem h2, Set.indicator_of_notMem h1, Pi.one_apply]
        constructor <;> nlinarith
      · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, hc0.le]
  · have hpt : ∀ ω, Y ω * (c * A.indicator 1 ω + (c * θ) * B.indicator 1 ω) =
        q * (c * A.indicator 1 ω + (c * θ) * B.indicator 1 ω) + c * max (Y ω - q) 0 := by
      intro ω
      by_cases h1 : ω ∈ A
      · have h2 : ω ∉ B := Set.disjoint_left.1 hdis h1
        have h1' : q < Y ω := h1
        simp only [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Pi.one_apply,
          max_eq_left (by linarith : 0 ≤ Y ω - q)]
        ring
      · have h1' : ¬ q < Y ω := h1
        rw [max_eq_right (by linarith : Y ω - q ≤ 0)]
        by_cases h2 : ω ∈ B
        · have h2' : Y ω = q := h2
          rw [h2']; ring
        · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    show ∫ ω, Y ω * (c * A.indicator 1 ω + (c * θ) * B.indicator 1 ω) ∂P = _
    simp_rw [hpt]
    rw [integral_add (f := fun ω => q * (c * A.indicator 1 ω + (c * θ) * B.indicator 1 ω))
      (g := fun ω => c * max (Y ω - q) 0) (hIZ.const_mul q)
      ((hYi.sub (integrable_const q)).pos_part.const_mul c), integral_const_mul,
      integral_const_mul, hEZ, mul_one]

end AV88

open MeasureTheory

namespace AV88
open MultistageStochastic

theorem var_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (c : ℝ) (hZ : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ c) (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    0 ≤ valueAtRisk P Z u ∧ valueAtRisk P Z u ≤ c := by
  unfold valueAtRisk
  have hmem : c ∈ {y : ℝ | ENNReal.ofReal u ≤ P {ω | Z ω ≤ y}} := by
    show ENNReal.ofReal u ≤ P {ω | Z ω ≤ c}
    have : {ω | Z ω ≤ c} = Set.univ := Set.eq_univ_of_forall (fun ω => (hZ ω).2)
    rw [this, measure_univ]; exact ENNReal.ofReal_le_one.2 hu1
  have hlb : ∀ y ∈ {y : ℝ | ENNReal.ofReal u ≤ P {ω | Z ω ≤ y}}, 0 ≤ y := by
    intro y hy
    by_contra h
    push_neg at h
    have : {ω | Z ω ≤ y} = ∅ := Set.eq_empty_of_forall_notMem (fun ω hω => by
      have := (hZ ω).1; simp only [Set.mem_setOf_eq] at hω; linarith)
    have hy' : ENNReal.ofReal u ≤ P {ω | Z ω ≤ y} := hy
    rw [this, measure_empty, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hy'
    linarith
  exact ⟨le_csInf ⟨c, hmem⟩ hlb, csInf_le ⟨0, hlb⟩ hmem⟩

theorem avar_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (c : ℝ) (hZ : ∀ ω, 0 ≤ Z ω ∧ Z ω ≤ c) (hc : 0 ≤ c) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : averageValueAtRisk P Z p ≤ c := by
  unfold averageValueAtRisk
  split_ifs with h
  · unfold essSupBook
    refine Real.sSup_le (fun y hy => ?_) hc
    by_contra hlt
    push_neg at hlt
    have : {ω | Z ω ≤ y} = Set.univ := Set.eq_univ_of_forall (fun ω => ((hZ ω).2.trans hlt.le))
    have hy : P {ω | Z ω ≤ y} < 1 := hy
    rw [this, measure_univ] at hy
    exact lt_irrefl _ hy
  · have hp : p < 1 := lt_of_le_of_ne hp1 h
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioo p 1)
      (f := fun u => valueAtRisk P Z u) (C := c) measure_Ioo_lt_top (fun u hu => by
        have := var_bdd P Z c hZ u (by linarith [hu.1]) hu.2.le
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
    rw [Real.volume_real_Ioo_of_le hp1, Real.norm_eq_abs] at hb
    have h1p : 0 < 1 - p := by linarith
    calc (1 - p)⁻¹ * ∫ u in Set.Ioo p 1, valueAtRisk P Z u ≤ (1 - p)⁻¹ * (c * (1 - p)) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) (inv_nonneg.2 h1p.le)
      _ = c := by field_simp

theorem le_of_avar_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZm : Measurable Z) (hZi : Integrable Z P) (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1)
    (hA : ∀ p : ℝ, α ≤ p → p < 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹) :
    ∀ᵐ ω ∂P, Z ω ≤ (1 - α)⁻¹ := by
  set c := (1 - α)⁻¹ with hc
  by_contra hne
  have hpos : P {ω | ¬ Z ω ≤ c} ≠ 0 := fun h => hne (ae_iff.2 h)
  have hU : {ω | ¬ Z ω ≤ c} = ⋃ n : ℕ, {ω | c + 1 / ((n:ℝ) + 1) < Z ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_le]
    constructor
    · intro h; obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h); exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩; have : 0 < 1 / ((n:ℝ)+1) := by positivity
      linarith
  rw [hU] at hpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P {ω | c + 1 / ((n:ℝ) + 1) < Z ω} ≠ 0 := by
    by_contra h; push_neg at h; exact hpos (measure_iUnion_null_iff.2 h)
  set c' := c + 1 / ((n:ℝ) + 1) with hc'
  have hcc : c < c' := by
    have : 0 < 1 / ((n:ℝ)+1) := by positivity
    linarith
  set δ := P.real {ω | c' < Z ω} with hδ
  have hδ0 : 0 < δ := ENNReal.toReal_pos hn (measure_ne_top _ _)
  set μ := P.map Z with hμ
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hZm.aemeasurable
  have hI : Integrable (fun y : ℝ => y) μ :=
    (integrable_map_measure aestronglyMeasurable_id hZm.aemeasurable).2 hZi
  have hqI : IntegrableOn (g79q_q μ) (Set.Icc 0 1) := by
    simpa using (g79n_E μ (fun y => y) measurable_id hI).1
  set p := max α (1 - δ / 2) with hp
  have hp1 : p < 1 := max_lt h1 (by linarith)
  have hαp : α ≤ p := le_max_left _ _
  have hδp : 1 - δ / 2 ≤ p := le_max_right _ _
  have hcomp : P.real {ω | Z ω ≤ c'} = 1 - δ := by
    rw [hδ, ← probReal_compl_eq_one_sub (measurableSet_lt measurable_const hZm)]
    congr 1; ext ω; simp
  have hq : ∀ u ∈ Set.Ioo p 1, c' ≤ g79q_q μ u := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1, hαp]
    by_contra hlt; push_neg at hlt
    have h2 := (g79q_qle' μ hu0 hu.2 (g79q_q μ u)).1 le_rfl
    rw [F_eq P Z hZm] at h2
    have h3 : P.real {ω | Z ω ≤ g79q_q μ u} ≤ P.real {ω | Z ω ≤ c'} :=
      measureReal_mono (fun ω hω => le_trans hω hlt.le)
    linarith [hu.1]
  have hsub : Set.Ioo p 1 ⊆ Set.Icc 0 1 := fun u hu => ⟨by linarith [hu.1], hu.2.le⟩
  have hint : c' * (1 - p) ≤ ∫ u in Set.Ioo p 1, g79q_q μ u := by
    have := setIntegral_mono_on (integrableOn_const measure_Ioo_lt_top.ne)
      (hqI.mono_set hsub) measurableSet_Ioo hq
    rw [setIntegral_const, Real.volume_real_Ioo_of_le hp1.le, smul_eq_mul] at this
    linarith
  have hav := hA p hαp hp1
  unfold averageValueAtRisk at hav
  rw [if_neg hp1.ne] at hav
  simp_rw [var_eq P Z hZm] at hav
  rw [← hμ] at hav
  have h1p : 0 < 1 - p := by linarith
  have : c' ≤ (1 - p)⁻¹ * ∫ u in Set.Ioo p 1, g79q_q μ u := by
    calc c' = (1 - p)⁻¹ * (c' * (1 - p)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hint (inv_nonneg.2 h1p.le)
  linarith

theorem le_of_avar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZi : Integrable Z P) (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1)
    (hA : ∀ p : ℝ, α ≤ p → p < 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹) :
    ∀ᵐ ω ∂P, Z ω ≤ (1 - α)⁻¹ := by
  set Z' := hZi.aemeasurable.mk Z with hZ'
  have hZZ : Z =ᵐ[P] Z' := hZi.aemeasurable.ae_eq_mk
  have hZ'm : Measurable Z' := hZi.aemeasurable.measurable_mk
  have hvar : ∀ u, valueAtRisk P Z u = valueAtRisk P Z' u := by
    intro u; unfold valueAtRisk
    congr 1; ext y; simp only [Set.mem_setOf_eq]
    rw [measure_congr (s := {ω | Z ω ≤ y}) (t := {ω | Z' ω ≤ y})
      (Filter.eventuallyEq_set.2 (by filter_upwards [hZZ] with ω hω; simp [hω]))]
  have hA' : ∀ p, α ≤ p → p < 1 → averageValueAtRisk P Z' p ≤ (1 - α)⁻¹ := by
    intro p hp hp1
    have := hA p hp hp1
    unfold averageValueAtRisk at this ⊢
    rw [if_neg hp1.ne] at this ⊢
    simp_rw [hvar] at this
    exact this
  filter_upwards [le_of_avar_meas P Z' hZ'm (hZi.congr hZZ) α h0 h1 hA', hZZ] with ω h1 h2
  rw [h2]; exact h1

end AV88

open MeasureTheory

namespace AV88
open MultistageStochastic

theorem part3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    essSupBook P Y = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by
  obtain ⟨hYm, C, hC⟩ := hY
  have hC' : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ C := by simpa [Real.norm_eq_abs] using hC
  set S := {y : ℝ | P {ω | Y ω ≤ y} < 1} with hS
  have hSbdd : BddAbove S := by
    refine ⟨C, fun y hy => ?_⟩
    by_contra hlt; push_neg at hlt
    have hae : ∀ᵐ ω ∂P, Y ω ≤ y := by
      filter_upwards [hC] with ω hω; linarith [(abs_le.1 hω).2]
    have h1 := ae_one P _ (measurableSet_le hYm measurable_const) hae
    have hy' : P {ω | Y ω ≤ y} < 1 := hy
    rw [measureReal_def] at h1
    have : P {ω | Y ω ≤ y} = 1 := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _), h1, ENNReal.ofReal_one]
    rw [this] at hy'; exact lt_irrefl _ hy'
  have hSne : (-C - 1) ∈ S := by
    have hae : ∀ᵐ ω ∂P, ¬ (Y ω ≤ -C - 1) := by
      filter_upwards [hC] with ω hω; rw [not_le]; linarith [(abs_le.1 hω).1]
    have h0 := ae_iff.1 hae
    simp only [not_not] at h0
    show P {ω | Y ω ≤ -C - 1} < 1
    rw [h0]; exact zero_lt_one
  set M := sSup S with hM
  have hYM : ∀ᵐ ω ∂P, Y ω ≤ M := by
    have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, Y ω ≤ M + 1 / ((n:ℝ)+1) := by
      intro n
      have hnot : M + 1/((n:ℝ)+1) ∉ S := fun h => by
        have := le_csSup hSbdd h
        have : 0 < 1/((n:ℝ)+1) := by positivity
        linarith
      have h1 : P {ω | Y ω ≤ M + 1/((n:ℝ)+1)} = 1 := by
        have : ¬ (P {ω | Y ω ≤ M + 1/((n:ℝ)+1)} < 1) := hnot
        exact le_antisymm prob_le_one (not_lt.1 this)
      have h2 := (prob_compl_eq_zero_iff (measurableSet_le hYm measurable_const)).2 h1
      exact ae_iff.2 h2
    filter_upwards [ae_all_iff.2 hn] with ω hω
    by_contra h; push_neg at h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    linarith [hω n]
  have hup : ∀ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P ≤ M := by
    rintro ⟨Z, hZi, hZ1, hZ0⟩
    have hYZ : Integrable (fun ω => Y ω * Z ω) P := hZi.bdd_mul hYm.aestronglyMeasurable hC'
    have := integral_mono_ae hYZ (hZi.const_mul M) (by
      filter_upwards [hYM, hZ0] with ω h1 h2; exact mul_le_mul_of_nonneg_right h1 h2)
    rw [integral_const_mul, hZ1, mul_one] at this
    exact this
  have hlow : ∀ s ∈ S, ∃ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
      s ≤ ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by
    intro s hs
    set A := {ω | s < Y ω} with hA
    have hAm : MeasurableSet A := measurableSet_lt measurable_const hYm
    have hApos : 0 < P.real A := by
      have hc := probReal_compl_eq_one_sub (μ := P) hAm
      have : Aᶜ = {ω | Y ω ≤ s} := by ext ω; simp [A]
      rw [this] at hc
      have hs' : P {ω | Y ω ≤ s} < 1 := hs
      have : P.real {ω | Y ω ≤ s} < 1 := by
        rw [measureReal_def]
        simpa using (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hs'
      linarith
    set r := (P.real A)⁻¹ with hr
    have hr0 : 0 < r := inv_pos.2 hApos
    have hZi : Integrable (fun ω => r * A.indicator (1 : Ω → ℝ) ω) P :=
      ((integrable_const (1:ℝ)).indicator hAm).const_mul r
    have hZ1 : ∫ ω, r * A.indicator (1 : Ω → ℝ) ω ∂P = 1 := by
      rw [integral_const_mul, integral_indicator_one hAm, hr]
      exact inv_mul_cancel₀ hApos.ne'
    have hZ0 : ∀ ω, 0 ≤ r * A.indicator (1 : Ω → ℝ) ω := fun ω =>
      mul_nonneg hr0.le (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    refine ⟨⟨fun ω => r * A.indicator 1 ω, hZi, hZ1, Filter.Eventually.of_forall hZ0⟩, ?_⟩
    show s ≤ ∫ ω, Y ω * (r * A.indicator 1 ω) ∂P
    have hYZ : Integrable (fun ω => Y ω * (r * A.indicator (1 : Ω → ℝ) ω)) P :=
      hZi.bdd_mul hYm.aestronglyMeasurable hC'
    have hpt : ∀ ω, s * (r * A.indicator (1 : Ω → ℝ) ω) ≤ Y ω * (r * A.indicator 1 ω) := by
      intro ω
      by_cases h : ω ∈ A
      · have h' : s < Y ω := h
        rw [Set.indicator_of_mem h]
        simp only [Pi.one_apply, mul_one]
        exact mul_le_mul_of_nonneg_right h'.le hr0.le
      · rw [Set.indicator_of_notMem h]; simp
    have := integral_mono (hZi.const_mul s) hYZ hpt
    rw [integral_const_mul, hZ1, mul_one] at this
    exact this
  have : Nonempty {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω} :=
    ⟨⟨fun _ => 1, integrable_const 1, by simp, Filter.Eventually.of_forall (fun _ => zero_le_one)⟩⟩
  have hB : BddAbove (Set.range fun Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
      ∀ᵐ ω ∂P, 0 ≤ Z ω} => ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) :=
    ⟨M, by rintro _ ⟨Z, rfl⟩; exact hup Z⟩
  have hE : essSupBook P Y = M := rfl
  rw [hE]
  apply le_antisymm
  · refine csSup_le ⟨_, hSne⟩ (fun s hs => ?_)
    obtain ⟨Z, hZ⟩ := hlow s hs
    exact hZ.trans (le_ciSup hB Z)
  · exact ciSup_le hup

theorem part2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α) (h1 : α < 1) :
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by
  obtain ⟨q, ha, hb, hV⟩ := ru P Y hY α hα h1
  have hYi : Integrable Y P := Integrable.of_bound hY.1.aestronglyMeasurable hY.2.choose
    (by simpa [Real.norm_eq_abs] using hY.2.choose_spec)
  obtain ⟨Zs, hZsi, hZs1, hZsb, hZsv⟩ := opt P Y hY.1 hYi α h1 q ha hb
  have hup : ∀ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹},
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P ≤ q + (1 - α)⁻¹ * ∫ ω, max (Y ω - q) 0 ∂P :=
    fun Z => upper P Y hY q _ Z.1 Z.2.1 Z.2.2.1 Z.2.2.2
  have : Nonempty {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹} :=
    ⟨⟨Zs, hZsi, hZs1, Filter.Eventually.of_forall hZsb⟩⟩
  have hB : BddAbove (Set.range fun Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹} => ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) :=
    ⟨_, by rintro _ ⟨Z, rfl⟩; exact hup Z⟩
  rw [hV]
  apply le_antisymm
  · exact le_ciSup_of_le hB ⟨Zs, hZsi, hZs1, Filter.Eventually.of_forall hZsb⟩ hZsv.ge
  · exact ciSup_le hup

theorem part1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α) (h1 : α < 1) :
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by
  obtain ⟨q, ha, hb, hV⟩ := ru P Y hY α hα h1
  have hYi : Integrable Y P := Integrable.of_bound hY.1.aestronglyMeasurable hY.2.choose
    (by simpa [Real.norm_eq_abs] using hY.2.choose_spec)
  obtain ⟨Zs, hZsi, hZs1, hZsb, hZsv⟩ := opt P Y hY.1 hYi α h1 q ha hb
  have hc0 : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 (by linarith)
  have hup : ∀ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹},
      ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P ≤ q + (1 - α)⁻¹ * ∫ ω, max (Y ω - q) 0 ∂P := by
    rintro ⟨Z, hZi, hZ1, hZ0, hZA⟩
    have hle := le_of_avar P Z hZi α hα h1 (fun p hp hp1 => hZA p hp hp1.le)
    exact upper P Y hY q _ Z hZi hZ1 (by filter_upwards [hZ0, hle] with ω h1 h2; exact ⟨h1, h2⟩)
  have hmem : Integrable Zs P ∧ ∫ ω, Zs ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Zs ω) ∧
      ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Zs p ≤ (1 - α)⁻¹ :=
    ⟨hZsi, hZs1, Filter.Eventually.of_forall (fun ω => (hZsb ω).1),
      fun p hp hp1 => avar_bdd P Zs _ hZsb hc0 p (hα.trans hp) hp1⟩
  have : Nonempty {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹} := ⟨⟨Zs, hmem⟩⟩
  have hB : BddAbove (Set.range fun Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
      (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧ ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹} =>
        ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) :=
    ⟨_, by rintro _ ⟨Z, rfl⟩; exact hup Z⟩
  rw [hV]
  apply le_antisymm
  · exact le_ciSup_of_le hB ⟨Zs, hmem⟩ hZsv.ge
  · exact ciSup_le hup

end AV88

open MeasureTheory MultistageStochastic in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α) :
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α = 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) := by
  refine ⟨fun h1 => AV88.part1 P Y hY α hα h1, fun h1 => AV88.part2 P Y hY α hα h1, fun h1 => ?_⟩
  subst h1
  unfold averageValueAtRisk
  rw [if_pos rfl]
  exact AV88.part3 P Y hY

