-- Prove2me | solution 1 for HumanAIComp.Bound.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T06:35:36.939482+00:00
-- url     : https://prove2.me/submissions/79a24951-fa3c-4b58-8fd2-a62bf554fe5a

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_HumanAIComp_Bound_MakarovBound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology HumanAIComp.Bound

namespace AC9B

/-- Quantile function (generalised inverse of the cdf), junk value 0 outside `(0,1)`. -/
noncomputable def Q (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then sInf {t | u ≤ cdf μ t} else 0

lemma Q_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (t : ℝ) : Q μ u ≤ t ↔ u ≤ cdf μ t := by
  have hne : {t | u ≤ cdf μ t}.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_order.1 (tendsto_cdf_atTop μ)).1 u hu1).exists
    exact ⟨x, hx.le⟩
  obtain ⟨x0, hx0⟩ := Filter.eventually_atBot.1 ((tendsto_order.1 (tendsto_cdf_atBot μ)).2 u hu0)
  have hbdd : BddBelow {t | u ≤ cdf μ t} := by
    refine ⟨x0, fun t ht => ?_⟩
    by_contra h
    push_neg at h
    have h1 := hx0 t h.le
    have h2 : u ≤ cdf μ t := ht
    linarith
  have hQ : Q μ u = sInf {t | u ≤ cdf μ t} := by
    unfold Q
    exact if_pos ⟨hu0, hu1⟩
  rw [hQ]
  constructor
  · intro h
    have hq : u ≤ cdf μ (sInf {t | u ≤ cdf μ t}) := by
      rw [← (cdf μ).iInf_Ioi_eq (sInf {t | u ≤ cdf μ t})]
      apply le_ciInf
      intro r
      obtain ⟨t, ht, htr⟩ := exists_lt_of_csInf_lt hne r.2
      exact le_trans (show u ≤ cdf μ t from ht) ((cdf μ).mono htr.le)
    exact le_trans hq ((cdf μ).mono h)
  · intro h
    exact csInf_le hbdd h

lemma Q_measurable (μ : Measure ℝ) [IsProbabilityMeasure μ] : Measurable (Q μ) := by
  refine measurable_of_Iic fun t => ?_
  have : Q μ ⁻¹' Iic t = (Ioo 0 1 ∩ Iic (cdf μ t)) ∪ ((Ioo 0 1)ᶜ ∩ {_u | (0 : ℝ) ≤ t}) := by
    ext u
    by_cases h : 0 < u ∧ u < 1
    · have := Q_le_iff μ h.1 h.2 t
      simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_Ioo, mem_compl_iff,
        mem_setOf_eq]
      tauto
    · have hQ : Q μ u = 0 := by
        unfold Q
        exact if_neg h
      simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_Ioo, mem_compl_iff,
        mem_setOf_eq, hQ]
      tauto
  rw [this]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

lemma vol_Ioo_inter_Iic (p q x : ℝ) :
    volume (Ioo p q ∩ Iic x) = ENNReal.ofReal (min q x - p) := by
  rcases le_or_gt q x with h | h
  · have : Ioo p q ∩ Iic x = Ioo p q := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, and_iff_left_iff_imp]
      intro hu
      linarith [hu.2]
    rw [this, Real.volume_Ioo, min_eq_left h]
  · have : Ioo p q ∩ Iic x = Ioc p x := by
      ext u
      simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [this, Real.volume_Ioc, min_eq_right h.le]

lemma map_Q_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] {p q c : ℝ}
    (hp : 0 ≤ p + c) (hq : q + c ≤ 1) (t : ℝ) :
    ((volume.restrict (Ioo p q)).map (fun u => Q μ (u + c))) (Iic t)
      = ENNReal.ofReal (min q (cdf μ t - c) - p) := by
  have hm : Measurable (fun u : ℝ => Q μ (u + c)) :=
    (Q_measurable μ).comp (measurable_add_const c)
  rw [Measure.map_apply hm measurableSet_Iic,
    Measure.restrict_apply (hm measurableSet_Iic), ← vol_Ioo_inter_Iic]
  congr 1
  ext u
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h2, h3⟩, ?_⟩
    have := (Q_le_iff μ (by linarith) (by linarith) t).1 h1
    linarith
  · rintro ⟨⟨h2, h3⟩, h1⟩
    exact ⟨(Q_le_iff μ (by linarith) (by linarith) t).2 (by linarith), h2, h3⟩

lemma part_one {Ω : Type*} [MeasurableSpace Ω] (δ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b) :
    makarovBound δ (P.map a) (P.map b) ≤ P.real {ω | δ < b ω - a ω} := by
  haveI : IsProbabilityMeasure (P.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  haveI : IsProbabilityMeasure (P.map b) := Measure.isProbabilityMeasure_map hb.aemeasurable
  unfold makarovBound
  apply ciSup_le
  intro t
  rw [cdf_eq_real (P.map a) t, cdf_eq_real (P.map b) (t + δ),
    map_measureReal_apply ha measurableSet_Iic, map_measureReal_apply hb measurableSet_Iic]
  have hsub : a ⁻¹' Iic t ⊆ {ω | δ < b ω - a ω} ∪ b ⁻¹' Iic (t + δ) := by
    intro ω hω
    simp only [mem_preimage, mem_Iic] at hω
    by_cases h : b ω ≤ t + δ
    · exact Or.inr h
    · left
      simp only [mem_setOf_eq]
      push_neg at h
      linarith
  have := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  linarith

lemma bound_bdd (δ : ℝ) (μa μb : Measure ℝ) :
    BddAbove (Set.range fun t : ℝ => cdf μa t - cdf μb (t + δ)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  show cdf μa t - cdf μb (t + δ) ≤ 1
  linarith [cdf_le_one μa t, cdf_nonneg μb (t + δ)]

lemma bound_nonneg (δ : ℝ) (μa μb : Measure ℝ) : 0 ≤ makarovBound δ μa μb := by
  have h1 : Tendsto (fun t => cdf μa t - cdf μb (t + δ)) atTop (𝓝 (1 - 1)) :=
    (tendsto_cdf_atTop μa).sub
      ((tendsto_cdf_atTop μb).comp (tendsto_atTop_add_const_right atTop δ tendsto_id))
  rw [sub_self] at h1
  exact le_of_tendsto' h1 (fun t => le_ciSup (bound_bdd δ μa μb) t)

lemma bound_le_one (δ : ℝ) (μa μb : Measure ℝ) : makarovBound δ μa μb ≤ 1 := by
  unfold makarovBound
  exact ciSup_le fun t => by linarith [cdf_le_one μa t, cdf_nonneg μb (t + δ)]

noncomputable def cpl1 (μa μb : Measure ℝ) (s : ℝ) (u : ℝ) : ℝ × ℝ :=
  (Q μa (u + 0), Q μb (u + -s))

noncomputable def cpl2 (μa μb : Measure ℝ) (s : ℝ) (u : ℝ) : ℝ × ℝ :=
  (Q μa (u + 0), Q μb (u + (1 - s)))

lemma cpl1_meas (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (s : ℝ) : Measurable (cpl1 μa μb s) :=
  ((Q_measurable μa).comp (measurable_add_const _)).prodMk
    ((Q_measurable μb).comp (measurable_add_const _))

lemma cpl2_meas (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    (s : ℝ) : Measurable (cpl2 μa μb s) :=
  ((Q_measurable μa).comp (measurable_add_const _)).prodMk
    ((Q_measurable μb).comp (measurable_add_const _))

lemma cpl_fst (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((volume.restrict (Ioo s 1)).map (cpl1 μa μb s)
      + (volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)).map Prod.fst = μa := by
  have e1 : ((volume.restrict (Ioo s 1)).map (cpl1 μa μb s)).map Prod.fst
      = (volume.restrict (Ioo s 1)).map (fun u => Q μa (u + 0)) := by
    rw [Measure.map_map measurable_fst (cpl1_meas μa μb s)]
    rfl
  have e2 : ((volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)).map Prod.fst
      = (volume.restrict (Ioo 0 s)).map (fun u => Q μa (u + 0)) := by
    rw [Measure.map_map measurable_fst (cpl2_meas μa μb s)]
    rfl
  rw [Measure.map_add _ _ measurable_fst, e1, e2]
  refine (Measure.ext_of_Iic μa _ (fun t => ?_)).symm
  rw [Measure.add_apply,
    map_Q_Iic μa (p := s) (q := 1) (c := 0) (by linarith) (by linarith),
    map_Q_Iic μa (p := 0) (q := s) (c := 0) (by linarith) (by linarith),
    ← ofReal_cdf μa t]
  have h0 := cdf_nonneg μa t
  have h1 := cdf_le_one μa t
  rcases le_total (cdf μa t) s with h | h
  · have e3 : min 1 (cdf μa t - 0) - s ≤ 0 := by
      have := min_le_right 1 (cdf μa t - 0)
      linarith
    have e4 : min s (cdf μa t - 0) - 0 = cdf μa t := by
      rw [min_eq_right (by linarith)]
      ring
    rw [ENNReal.ofReal_of_nonpos e3, e4, zero_add]
  · have e3 : min 1 (cdf μa t - 0) - s = cdf μa t - s := by
      rw [min_eq_right (by linarith)]
      ring
    have e4 : min s (cdf μa t - 0) - 0 = s := by
      rw [min_eq_left (by linarith)]
      ring
    have hp : (0 : ℝ) ≤ cdf μa t - s := by linarith
    rw [e3, e4, ← ENNReal.ofReal_add hp hs0, sub_add_cancel]

lemma cpl_snd (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ((volume.restrict (Ioo s 1)).map (cpl1 μa μb s)
      + (volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)).map Prod.snd = μb := by
  have e1 : ((volume.restrict (Ioo s 1)).map (cpl1 μa μb s)).map Prod.snd
      = (volume.restrict (Ioo s 1)).map (fun u => Q μb (u + -s)) := by
    rw [Measure.map_map measurable_snd (cpl1_meas μa μb s)]
    rfl
  have e2 : ((volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)).map Prod.snd
      = (volume.restrict (Ioo 0 s)).map (fun u => Q μb (u + (1 - s))) := by
    rw [Measure.map_map measurable_snd (cpl2_meas μa μb s)]
    rfl
  rw [Measure.map_add _ _ measurable_snd, e1, e2]
  refine (Measure.ext_of_Iic μb _ (fun t => ?_)).symm
  rw [Measure.add_apply,
    map_Q_Iic μb (p := s) (q := 1) (c := -s) (by linarith) (by linarith),
    map_Q_Iic μb (p := 0) (q := s) (c := 1 - s) (by linarith) (by linarith),
    ← ofReal_cdf μb t]
  have h0 := cdf_nonneg μb t
  have h1 := cdf_le_one μb t
  rcases le_total (cdf μb t + s) 1 with h | h
  · have e3 : min 1 (cdf μb t - -s) - s = cdf μb t := by
      rw [min_eq_right (by linarith)]
      ring
    have e4 : min s (cdf μb t - (1 - s)) - 0 ≤ 0 := by
      have := min_le_right s (cdf μb t - (1 - s))
      linarith
    rw [e3, ENNReal.ofReal_of_nonpos e4, add_zero]
  · have e3 : min 1 (cdf μb t - -s) - s = 1 - s := by
      rw [min_eq_left (by linarith)]
    have e4 : min s (cdf μb t - (1 - s)) - 0 = cdf μb t - (1 - s) := by
      rw [min_eq_right (by linarith)]
      ring
    have hp : (0 : ℝ) ≤ 1 - s := by linarith
    have hq : (0 : ℝ) ≤ cdf μb t - (1 - s) := by linarith
    rw [e3, e4, ← ENNReal.ofReal_add hp hq]
    congr 1
    ring

lemma part_two (δ : ℝ) (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb] :
    ∃ π ∈ MongeKantorovichYao.transferencePlans μa μb,
      π.real {p : ℝ × ℝ | δ < p.2 - p.1} = makarovBound δ μa μb := by
  have hkey : ∀ t, cdf μa t - makarovBound δ μa μb ≤ cdf μb (t + δ) := fun t => by
    have : cdf μa t - cdf μb (t + δ) ≤ makarovBound δ μa μb := le_ciSup (bound_bdd δ μa μb) t
    linarith
  have hs0 := bound_nonneg δ μa μb
  have hs1 := bound_le_one δ μa μb
  set s := makarovBound δ μa μb with hs
  have hfst := cpl_fst μa μb hs0 hs1
  have hsnd := cpl_snd μa μb hs0 hs1
  have hE : MeasurableSet {p : ℝ × ℝ | δ < p.2 - p.1} :=
    measurableSet_lt measurable_const (measurable_snd.sub measurable_fst)
  have hf1 := cpl1_meas μa μb s
  have hf2 := cpl2_meas μa μb s
  have hπ1 : ((volume.restrict (Ioo s 1)).map (cpl1 μa μb s)) {p : ℝ × ℝ | δ < p.2 - p.1} = 0 := by
    rw [Measure.map_apply hf1 hE, Measure.restrict_apply (hf1 hE)]
    have hempty : cpl1 μa μb s ⁻¹' {p : ℝ × ℝ | δ < p.2 - p.1} ∩ Ioo s 1 = ∅ := by
      ext u
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨hu, hsu, hu1⟩
      simp only [mem_preimage, mem_setOf_eq, cpl1] at hu
      have hA := (Q_le_iff μa (u := u + 0) (by linarith) (by linarith) (Q μa (u + 0))).1 le_rfl
      have hB : Q μb (u + -s) ≤ Q μa (u + 0) + δ :=
        (Q_le_iff μb (by linarith) (by linarith) _).2 (by linarith [hkey (Q μa (u + 0))])
      linarith
    rw [hempty, measure_empty]
  have hπ2 : ((volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)) {p : ℝ × ℝ | δ < p.2 - p.1}
      ≤ ENNReal.ofReal s := by
    calc ((volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)) {p : ℝ × ℝ | δ < p.2 - p.1}
        ≤ ((volume.restrict (Ioo 0 s)).map (cpl2 μa μb s)) univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal s := by
        rw [Measure.map_apply hf2 MeasurableSet.univ, preimage_univ,
          Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
  set π := (volume.restrict (Ioo s 1)).map (cpl1 μa μb s)
      + (volume.restrict (Ioo 0 s)).map (cpl2 μa μb s) with hπ
  have hprob : IsProbabilityMeasure π := by
    constructor
    have h := congrArg (fun m : Measure ℝ => m univ) hfst
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, measure_univ (μ := μa)] at h
    exact h
  have hle : π.real {p : ℝ × ℝ | δ < p.2 - p.1} ≤ s := by
    rw [measureReal_def]
    apply ENNReal.toReal_le_of_le_ofReal hs0
    rw [hπ, Measure.add_apply, hπ1, zero_add]
    exact hπ2
  refine ⟨π, ⟨hprob, hfst, hsnd⟩, le_antisymm hle ?_⟩
  have h := part_one δ π Prod.fst Prod.snd measurable_fst measurable_snd
  rw [hfst, hsnd] at h
  exact h

end AC9B

open MeasureTheory ProbabilityTheory HumanAIComp.Bound in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ (P : Measure Ω) [IsProbabilityMeasure P] (a b : Ω → ℝ), Measurable a → Measurable b →
        makarovBound δ (P.map a) (P.map b) ≤ P.real {ω | δ < b ω - a ω}) ∧
    (∀ (μa μb : Measure ℝ) [IsProbabilityMeasure μa] [IsProbabilityMeasure μb],
        ∃ π ∈ MongeKantorovichYao.transferencePlans μa μb,
          π.real {p : ℝ × ℝ | δ < p.2 - p.1} = makarovBound δ μa μb) := by
  constructor
  · intro P _ a b ha hb
    exact AC9B.part_one δ P a b ha hb
  · intro μa μb _ _
    exact AC9B.part_two δ μa μb
