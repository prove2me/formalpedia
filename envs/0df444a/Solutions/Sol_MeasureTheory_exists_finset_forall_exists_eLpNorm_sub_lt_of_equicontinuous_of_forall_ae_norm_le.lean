-- Prove2me | solution 1 for MeasureTheory.exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fb0bafe7-12eb-5694-97c8-3e94bce4a4b5

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le

set_option autoImplicit false

p2m_open "MeasureTheory P2MW.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.MeasureTheory Topology Filter Set BoundedContinuousFunction MeasureTheory.BoundedContinuousFunction"
p2m_open_scoped "ENNReal NNReal BoundedContinuousFunction.NNReal"

namespace MeasureTheory
p2m_export "MeasureTheory" "Measure.restrict_apply_univ Measure ae_restrict_iff' measure_ne_top ae_restrict_of_ae eLpNorm_add_le eLpNorm_le_of_ae_bound IsFiniteMeasure eLpNorm AEStronglyMeasurable measure_mono eLpNorm_indicator_eq_eLpNorm_restrict"
p2m_open "MeasureTheory"

theorem exists_forall_norm_le_of_equicontinuous_of_isCompact
    {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E] {ι : Type*}
    (u : ι → X → E) (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀) {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ i, ∀ x ∈ K, ‖u i x‖ ≤ B := by
  refine hK.induction_on (p := fun s => ∃ B : ℝ, ∀ i, ∀ x ∈ s, ‖u i x‖ ≤ B)
    ⟨0, fun i x hx => hx.elim⟩
    (fun s t hst h => by obtain ⟨B, hB⟩ := h; exact ⟨B, fun i x hx => hB i x (hst hx)⟩)
    (fun s t h h' => by
      obtain ⟨B, hB⟩ := h; obtain ⟨B', hB'⟩ := h'
      exact ⟨max B B', fun i x hx => hx.elim (fun h => (hB i x h).trans (le_max_left _ _))
        (fun h => (hB' i x h).trans (le_max_right _ _))⟩) ?_
  intro x _
  obtain ⟨C₀, hC₀⟩ := hpt x
  have h1 : ∀ᶠ y in 𝓝 x, ∀ i, dist (u i x) (u i y) < 1 :=
    Metric.equicontinuousAt_iff_right.mp (hequi x) 1 one_pos
  refine ⟨{y | ∀ i, dist (u i x) (u i y) < 1}, mem_nhdsWithin_of_mem_nhds h1, C₀ + 1, fun i y hy => ?_⟩
  have hyi := hy i
  rw [dist_eq_norm] at hyi
  exact (norm_le_insert (u i x) (u i y)).trans (add_le_add (hC₀ i) hyi.le)

end MeasureTheory

p2m_open "MeasureTheory P2MW.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le.MeasureTheory"

theorem solution
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {ι : Type*} (u : ι → X → E) (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℝ≥0∞) (hp₁ : 1 ≤ p) (hp : p ≠ ∞)
    (htight : ∀ η : ℝ≥0∞, 0 < η → ∃ K : Set X, IsCompact K ∧ μ Kᶜ < η)
    (hequi : Equicontinuous u)
    (hpt : ∀ x, ∃ C₀ : ℝ, ∀ i, ‖u i x‖ ≤ C₀)
    (C : ℝ) (hbound : ∀ i, ∀ᵐ x ∂μ, ‖u i x‖ ≤ C)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ s : Finset ι, ∀ i, ∃ j ∈ s, eLpNorm (u i - u j) p μ < ε := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨∅, fun i => (IsEmpty.false i).elim⟩
  inhabit ι
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  set q : ℝ := p.toReal with hq
  have hp0 : p ≠ 0 := (one_pos.trans_le hp₁).ne'
  have hq_pos : 0 < q := ENNReal.toReal_pos hp0 hp

  obtain ⟨n, hn_pos, hn⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (a := ENNReal.ofReal (C + C)) ENNReal.ofReal_ne_top hε2
  obtain ⟨K, hK, hμK⟩ := htight ((n : ℝ≥0∞) ^ q)
    (ENNReal.rpow_pos_of_nonneg (ENNReal.coe_pos.2 hn_pos) hq_pos.le)
  have hKm : MeasurableSet K := hK.measurableSet

  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_equicontinuous_of_isCompact u hequi hpt hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let v : ι → (K →ᵇ E) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x : K => u i x, (hequi.continuous i).comp continuous_subtype_val⟩
  have hv : ∀ i (x : K), v i x = u i x := fun i x => rfl
  have hequiK : Equicontinuous (fun i => ⇑(v i)) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro δ hδ
    have h := Metric.equicontinuousAt_iff_right.mp (hequi (x₀ : X)) δ hδ
    rw [nhds_subtype]
    exact (h.comap Subtype.val).mono fun y hy i => hy i
  set A : Set (K →ᵇ E) := Set.range v with hA
  have hA_equi : Equicontinuous (fun a : A => ⇑(a : K →ᵇ E)) := by
    have : (fun a : A => ⇑(a : K →ᵇ E)) = (fun i => ⇑(v i)) ∘ (fun a : A => a.2.choose) := by
      funext a; simp only [Function.comp_apply]; rw [a.2.choose_spec]
    rw [this]; exact hequiK.comp _
  have hA_cpt : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : E) B) (isCompact_closedBall 0 B) A
      (fun g x hg => by
        obtain ⟨i, rfl⟩ := hg
        rw [Metric.mem_closedBall, dist_zero_right, hv]
        exact hB i x x.2)
      hA_equi
  have hA_tb : TotallyBounded A := hA_cpt.totallyBounded.subset subset_closure

  obtain ⟨d, hd_pos, hd⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := μ Set.univ ^ q⁻¹)
    (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hq_pos.le) (measure_ne_top μ Set.univ)) hε2
  obtain ⟨t, htA, htfin, hAt⟩ := Metric.finite_approx_of_totallyBounded hA_tb d (NNReal.coe_pos.2 hd_pos)
  let inv : (K →ᵇ E) → ι := fun y => if h : ∃ i, v i = y then h.choose else default
  have hinv : ∀ y ∈ A, v (inv y) = y := fun y hy => by
    have hy' : ∃ i, v i = y := hy
    simp only [inv, dif_pos hy']
    exact hy'.choose_spec
  refine ⟨htfin.toFinset.image inv, fun i => ?_⟩
  obtain ⟨y, hyt, hiy⟩ := Set.mem_iUnion₂.mp (hAt ⟨i, rfl⟩)
  refine ⟨inv y, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hyt), ?_⟩
  have hvj : v (inv y) = y := hinv y (htA hyt)
  have hdist : ∀ x ∈ K, ‖u i x - u (inv y) x‖ ≤ d := fun x hx => by
    rw [← dist_eq_norm, ← hv i ⟨x, hx⟩, ← hv (inv y) ⟨x, hx⟩]
    refine (dist_coe_le_dist _).trans ?_
    rw [hvj]
    exact (Metric.mem_ball.1 hiy).le

  have hmeas : ∀ k, AEStronglyMeasurable (u k) μ := fun k => (hequi.continuous k).aestronglyMeasurable
  set g : X → E := u i - u (inv y) with hg
  have hgm : AEStronglyMeasurable g μ := (hmeas i).sub (hmeas (inv y))
  have h1 : eLpNorm (K.indicator g) p μ ≤ μ Set.univ ^ q⁻¹ * ENNReal.ofReal d := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm]
    refine (eLpNorm_le_of_ae_bound (C := (d : ℝ)) ?_).trans ?_
    · rw [ae_restrict_iff' hKm]
      exact Filter.Eventually.of_forall fun x hx => hdist x hx
    · rw [Measure.restrict_apply_univ]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (measure_mono (Set.subset_univ K))
        (inv_nonneg.2 hq_pos.le)) _
  have h2 : eLpNorm (Kᶜ.indicator g) p μ ≤ μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hKm.compl]
    refine (eLpNorm_le_of_ae_bound (C := C + C) ?_).trans (by rw [Measure.restrict_apply_univ])
    refine ae_restrict_of_ae ?_
    filter_upwards [hbound i, hbound (inv y)] with x hxi hxj
    exact (norm_sub_le _ _).trans (add_le_add hxi hxj)
  have hsum : eLpNorm g p μ ≤ eLpNorm (K.indicator g) p μ + eLpNorm (Kᶜ.indicator g) p μ := by
    have h := eLpNorm_add_le (hgm.indicator hKm) (hgm.indicator hKm.compl) hp₁ (μ := μ)
    rwa [Set.indicator_self_add_compl] at h
  have hlt1 : μ Set.univ ^ q⁻¹ * ENNReal.ofReal d < ε / 2 := by
    rw [ENNReal.ofReal_coe_nnreal, mul_comm]; exact hd
  have hlt2 : μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) < ε / 2 := by
    refine lt_of_le_of_lt (mul_le_mul_left ?_ _) hn
    calc μ Kᶜ ^ q⁻¹ ≤ ((n : ℝ≥0∞) ^ q) ^ q⁻¹ := ENNReal.rpow_le_rpow hμK.le (inv_nonneg.2 hq_pos.le)
      _ = n := ENNReal.rpow_rpow_inv hq_pos.ne' _
  calc eLpNorm (u i - u (inv y)) p μ = eLpNorm g p μ := rfl
    _ ≤ eLpNorm (K.indicator g) p μ + eLpNorm (Kᶜ.indicator g) p μ := hsum
    _ ≤ μ Set.univ ^ q⁻¹ * ENNReal.ofReal d + μ Kᶜ ^ q⁻¹ * ENNReal.ofReal (C + C) := add_le_add h1 h2
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hlt1 hlt2
    _ = ε := ENNReal.add_halves ε

end S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le
end P2MW
export P2MW.S_MeasureTheory_exists_finset_forall_exists_eLpNorm_sub_lt_of_equicontinuous_of_forall_ae_norm_le (solution)
