-- Prove2me | solution 1 for MFGLiquidation.Equilibrium.fact_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:20:03.284211+00:00
-- url     : https://prove2.me/submissions/6b05c7e5-1915-49c5-8100-65e1fa660f55

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open MFGLiquidation.Equilibrium Peng1990.SMP

/-- Pointwise weight comparison: `(T - x)^{-(l-1)} c ≤ T · (T - x)^{-l} c` for `0 ≤ x ≤ T`. -/
lemma fact22_weight_le (T : ℝ≥0) (hT : 0 < T) (l x : ℝ) (hx0 : 0 ≤ x) (hxT : x ≤ T)
    (c : ℝ≥0∞) :
    ENNReal.ofReal ((T : ℝ) - x) ^ (-(l - 1)) * c ≤
      (T : ℝ≥0∞) * (ENNReal.ofReal ((T : ℝ) - x) ^ (-l) * c) := by
  rcases lt_or_eq_of_le hxT with hlt | heq
  · have ha0 : ENNReal.ofReal ((T : ℝ) - x) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have hat : ENNReal.ofReal ((T : ℝ) - x) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hsplit : ENNReal.ofReal ((T : ℝ) - x) ^ (-(l - 1)) =
        ENNReal.ofReal ((T : ℝ) - x) ^ (-l) * ENNReal.ofReal ((T : ℝ) - x) := by
      rw [show -(l - 1) = -l + 1 by ring, ENNReal.rpow_add _ _ ha0 hat, ENNReal.rpow_one]
    have hle : ENNReal.ofReal ((T : ℝ) - x) ≤ (T : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal (by linarith)
    rw [hsplit]
    calc ENNReal.ofReal ((T : ℝ) - x) ^ (-l) * ENNReal.ofReal ((T : ℝ) - x) * c
        ≤ ENNReal.ofReal ((T : ℝ) - x) ^ (-l) * (T : ℝ≥0∞) * c := by gcongr
      _ = (T : ℝ≥0∞) * (ENNReal.ofReal ((T : ℝ) - x) ^ (-l) * c) := by ring
  · subst heq
    simp only [sub_self, ENNReal.ofReal_zero]
    by_cases hc : c = 0
    · simp [hc]
    by_cases hl : 0 < -(l - 1)
    · rw [ENNReal.zero_rpow_of_pos hl, zero_mul]; exact zero_le
    · have : (-l) < 0 := by linarith
      rw [ENNReal.zero_rpow_of_neg this, ENNReal.top_mul hc, ENNReal.mul_top]
      · exact le_top
      · exact_mod_cast hT.ne'

lemma fact22_part1 {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (T : ℝ≥0) (hT : 0 < T) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) (hY : MemH G P T l Y) :
    MemH G P T (l - 1) Y ∧ hNormSq T P (l - 1) Y ≤ (T : ℝ≥0∞) ^ 2 * hNormSq T P l Y := by
  have key : hNormSq T P (l - 1) Y ≤ (T : ℝ≥0∞) ^ 2 * hNormSq T P l Y := by
    unfold hNormSq
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun ω => ?_
    rw [← mul_pow]
    gcongr
    rw [ENNReal.mul_iSup]
    refine iSup₂_le fun t ht => ?_
    refine (fact22_weight_le T hT l t t.2 (by exact_mod_cast ht) _).trans ?_
    refine le_trans ?_ (le_iSup _ t)
    rw [ENNReal.mul_iSup]
    exact le_iSup_of_le ht le_rfl
  refine ⟨⟨hY.1, lt_of_le_of_lt key (ENNReal.mul_lt_top (by simp) hY.2)⟩, key⟩

lemma fact22_part2 {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (K : ℝ≥0 → Ω → ℝ) (hl : 0 < l) (hK : MemH G P T l K) :
    ∀ᵐ ω ∂P, K T ω = 0 := by
  set S := {ω | K T ω ≠ 0} with hS
  have hmeas : MeasurableSet S := by
    have : Measurable (K T) :=
      ((hK.1.stronglyAdapted T).mono (G.le T)).measurable
    exact (measurableSet_singleton 0).compl.preimage this
  have hind : ∀ ω, S.indicator (fun _ => (⊤ : ℝ≥0∞)) ω ≤
      (⨆ t ∈ Set.Iic T, ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖K t ω‖ₑ) ^ 2 := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have h1 : ENNReal.ofReal ((T : ℝ) - T) ^ (-l) * ‖K T ω‖ₑ = ⊤ := by
        rw [sub_self, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
          ENNReal.top_mul (enorm_ne_zero.2 hω)]
      have h2 : (⊤ : ℝ≥0∞) ≤ ⨆ t ∈ Set.Iic T, ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖K t ω‖ₑ :=
        h1 ▸ le_iSup₂_of_le T (Set.mem_Iic.2 le_rfl) le_rfl
      rw [top_le_iff] at h2
      rw [h2]; simp
    · rw [Set.indicator_of_notMem hω]; exact zero_le
  have hle : ⊤ * P S ≤ hNormSq T P l K := by
    rw [← lintegral_indicator_const hmeas]
    exact lintegral_mono hind
  have hPS : P S = 0 := by
    by_contra h
    have := lt_of_le_of_lt hle hK.2
    rw [ENNReal.top_mul h] at this
    exact lt_irrefl _ this
  rw [ae_iff]
  simpa [hS] using hPS

lemma fact22_ae_fst {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] (T : ℝ≥0) :
    ∀ᵐ p ∂(dtP T P), p.1 ∈ Set.Icc (0 : ℝ) T :=
  (Measure.quasiMeasurePreserving_fst).ae (ae_restrict_mem measurableSet_Icc)

lemma fact22_part4 {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) [SFinite P] (T : ℝ≥0) (hT : 0 < T) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ)
    (hY : MemM G P T l Y) :
    MemM G P T (l - 1) Y ∧ mNorm T P (l - 1) Y ≤ (T : ℝ≥0∞) * mNorm T P l Y := by
  have key : mNorm T P (l - 1) Y ≤ (T : ℝ≥0∞) * mNorm T P l Y := by
    unfold mNorm
    rw [← ENNReal.essSup_const_mul]
    refine essSup_mono_ae ?_
    filter_upwards [fact22_ae_fst P T] with p hp
    exact fact22_weight_le T hT l p.1 hp.1 hp.2 _
  exact ⟨⟨hY.1, lt_of_le_of_lt key (ENNReal.mul_lt_top (by simp) hY.2)⟩, key⟩

lemma fact22_part3 {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) [SFinite P] (T : ℝ≥0) (hT : 0 < T) (l : ℝ) (K₁ K₂ : ℝ≥0 → Ω → ℝ)
    (h1 : MemM G P T (-1) K₁) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => K₁ t ω) (Set.Iio T))
    (h2 : MemH G P T l K₂) : MemH G P T (l - 1) (fun t ω => K₁ t ω * K₂ t ω) := by
  set C := mNorm T P (-1) K₁ with hC
  have hCt : C ≠ ⊤ := h1.2.ne
  -- a.e. bound on the product space
  have hae : ∀ᵐ p ∂(dtP T P),
      ENNReal.ofReal ((T : ℝ) - p.1) ^ (-(-1 : ℝ)) * ‖K₁ p.1.toNNReal p.2‖ₑ ≤ C :=
    ae_le_essSup
  -- swap to get: a.e. ω, a.e. t
  have hae2 : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ENNReal.ofReal ((T : ℝ) - x) ^ (-(-1 : ℝ)) * ‖K₁ x.toNNReal ω‖ₑ ≤ C := by
    have hsw : dtP T P = (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).map Prod.swap := by
      unfold dtP; rw [Measure.prod_swap]
    rw [hsw] at hae
    have := ae_of_ae_map measurable_swap.aemeasurable hae
    exact Measure.ae_ae_of_ae_prod this
  -- pointwise bound for all t < T, a.e. ω
  have hbd : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < T → ENNReal.ofReal ((T : ℝ) - t) * ‖K₁ t ω‖ₑ ≤ C := by
    filter_upwards [hae2, hc] with ω hω hcω
    set h : ℝ → ℝ := fun x => ((T : ℝ) - x) * |K₁ x.toNNReal ω| with hh
    have hcont : ContinuousOn h (Set.Ico 0 (T : ℝ)) := by
      refine (continuousOn_const.sub continuousOn_id).mul ?_
      refine ContinuousOn.abs ?_
      refine hcω.comp continuous_real_toNNReal.continuousOn ?_
      intro x hx
      exact (Real.toNNReal_lt_iff_lt_coe hx.1).2 hx.2
    have hω' : ∀ᵐ x ∂volume, x ∈ Set.Icc (0 : ℝ) T → h x ≤ C.toReal := by
      rw [← ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with x hx hxI
      rw [neg_neg, ENNReal.rpow_one, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_mul (by linarith [hxI.2])] at hx
      exact (ENNReal.ofReal_le_iff_le_toReal hCt).1 hx
    have hall : ∀ x ∈ Set.Ico (0 : ℝ) T, h x ≤ C.toReal := by
      intro x0 hx0
      by_contra hgt
      push Not at hgt
      have hcw : ContinuousWithinAt h (Set.Ioi x0) x0 := by
        have := (hcont x0 hx0).mono (Set.Ioo_subset_Ico_self.trans
          (Set.Ico_subset_Ico_left hx0.1) : Set.Ioo x0 (T : ℝ) ⊆ Set.Ico 0 (T : ℝ))
        exact this.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hx0.2)
      have hev : ∀ᶠ x in 𝓝[>] x0, C.toReal < h x := hcw.eventually (lt_mem_nhds hgt)
      have hev2 : ∀ᶠ x in 𝓝[>] x0, C.toReal < h x ∧ x < T :=
        hev.and (Ioo_mem_nhdsGT hx0.2 |> fun hm => Filter.mem_of_superset hm fun x hx => hx.2)
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev2
      have hnull : volume (Set.Ioo x0 u) = 0 := by
        refine measure_mono_null ?_ (ae_iff.1 hω')
        intro x hx
        have hx' := hsub hx
        show ¬ (_ → _)
        intro himp
        exact absurd (himp ⟨by linarith [hx0.1, hx.1], hx'.2.le⟩) (not_le.2 hx'.1)
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hnull
      linarith [Set.mem_Ioi.1 hu]
    intro t ht
    have := hall t ⟨t.2, by exact_mod_cast ht⟩
    simp only [hh, Real.toNNReal_coe] at this
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by
      have : (t : ℝ) < T := by exact_mod_cast ht
      linarith)]
    calc ENNReal.ofReal (((T : ℝ) - t) * |K₁ t ω|) ≤ ENNReal.ofReal C.toReal :=
          ENNReal.ofReal_le_ofReal this
      _ = C := ENNReal.ofReal_toReal hCt
  set C' := C + 1 with hC'
  have hC'0 : C' ≠ 0 := by simp [hC']
  have hC't : C' ≠ ⊤ := by simp [hC', hCt]
  refine ⟨h1.1.mul h2.1, ?_⟩
  have key : hNormSq T P (l - 1) (fun t ω => K₁ t ω * K₂ t ω) ≤ C' ^ 2 * hNormSq T P l K₂ := by
    unfold hNormSq
    rw [← lintegral_const_mul' _ _ (by simp [hC't])]
    refine lintegral_mono_ae ?_
    filter_upwards [hbd] with ω hω
    rw [← mul_pow]
    gcongr
    rw [ENNReal.mul_iSup]
    refine iSup₂_le fun t ht => ?_
    refine le_trans ?_ (le_iSup _ t)
    rw [ENNReal.mul_iSup]
    refine le_iSup_of_le ht ?_
    rw [enorm_mul]
    rcases lt_or_eq_of_le (show t ≤ T from ht) with hlt | heq
    · have hlt' : (t : ℝ) < T := by exact_mod_cast hlt
      have ha0 : ENNReal.ofReal ((T : ℝ) - t) ≠ 0 := by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
      have hat : ENNReal.ofReal ((T : ℝ) - t) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [show -(l - 1) = 1 + -l by ring, ENNReal.rpow_add _ _ ha0 hat, ENNReal.rpow_one]
      calc ENNReal.ofReal ((T : ℝ) - t) * ENNReal.ofReal ((T : ℝ) - t) ^ (-l) *
            (‖K₁ t ω‖ₑ * ‖K₂ t ω‖ₑ)
          = (ENNReal.ofReal ((T : ℝ) - t) * ‖K₁ t ω‖ₑ) *
            (ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖K₂ t ω‖ₑ) := by ring
        _ ≤ C' * (ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖K₂ t ω‖ₑ) := by
          gcongr
          exact (hω t hlt).trans le_self_add
    · subst heq
      simp only [sub_self, ENNReal.ofReal_zero]
      by_cases hK2 : ‖K₂ t ω‖ₑ = 0
      · simp [hK2]
      by_cases hl : 0 < -(l - 1)
      · rw [ENNReal.zero_rpow_of_pos hl, zero_mul]; exact zero_le
      · have : (-l) < 0 := by linarith
        rw [ENNReal.zero_rpow_of_neg this, ENNReal.top_mul hK2, ENNReal.mul_top hC'0]
        exact le_top
  exact lt_of_le_of_lt key (ENNReal.mul_lt_top (ENNReal.pow_ne_top hC't).lt_top h2.2)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) [SFinite P] (T : ℝ≥0) (hT : 0 < T) :
    (∀ (l : ℝ) (Y : ℝ≥0 → Ω → ℝ), MemH G P T l Y →
      MemH G P T (l - 1) Y ∧ hNormSq T P (l - 1) Y ≤ (T : ℝ≥0∞) ^ 2 * hNormSq T P l Y) ∧
    (∀ (l : ℝ) (K : ℝ≥0 → Ω → ℝ), 0 < l → MemH G P T l K → ∀ᵐ ω ∂P, K T ω = 0) ∧
    (∀ (l : ℝ) (K₁ K₂ : ℝ≥0 → Ω → ℝ), MemM G P T (-1) K₁ →
      (∀ᵐ ω ∂P, ContinuousOn (fun t => K₁ t ω) (Set.Iio T)) → MemH G P T l K₂ →
      MemH G P T (l - 1) (fun t ω => K₁ t ω * K₂ t ω)) ∧
    (∀ (l : ℝ) (Y : ℝ≥0 → Ω → ℝ), MemM G P T l Y →
      MemM G P T (l - 1) Y ∧ mNorm T P (l - 1) Y ≤ (T : ℝ≥0∞) * mNorm T P l Y) :=
  ⟨fun l Y hY => fact22_part1 G P T hT l Y hY,
   fun l K hl hK => fact22_part2 G P T l K hl hK,
   fun l K₁ K₂ h1 hc h2 => fact22_part3 G P T hT l K₁ K₂ h1 hc h2,
   fun l Y hY => fact22_part4 G P T hT l Y hY⟩
