-- Prove2me | solution 1 for InertialAVD.Traj.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T10:00:14.341854+00:00
-- url     : https://prove2.me/submissions/f16e9cb9-a6b2-4aad-a0d4-0cd571514e89

import Mathlib
set_option autoImplicit false
open Filter Topology MeasureTheory

theorem key_mono (a b : ℝ) (hab : a ≤ b) (φ φ' h : ℝ → ℝ)
    (hφ : ∀ x ∈ Set.Icc a b, HasDerivWithinAt φ (φ' x) (Set.Icc a b) x)
    (hh : IntegrableOn h (Set.Icc a b))
    (h0 : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), 0 ≤ h x)
    (hle : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)), φ' x ≤ h x) :
    φ b - φ a ≤ ∫ x in Set.Icc a b, h x := by
  have hI0 : 0 ≤ ∫ x in Set.Icc a b, h x := setIntegral_nonneg_of_ae_restrict h0
  by_cases hlt : φ a < φ b
  swap
  · linarith [not_lt.mp hlt]
  have hcont : ContinuousOn φ (Set.Icc a b) := fun x hx => (hφ x hx).continuousWithinAt
  set X : Set ℝ := {x | x ∈ Set.Icc a b ∧ ∀ x' ∈ Set.Icc a b, x ≤ x' → φ x ≤ φ x'} with hX
  have hXc : IsClosed X := by
    have : X = Set.Icc a b ∩ ⋂ x' ∈ Set.Icc a b,
        ((Set.Icc a b ∩ Set.Ici x') ∪ (Set.Icc a b ∩ φ ⁻¹' Set.Iic (φ x'))) := by
      ext x
      simp only [hX, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
        Set.mem_Ici, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨hx, H⟩ 
        refine ⟨hx, fun x' hx' => ?_⟩
        by_cases hxx : x ≤ x'
        · exact Or.inr ⟨hx, H x' hx' hxx⟩
        · exact Or.inl ⟨hx, (not_le.mp hxx).le⟩
      · rintro ⟨hx, H⟩
        refine ⟨hx, fun x' hx' hxx => ?_⟩
        rcases H x' hx' with h1 | h1
        · have : x = x' := le_antisymm hxx h1.2
          subst this; exact le_rfl
        · exact h1.2
    rw [this]
    refine isClosed_Icc.inter (isClosed_biInter fun x' hx' => ?_)
    exact (isClosed_Icc.inter isClosed_Ici).union
      (hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
  set X0 : Set ℝ := X ∩ Set.Iio b with hX0
  have hX0m : MeasurableSet X0 := hXc.measurableSet.inter measurableSet_Iio
  have hX0Icc : X0 ⊆ Set.Icc a b := fun x hx => hx.1.1
  -- covering
  have hcover : ∀ y ∈ Set.Ioo (φ a) (φ b), ∃ x ∈ X0, φ x = y := by
    intro y hy
    set S : Set ℝ := {x | x ∈ Set.Icc a b ∧ φ x ≤ y} with hS
    have hSc : IsClosed S := by
      have : S = Set.Icc a b ∩ φ ⁻¹' Set.Iic y := rfl
      rw [this]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, hy.1.le⟩
    have hSb : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
    have hxS : sSup S ∈ S := hSc.csSup_mem ⟨a, haS⟩ hSb
    set x0 := sSup S with hx0
    have hx0b : x0 < b := by
      rcases lt_or_eq_of_le hxS.1.2 with h1 | h1
      · exact h1
      · exfalso; have := hxS.2; rw [h1] at this; linarith [hy.2]
    have hgt : ∀ x', x0 < x' → x' ≤ b → y < φ x' := by
      intro x' h1 h2
      by_contra hc
      have : x' ∈ S := ⟨⟨by linarith [hxS.1.1], h2⟩, not_lt.mp hc⟩
      have := le_csSup hSb this
      linarith
    have hge : y ≤ φ x0 := by
      have hc : ContinuousWithinAt φ (Set.Ioc x0 b) x0 :=
        (hcont x0 hxS.1).mono (fun x hx => ⟨by linarith [hxS.1.1, hx.1], hx.2⟩)
      rw [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsGT hx0b] at hc
      refine ge_of_tendsto hc ?_
      filter_upwards [Ioo_mem_nhdsGT hx0b] with x hx using (hgt x hx.1 hx.2.le).le
    have heq : φ x0 = y := le_antisymm hxS.2 hge
    refine ⟨x0, ⟨⟨hxS.1, fun x' hx' hxx => ?_⟩, hx0b⟩, heq⟩
    rcases eq_or_lt_of_le hxx with h1 | h1
    · rw [h1]
    · rw [heq]; exact (hgt x' h1 hx'.2).le
  have hnonneg : ∀ x ∈ X0, 0 ≤ φ' x := by
    intro x hx
    have hxb : x < b := hx.2
    have h1 := hφ x (hX0Icc hx)
    rw [hasDerivWithinAt_iff_tendsto_slope] at h1
    have sub : Set.Ioo x b ⊆ Set.Icc a b \ {x} := fun z hz =>
      ⟨⟨by linarith [(hX0Icc hx).1, hz.1], hz.2.le⟩, fun h => by simp at h; linarith [hz.1]⟩
    have h2 := h1.mono_left (nhdsWithin_mono x sub)
    rw [nhdsWithin_Ioo_eq_nhdsGT hxb] at h2
    refine ge_of_tendsto h2 ?_
    filter_upwards [Ioo_mem_nhdsGT hxb] with z hz
    rw [slope_def_field]
    exact div_nonneg (by linarith [hx.1.2 z ⟨by linarith [(hX0Icc hx).1, hz.1], hz.2.le⟩ hz.1.le]) (by linarith [hz.1])
  have hD : ∀ x ∈ X0, HasFDerivWithinAt φ ((1 : ℝ →L[ℝ] ℝ).smulRight (φ' x)) X0 x :=
    fun x hx => ((hφ x (hX0Icc hx)).mono hX0Icc).hasFDerivWithinAt
  have harea := addHaar_image_le_lintegral_abs_det_fderiv volume hX0m hD
  have hdet : ∀ x, ((1 : ℝ →L[ℝ] ℝ).smulRight (φ' x)).det = φ' x := by
    intro x
    simp [ContinuousLinearMap.det]
  simp only [hdet] at harea
  have hsub : Set.Ioo (φ a) (φ b) ⊆ φ '' X0 := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hcover y hy
    exact ⟨x, hx, rfl⟩
  have e1 : ∫⁻ x in X0, ENNReal.ofReal |φ' x| = ∫⁻ x in X0, ENNReal.ofReal (φ' x) :=
    setLIntegral_congr_fun hX0m (fun x hx => by rw [abs_of_nonneg (hnonneg x hx)])
  have hae : ∀ᵐ x ∂(volume.restrict X0), φ' x ≤ h x :=
    ae_restrict_of_ae_restrict_of_subset hX0Icc hle
  have e2 : ∫⁻ x in X0, ENNReal.ofReal (φ' x) ≤ ∫⁻ x in X0, ENNReal.ofReal (h x) :=
    lintegral_mono_ae (hae.mono fun x hx => ENNReal.ofReal_le_ofReal hx)
  have e3 : ∫⁻ x in X0, ENNReal.ofReal (h x) ≤ ∫⁻ x in Set.Icc a b, ENNReal.ofReal (h x) :=
    lintegral_mono_set hX0Icc
  have e4 : ∫⁻ x in Set.Icc a b, ENNReal.ofReal (h x) = ENNReal.ofReal (∫ x in Set.Icc a b, h x) :=
    (ofReal_integral_eq_lintegral_ofReal hh h0).symm
  have hmain : ENNReal.ofReal (φ b - φ a) ≤ ENNReal.ofReal (∫ x in Set.Icc a b, h x) := by
    calc ENNReal.ofReal (φ b - φ a) = volume (Set.Ioo (φ a) (φ b)) := by simp
      _ ≤ volume (φ '' X0) := measure_mono hsub
      _ ≤ _ := harea
      _ ≤ _ := by rw [e1]; exact e2.trans (e3.trans e4.le)
  exact (ENNReal.ofReal_le_ofReal_iff hI0).mp hmain

theorem a4_deriv (δ α : ℝ) (hδ : 0 < δ) (w' w'' : ℝ → ℝ)
    (hw' : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w' (w'' t) (Set.Ici δ) t) (t : ℝ)
    (ht : t ∈ Set.Ici δ) :
    HasDerivWithinAt (fun x => x ^ α * w' x) (t ^ (α - 1) * (t * w'' t + α * w' t))
      (Set.Ici δ) t := by
  have htp : 0 < t := lt_of_lt_of_le hδ ht
  have h1 : HasDerivAt (fun x : ℝ => x ^ α) (α * t ^ (α - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl htp.ne')
  have h2 := h1.hasDerivWithinAt.mul (hw' t ht)
  refine h2.congr_deriv ?_
  have : t ^ α = t ^ (α - 1) * t := by
    rw [Real.rpow_sub_one htp.ne']; field_simp
  rw [this]; ring

theorem a4_ae_Icc (δ T : ℝ) (P : ℝ → Prop)
    (hP : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), P t) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc δ T)), P t := by
  have : ∀ᵐ t ∂(volume.restrict (Set.Ioc δ T)), P t :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self hP
  rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at this

theorem a4_bound (δ α : ℝ) (hδ : 0 < δ) (w' w'' g : ℝ → ℝ)
    (hw' : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w' (w'' t) (Set.Ici δ) t)
    (hineq : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), t * w'' t + α * w' t ≤ g t)
    (hg_nonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), 0 ≤ g t)
    (hg_int : IntegrableOn g (Set.Ioi δ)) (t : ℝ) (ht : δ ≤ t) :
    w' t ≤ t ^ (-α) * (δ ^ α * w' δ + ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x) := by
  have htp : 0 < t := lt_of_lt_of_le hδ ht
  have hcl : IntegrableOn g (Set.Icc δ t) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hg_int.mono_set Set.Ioc_subset_Ioi_self
  have hpow : ContinuousOn (fun x : ℝ => x ^ (α - 1)) (Set.Icc δ t) :=
    fun x hx => (Real.continuousAt_rpow_const x (α - 1)
      (Or.inl (lt_of_lt_of_le hδ hx.1).ne')).continuousWithinAt
  have hh : IntegrableOn (fun x => x ^ (α - 1) * g x) (Set.Icc δ t) :=
    hcl.continuousOn_mul hpow isCompact_Icc
  have hpos : ∀ᵐ x ∂(volume.restrict (Set.Icc δ t)), 0 < x ^ (α - 1) := by
    have : ∀ᵐ x ∂(volume.restrict (Set.Icc δ t)), x ∈ Set.Icc δ t :=
      ae_restrict_mem measurableSet_Icc
    exact this.mono fun x hx => Real.rpow_pos_of_pos (lt_of_lt_of_le hδ hx.1) _
  have h0 : ∀ᵐ x ∂(volume.restrict (Set.Icc δ t)), 0 ≤ x ^ (α - 1) * g x := by
    filter_upwards [a4_ae_Icc δ t _ hg_nonneg, hpos] with x h1 h2 using mul_nonneg h2.le h1
  have hle : ∀ᵐ x ∂(volume.restrict (Set.Icc δ t)),
      x ^ (α - 1) * (x * w'' x + α * w' x) ≤ x ^ (α - 1) * g x := by
    filter_upwards [a4_ae_Icc δ t _ hineq, hpos] with x h1 h2 using
      mul_le_mul_of_nonneg_left h1 h2.le
  have hφ : ∀ x ∈ Set.Icc δ t, HasDerivWithinAt (fun x => x ^ α * w' x)
      (x ^ (α - 1) * (x * w'' x + α * w' x)) (Set.Icc δ t) x := fun x hx =>
    (a4_deriv δ α hδ w' w'' hw' x (Set.mem_Ici.mpr hx.1)).mono (fun y hy => hy.1)
  have key := key_mono δ t ht _ _ _ hφ hh h0 hle
  rw [integral_Icc_eq_integral_Ioc] at key
  have : t ^ α * w' t ≤ δ ^ α * w' δ + ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x := by linarith
  have e : w' t = t ^ (-α) * (t ^ α * w' t) := by
    rw [← mul_assoc, ← Real.rpow_add htp]; simp
  rw [e]
  have hnn : 0 < t ^ (-α) := Real.rpow_pos_of_pos htp _
  exact mul_le_mul_of_nonneg_left this hnn.le

theorem a4_int (δ α : ℝ) (hδ : 0 < δ) (hα : 1 < α) (g : ℝ → ℝ)
    (hg_int : IntegrableOn g (Set.Ioi δ)) :
    IntegrableOn (fun t => t ^ (-α) * ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x) (Set.Ioi δ) := by
  set c : ℝ → ℝ := fun s => s ^ (α - 1) * g s with hc_def
  have hcm : AEStronglyMeasurable c (volume.restrict (Set.Ioi δ)) :=
    (measurable_id.pow_const (α - 1)).aestronglyMeasurable.mul hg_int.1
  set μ : Measure ℝ := volume.restrict (Set.Ioi δ) with hμ
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator
    (fun p => c p.1 * p.2 ^ (-α)) with hF
  have hFm : AEStronglyMeasurable F (μ.prod μ) := by
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_le measurable_fst measurable_snd)
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => c p.1) (μ.prod μ) := hcm.comp_fst
    exact h1.mul (measurable_snd.pow_const _).aestronglyMeasurable
  have hFs : ∀ s, δ < s → ∀ t, F (s, t) = c s * (Set.Ici s).indicator (fun t => t ^ (-α)) t := by
    intro s hs t
    simp only [hF, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ici]
    split_ifs <;> simp
  have hint1 : ∀ s, δ < s → IntegrableOn (fun t => t ^ (-α)) (Set.Ici s) := by
    intro s hs
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)
  have hF1 : ∀ᵐ s ∂μ, Integrable (fun t => F (s, t)) μ := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs' : δ < s := hs
    have : (fun t => F (s, t)) = fun t => c s * (Set.Ici s).indicator (fun t => t ^ (-α)) t :=
      funext (hFs s hs')
    rw [this]
    refine Integrable.const_mul ?_ _
    exact ((integrable_indicator_iff measurableSet_Ici).mpr (hint1 s hs')).mono_measure
      Measure.restrict_le_self
  have hF2 : Integrable (fun s => ∫ t, ‖F (s, t)‖ ∂μ) μ := by
    have hcongr : ∀ s ∈ Set.Ioi δ, |g s| / (α - 1) = ∫ t, ‖F (s, t)‖ ∂μ := by
      intro s hs
      have hs' : δ < s := hs
      have hsp : 0 < s := lt_trans hδ hs'
      have hnorm : (fun t => ‖F (s, t)‖) =
          fun t => |c s| * (Set.Ici s).indicator (fun t => t ^ (-α)) t := by
        funext t
        rw [hFs s hs' t, norm_mul, Real.norm_eq_abs]
        congr 1
        by_cases hst : s ≤ t
        · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hst), Real.norm_eq_abs, abs_of_nonneg]
          exact (Real.rpow_pos_of_pos (lt_of_lt_of_le hsp hst) _).le
        · rw [Set.indicator_of_notMem (by simpa using hst)]; simp
      rw [hnorm, integral_const_mul, hμ, integral_indicator measurableSet_Ici,
        Measure.restrict_restrict measurableSet_Ici]
      have : Set.Ici s ∩ Set.Ioi δ = Set.Ici s :=
        Set.inter_eq_left.mpr (fun x hx => lt_of_lt_of_le hs' hx)
      rw [this, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hsp]
      have hα1 : α - 1 ≠ 0 := by linarith
      have hsα : s ^ (α - 1) * s ^ (-α + 1) = 1 := by
        rw [← Real.rpow_add hsp]; simp
      have hcs : |c s| = s ^ (α - 1) * |g s| := by
        simp only [hc_def, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hsp _)]
      rw [hcs]
      have : -α + 1 ≠ 0 := by linarith
      field_simp
      linear_combination (|g s| * (α - 1)) * hsα
    have h3 : Integrable (fun s => |g s| / (α - 1)) μ := by
      have := hg_int.norm.div_const (α - 1)
      simpa using this
    refine h3.congr ?_
    rw [hμ, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall hcongr
  have hFi : Integrable F (μ.prod μ) := (integrable_prod_iff hFm).mpr ⟨hF1, hF2⟩
  have h4 := hFi.integral_prod_right
  refine h4.congr ?_
  rw [hμ, Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have e1 : ∀ s, F (s, t) = (Set.Iic t).indicator c s * t ^ (-α) := by
    intro s
    simp only [hF, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iic]
    split_ifs <;> simp
  simp only [e1]
  rw [integral_mul_const, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have : Set.Iic t ∩ Set.Ioi δ = Set.Ioc δ t := by
    ext x; simp [and_comm]
  rw [this, mul_comm]

theorem solution (δ : ℝ) (hδ : 0 < δ) (α : ℝ) (hα : 1 < α) (w w' w'' g : ℝ → ℝ)
    (hw : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w (w' t) (Set.Ici δ) t)
    (hw' : ∀ t ∈ Set.Ici δ, HasDerivWithinAt w' (w'' t) (Set.Ici δ) t)
    (hbdd : BddBelow (w '' Set.Ici δ))
    (hineq : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), t * w'' t + α * w' t ≤ g t)
    (hg_nonneg : ∀ᵐ t ∂(volume.restrict (Set.Ioi δ)), 0 ≤ g t)
    (hg_int : IntegrableOn g (Set.Ioi δ)) :
    IntegrableOn (fun t => max (w' t) 0) (Set.Ioi δ) ∧ ∃ ℓ : ℝ, Tendsto w atTop (𝓝 ℓ) := by
  obtain ⟨B, hB⟩ := hbdd
  have hBw : ∀ t, δ ≤ t → B ≤ w t := fun t ht => hB ⟨t, Set.mem_Ici.mpr ht, rfl⟩
  have hcontu : ContinuousOn w' (Set.Ici δ) := (fun t ht => (hw' t ht).continuousWithinAt : ContinuousOn w' (Set.Ici δ))
  have hcontw : ContinuousOn w (Set.Ici δ) := fun t ht => (hw t ht).continuousWithinAt
  have hcontp : ContinuousOn (fun t => max (w' t) 0) (Set.Ici δ) := (continuous_id.max continuous_const).comp_continuousOn hcontu
  set C : ℝ := δ ^ α * w' δ with hC
  have hK : ∀ t, δ < t → 0 ≤ ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x := by
    intro t ht
    refine setIntegral_nonneg_of_ae_restrict ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self hg_nonneg,
      ae_restrict_mem measurableSet_Ioc] with x h1 h2
    exact mul_nonneg (Real.rpow_nonneg (lt_trans hδ h2.1).le _) h1
  have hplus : IntegrableOn (fun t => max (w' t) 0) (Set.Ioi δ) := by
    have hb : IntegrableOn (fun t => |C| * t ^ (-α) +
        t ^ (-α) * ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x) (Set.Ioi δ) :=
      ((integrableOn_Ioi_rpow_of_lt (by linarith) hδ).const_mul |C|).add
        (a4_int δ α hδ hα g hg_int)
    refine Integrable.mono' hb ?_ ?_
    · exact (hcontp.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun t ht => ?_
      have ht' : δ < t := ht
      have htp : 0 < t := lt_trans hδ ht'
      have hnn : 0 < t ^ (-α) := Real.rpow_pos_of_pos htp _
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ?_ ?_
      · have := a4_bound δ α hδ w' w'' g hw' hineq hg_nonneg hg_int t ht'.le
        have h2 : C ≤ |C| := le_abs_self C
        calc w' t ≤ t ^ (-α) * (C + ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x) := this
          _ ≤ t ^ (-α) * (|C| + ∫ x in Set.Ioc δ t, x ^ (α - 1) * g x) :=
            mul_le_mul_of_nonneg_left (by linarith) hnn.le
          _ = _ := by ring
      · have := hK t ht'
        positivity
  refine ⟨hplus, ?_⟩
  -- convergence
  set P : ℝ → ℝ := fun t => ∫ x in δ..t, max (w' x) 0 with hP
  have hii : ∀ a b, δ ≤ a → a ≤ b → IntervalIntegrable w' volume a b := by
    intro a b ha hab
    exact ((show ContinuousOn w' (Set.Ici δ) from hcontu).mono (by rw [Set.uIcc_of_le hab]; exact fun x hx => le_trans ha hx.1)).intervalIntegrable
  have hiip : ∀ a b, δ ≤ a → a ≤ b → IntervalIntegrable (fun x => max (w' x) 0) volume a b := by
    intro a b ha hab
    exact (hcontp.mono (by rw [Set.uIcc_of_le hab]; exact fun x hx => le_trans ha hx.1)).intervalIntegrable
  have hFTC : ∀ a b, δ ≤ a → a ≤ b → w b - w a = ∫ x in a..b, w' x := by
    intro a b ha hab
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ (hii a b ha hab)
    · exact (show ContinuousOn w (Set.Ici δ) from hcontw).mono (fun x hx => le_trans ha hx.1)
    · intro x hx
      exact (hw x (Set.mem_Ici.mpr (le_trans ha hx.1.le))).hasDerivAt
        (Ici_mem_nhds (lt_of_le_of_lt ha hx.1))
  have hPadd : ∀ a b, δ ≤ a → a ≤ b → P b = P a + ∫ x in a..b, max (w' x) 0 := by
    intro a b ha hab
    simp only [hP]
    rw [intervalIntegral.integral_add_adjacent_intervals (hiip δ a le_rfl ha) (hiip a b ha hab)]
  have hD : ∀ a b, δ ≤ a → a ≤ b → w b - P b ≤ w a - P a := by
    intro a b ha hab
    have h1 := hFTC a b ha hab
    have h2 := hPadd a b ha hab
    have h3 : ∫ x in a..b, w' x ≤ ∫ x in a..b, max (w' x) 0 :=
      intervalIntegral.integral_mono_on hab (hii a b ha hab) (hiip a b ha hab)
        (fun x _ => le_max_left _ _)
    linarith
  have hPt : Tendsto P atTop (𝓝 (∫ x in Set.Ioi δ, max (w' x) 0)) :=
    intervalIntegral_tendsto_integral_Ioi δ hplus tendsto_id
  have hPle : ∀ t, δ ≤ t → P t ≤ ∫ x in Set.Ioi δ, max (w' x) 0 := by
    intro t ht
    simp only [hP]
    rw [intervalIntegral.integral_of_le ht]
    refine setIntegral_mono_set hplus ?_ (Set.Ioc_subset_Ioi_self.eventuallyLE)
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun x _ => le_max_right _ _
  set M := ∫ x in Set.Ioi δ, max (w' x) 0 with hM
  set Dt : ℝ → ℝ := fun t => w (max t δ) - P (max t δ) with hDt
  have hanti : Antitone Dt := fun a b hab =>
    hD _ _ (le_max_right _ _) (max_le_max hab le_rfl)
  have hbdd : BddBelow (Set.range Dt) := by
    refine ⟨B - M, ?_⟩
    rintro _ ⟨t, rfl⟩
    have := hBw (max t δ) (le_max_right _ _)
    have := hPle (max t δ) (le_max_right _ _)
    simp only [hDt]; linarith
  have hDlim := tendsto_atTop_ciInf hanti hbdd
  refine ⟨(⨅ t, Dt t) + M, ?_⟩
  refine (hDlim.add hPt).congr' ?_
  filter_upwards [eventually_ge_atTop δ] with t ht
  simp only [hDt, max_eq_left ht]; ring
