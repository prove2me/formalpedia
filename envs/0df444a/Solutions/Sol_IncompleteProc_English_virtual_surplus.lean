-- Prove2me | solution 1 for IncompleteProc.English.virtual_surplus
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:12:55.857981+00:00
-- url     : https://prove2.me/submissions/cdd08c44-de83-46f7-8c83-67e3ced83813

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Theorems.Thm_IncompleteProc_English_lemma_1

open MeasureTheory Set Filter Topology

namespace IncProcInfra

open IncompleteProc.English

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The one-dimensional cost law: density `f` on `[c̲, c̄]`. -/
noncomputable def nu (E : Env Ω) : Measure ℝ :=
  (volume.restrict (Icc E.clo E.chi)).withDensity fun c => ENNReal.ofReal (E.f c)

theorem f_nonneg (E : Env Ω) (hS : E.Standing) : ∀ c ∈ Icc E.clo E.chi, 0 ≤ E.f c := by
  obtain ⟨_, _, _, _, _, _, _, ⟨δ, hδ, hfδ⟩, _⟩ := hS
  exact fun c hc => le_trans hδ.le (hfδ c hc)

theorem ind_nonneg (E : Env Ω) (hS : E.Standing) (s : Set ℝ) :
    ∀ x, 0 ≤ (s ∩ Icc E.clo E.chi).indicator E.f x := by
  intro x
  by_cases hx : x ∈ s ∩ Icc E.clo E.chi
  · rw [indicator_of_mem hx]; exact f_nonneg E hS x hx.2
  · rw [indicator_of_notMem hx]

theorem ind_integrable (E : Env Ω) (hS : E.Standing) {s : Set ℝ} (hs : MeasurableSet s) :
    Integrable ((s ∩ Icc E.clo E.chi).indicator E.f) := by
  obtain ⟨_, _, _, _, _, hfi, _⟩ := hS
  exact (integrable_indicator_iff (hs.inter measurableSet_Icc)).mpr
    (hfi.mono_set inter_subset_right)

theorem nu_apply (E : Env Ω) (hS : E.Standing) {s : Set ℝ} (hs : MeasurableSet s) :
    nu E s = ENNReal.ofReal (∫ c, (s ∩ Icc E.clo E.chi).indicator E.f c) := by
  rw [nu, withDensity_apply _ hs, Measure.restrict_restrict hs,
    ← lintegral_indicator (hs.inter measurableSet_Icc),
    ofReal_integral_eq_lintegral_ofReal (ind_integrable E hS hs)
      (ae_of_all _ (ind_nonneg E hS s))]
  congr 1
  funext x
  by_cases hx : x ∈ s ∩ Icc E.clo E.chi
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx]

theorem nu_prob (E : Env Ω) (hS : E.Standing) : IsProbabilityMeasure (nu E) := by
  constructor
  rw [nu_apply E hS MeasurableSet.univ, univ_inter, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hS.2.2.2.1.le,
    hS.2.2.2.2.2.2.1, ENNReal.ofReal_one]

theorem profileLaw_eq (E : Env Ω) (hS : E.Standing) :
    E.profileLaw = Measure.pi fun _ : Fin E.n => nu E := by
  have := nu_prob E hS
  symm
  apply Measure.pi_eq
  intro s hs
  have hps : MeasurableSet (univ.pi s) := MeasurableSet.univ_pi hs
  have hcube : MeasurableSet E.cube := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  set g : Fin E.n → ℝ → ℝ := fun i => (s i ∩ Icc E.clo E.chi).indicator E.f with hgdef
  have hg0 : ∀ i x, 0 ≤ g i x := fun i x => ind_nonneg E hS (s i) x
  have hgi : ∀ i, Integrable (g i) := fun i => ind_integrable E hS (hs i)
  have hprod : Integrable (fun C : Fin E.n → ℝ => ∏ i, g i (C i))
      (Measure.pi fun _ => volume) := Integrable.fintype_prod hgi
  rw [Env.profileLaw, withDensity_apply _ hps, Measure.restrict_restrict hps,
    ← lintegral_indicator (hps.inter hcube)]
  have hfun : ((univ.pi s ∩ E.cube).indicator fun C => ∏ i, ENNReal.ofReal (E.f (C i))) =
      fun C => ENNReal.ofReal (∏ i, g i (C i)) := by
    funext C
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 i (C i))]
    by_cases hC : C ∈ univ.pi s ∩ E.cube
    · rw [indicator_of_mem hC]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hgdef]; simp only
      rw [indicator_of_mem (show C i ∈ s i ∩ Icc E.clo E.chi from
        ⟨hC.1 i (mem_univ _), hC.2 i (mem_univ _)⟩)]
    · rw [indicator_of_notMem hC]
      have : ∃ i, C i ∉ s i ∩ Icc E.clo E.chi := by
        by_contra hcon
        push Not at hcon
        exact hC ⟨fun i _ => (hcon i).1, fun i _ => (hcon i).2⟩
      obtain ⟨i, hi⟩ := this
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hgdef]; simp only
      rw [indicator_of_notMem hi, ENNReal.ofReal_zero]
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (by rw [volume_pi]; exact hprod)
    (ae_of_all _ fun C => Finset.prod_nonneg fun i _ => hg0 i (C i)), volume_pi,
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => integral_nonneg (hg0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nu_apply E hS (hs i)]

theorem update_mp (E : Env Ω) (hS : E.Standing) (i : Fin E.n) :
    MeasurePreserving (fun p : (Fin E.n → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi fun _ : Fin E.n => nu E).prod (nu E)) (Measure.pi fun _ => nu E) := by
  have := nu_prob E hS
  refine ⟨measurable_update', ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin E.n → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' univ.pi s =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext ⟨C, c⟩
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · have := h1 j
        rw [Function.update_of_ne hj] at this ⊢
        exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fintype.prod_eq_mul_prod_compl i,
    Fintype.prod_eq_mul_prod_compl i (fun j => nu E (s j))]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (by simpa using hj)]

theorem integral_marg (E : Env Ω) (hS : E.Standing) (i : Fin E.n)
    {g : (Fin E.n → ℝ) → ℝ} (hg : Integrable g (Measure.pi fun _ => nu E)) :
    ∫ C, g C ∂(Measure.pi fun _ => nu E) =
      ∫ c, ∫ C, g (Function.update C i c) ∂(Measure.pi fun _ => nu E) ∂(nu E) := by
  have := nu_prob E hS
  have hmp := update_mp E hS i
  have h1 : ∫ C, g C ∂(Measure.pi fun _ => nu E) =
      ∫ p, g (Function.update p.1 i p.2) ∂((Measure.pi fun _ : Fin E.n => nu E).prod (nu E)) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [h1]
  exact integral_prod_symm _ (hmp.integrable_comp_of_integrable hg)

theorem k_clamp_meas (E : Env Ω) (hS : E.Standing) :
    Measurable (fun p : ℝ × Ω => E.k (max E.clo (min p.1 E.chi)) p.2) := by
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, hkd, _, hkm, _, _⟩ := hS
  have hcl_mem : ∀ s, max E.clo (min s E.chi) ∈ Icc E.clo E.chi :=
    fun s => ⟨le_max_left _ _, max_le hlt.le (min_le_right _ _)⟩
  have hcont : ∀ ω, Continuous fun s => E.k (max E.clo (min s E.chi)) ω := by
    intro ω
    have hk : ContinuousOn (fun s => E.k s ω) (Icc E.clo E.chi) :=
      fun s hs => (hkd ω s hs).continuousWithinAt
    exact hk.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hcl_mem
  exact measurable_uncurry_of_continuous_of_measurable (u := fun s ω => E.k (max E.clo (min s E.chi)) ω)
    hcont (fun s => hkm _)

theorem clamp_eq (E : Env Ω) {s : ℝ} (hs : s ∈ Icc E.clo E.chi) :
    max E.clo (min s E.chi) = s := by
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem kc_aesm (E : Env Ω) (hS : E.Standing) {β : Type*} [MeasurableSpace β] (m : Measure β)
    {φ : β → ℝ × Ω} (hφ : Measurable φ) (hae : ∀ᵐ x ∂m, (φ x).1 ∈ Ico E.clo E.chi) :
    AEStronglyMeasurable (fun x => E.kc (φ x).1 (φ x).2) m := by
  have hK := k_clamp_meas E hS
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, hkd, _, hkm, _, _⟩ := hS
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (n : ℕ) x => ((n : ℝ) + 1) *
      (E.k (max E.clo (min ((φ x).1 + 1 / ((n : ℝ) + 1)) E.chi)) (φ x).2 -
        E.k (max E.clo (min (φ x).1 E.chi)) (φ x).2)) (fun n => ?_) ?_
  · have h1 : Measurable fun x =>
        E.k (max E.clo (min ((φ x).1 + 1 / ((n : ℝ) + 1)) E.chi)) (φ x).2 :=
      hK.comp (((measurable_fst.comp hφ).add_const _).prodMk (measurable_snd.comp hφ))
    have h2 : Measurable fun x => E.k (max E.clo (min (φ x).1 E.chi)) (φ x).2 := hK.comp hφ
    exact (measurable_const.mul (h1.sub h2)).aestronglyMeasurable
  · filter_upwards [hae] with x hx
    have hd := (hasDerivWithinAt_iff_tendsto_slope).mp
      (hkd (φ x).2 (φ x).1 (Ico_subset_Icc_self hx))
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < E.chi - (φ x).1 :=
      h0.eventually (gt_mem_nhds (sub_pos.mpr hx.2))
    have ht : Tendsto (fun n : ℕ => (φ x).1 + 1 / ((n : ℝ) + 1)) atTop
        (𝓝[Icc E.clo E.chi \ {(φ x).1}] (φ x).1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa using h0.const_add (φ x).1
      · filter_upwards [hev] with n hn
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        refine ⟨⟨by linarith [hx.1], by linarith⟩, ?_⟩
        simp only [mem_singleton_iff]
        intro h; linarith
    refine (hd.comp ht).congr' ?_
    filter_upwards [hev] with n hn
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hmem : (φ x).1 + 1 / ((n : ℝ) + 1) ∈ Icc E.clo E.chi :=
      ⟨by linarith [hx.1], by linarith⟩
    simp only [Function.comp_apply, slope_def_field, clamp_eq E hmem,
      clamp_eq E (Ico_subset_Icc_self hx), add_sub_cancel_left]
    field_simp

theorem ae_nu_Ico (E : Env Ω) : ∀ᵐ c ∂(nu E), c ∈ Ico E.clo E.chi := by
  unfold nu
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  show ∀ᵐ c ∂(volume.restrict (Icc E.clo E.chi)), c ∈ Ico E.clo E.chi
  rw [ae_restrict_iff' measurableSet_Icc]
  have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
  filter_upwards [hne] with x hx hxI
  exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

theorem ae_pi_Ico (E : Env Ω) (hS : E.Standing) (i : Fin E.n) :
    ∀ᵐ C ∂(Measure.pi fun _ : Fin E.n => nu E), C i ∈ Ico E.clo E.chi := by
  have := nu_prob E hS
  exact (measurePreserving_eval (μ := fun _ : Fin E.n => nu E) i).quasiMeasurePreserving.ae
    (ae_nu_Ico E)

theorem F_bounds (E : Env Ω) (hS : E.Standing) :
    ∀ c ∈ Icc E.clo E.chi, 0 ≤ E.F c ∧ E.F c ≤ 1 := by
  intro c hc
  have hf0 := f_nonneg E hS
  obtain ⟨_, _, _, hlt, _, hfi, hf1, _⟩ := hS
  have hfI : IntervalIntegrable E.f volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hfi
  have h1 : IntervalIntegrable E.f volume E.clo c :=
    hfI.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le hlt.le]; exact Icc_subset_Icc le_rfl hc.2)
  have h2 : IntervalIntegrable E.f volume c E.chi :=
    hfI.mono_set (by rw [uIcc_of_le hc.2, uIcc_of_le hlt.le]; exact Icc_subset_Icc hc.1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hn1 : 0 ≤ ∫ s in E.clo..c, E.f s :=
    intervalIntegral.integral_nonneg hc.1 fun u hu => hf0 u ⟨hu.1, hu.2.trans hc.2⟩
  have hn2 : 0 ≤ ∫ s in c..E.chi, E.f s :=
    intervalIntegral.integral_nonneg hc.2 fun u hu => hf0 u ⟨hc.1.trans hu.1, hu.2⟩
  unfold Env.F
  constructor
  · exact hn1
  · linarith

theorem F_contOn (E : Env Ω) (hS : E.Standing) : ContinuousOn E.F (Icc E.clo E.chi) := by
  obtain ⟨_, _, _, hlt, _, hfi, _⟩ := hS
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := E.clo)
    (b := E.chi) (f := E.f) (by rw [uIcc_of_le hlt.le]; exact hfi)
  rwa [uIcc_of_le hlt.le] at this

theorem Fc_meas (E : Env Ω) (hS : E.Standing) :
    Measurable (fun c => E.F (max E.clo (min c E.chi))) := by
  have hlt := hS.2.2.2.1
  have hcl_mem : ∀ s, max E.clo (min s E.chi) ∈ Icc E.clo E.chi :=
    fun s => ⟨le_max_left _ _, max_le hlt.le (min_le_right _ _)⟩
  exact ((F_contOn E hS).comp_continuous
    (continuous_const.max (continuous_id.min continuous_const)) hcl_mem).measurable

/-- `F/f` is bounded by `1/δ` on the support. -/
theorem Ff_bounds (E : Env Ω) (hS : E.Standing) :
    ∃ B, 0 ≤ B ∧ ∀ c ∈ Icc E.clo E.chi, 0 ≤ E.F c / E.f c ∧ E.F c / E.f c ≤ B := by
  have hFb := F_bounds E hS
  obtain ⟨_, _, _, _, _, _, _, ⟨δ, hδ, hfδ⟩, _⟩ := hS
  refine ⟨1 / δ, by positivity, fun c hc => ⟨div_nonneg (hFb c hc).1 (hδ.le.trans (hfδ c hc)), ?_⟩⟩
  calc E.F c / E.f c ≤ 1 / E.f c :=
        div_le_div_of_nonneg_right (hFb c hc).2 (hδ.le.trans (hfδ c hc))
    _ ≤ 1 / δ := one_div_le_one_div_of_le hδ (hfδ c hc)

theorem Ff_aesm (E : Env Ω) (hS : E.Standing) {β : Type*} [MeasurableSpace β] (m : Measure β)
    {φ : β → ℝ} (hφ : Measurable φ) (hae : ∀ᵐ x ∂m, φ x ∈ Icc E.clo E.chi) :
    AEStronglyMeasurable (fun x => E.F (φ x) / E.f (φ x)) m := by
  have hm : Measurable fun x => E.F (max E.clo (min (φ x) E.chi)) / E.f (φ x) :=
    ((Fc_meas E hS).comp hφ).div (hS.2.2.2.2.1.comp hφ)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with x hx
  simp only [clamp_eq E hx]

theorem nu_integral (E : Env Ω) (hS : E.Standing) (g : ℝ → ℝ) :
    ∫ c, g c ∂(nu E) = ∫ c in Icc E.clo E.chi, E.f c * g c := by
  rw [nu, integral_withDensity_eq_integral_toReal_smul hS.2.2.2.2.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Icc fun c hc => ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (f_nonneg E hS c hc)]

theorem ibp (E : Env Ω) (hS : E.Standing) {ψ : ℝ → ℝ}
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Icc E.clo E.chi))) {B : ℝ}
    (hψb : ∀ s ∈ Icc E.clo E.chi, |ψ s| ≤ B) :
    ∫ c, (∫ s in c..E.chi, ψ s) ∂(nu E) = ∫ c, (E.F c / E.f c) * ψ c ∂(nu E) := by
  have hf0 := f_nonneg E hS
  have hS' := hS
  obtain ⟨_, _, _, hlt, _, hfi, _, ⟨δ, hδ, hfδ⟩, _⟩ := hS'
  have hfI : IntervalIntegrable E.f volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hfi
  have hψi : IntegrableOn ψ (Icc E.clo E.chi) :=
    IntegrableOn.of_bound measure_Icc_lt_top hψm B
      ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun s hs => by
        rw [Real.norm_eq_abs]; exact hψb s hs))
  have hψI : IntervalIntegrable ψ volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hψi
  rw [nu_integral E hS, nu_integral E hS]
  have hR : ∫ c in Icc E.clo E.chi, E.f c * (E.F c / E.f c * ψ c) =
      ∫ c in Icc E.clo E.chi, E.F c * ψ c := by
    refine setIntegral_congr_fun measurableSet_Icc fun c hc => ?_
    have : E.f c ≠ 0 := (lt_of_lt_of_le hδ (hfδ c hc)).ne'
    field_simp
  rw [hR, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlt.le, ← intervalIntegral.integral_of_le hlt.le]
  -- integration by parts
  have hFac : AbsolutelyContinuousOnInterval E.F E.clo E.chi :=
    hfI.absolutelyContinuousOnInterval_intervalIntegral (c := E.clo) (by simp)
  set Ψ : ℝ → ℝ := fun c => ∫ s in c..E.chi, ψ s with hΨ
  have hΨeq : Ψ = fun c => -∫ s in E.chi..c, ψ s := by
    funext c; rw [hΨ, intervalIntegral.integral_symm]; simp
  have hΨac : AbsolutelyContinuousOnInterval Ψ E.clo E.chi := by
    rw [hΨeq]
    exact (hψI.absolutelyContinuousOnInterval_intervalIntegral (c := E.chi) (by simp)).neg
  have hibp := hFac.integral_mul_deriv_eq_deriv_mul hΨac
  have hΨchi : Ψ E.chi = 0 := by simp [hΨ]
  have hFclo : E.F E.clo = 0 := by simp [Env.F]
  rw [hΨchi, hFclo, mul_zero, zero_mul, sub_zero, zero_sub] at hibp
  have h1 : ∫ x in E.clo..E.chi, deriv E.F x * Ψ x = ∫ x in E.clo..E.chi, E.f x * Ψ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfI.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ uIcc E.clo E.chi := uIoc_subset_uIcc hxI
    have hx' : HasDerivAt E.F (E.f x) x := hx hxu E.clo (by simp)
    rw [hx'.deriv]
  have h2 : ∫ x in E.clo..E.chi, E.F x * deriv Ψ x = ∫ x in E.clo..E.chi, -(E.F x * ψ x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hψI.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ uIcc E.clo E.chi := uIoc_subset_uIcc hxI
    have hd : HasDerivAt Ψ (-ψ x) x := by
      rw [hΨeq]; exact (hx hxu E.chi (by simp)).neg
    rw [hd.deriv]; ring
  rw [h1, h2, intervalIntegral.integral_neg] at hibp
  linarith

theorem cube_meas (E : Env Ω) : MeasurableSet E.cube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem ae_cube (E : Env Ω) : ∀ᵐ C ∂E.profileLaw, C ∈ E.cube := by
  unfold Env.profileLaw
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (cube_meas E))

theorem finite (E : Env Ω) (hS : E.Standing) : IsFiniteMeasure E.profileLaw := by
  obtain ⟨_, _, _, _, _, hfi, _, ⟨δ, hδ, hfδ⟩, _⟩ := hS
  set g : ℝ → ℝ := (Icc E.clo E.chi).indicator E.f with hgdef
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    by_cases hx : x ∈ Icc E.clo E.chi
    · rw [hgdef, indicator_of_mem hx]; exact le_trans hδ.le (hfδ x hx)
    · rw [hgdef, indicator_of_notMem hx]
  have hgi : Integrable g := (integrable_indicator_iff measurableSet_Icc).mpr hfi
  have hprod : Integrable (fun C : Fin E.n → ℝ => ∏ i, g (C i))
      (Measure.pi fun _ => volume) := Integrable.fintype_prod (fun _ => hgi)
  constructor
  rw [Env.profileLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← lintegral_indicator (cube_meas E)]
  refine lt_of_le_of_lt ?_ hprod.2
  rw [volume_pi]
  apply lintegral_mono
  intro C
  by_cases hC : C ∈ E.cube
  · rw [indicator_of_mem hC]
    have hgC : ∀ i, g (C i) = E.f (C i) := fun i => indicator_of_mem (hC i (mem_univ _)) _
    show _ ≤ ‖∏ i, g (C i)‖ₑ
    rw [Real.enorm_eq_ofReal (Finset.prod_nonneg fun i _ => hg0 (C i)),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 (C i))]
    simp_rw [hgC]
    exact le_rfl
  · rw [indicator_of_notMem hC]; exact bot_le

theorem update_mem (E : Env Ω) (i : Fin E.n) {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ}
    (hd : d ∈ Icc E.clo E.chi) : Function.update C i d ∈ E.cube := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hd
  · rw [Function.update_of_ne hj]; exact hC j (mem_univ _)

theorem bounds1 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) :
    0 ≤ M.x1 (Function.update C i d) i ∧ M.x1 (Function.update C i d) i ≤ 1 := by
  obtain ⟨h1, h2⟩ := hM.1 _ (update_mem E i hC hd)
  have hx1 : M.x1 (Function.update C i d) i ≤ ∑ j, M.x1 (Function.update C i d) j :=
    Finset.single_le_sum (fun j _ => h1 j) (Finset.mem_univ i)
  exact ⟨h1 i, hx1.trans h2⟩

theorem bounds2 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) (ω : Ω) :
    0 ≤ M.x2 (Function.update C i d) ω i ∧ M.x2 (Function.update C i d) ω i ≤ 1 := by
  obtain ⟨h1, h2⟩ := hM.1 _ (update_mem E i hC hd)
  obtain ⟨h3, h4⟩ := hM.2.1 _ (update_mem E i hC hd) ω
  have hx2 : M.x2 (Function.update C i d) ω i ≤ ∑ j, M.x2 (Function.update C i d) ω j :=
    Finset.single_le_sum (fun j _ => h3 j) (Finset.mem_univ i)
  exact ⟨h3 i, (hx2.trans h4).trans h2⟩

theorem X1_bounds (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) :
    0 ≤ M.X1 E i d ∧ M.X1 E i d ≤ E.profileLaw.real univ := by
  have := finite E hS
  have hae : ∀ᵐ C ∂E.profileLaw,
      0 ≤ M.x1 (Function.update C i d) i ∧ M.x1 (Function.update C i d) i ≤ 1 := by
    filter_upwards [ae_cube E] with C hC using bounds1 E M hM i hC hd
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun C h => h.1)
  · calc M.X1 E i d ≤ ∫ _C, (1 : ℝ) ∂E.profileLaw :=
          integral_mono_of_nonneg (hae.mono fun C h => h.1) (integrable_const 1)
            (hae.mono fun C h => h.2)
      _ = E.profileLaw.real univ := by simp

theorem X2_bounds (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) {d : ℝ} (hd : d ∈ Icc E.clo E.chi) (ω : Ω) :
    0 ≤ M.X2 E i d ω ∧ M.X2 E i d ω ≤ E.profileLaw.real univ := by
  have := finite E hS
  have hae : ∀ᵐ C ∂E.profileLaw,
      0 ≤ M.x2 (Function.update C i d) ω i ∧ M.x2 (Function.update C i d) ω i ≤ 1 := by
    filter_upwards [ae_cube E] with C hC using bounds2 E M hM i hC hd ω
  constructor
  · exact integral_nonneg_of_ae (hae.mono fun C h => h.1)
  · calc M.X2 E i d ω ≤ ∫ _C, (1 : ℝ) ∂E.profileLaw :=
          integral_mono_of_nonneg (hae.mono fun C h => h.1) (integrable_const 1)
            (hae.mono fun C h => h.2)
      _ = E.profileLaw.real univ := by simp

theorem X2_meas (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) (d : ℝ) : StronglyMeasurable (fun ω => M.X2 E i d ω) := by
  have := finite E hS
  have hj : StronglyMeasurable
      (fun p : (Fin E.n → ℝ) × Ω => M.x2 (Function.update p.1 i d) p.2 i) :=
    ((hM.2.2.2.1 i).comp ((measurable_update_left.comp measurable_fst).prodMk
      measurable_snd)).stronglyMeasurable
  exact hj.integral_prod_left'


end IncProcInfra

namespace IncProcVSAux

open IncompleteProc.English IncProcInfra

variable {Ω : Type*} [MeasurableSpace Ω]

theorem profile_prob (E : Env Ω) (hS : E.Standing) : IsProbabilityMeasure E.profileLaw := by
  have := nu_prob E hS
  rw [profileLaw_eq E hS]
  infer_instance

theorem marg (E : Env Ω) (hS : E.Standing) (i : Fin E.n) {g : (Fin E.n → ℝ) → ℝ}
    (hg : Integrable g E.profileLaw) :
    ∫ C, g C ∂E.profileLaw = ∫ c, ∫ C, g (Function.update C i c) ∂E.profileLaw ∂(nu E) := by
  rw [profileLaw_eq E hS] at hg ⊢
  exact integral_marg E hS i hg

theorem marg_sec (E : Env Ω) (hS : E.Standing) (i : Fin E.n) {g : (Fin E.n → ℝ) → ℝ}
    (hg : Integrable g E.profileLaw) :
    ∀ᵐ c ∂(nu E), Integrable (fun C => g (Function.update C i c)) E.profileLaw := by
  have := nu_prob E hS
  rw [profileLaw_eq E hS] at hg ⊢
  exact ((update_mp E hS i).integrable_comp_of_integrable hg).prod_left_ae

theorem bdd_int {β : Type*} [MeasurableSpace β] {m : Measure β} [IsFiniteMeasure m]
    {h : β → ℝ} (hm : AEStronglyMeasurable h m) (B : ℝ) (hb : ∀ᵐ x ∂m, |h x| ≤ B) :
    Integrable h m :=
  Integrable.of_bound hm B (hb.mono fun x hx => by rwa [Real.norm_eq_abs])

theorem X1_meas (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) : StronglyMeasurable (fun s => M.X1 E i s) := by
  have := finite E hS
  have hj : StronglyMeasurable
      (fun p : (Fin E.n → ℝ) × ℝ => M.x1 (Function.update p.1 i p.2) i) :=
    ((hM.2.2.1 i).comp measurable_update').stronglyMeasurable
  exact hj.integral_prod_left'

theorem X2_joint (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) : StronglyMeasurable (fun p : ℝ × Ω => M.X2 E i p.1 p.2) := by
  have := finite E hS
  have hj : StronglyMeasurable (fun q : (Fin E.n → ℝ) × (ℝ × Ω) =>
      M.x2 (Function.update q.1 i q.2.1) q.2.2 i) :=
    ((hM.2.2.2.1 i).comp ((measurable_update'.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd))).stronglyMeasurable
  exact hj.integral_prod_left'

theorem psi_aesm (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) :
    AEStronglyMeasurable (fun s => M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)
      (volume.restrict (Icc E.clo E.chi)) := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  refine (X1_meas E hS M hM i).aestronglyMeasurable.add ?_
  refine AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Ω => E.Q * E.kc p.1 p.2 * M.X2 E i p.1 p.2) ?_
  have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
  have hae1 : ∀ᵐ s ∂(volume.restrict (Icc E.clo E.chi)), s ∈ Ico E.clo E.chi := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with x hx hxI
    exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩
  have hae : ∀ᵐ p ∂((volume.restrict (Icc E.clo E.chi)).prod E.G), p.1 ∈ Ico E.clo E.chi :=
    Measure.quasiMeasurePreserving_fst.ae hae1
  exact (aestronglyMeasurable_const.mul (kc_aesm E hS _ (φ := fun p : ℝ × Ω => p)
    measurable_id hae)).mul (X2_joint E hS M hM i).aestronglyMeasurable

theorem psi_bound (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) : ∀ s ∈ Icc E.clo E.chi,
      |M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G| ≤
        E.profileLaw.real univ + E.Q * E.K * E.profileLaw.real univ := by
  intro s hs
  have hS' := hS
  obtain ⟨_, hQ, _, _, _, _, _, _, hG, _, _, hkcb, _, _, _⟩ := hS'
  obtain ⟨h0, h1⟩ := X1_bounds E hS M hM i hs
  have hb : ∀ ω, ‖E.Q * E.kc s ω * M.X2 E i s ω‖ ≤ E.Q * E.K * E.profileLaw.real univ := by
    intro ω
    obtain ⟨g0, g1⟩ := X2_bounds E hS M hM i hs ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg g0,
      abs_of_nonneg (hkcb ω s hs).1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hkcb ω s hs).2 hQ.le) g1 g0
      (mul_nonneg hQ.le ((hkcb ω s hs).1.trans (hkcb ω s hs).2))
  have := norm_integral_le_of_norm_le_const (μ := E.G) (ae_of_all _ hb)
  simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
  calc _ ≤ |M.X1 E i s| + |∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G| := abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg h0]; linarith

theorem Psi1_bound (E : Env Ω) (hS : E.Standing) :
    ∃ P, ∀ c ∈ Icc E.clo E.chi, |E.Psi1 c| ≤ P := by
  obtain ⟨B, _, hB⟩ := Ff_bounds E hS
  refine ⟨|E.clo| + |E.chi| + B, fun c hc => ?_⟩
  unfold Env.Psi1
  have h1 : |c| ≤ |E.clo| + |E.chi| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le E.clo, le_abs_self E.chi, abs_nonneg E.clo,
      abs_nonneg E.chi, hc.1, hc.2]
  have h2 : |E.F c / E.f c| ≤ B := by rw [abs_of_nonneg (hB c hc).1]; exact (hB c hc).2
  calc |c + E.F c / E.f c| ≤ |c| + |E.F c / E.f c| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem Psi2_bound (E : Env Ω) (hS : E.Standing) :
    ∃ P, ∀ c ∈ Icc E.clo E.chi, ∀ ω, |E.Psi2 c ω| ≤ P := by
  obtain ⟨B, hB0, hB⟩ := Ff_bounds E hS
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hkcb, _, _, ⟨Mk, hMk⟩⟩ := hS
  refine ⟨Mk + B * E.K, fun c hc ω => ?_⟩
  unfold Env.Psi2
  have h2 : |E.F c / E.f c * E.kc c ω| ≤ B * E.K := by
    rw [abs_mul, abs_of_nonneg (hB c hc).1, abs_of_nonneg (hkcb ω c hc).1]
    exact mul_le_mul (hB c hc).2 (hkcb ω c hc).2 (hkcb ω c hc).1 hB0
  calc |E.k c ω + E.F c / E.f c * E.kc c ω| ≤ |E.k c ω| + |E.F c / E.f c * E.kc c ω| :=
        abs_add_le _ _
    _ ≤ _ := by linarith [hMk c hc ω]

theorem Psi1_aesm (E : Env Ω) (hS : E.Standing) {β : Type*} [MeasurableSpace β]
    (m : Measure β) {φ : β → ℝ} (hφ : Measurable φ) (hae : ∀ᵐ x ∂m, φ x ∈ Icc E.clo E.chi) :
    AEStronglyMeasurable (fun x => E.Psi1 (φ x)) m := by
  unfold Env.Psi1
  exact hφ.aestronglyMeasurable.add (Ff_aesm E hS m hφ hae)

theorem Psi2_aesm (E : Env Ω) (hS : E.Standing) {β : Type*} [MeasurableSpace β]
    (m : Measure β) {φ : β → ℝ × Ω} (hφ : Measurable φ)
    (hae : ∀ᵐ x ∂m, (φ x).1 ∈ Ico E.clo E.chi) :
    AEStronglyMeasurable (fun x => E.Psi2 (φ x).1 (φ x).2) m := by
  unfold Env.Psi2
  have hk : AEStronglyMeasurable (fun x => E.k (φ x).1 (φ x).2) m := by
    refine ((k_clamp_meas E hS).comp hφ).aestronglyMeasurable.congr ?_
    filter_upwards [hae] with x hx
    simp only [Function.comp_apply, clamp_eq E (Ico_subset_Icc_self hx)]
  have hF : AEStronglyMeasurable (fun x => E.F (φ x).1 / E.f (φ x).1) m :=
    Ff_aesm E hS m (measurable_fst.comp hφ) (hae.mono fun x hx => Ico_subset_Icc_self hx)
  exact hk.add (hF.mul (kc_aesm E hS m hφ hae))

theorem cube_b1 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) : 0 ≤ M.x1 C i ∧ M.x1 C i ≤ 1 := by
  have h := bounds1 E M hM i hC (hC i (mem_univ _))
  simpa only [Function.update_eq_self] using h

theorem cube_b2 (E : Env Ω) (M : Mech E.n Ω) (hM : M.Admissible E) (i : Fin E.n)
    {C : Fin E.n → ℝ} (hC : C ∈ E.cube) (ω : Ω) : 0 ≤ M.x2 C ω i ∧ M.x2 C ω i ≤ 1 := by
  have h := bounds2 E M hM i hC (hC i (mem_univ _)) ω
  simpa only [Function.update_eq_self] using h

theorem ae_prod_Ico (E : Env Ω) (hS : E.Standing) (i : Fin E.n) :
    ∀ᵐ p ∂(E.profileLaw.prod E.G), (p.1 i, p.2).1 ∈ Ico E.clo E.chi := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have h1 : ∀ᵐ C ∂E.profileLaw, C i ∈ Ico E.clo E.chi := by
    rw [profileLaw_eq E hS]; exact ae_pi_Ico E hS i
  exact Measure.quasiMeasurePreserving_fst.ae h1

theorem ae_prod_cube (E : Env Ω) (hS : E.Standing) :
    ∀ᵐ p ∂(E.profileLaw.prod E.G), p.1 ∈ E.cube := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  exact Measure.quasiMeasurePreserving_fst.ae (ae_cube E)

theorem int_a (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) :
    Integrable (fun C => E.R * M.x1 C i + ∫ ω, E.Q * E.R * M.x2 C ω i ∂E.G - M.t C i)
      E.profileLaw := by
  have := profile_prob E hS
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hQ := hS.2.1
  have hR := hS.2.2.1
  refine Integrable.sub (Integrable.add ?_ ?_) (hM.2.2.2.2 i)
  · refine bdd_int ((hM.2.2.1 i).const_mul E.R).aestronglyMeasurable E.R ?_
    filter_upwards [ae_cube E] with C hC
    have h := cube_b1 E M hM i hC
    rw [abs_mul, abs_of_pos hR, abs_of_nonneg h.1]
    nlinarith
  · have hm : StronglyMeasurable (fun p : (Fin E.n → ℝ) × Ω => E.Q * E.R * M.x2 p.1 p.2 i) :=
      (measurable_const.mul (hM.2.2.2.1 i)).stronglyMeasurable
    refine bdd_int hm.integral_prod_right'.aestronglyMeasurable (E.Q * E.R) ?_
    filter_upwards [ae_cube E] with C hC
    have hb : ∀ ω, ‖E.Q * E.R * M.x2 C ω i‖ ≤ E.Q * E.R := by
      intro ω
      have h := cube_b2 E M hM i hC ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos hQ hR), abs_of_nonneg h.1]
      nlinarith [mul_pos hQ hR]
    have := norm_integral_le_of_norm_le_const (μ := E.G) (ae_of_all _ hb)
    simpa [Real.norm_eq_abs] using this

theorem int_b (E : Env Ω) (hS : E.Standing) (M : Mech E.n Ω) (hM : M.Admissible E)
    (i : Fin E.n) :
    Integrable (fun C => M.x1 C i * (E.R - E.Psi1 (C i)) +
      ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) E.profileLaw := by
  have := profile_prob E hS
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hQ := hS.2.1
  have hR := hS.2.2.1
  obtain ⟨P1, hP1⟩ := Psi1_bound E hS
  obtain ⟨P2, hP2⟩ := Psi2_bound E hS
  have haeI : ∀ᵐ C ∂E.profileLaw, C i ∈ Icc E.clo E.chi :=
    (ae_cube E).mono fun C hC => hC i (mem_univ _)
  refine Integrable.add ?_ ?_
  · refine bdd_int ((hM.2.2.1 i).aestronglyMeasurable.mul (aestronglyMeasurable_const.sub
      (Psi1_aesm E hS _ (measurable_pi_apply i) haeI))) (E.R + P1) ?_
    filter_upwards [ae_cube E] with C hC
    have h := cube_b1 E M hM i hC
    have hp := hP1 (C i) (hC i (mem_univ _))
    rw [abs_mul, abs_of_nonneg h.1]
    have : |E.R - E.Psi1 (C i)| ≤ E.R + P1 := by
      calc |E.R - E.Psi1 (C i)| ≤ |E.R| + |E.Psi1 (C i)| := abs_sub _ _
        _ ≤ E.R + P1 := by rw [abs_of_pos hR]; linarith
    calc M.x1 C i * |E.R - E.Psi1 (C i)| ≤ 1 * (E.R + P1) :=
          mul_le_mul h.2 this (abs_nonneg _) zero_le_one
      _ = E.R + P1 := one_mul _
  · have hm : AEStronglyMeasurable (fun p : (Fin E.n → ℝ) × Ω =>
        E.Q * M.x2 p.1 p.2 i * (E.R - E.Psi2 (p.1 i) p.2)) (E.profileLaw.prod E.G) :=
      ((measurable_const.mul (hM.2.2.2.1 i)).aestronglyMeasurable).mul
        (aestronglyMeasurable_const.sub (Psi2_aesm E hS _ (φ := fun p : (Fin E.n → ℝ) × Ω => (p.1 i, p.2))
          ((measurable_pi_apply i).comp measurable_fst |>.prodMk measurable_snd)
          (ae_prod_Ico E hS i)))
    refine bdd_int hm.integral_prod_right' (E.Q * (E.R + P2)) ?_
    filter_upwards [ae_cube E] with C hC
    have hb : ∀ ω, ‖E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω)‖ ≤ E.Q * (E.R + P2) := by
      intro ω
      have h := cube_b2 E M hM i hC ω
      have hp := hP2 (C i) (hC i (mem_univ _)) ω
      have : |E.R - E.Psi2 (C i) ω| ≤ E.R + P2 := by
        calc |E.R - E.Psi2 (C i) ω| ≤ |E.R| + |E.Psi2 (C i) ω| := abs_sub _ _
          _ ≤ E.R + P2 := by rw [abs_of_pos hR]; linarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg h.1]
      calc E.Q * M.x2 C ω i * |E.R - E.Psi2 (C i) ω| ≤ E.Q * 1 * (E.R + P2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h.2 hQ.le) this (abs_nonneg _)
              (by linarith)
        _ = E.Q * (E.R + P2) := by ring
    have := norm_integral_le_of_norm_le_const (μ := E.G) (ae_of_all _ hb)
    simpa [Real.norm_eq_abs] using this

theorem sec_value (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (M : Mech E.n Ω)
    (hM : M.Admissible E) (hIC : M.IsIC E) (i : Fin E.n) {c : ℝ}
    (hc : c ∈ Ico E.clo E.chi)
    (htc : Integrable (fun C => M.t (Function.update C i c) i) E.profileLaw) :
    ∫ C, ((E.R * M.x1 (Function.update C i c) i +
        ∫ ω, E.Q * E.R * M.x2 (Function.update C i c) ω i ∂E.G -
          M.t (Function.update C i c) i) -
      (M.x1 (Function.update C i c) i * (E.R - E.Psi1 (Function.update C i c i)) +
        ∫ ω, E.Q * M.x2 (Function.update C i c) ω i *
          (E.R - E.Psi2 (Function.update C i c i) ω) ∂E.G)) ∂E.profileLaw =
    E.F c / E.f c * (M.X1 E i c + ∫ ω, E.Q * E.kc c ω * M.X2 E i c ω ∂E.G) -
      (∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) -
        M.U E i E.chi E.chi := by
  have := profile_prob E hS
  have := finite E hS
  have hcI : c ∈ Icc E.clo E.chi := Ico_subset_Icc_self hc
  have hS' := hS
  obtain ⟨_, hQ, hR, hlt, _, _, _, _, hG, _, _, hkcb, hkm, hkcm, ⟨Mk, hMk⟩⟩ := hS'
  obtain ⟨P2, hP2⟩ := Psi2_bound E hS
  have hPsi2m : Measurable (fun ω => E.Psi2 c ω) := by
    unfold Env.Psi2; exact (hkm c).add (measurable_const.mul (hkcm c))
  have hx2m : ∀ C, Measurable (fun ω => M.x2 (Function.update C i c) ω i) := fun C =>
    (hM.2.2.2.1 i).comp (measurable_const.prodMk measurable_id)
  -- Step 1: pointwise simplification on the cube
  have hpt : ∀ᵐ C ∂E.profileLaw,
      ((E.R * M.x1 (Function.update C i c) i +
        ∫ ω, E.Q * E.R * M.x2 (Function.update C i c) ω i ∂E.G -
          M.t (Function.update C i c) i) -
      (M.x1 (Function.update C i c) i * (E.R - E.Psi1 (Function.update C i c i)) +
        ∫ ω, E.Q * M.x2 (Function.update C i c) ω i *
          (E.R - E.Psi2 (Function.update C i c i) ω) ∂E.G)) =
      M.x1 (Function.update C i c) i * E.Psi1 c +
        ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * E.Psi2 c ω ∂E.G -
          M.t (Function.update C i c) i := by
    filter_upwards [ae_cube E] with C hC
    simp only [Function.update_self]
    have hb : ∀ ω, 0 ≤ M.x2 (Function.update C i c) ω i ∧ M.x2 (Function.update C i c) ω i ≤ 1 :=
      bounds2 E M hM i hC hcI
    have i1 : Integrable (fun ω => E.Q * E.R * M.x2 (Function.update C i c) ω i) E.G := by
      refine bdd_int (measurable_const.mul (hx2m C)).aestronglyMeasurable (E.Q * E.R)
        (ae_of_all _ fun ω => ?_)
      rw [abs_mul, abs_of_pos (mul_pos hQ hR), abs_of_nonneg (hb ω).1]
      nlinarith [(hb ω).2, mul_pos hQ hR]
    have i2 : Integrable (fun ω => E.Q * M.x2 (Function.update C i c) ω i *
        (E.R - E.Psi2 c ω)) E.G := by
      refine bdd_int ((measurable_const.mul (hx2m C)).mul (measurable_const.sub hPsi2m)
        ).aestronglyMeasurable (E.Q * (E.R + P2)) (ae_of_all _ fun ω => ?_)
      have : |E.R - E.Psi2 c ω| ≤ E.R + P2 := by
        calc |E.R - E.Psi2 c ω| ≤ |E.R| + |E.Psi2 c ω| := abs_sub _ _
          _ ≤ E.R + P2 := by rw [abs_of_pos hR]; linarith [hP2 c hcI ω]
      rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg (hb ω).1]
      calc E.Q * M.x2 (Function.update C i c) ω i * |E.R - E.Psi2 c ω| ≤ E.Q * 1 * (E.R + P2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hb ω).2 hQ.le) this (abs_nonneg _)
              (by linarith)
        _ = E.Q * (E.R + P2) := by ring
    have hsplit : ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * E.Psi2 c ω ∂E.G =
        (∫ ω, E.Q * E.R * M.x2 (Function.update C i c) ω i ∂E.G) -
          ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * (E.R - E.Psi2 c ω) ∂E.G := by
      rw [← integral_sub i1 i2]
      congr 1; funext ω; ring
    rw [hsplit]; ring
  rw [integral_congr_ae hpt]
  have hx1m : Measurable (fun C => M.x1 (Function.update C i c) i) :=
    (hM.2.2.1 i).comp measurable_update_left
  have hjm : Measurable (fun p : (Fin E.n → ℝ) × Ω =>
      E.Q * M.x2 (Function.update p.1 i c) p.2 i * E.Psi2 c p.2) :=
    (measurable_const.mul ((hM.2.2.2.1 i).comp ((measurable_update_left.comp
      measurable_fst).prodMk measurable_snd))).mul (hPsi2m.comp measurable_snd)
  have hjb : ∀ᵐ p ∂(E.profileLaw.prod E.G),
      |E.Q * M.x2 (Function.update p.1 i c) p.2 i * E.Psi2 c p.2| ≤ E.Q * P2 := by
    filter_upwards [ae_prod_cube E hS] with p hp
    have hb := bounds2 E M hM i hp hcI p.2
    rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg hb.1]
    calc _ ≤ E.Q * 1 * P2 := mul_le_mul (mul_le_mul_of_nonneg_left hb.2 hQ.le)
          (hP2 c hcI p.2) (abs_nonneg _) (by linarith)
      _ = _ := by ring
  have hjint : Integrable (fun p : (Fin E.n → ℝ) × Ω =>
      E.Q * M.x2 (Function.update p.1 i c) p.2 i * E.Psi2 c p.2) (E.profileLaw.prod E.G) :=
    bdd_int hjm.aestronglyMeasurable _ hjb
  have hI1 : Integrable (fun C => M.x1 (Function.update C i c) i * E.Psi1 c) E.profileLaw := by
    refine bdd_int (hx1m.mul_const _).aestronglyMeasurable (|E.Psi1 c|) ?_
    filter_upwards [ae_cube E] with C hC
    have hb := bounds1 E M hM i hC hcI
    rw [abs_mul, abs_of_nonneg hb.1]
    nlinarith [abs_nonneg (E.Psi1 c)]
  have hI2 : Integrable (fun C => ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * E.Psi2 c ω ∂E.G)
      E.profileLaw := hjint.integral_prod_left
  have hI12 : Integrable (fun C => M.x1 (Function.update C i c) i * E.Psi1 c +
      ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * E.Psi2 c ω ∂E.G) E.profileLaw :=
    hI1.add hI2
  rw [integral_sub hI12 htc, integral_add hI1 hI2, integral_mul_const]
  have hswap : ∫ C, ∫ ω, E.Q * M.x2 (Function.update C i c) ω i * E.Psi2 c ω ∂E.G
      ∂E.profileLaw = ∫ ω, E.Q * E.Psi2 c ω * M.X2 E i c ω ∂E.G := by
    rw [integral_integral_swap (f := fun C ω => E.Q * M.x2 (Function.update C i c) ω i *
      E.Psi2 c ω) hjint]
    congr 1; funext ω
    unfold Mech.X2
    rw [← integral_const_mul]; congr 1; funext C; ring
  have hL1 := (lemma_1 E hS hA M hM hIC).1 i c hcI
  have hU : M.U E i c c = M.T E i c - M.X1 E i c * c -
      ∫ ω, E.Q * E.k c ω * M.X2 E i c ω ∂E.G := rfl
  have hT : M.T E i c = ∫ C, M.t (Function.update C i c) i ∂E.profileLaw := rfl
  have hX1 : M.X1 E i c = ∫ C, M.x1 (Function.update C i c) i ∂E.profileLaw := rfl
  have hX2b := X2_bounds E hS M hM i hcI
  have hX2m := X2_meas E hS M hM i c
  set m := E.profileLaw.real univ with hm
  have iK : Integrable (fun ω => E.Q * E.k c ω * M.X2 E i c ω) E.G := by
    refine bdd_int ((measurable_const.mul (hkm c)).stronglyMeasurable.mul hX2m
      ).aestronglyMeasurable (E.Q * Mk * m) (ae_of_all _ fun ω => ?_)
    rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg (hX2b ω).1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hMk c hcI ω) hQ.le) (hX2b ω).2 (hX2b ω).1
      (mul_nonneg hQ.le ((abs_nonneg _).trans (hMk c hcI ω)))
  have iKc : Integrable (fun ω => E.Q * E.kc c ω * M.X2 E i c ω) E.G := by
    refine bdd_int ((measurable_const.mul (hkcm c)).stronglyMeasurable.mul hX2m
      ).aestronglyMeasurable (E.Q * E.K * m) (ae_of_all _ fun ω => ?_)
    rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg (hX2b ω).1,
      abs_of_nonneg (hkcb ω c hcI).1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hkcb ω c hcI).2 hQ.le) (hX2b ω).2 (hX2b ω).1
      (mul_nonneg hQ.le ((hkcb ω c hcI).1.trans (hkcb ω c hcI).2))
  have hsplit2 : ∫ ω, E.Q * E.Psi2 c ω * M.X2 E i c ω ∂E.G =
      (∫ ω, E.Q * E.k c ω * M.X2 E i c ω ∂E.G) +
        E.F c / E.f c * ∫ ω, E.Q * E.kc c ω * M.X2 E i c ω ∂E.G := by
    rw [← integral_const_mul, ← integral_add iK (iKc.const_mul _)]
    congr 1; funext ω; unfold Env.Psi2; ring
  have hPsi1 : E.Psi1 c = c + E.F c / E.f c := rfl
  rw [hswap, hsplit2, hPsi1, ← hX1, ← hT]
  have hTe : M.T E i c = M.U E i E.chi E.chi +
      (∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) +
      M.X1 E i c * c + ∫ ω, E.Q * E.k c ω * M.X2 E i c ω ∂E.G := by linarith [hL1, hU]
  rw [hTe]; ring

theorem per_i (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (M : Mech E.n Ω)
    (hM : M.Admissible E) (hIC : M.IsIC E) (i : Fin E.n) :
    ∫ C, (E.R * M.x1 C i + ∫ ω, E.Q * E.R * M.x2 C ω i ∂E.G - M.t C i) ∂E.profileLaw =
      (∫ C, (M.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ∂E.profileLaw) -
        M.U E i E.chi E.chi := by
  have hν := nu_prob E hS
  have ha := int_a E hS M hM i
  have hb := int_b E hS M hM i
  have hlt := hS.2.2.2.1
  obtain ⟨B, hB0, hB⟩ := Ff_bounds E hS
  set L := E.profileLaw.real univ + E.Q * E.K * E.profileLaw.real univ with hL
  have hψb := psi_bound E hS M hM i
  have hψm := psi_aesm E hS M hM i
  have hac : nu E ≪ volume.restrict (Icc E.clo E.chi) := withDensity_absolutelyContinuous _ _
  have haeI : ∀ᵐ c ∂(nu E), c ∈ Icc E.clo E.chi :=
    (ae_nu_Ico E).mono fun c hc => Ico_subset_Icc_self hc
  have hψi : IntegrableOn (fun s => M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)
      (Icc E.clo E.chi) :=
    IntegrableOn.of_bound measure_Icc_lt_top hψm L
      ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun s hs => by
        rw [Real.norm_eq_abs]; exact hψb s hs))
  have hFfψ : Integrable (fun c => E.F c / E.f c *
      (M.X1 E i c + ∫ ω, E.Q * E.kc c ω * M.X2 E i c ω ∂E.G)) (nu E) := by
    refine bdd_int ((Ff_aesm E hS (nu E) measurable_id haeI).mul (hψm.mono_ac hac)) (B * L) ?_
    filter_upwards [haeI] with c hc
    rw [abs_mul, abs_of_nonneg (hB c hc).1]
    exact mul_le_mul (hB c hc).2 (hψb c hc) (abs_nonneg _) hB0
  have hΨ : Integrable (fun c => ∫ s in c..E.chi,
      (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) (nu E) := by
    have hco := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (a := E.clo) (b := E.chi) (by rw [uIcc_of_le hlt.le]; exact hψi)
    rw [uIcc_of_le hlt.le] at hco
    refine bdd_int ((hco.aestronglyMeasurable measurableSet_Icc).mono_ac hac)
      (L * (E.chi - E.clo)) ?_
    filter_upwards [haeI] with c hc
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := E.chi)
      (C := L) (f := fun s => M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)
      (fun s hs => by
        rw [uIoc_of_le hc.2] at hs
        rw [Real.norm_eq_abs]; exact hψb s ⟨hc.1.trans hs.1.le, hs.2⟩)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc.2)] at this
    have hL0 : 0 ≤ L := le_trans (abs_nonneg _) (hψb c hc)
    nlinarith [hc.1]
  have hd : ∫ C, ((E.R * M.x1 C i + ∫ ω, E.Q * E.R * M.x2 C ω i ∂E.G - M.t C i) -
      (M.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G)) ∂E.profileLaw =
      -M.U E i E.chi E.chi := by
    have hab : Integrable (fun C => (E.R * M.x1 C i + ∫ ω, E.Q * E.R * M.x2 C ω i ∂E.G -
        M.t C i) - (M.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G)) E.profileLaw := ha.sub hb
    rw [marg E hS i hab]
    have hae : ∀ᵐ c ∂(nu E), ∫ C, ((E.R * M.x1 (Function.update C i c) i +
        ∫ ω, E.Q * E.R * M.x2 (Function.update C i c) ω i ∂E.G -
          M.t (Function.update C i c) i) -
      (M.x1 (Function.update C i c) i * (E.R - E.Psi1 (Function.update C i c i)) +
        ∫ ω, E.Q * M.x2 (Function.update C i c) ω i *
          (E.R - E.Psi2 (Function.update C i c i) ω) ∂E.G)) ∂E.profileLaw =
        E.F c / E.f c * (M.X1 E i c + ∫ ω, E.Q * E.kc c ω * M.X2 E i c ω ∂E.G) -
          (∫ s in c..E.chi, (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) -
            M.U E i E.chi E.chi := by
      filter_upwards [ae_nu_Ico E, marg_sec E hS i (hM.2.2.2.2 i)] with c hc htc
      exact sec_value E hS hA M hM hIC i hc htc
    have hFΨ : Integrable (fun c => E.F c / E.f c *
        (M.X1 E i c + ∫ ω, E.Q * E.kc c ω * M.X2 E i c ω ∂E.G) - ∫ s in c..E.chi,
        (M.X1 E i s + ∫ ω, E.Q * E.kc s ω * M.X2 E i s ω ∂E.G)) (nu E) := hFfψ.sub hΨ
    rw [integral_congr_ae hae, integral_sub hFΨ (integrable_const _),
      integral_sub hFfψ hΨ, integral_const,
      ibp E hS hψm hψb]
    simp
  rw [integral_sub ha hb] at hd
  linarith

end IncProcVSAux

open IncompleteProc.English IncProcVSAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) (M : Mech E.n Ω) (hM : M.Admissible E) (hIC : M.IsIC E) :
    M.buyerSurplus E =
      (∫ C, ∑ i, (M.x1 C i * (E.R - E.Psi1 (C i)) +
          ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ∂E.profileLaw) -
        ∑ i, M.U E i E.chi E.chi := by
  unfold Mech.buyerSurplus
  rw [integral_finset_sum _ (fun i _ => int_a E hS M hM i),
    integral_finset_sum _ (fun i _ => int_b E hS M hM i), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => per_i E hS hA M hM hIC i
