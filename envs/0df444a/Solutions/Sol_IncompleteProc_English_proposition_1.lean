-- Prove2me | solution 1 for IncompleteProc.English.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:31:25.793044+00:00
-- url     : https://prove2.me/submissions/77e4113c-5c44-49b9-a547-2582d59e6eac

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Theorems.Thm_IncompleteProc_English_virtual_surplus

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


theorem cStar2_bdd (E : Env Ω) (hlt : E.clo < E.chi) (ω : Ω) :
    BddAbove (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}) := by
  refine ⟨E.chi, ?_⟩
  rintro y (rfl | ⟨hy, _⟩)
  · exact hlt.le
  · exact hy.2

theorem cStar2_mem (E : Env Ω) (hlt : E.clo < E.chi) (ω : Ω) :
    E.cStar2 ω ∈ Icc E.clo E.chi := by
  refine ⟨le_csSup (cStar2_bdd E hlt ω) (mem_insert _ _), csSup_le ⟨_, mem_insert _ _⟩ ?_⟩
  rintro y (rfl | ⟨hy, _⟩)
  · exact hlt.le
  · exact hy.2

theorem cStar2_meas (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    Measurable E.cStar2 := by
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, _, _, hkm, hkcm, _⟩ := hS
  have hPsi : ∀ q, Measurable (fun ω => E.Psi2 q ω) := by
    intro q; unfold Env.Psi2; exact (hkm q).add (measurable_const.mul (hkcm q))
  apply measurable_of_Ici
  intro x
  by_cases hx1 : x ≤ E.clo
  · convert MeasurableSet.univ
    ext ω
    simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
    exact hx1.trans (cStar2_mem E hlt ω).1
  by_cases hx2 : E.chi < x
  · convert MeasurableSet.empty
    ext ω
    simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false, not_le]
    exact (cStar2_mem E hlt ω).2.trans_lt hx2
  push Not at hx1 hx2
  have hset : E.cStar2 ⁻¹' Ici x =
      ⋂ q : ℚ, {ω | (E.clo < (q : ℝ) ∧ (q : ℝ) < x) → E.Psi2 q ω ≤ E.R} := by
    ext ω
    simp only [mem_preimage, mem_Ici, mem_iInter, mem_setOf_eq]
    have hc2 : E.cStar2 ω = sSup (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}) := rfl
    constructor
    · rintro hxc q ⟨hq1, hq2⟩
      obtain ⟨y, hyS, hqy⟩ := exists_lt_of_lt_csSup (⟨_, mem_insert _ _⟩ :
        (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}).Nonempty)
        (hc2 ▸ lt_of_lt_of_le hq2 hxc)
      rcases hyS with rfl | ⟨hyI, hyR⟩
      · exact absurd hq1 (not_lt.mpr hqy.le)
      · exact le_trans (hA.2 ω ⟨hq1.le, hqy.le.trans hyI.2⟩ hyI hqy.le) hyR
    · intro h
      by_contra hcon
      push Not at hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hx1 hcon)
      have hq := h q ⟨lt_of_le_of_lt (le_max_left _ _) hq1, hq2⟩
      have : (q : ℝ) ≤ E.cStar2 ω := le_csSup (cStar2_bdd E hlt ω)
        (Or.inr ⟨⟨(le_max_left _ _).trans hq1.le, hq2.le.trans hx2⟩, hq⟩)
      exact absurd (lt_of_le_of_lt (le_max_right _ _) hq1) (not_lt.mpr this)
  rw [hset]
  refine MeasurableSet.iInter fun q => ?_
  by_cases hq : E.clo < (q : ℝ) ∧ (q : ℝ) < x
  · convert measurableSet_le (hPsi q) (measurable_const (a := E.R)) using 1
    ext ω; simp [hq]
  · convert MeasurableSet.univ using 1
    ext ω; simp [hq]

theorem kc2_meas (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    Measurable (fun ω => E.k (E.cStar2 ω) ω) := by
  have hS' := hS
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, hkd, _, hkm, _, _⟩ := hS'
  set cl : ℝ → ℝ := fun s => max E.clo (min s E.chi) with hcl
  have hcl_mem : ∀ s, cl s ∈ Icc E.clo E.chi :=
    fun s => ⟨le_max_left _ _, max_le hlt.le (min_le_right _ _)⟩
  have hcl_id : ∀ s ∈ Icc E.clo E.chi, cl s = s := fun s hs => by
    simp only [hcl, min_eq_left hs.2, max_eq_right hs.1]
  have hcont : ∀ ω, Continuous fun s => E.k (cl s) ω := by
    intro ω
    have hk : ContinuousOn (fun s => E.k s ω) (Icc E.clo E.chi) :=
      fun s hs => (hkd ω s hs).continuousWithinAt
    exact hk.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hcl_mem
  have hj : Measurable (Function.uncurry fun s ω => E.k (cl s) ω) :=
    measurable_uncurry_of_continuous_of_measurable hcont (fun s => hkm (cl s))
  have hfun : (fun ω => E.k (E.cStar2 ω) ω) =
      fun ω => Function.uncurry (fun s ω => E.k (cl s) ω) (E.cStar2 ω, ω) := by
    funext ω
    simp only [Function.uncurry_apply_pair, hcl_id _ (cStar2_mem E hlt ω)]
  rw [hfun]
  exact hj.comp ((cStar2_meas E hS hA).prodMk measurable_id)


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

end IncProcVSAux

namespace IncProcP1Aux

open IncompleteProc.English IncProcInfra IncProcVSAux

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cStar1_mem (E : Env Ω) (hlt : E.clo < E.chi) : E.cStar1 ∈ Icc E.clo E.chi := by
  have hbdd : BddAbove (insert E.clo {c ∈ Icc E.clo E.chi |
      E.Psi1 c ≤ E.R + ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G}) := by
    refine ⟨E.chi, ?_⟩
    rintro y (rfl | ⟨hy, _⟩)
    · exact hlt.le
    · exact hy.2
  refine ⟨le_csSup hbdd (mem_insert _ _), csSup_le ⟨_, mem_insert _ _⟩ ?_⟩
  rintro y (rfl | ⟨hy, _⟩)
  · exact hlt.le
  · exact hy.2

theorem lowest_unique {n : ℕ} {C : Fin n → ℝ} {i j : Fin n} (hi : isLowest C i)
    (hj : isLowest C j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 := hj.1 i h
    have h2 := hi.2 j h
    linarith
  · have h1 := hi.1 j h
    have h2 := hj.2 i h
    linarith

theorem exists_lowest {n : ℕ} (hn : 1 ≤ n) (C : Fin n → ℝ) : ∃ i, isLowest C i := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne C with hm
  have hS : (Finset.univ.filter fun j => C j = m).Nonempty := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' hne C
    exact ⟨j, by simp [hj, hm]⟩
  set i := (Finset.univ.filter fun j => C j = m).min' hS with hi
  have hiS : i ∈ Finset.univ.filter fun j => C j = m := Finset.min'_mem _ hS
  have hCi : C i = m := (Finset.mem_filter.mp hiS).2
  refine ⟨i, fun j hj => ?_, fun j _ => ?_⟩
  · have hle : m ≤ C j := Finset.inf'_le _ (Finset.mem_univ j)
    rcases lt_or_eq_of_le hle with h | h
    · rw [hCi]; exact h
    · exfalso
      have : i ≤ j := Finset.min'_le _ _ (by simp [h])
      exact absurd hj (not_lt.mpr this)
  · rw [hCi]; exact Finset.inf'_le _ (Finset.mem_univ j)

/-- The boxes describing the event that supplier `i` with cost `c` is the lowest. -/
def sL {n : ℕ} (c : ℝ) (i : Fin n) (j : Fin n) : Set ℝ :=
  if j = i then univ else if j < i then Ioi c else Ici c

theorem isLowest_update_iff {n : ℕ} (C : Fin n → ℝ) (i : Fin n) (c : ℝ) :
    isLowest (Function.update C i c) i ↔ C ∈ univ.pi (sL c i) := by
  simp only [isLowest, Function.update_self, Set.mem_pi, mem_univ, true_implies, sL]
  constructor
  · rintro ⟨h1, h2⟩ j
    by_cases hji : j = i
    · simp [hji]
    · rw [if_neg hji]
      rcases lt_or_gt_of_ne hji with h | h
      · rw [if_pos h]; have := h1 j h; rwa [Function.update_of_ne hji] at this
      · rw [if_neg (not_lt.mpr h.le)]
        have := h2 j h; rw [Function.update_of_ne hji] at this; exact this
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hji : j ≠ i := hj.ne
      have := h j; rw [if_neg hji, if_pos hj] at this
      rw [Function.update_of_ne hji]; exact this
    · have hji : j ≠ i := hj.ne'
      have := h j; rw [if_neg hji, if_neg (not_lt.mpr hj.le)] at this
      rw [Function.update_of_ne hji]; exact this

theorem sL_meas {n : ℕ} (c : ℝ) (i : Fin n) (j : Fin n) : MeasurableSet (sL c i j) := by
  unfold sL
  split_ifs
  · exact MeasurableSet.univ
  · exact measurableSet_Ioi
  · exact measurableSet_Ici

theorem nu_singleton (E : Env Ω) (c : ℝ) : nu E {c} = 0 := by
  unfold nu
  exact withDensity_absolutelyContinuous _ _
    (by rw [Measure.restrict_apply (measurableSet_singleton c)]
        exact measure_mono_null inter_subset_left (measure_singleton c))

theorem nu_Ici (E : Env Ω) (hS : E.Standing) {c : ℝ} (hc : c ∈ Icc E.clo E.chi) :
    nu E (Ici c) = ENNReal.ofReal (1 - E.F c) := by
  rw [nu_apply E hS measurableSet_Ici]
  congr 1
  have hlt := hS.2.2.2.1
  have hfi := hS.2.2.2.2.2.1
  have hf1 := hS.2.2.2.2.2.2.1
  have hfI : IntervalIntegrable E.f volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hfi
  have h1 : IntervalIntegrable E.f volume E.clo c :=
    hfI.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le hlt.le]; exact Icc_subset_Icc le_rfl hc.2)
  have h2 : IntervalIntegrable E.f volume c E.chi :=
    hfI.mono_set (by rw [uIcc_of_le hc.2, uIcc_of_le hlt.le]; exact Icc_subset_Icc hc.1 le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hset : Ici c ∩ Icc E.clo E.chi = Icc c E.chi := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, hc.1.trans h1, h3⟩
  rw [hset, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hc.2]
  unfold Env.F
  linarith

theorem nu_Ioi (E : Env Ω) (hS : E.Standing) {c : ℝ} (hc : c ∈ Icc E.clo E.chi) :
    nu E (Ioi c) = ENNReal.ofReal (1 - E.F c) := by
  rw [← nu_Ici E hS hc]
  exact measure_congr (Ioi_ae_eq_Ici' (nu_singleton E c))

theorem prob_lowest (E : Env Ω) (hS : E.Standing) (i : Fin E.n) {c : ℝ}
    (hc : c ∈ Icc E.clo E.chi) :
    E.profileLaw.real {C | isLowest (Function.update C i c) i} = E.H c := by
  have := nu_prob E hS
  have hset : {C | isLowest (Function.update C i c) i} = univ.pi (sL c i) := by
    ext C; exact isLowest_update_iff C i c
  have hF := (F_bounds E hS c hc)
  rw [hset, profileLaw_eq E hS, measureReal_def, Measure.pi_pi]
  have hfac : ∀ j, nu E (sL c i j) = if j = i then 1 else ENNReal.ofReal (1 - E.F c) := by
    intro j
    unfold sL
    by_cases hji : j = i
    · simp [hji]
    · rw [if_neg hji, if_neg hji]
      split_ifs
      · exact nu_Ioi E hS hc
      · exact nu_Ici E hS hc
  simp_rw [hfac]
  rw [Fintype.prod_eq_mul_prod_compl i, if_pos rfl, one_mul]
  have : ∏ j ∈ ({i}ᶜ : Finset (Fin E.n)), (if j = i then (1 : ENNReal) else
      ENNReal.ofReal (1 - E.F c)) = ∏ j ∈ ({i}ᶜ : Finset (Fin E.n)), ENNReal.ofReal (1 - E.F c) :=
    Finset.prod_congr rfl fun j hj => if_neg (by simpa using hj)
  rw [this, Finset.prod_const, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by linarith [hF.2])]
  rfl

theorem F_mono (E : Env Ω) (hS : E.Standing) {a b : ℝ} (ha : a ∈ Icc E.clo E.chi)
    (hb : b ∈ Icc E.clo E.chi) (hab : a ≤ b) : E.F a ≤ E.F b := by
  have hf0 := f_nonneg E hS
  have hlt := hS.2.2.2.1
  have hfi := hS.2.2.2.2.2.1
  have hfI : IntervalIntegrable E.f volume E.clo E.chi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le).mpr hfi
  have h1 : IntervalIntegrable E.f volume E.clo a :=
    hfI.mono_set (by rw [uIcc_of_le ha.1, uIcc_of_le hlt.le]; exact Icc_subset_Icc le_rfl ha.2)
  have h2 : IntervalIntegrable E.f volume a b :=
    hfI.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hlt.le]; exact Icc_subset_Icc ha.1 hb.2)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hn : 0 ≤ ∫ s in a..b, E.f s :=
    intervalIntegral.integral_nonneg hab fun u hu => hf0 u ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
  unfold Env.F
  linarith

theorem H_bounds (E : Env Ω) (hS : E.Standing) {c : ℝ} (hc : c ∈ Icc E.clo E.chi) :
    0 ≤ E.H c ∧ E.H c ≤ 1 := by
  have hF := F_bounds E hS c hc
  unfold Env.H
  exact ⟨pow_nonneg (by linarith) _, pow_le_one₀ (by linarith) (by linarith)⟩

theorem H_anti (E : Env Ω) (hS : E.Standing) {a b : ℝ} (ha : a ∈ Icc E.clo E.chi)
    (hb : b ∈ Icc E.clo E.chi) (hab : a ≤ b) : E.H b ≤ E.H a := by
  have hF := F_bounds E hS b hb
  have hm := F_mono E hS ha hb hab
  unfold Env.H
  exact pow_le_pow_left₀ (by linarith) (by linarith) _

theorem lowest_meas {n : ℕ} (i : Fin n) (c : ℝ) :
    MeasurableSet {C : Fin n → ℝ | isLowest (Function.update C i c) i} := by
  have hset : {C : Fin n → ℝ | isLowest (Function.update C i c) i} = univ.pi (sL c i) := by
    ext C; exact isLowest_update_iff C i c
  rw [hset]; exact MeasurableSet.univ_pi (sL_meas c i)

open Classical in
theorem X1opt (E : Env Ω) (hS : E.Standing) (i : Fin E.n) {c : ℝ}
    (hc : c ∈ Icc E.clo E.chi) :
    E.optMech.X1 E i c = if c ≤ E.cStar1 then E.H c else 0 := by
  unfold Mech.X1 Env.optMech
  simp only [Function.update_self]
  by_cases hc1 : c ≤ E.cStar1
  · simp only [hc1, true_and, if_true]
    have : (fun C : Fin E.n → ℝ => if isLowest (Function.update C i c) i then (1 : ℝ) else 0) =
        {C | isLowest (Function.update C i c) i}.indicator 1 := by
      funext C; simp [Set.indicator]
    rw [this, integral_indicator_one (lowest_meas i c), prob_lowest E hS i hc]
  · simp [hc1]

theorem contSet_meas (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (s : ℝ) :
    MeasurableSet (E.contSet s) :=
  measurableSet_le (hS.2.2.2.2.2.2.2.2.2.2.2.2.1 s) (kc2_meas E hS hA)

open Classical in
theorem X2opt (E : Env Ω) (hS : E.Standing) (i : Fin E.n) {c : ℝ}
    (hc : c ∈ Icc E.clo E.chi) (ω : Ω) :
    E.optMech.X2 E i c ω = if c ≤ E.cStar1 ∧ ω ∈ E.contSet c then E.H c else 0 := by
  unfold Mech.X2 Env.optMech
  simp only [Function.update_self]
  by_cases hc1 : c ≤ E.cStar1 ∧ ω ∈ E.contSet c
  · have hk : E.k c ω ≤ E.k (E.cStar2 ω) ω := hc1.2
    simp only [hc1.1, hk, hc.1, true_and, and_true, if_true, hc1]
    have : (fun C : Fin E.n → ℝ => if isLowest (Function.update C i c) i then (1 : ℝ) else 0) =
        {C | isLowest (Function.update C i c) i}.indicator 1 := by
      funext C; simp [Set.indicator]
    rw [this, integral_indicator_one (lowest_meas i c), prob_lowest E hS i hc]
  · rw [if_neg hc1]
    have : ∀ C : Fin E.n → ℝ, ¬ (c ≤ E.cStar1 ∧ isLowest (Function.update C i c) i ∧
        E.clo ≤ c ∧ E.k c ω ≤ E.k (E.cStar2 ω) ω) := by
      rintro C ⟨h1, _, _, h4⟩; exact hc1 ⟨h1, h4⟩
    simp [this]

theorem Topt (E : Env Ω) (hS : E.Standing) (i : Fin E.n) (c : ℝ) :
    E.optMech.T E i c = E.optTransfer c := by
  have := profile_prob E hS
  unfold Mech.T Env.optMech
  simp

theorem contSet_anti (E : Env Ω) (hS : E.Standing) {s t : ℝ} (hs : s ∈ Icc E.clo E.chi)
    (ht : t ∈ Icc E.clo E.chi) (hst : s ≤ t) : E.contSet t ⊆ E.contSet s := by
  intro ω hω
  have hmono := (hS.2.2.2.2.2.2.2.2.2.1 ω).monotoneOn hs ht hst
  exact le_trans hmono hω

theorem ae_Ico_of_sub (E : Env Ω) {a b : ℝ} (ha : E.clo ≤ a) (hb : b ≤ E.chi) :
    ∀ᵐ s ∂(volume.restrict (Ioc a b)), s ∈ Ico E.clo E.chi := by
  have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hne] with x hx hxI
  exact ⟨ha.trans hxI.1.le, lt_of_le_of_ne (hxI.2.trans hb) hx⟩

theorem ae_Ico_Icc (E : Env Ω) :
    ∀ᵐ s ∂(volume.restrict (Icc E.clo E.chi)), s ∈ Ico E.clo E.chi := by
  have hne : ∀ᵐ x : ℝ, x ≠ E.chi := by rw [ae_iff]; simp
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hne] with x hx hxI
  exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩

theorem KS (E : Env Ω) (hS : E.Standing) {a b : ℝ} (ha : a ∈ Icc E.clo E.chi)
    (hb : b ∈ Icc E.clo E.chi) (hab : a ≤ b) {S : Set Ω} :
    ∫ s in a..b, (∫ ω in S, E.kc s ω ∂E.G) = ∫ ω in S, (E.k b ω - E.k a ω) ∂E.G := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hS' := hS
  obtain ⟨_, _, _, hlt, _, _, _, _, _, _, hkd, hkcb, _, _, _⟩ := hS'
  rw [intervalIntegral.integral_of_le hab]
  have hae1 := ae_Ico_of_sub E ha.1 hb.2
  have hae : ∀ᵐ p ∂((volume.restrict (Ioc a b)).prod (E.G.restrict S)),
      p.1 ∈ Ico E.clo E.chi := Measure.quasiMeasurePreserving_fst.ae hae1
  have hint : Integrable (fun p : ℝ × Ω => E.kc p.1 p.2)
      ((volume.restrict (Ioc a b)).prod (E.G.restrict S)) := by
    refine bdd_int (kc_aesm E hS _ (φ := fun p : ℝ × Ω => p) measurable_id hae) E.K ?_
    filter_upwards [hae] with p hp
    have h := hkcb p.2 p.1 (Ico_subset_Icc_self hp)
    rw [abs_of_nonneg h.1]; exact h.2
  rw [integral_integral_swap (f := fun s ω => E.kc s ω) hint]
  congr 1; funext ω
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · intro x hx
    exact ((hkd ω x ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩).continuousWithinAt).mono
      (Icc_subset_Icc ha.1 hb.2)
  · intro x hx
    exact ((hkd ω x ⟨ha.1.trans hx.1.le, hx.2.le.trans hb.2⟩).hasDerivAt
      (Icc_mem_nhds (lt_of_le_of_lt ha.1 hx.1) (lt_of_lt_of_le hx.2 hb.2))).hasDerivWithinAt
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      (kc_aesm E hS (volume.restrict (Ioc a b)) (φ := fun s => (s, ω))
        (measurable_id.prodMk measurable_const) hae1) E.K ?_
    filter_upwards [hae1] with s hs
    have h := hkcb ω s (Ico_subset_Icc_self hs)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2

/-- `s ↦ ∫_{S} k_c(s, ω) dG` for a fixed set `S`. -/
theorem fixedS_aesm (E : Env Ω) (hS : E.Standing) (S : Set Ω) :
    AEStronglyMeasurable (fun s => ∫ ω in S, E.kc s ω ∂E.G)
      (volume.restrict (Icc E.clo E.chi)) := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  refine AEStronglyMeasurable.integral_prod_right' (f := fun p : ℝ × Ω => E.kc p.1 p.2) ?_
  exact kc_aesm E hS _ (φ := fun p : ℝ × Ω => p) measurable_id
    (Measure.quasiMeasurePreserving_fst.ae (ae_Ico_Icc E))

theorem cont_aesm (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    AEStronglyMeasurable (fun s => ∫ ω in E.contSet s, E.kc s ω ∂E.G)
      (volume.restrict (Icc E.clo E.chi)) := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hcm := contSet_meas E hS hA
  have heq : (fun s => ∫ ω in E.contSet s, E.kc s ω ∂E.G) =
      fun s => ∫ ω, (E.contSet s).indicator (fun ω => E.kc s ω) ω ∂E.G := by
    funext s; rw [integral_indicator (hcm s)]
  rw [heq]
  refine AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Ω => (E.contSet p.1).indicator (fun ω => E.kc p.1 ω) p.2) ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Icc E.clo E.chi)).prod E.G), p.1 ∈ Ico E.clo E.chi :=
    Measure.quasiMeasurePreserving_fst.ae (ae_Ico_Icc E)
  have hset : MeasurableSet {p : ℝ × Ω |
      E.k (max E.clo (min p.1 E.chi)) p.2 ≤ E.k (E.cStar2 p.2) p.2} :=
    measurableSet_le (k_clamp_meas E hS) ((kc2_meas E hS hA).comp measurable_snd)
  refine ((kc_aesm E hS _ (φ := fun p : ℝ × Ω => p) measurable_id hae).indicator hset).congr ?_
  filter_upwards [hae] with p hp
  simp only [Set.indicator, Env.contSet, mem_setOf_eq, clamp_eq E (Ico_subset_Icc_self hp)]

theorem H_contOn (E : Env Ω) (hS : E.Standing) : ContinuousOn E.H (Icc E.clo E.chi) := by
  unfold Env.H
  exact (continuousOn_const.sub (F_contOn E hS)).pow _

theorem kc_int (E : Env Ω) (hS : E.Standing) {s : ℝ} (hs : s ∈ Icc E.clo E.chi) :
    Integrable (fun ω => E.kc s ω) E.G := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  refine bdd_int (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 s).aestronglyMeasurable E.K
    (ae_of_all _ fun ω => ?_)
  have h := hS.2.2.2.2.2.2.2.2.2.2.2.1 ω s hs
  rw [abs_of_nonneg h.1]; exact h.2

theorem setkc_bounds (E : Env Ω) (hS : E.Standing) {s : ℝ} (hs : s ∈ Icc E.clo E.chi)
    (S : Set Ω) : 0 ≤ ∫ ω in S, E.kc s ω ∂E.G ∧ ∫ ω in S, E.kc s ω ∂E.G ≤ E.K := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hkcb := hS.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · exact integral_nonneg fun ω => (hkcb ω s hs).1
  · have h1 : ∫ ω in S, E.kc s ω ∂E.G ≤ ∫ ω in S, E.K ∂E.G :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => (hkcb ω s hs).1) (integrable_const _)
        (ae_of_all _ fun ω => (hkcb ω s hs).2)
    have hK0 : 0 ≤ E.K := (hkcb (Classical.choice (nonempty_of_isProbabilityMeasure E.G)) s
      hs).1.trans (hkcb (Classical.choice (nonempty_of_isProbabilityMeasure E.G)) s hs).2
    have h2 : ∫ ω in S, E.K ∂E.G ≤ E.K := by
      rw [setIntegral_const, smul_eq_mul]
      have : E.G.real S ≤ 1 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
      nlinarith [measureReal_nonneg (μ := E.G) (s := S)]
    linarith

theorem h_intOn (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    IntegrableOn (fun s => E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
      (Icc E.clo E.chi) := by
  have hQ := hS.2.1
  refine IntegrableOn.of_bound measure_Icc_lt_top
    (((H_contOn E hS).aestronglyMeasurable measurableSet_Icc).mul
      (aestronglyMeasurable_const.add (aestronglyMeasurable_const.mul (cont_aesm E hS hA))))
    (1 + E.Q * E.K) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine ae_of_all _ fun s hs => ?_
  obtain ⟨h0, h1⟩ := H_bounds E hS hs
  obtain ⟨g0, g1⟩ := setkc_bounds E hS hs (E.contSet s)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity)]
  calc E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) ≤ 1 * (1 + E.Q * E.K) :=
        mul_le_mul h1 (by nlinarith) (by positivity) zero_le_one
    _ = _ := one_mul _

theorem fixed_intOn (E : Env Ω) (hS : E.Standing) (S : Set Ω) :
    IntegrableOn (fun s => ∫ ω in S, E.kc s ω ∂E.G) (Icc E.clo E.chi) := by
  refine IntegrableOn.of_bound measure_Icc_lt_top (fixedS_aesm E hS S) E.K ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine ae_of_all _ fun s hs => ?_
  obtain ⟨g0, g1⟩ := setkc_bounds E hS hs S
  rw [Real.norm_eq_abs, abs_of_nonneg g0]; exact g1

theorem sub_uIcc (E : Env Ω) {a b : ℝ} (ha : a ∈ Icc E.clo E.chi) (hb : b ∈ Icc E.clo E.chi) :
    uIcc a b ⊆ Icc E.clo E.chi := by
  intro x hx
  rcases le_total a b with h | h
  · rw [uIcc_of_le h] at hx; exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  · rw [uIcc_of_ge h] at hx; exact ⟨hb.1.trans hx.1, hx.2.trans ha.2⟩

theorem lower (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) {a b : ℝ}
    (ha : a ∈ Icc E.clo E.chi) (hb : b ∈ Icc E.clo E.chi) (hab : a ≤ b) :
    E.H b * ((b - a) + E.Q * ∫ ω in E.contSet b, (E.k b ω - E.k a ω) ∂E.G) ≤
      ∫ s in a..b, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) := by
  have hQ := hS.2.1
  have hkcb := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← KS E hS ha hb hab]
  have hI : IntervalIntegrable (fun s => ∫ ω in E.contSet b, E.kc s ω ∂E.G) volume a b :=
    ((fixed_intOn E hS (E.contSet b)).mono_set (sub_uIcc E ha hb)).intervalIntegrable
  have hh : IntervalIntegrable (fun s => E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
      volume a b := ((h_intOn E hS hA).mono_set (sub_uIcc E ha hb)).intervalIntegrable
  have heq : E.H b * ((b - a) + E.Q * ∫ s in a..b, ∫ ω in E.contSet b, E.kc s ω ∂E.G) =
      ∫ s in a..b, E.H b * (1 + E.Q * ∫ ω in E.contSet b, E.kc s ω ∂E.G) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      (hI.const_mul _), intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    simp
  rw [heq]
  apply intervalIntegral.integral_mono_on hab ((intervalIntegrable_const.add (hI.const_mul E.Q)).const_mul _) hh
  intro s hs
  have hsI : s ∈ Icc E.clo E.chi := ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hH := H_anti E hS hsI hb hs.2
  have hI1 : ∫ ω in E.contSet b, E.kc s ω ∂E.G ≤ ∫ ω in E.contSet s, E.kc s ω ∂E.G :=
    setIntegral_mono_set (kc_int E hS hsI).integrableOn
      (ae_of_all _ fun ω => (hkcb ω s hsI).1)
      (contSet_anti E hS hsI hb hs.2).eventuallyLE
  have hI0 := (setkc_bounds E hS hsI (E.contSet b)).1
  have hHb0 := (H_bounds E hS hb).1
  have hHs0 := (H_bounds E hS hsI).1
  exact mul_le_mul hH (by nlinarith) (by positivity) hHs0

theorem upper (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) {a b : ℝ}
    (ha : a ∈ Icc E.clo E.chi) (hb : b ∈ Icc E.clo E.chi) (hab : a ≤ b) :
    ∫ s in a..b, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) ≤
      E.H a * ((b - a) + E.Q * ∫ ω in E.contSet a, (E.k b ω - E.k a ω) ∂E.G) := by
  have hQ := hS.2.1
  have hkcb := hS.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← KS E hS ha hb hab]
  have hI : IntervalIntegrable (fun s => ∫ ω in E.contSet a, E.kc s ω ∂E.G) volume a b :=
    ((fixed_intOn E hS (E.contSet a)).mono_set (sub_uIcc E ha hb)).intervalIntegrable
  have hh : IntervalIntegrable (fun s => E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
      volume a b := ((h_intOn E hS hA).mono_set (sub_uIcc E ha hb)).intervalIntegrable
  have heq : E.H a * ((b - a) + E.Q * ∫ s in a..b, ∫ ω in E.contSet a, E.kc s ω ∂E.G) =
      ∫ s in a..b, E.H a * (1 + E.Q * ∫ ω in E.contSet a, E.kc s ω ∂E.G) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add intervalIntegrable_const
      (hI.const_mul _), intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    simp
  rw [heq]
  apply intervalIntegral.integral_mono_on hab hh ((intervalIntegrable_const.add (hI.const_mul E.Q)).const_mul _)
  intro s hs
  have hsI : s ∈ Icc E.clo E.chi := ⟨ha.1.trans hs.1, hs.2.trans hb.2⟩
  have hH := H_anti E hS ha hsI hs.1
  have hI1 : ∫ ω in E.contSet s, E.kc s ω ∂E.G ≤ ∫ ω in E.contSet a, E.kc s ω ∂E.G :=
    setIntegral_mono_set (kc_int E hS hsI).integrableOn
      (ae_of_all _ fun ω => (hkcb ω s hsI).1)
      (contSet_anti E hS ha hsI hs.1).eventuallyLE
  have hI0 := (setkc_bounds E hS hsI (E.contSet s)).1
  have hHa0 := (H_bounds E hS ha).1
  have hHs0 := (H_bounds E hS hsI).1
  exact mul_le_mul hH (by nlinarith) (by positivity) hHa0

theorem k_int (E : Env Ω) (hS : E.Standing) {s : ℝ} (hs : s ∈ Icc E.clo E.chi) :
    Integrable (fun ω => E.k s ω) E.G := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  obtain ⟨Mk, hMk⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact bdd_int (hS.2.2.2.2.2.2.2.2.2.2.2.2.1 s).aestronglyMeasurable Mk
    (ae_of_all _ fun ω => hMk s hs ω)

open Classical in
theorem Uopt (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (i : Fin E.n) {c c' : ℝ}
    (hc : c ∈ Icc E.clo E.chi) (hc' : c' ∈ Icc E.clo E.chi) :
    E.optMech.U E i c c' = if c' ≤ E.cStar1 then
      E.H c' * (c' - c) + E.H c' * (E.Q * ∫ ω in E.contSet c', (E.k c' ω - E.k c ω) ∂E.G) +
        ∫ s in c'..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)
      else 0 := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  unfold Mech.U
  rw [Topt E hS, X1opt E hS i hc']
  simp_rw [X2opt E hS i hc']
  by_cases h1 : c' ≤ E.cStar1
  · simp only [h1, true_and, if_true]
    have hX : ∫ ω, E.Q * E.k c ω * (if ω ∈ E.contSet c' then E.H c' else 0) ∂E.G =
        E.H c' * ∫ ω in E.contSet c', E.Q * E.k c ω ∂E.G := by
      rw [← integral_const_mul, ← integral_indicator (contSet_meas E hS hA c')]
      congr 1; funext ω
      by_cases hω : ω ∈ E.contSet c'
      · simp [hω]; ring
      · simp [hω]
    rw [hX]
    unfold Env.optTransfer
    rw [if_pos h1]
    have hsub : ∫ ω in E.contSet c', (E.k c' ω - E.k c ω) ∂E.G =
        (∫ ω in E.contSet c', E.k c' ω ∂E.G) - ∫ ω in E.contSet c', E.k c ω ∂E.G :=
      integral_sub (k_int E hS hc').integrableOn (k_int E hS hc).integrableOn
    rw [hsub, integral_const_mul, integral_const_mul]
    ring
  · simp only [h1, false_and, if_false]
    unfold Env.optTransfer
    rw [if_neg h1]
    simp

theorem W_nonneg (E : Env Ω) (hS : E.Standing) {c : ℝ} (hc : c ∈ Icc E.clo E.chi)
    (hc1 : c ≤ E.cStar1) :
    0 ≤ ∫ s in c..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) := by
  have hQ := hS.2.1
  have hc1I := cStar1_mem E hS.2.2.2.1
  apply intervalIntegral.integral_nonneg hc1
  intro s hs
  have hsI : s ∈ Icc E.clo E.chi := ⟨hc.1.trans hs.1, hs.2.trans hc1I.2⟩
  have := (H_bounds E hS hsI).1
  have := (setkc_bounds E hS hsI (E.contSet s)).1
  positivity

theorem W_diff (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) {a b : ℝ}
    (ha : a ∈ Icc E.clo E.chi) (hb : b ∈ Icc E.clo E.chi) :
    (∫ s in a..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)) -
      (∫ s in b..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)) =
      ∫ s in a..b, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) := by
  have hc1I := cStar1_mem E hS.2.2.2.1
  have h1 := ((h_intOn E hS hA).mono_set (sub_uIcc E ha hb)).intervalIntegrable
  have h2 := ((h_intOn E hS hA).mono_set (sub_uIcc E hb hc1I)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

theorem optIC (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) : E.optMech.IsIC E := by
  intro i c hc c' hc'
  have hQ := hS.2.1
  have hc1I := cStar1_mem E hS.2.2.2.1
  have hkmono := hS.2.2.2.2.2.2.2.2.2.1
  rw [Uopt E hS hA i hc hc', Uopt E hS hA i hc hc]
  have hneg : ∀ {x y : ℝ}, x ∈ Icc E.clo E.chi → y ∈ Icc E.clo E.chi →
      ∫ ω in E.contSet c', (E.k x ω - E.k y ω) ∂E.G =
        -∫ ω in E.contSet c', (E.k y ω - E.k x ω) ∂E.G := by
    intro x y _ _
    rw [← integral_neg]; congr 1; funext ω; ring
  by_cases h1 : c ≤ E.cStar1
  · rw [if_pos h1]
    simp only [sub_self, mul_zero, integral_zero, zero_add]
    by_cases h2 : c' ≤ E.cStar1
    · rw [if_pos h2]
      rcases le_total c c' with h3 | h3
      · have hl := lower E hS hA hc hc' h3
        have hw := W_diff E hS hA hc hc'
        nlinarith
      · have hu := upper E hS hA hc' hc h3
        have hw := W_diff E hS hA hc' hc
        rw [hneg hc' hc] at *
        nlinarith
    · rw [if_neg h2]
      exact W_nonneg E hS hc h1
  · rw [if_neg h1]
    by_cases h2 : c' ≤ E.cStar1
    · rw [if_pos h2]
      push Not at h1
      have hu := upper E hS hA hc' hc1I h2
      have hH0 := (H_bounds E hS hc').1
      have hmono : ∫ ω in E.contSet c', (E.k E.cStar1 ω - E.k c' ω) ∂E.G ≤
          ∫ ω in E.contSet c', (E.k c ω - E.k c' ω) ∂E.G := by
        apply setIntegral_mono_on ((k_int E hS hc1I).sub (k_int E hS hc')).integrableOn
          ((k_int E hS hc).sub (k_int E hS hc')).integrableOn (contSet_meas E hS hA c')
        intro ω _
        have : E.k E.cStar1 ω ≤ E.k c ω := (hkmono ω).monotoneOn hc1I hc h1.le
        show E.k E.cStar1 ω - E.k c' ω ≤ E.k c ω - E.k c' ω
        linarith
      rw [hneg hc' hc]
      have : E.H c' * ((E.cStar1 - c') + E.Q * ∫ ω in E.contSet c', (E.k E.cStar1 ω - E.k c' ω) ∂E.G)
          ≤ E.H c' * ((c - c') + E.Q * ∫ ω in E.contSet c', (E.k c ω - E.k c' ω) ∂E.G) := by
        apply mul_le_mul_of_nonneg_left _ hH0
        nlinarith
      nlinarith
    · rw [if_neg h2]

theorem optIR (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) : E.optMech.IsIR E := by
  intro i c hc
  rw [Uopt E hS hA i hc hc]
  split_ifs with h1
  · simp only [sub_self, mul_zero, integral_zero, zero_add]
    exact W_nonneg E hS hc h1
  · exact le_rfl

theorem isLowest_meas {n : ℕ} (i : Fin n) : MeasurableSet {C : Fin n → ℝ | isLowest C i} := by
  have hset : {C : Fin n → ℝ | isLowest C i} =
      (⋂ j : Fin n, {C : Fin n → ℝ | j < i → C i < C j}) ∩
        ⋂ j : Fin n, {C : Fin n → ℝ | i < j → C i ≤ C j} := by
    ext C; simp [isLowest]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_) (MeasurableSet.iInter fun j => ?_)
  · by_cases hj : j < i
    · simp only [hj, true_implies]
      exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · simp only [hj, false_implies, setOf_true, MeasurableSet.univ]
  · by_cases hj : i < j
    · simp only [hj, true_implies]
      exact measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)
    · simp only [hj, false_implies, setOf_true, MeasurableSet.univ]

theorem kA_aesm (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    AEStronglyMeasurable (fun s => ∫ ω in E.contSet s, E.Q * E.k s ω ∂E.G)
      (volume.restrict (Icc E.clo E.chi)) := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hcm := contSet_meas E hS hA
  have heq : (fun s => ∫ ω in E.contSet s, E.Q * E.k s ω ∂E.G) =
      fun s => ∫ ω, (E.contSet s).indicator (fun ω => E.Q * E.k s ω) ω ∂E.G := by
    funext s; rw [integral_indicator (hcm s)]
  rw [heq]
  refine AEStronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × Ω => (E.contSet p.1).indicator (fun ω => E.Q * E.k p.1 ω) p.2) ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Icc E.clo E.chi)).prod E.G), p.1 ∈ Ico E.clo E.chi :=
    Measure.quasiMeasurePreserving_fst.ae (ae_Ico_Icc E)
  have hset : MeasurableSet {p : ℝ × Ω |
      E.k (max E.clo (min p.1 E.chi)) p.2 ≤ E.k (E.cStar2 p.2) p.2} :=
    measurableSet_le (k_clamp_meas E hS) ((kc2_meas E hS hA).comp measurable_snd)
  have hm : Measurable (fun p : ℝ × Ω => E.Q * E.k (max E.clo (min p.1 E.chi)) p.2) :=
    measurable_const.mul (k_clamp_meas E hS)
  refine (hm.aestronglyMeasurable.indicator hset).congr ?_
  filter_upwards [hae] with p hp
  simp only [Set.indicator, Env.contSet, mem_setOf_eq, clamp_eq E (Ico_subset_Icc_self hp)]

theorem optTransfer_aesm (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    AEStronglyMeasurable E.optTransfer (volume.restrict (Icc E.clo E.chi)) := by
  have hc1I := cStar1_mem E hS.2.2.2.1
  have hlt := hS.2.2.2.1
  have hW : ContinuousOn (fun c => ∫ s in c..E.cStar1,
      E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)) (Icc E.clo E.chi) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (a := E.clo) (b := E.chi)
      (f := fun s => E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
      (by rw [uIcc_of_le hlt.le]; exact h_intOn E hS hA)
    rw [uIcc_of_le hlt.le] at h
    have hfix : ∀ c ∈ Icc E.clo E.chi, (∫ s in c..E.cStar1,
        E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)) =
        (∫ s in c..E.chi, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)) -
          ∫ s in E.cStar1..E.chi, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) := by
      intro c hc
      have h1 := ((h_intOn E hS hA).mono_set (sub_uIcc E hc hc1I)).intervalIntegrable
      have h2 := ((h_intOn E hS hA).mono_set (sub_uIcc E hc1I
        ⟨hlt.le, le_rfl⟩)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]; ring
    exact (h.sub continuousOn_const).congr hfix
  have hmain : AEStronglyMeasurable (fun c => E.H c * (c + ∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G)
      + ∫ s in c..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
      (volume.restrict (Icc E.clo E.chi)) :=
    (((H_contOn E hS).aestronglyMeasurable measurableSet_Icc).mul
      (aestronglyMeasurable_id.add (kA_aesm E hS hA))).add
      (hW.aestronglyMeasurable measurableSet_Icc)
  unfold Env.optTransfer
  exact (hmain.indicator (measurableSet_Iic (a := E.cStar1))).congr
    (ae_of_all _ fun c => by by_cases h : c ≤ E.cStar1 <;> simp [Set.indicator, h])

theorem setInt_bound (E : Env Ω) (hS : E.Standing) {g : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ ω, |g ω| ≤ B) (S : Set Ω) : |∫ ω in S, g ω ∂E.G| ≤ B := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have := norm_integral_le_of_norm_le_const (μ := E.G.restrict S) (C := B)
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg ω)
  rw [Real.norm_eq_abs] at this
  have h1 : (E.G.restrict S).real univ ≤ 1 := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have h0 : 0 ≤ (E.G.restrict S).real univ := measureReal_nonneg
  nlinarith

theorem optTransfer_bound (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    ∃ BT, ∀ c ∈ Icc E.clo E.chi, |E.optTransfer c| ≤ BT := by
  have hQ := hS.2.1
  have hlt := hS.2.2.2.1
  have hc1I := cStar1_mem E hlt
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hkcb := hS.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Mk, hMk⟩ := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hK0 : 0 ≤ E.K := (hkcb (Classical.choice (nonempty_of_isProbabilityMeasure E.G)) E.clo
      ⟨le_rfl, hlt.le⟩).1.trans (hkcb (Classical.choice (nonempty_of_isProbabilityMeasure E.G))
        E.clo ⟨le_rfl, hlt.le⟩).2
  have hMk0 : 0 ≤ Mk := (abs_nonneg _).trans (hMk E.clo ⟨le_rfl, hlt.le⟩
    (Classical.choice (nonempty_of_isProbabilityMeasure E.G)))
  refine ⟨(|E.clo| + |E.chi| + E.Q * Mk) + (E.chi - E.clo) * (1 + E.Q * E.K), fun c hc => ?_⟩
  unfold Env.optTransfer
  split_ifs with h1
  · obtain ⟨H0, H1⟩ := H_bounds E hS hc
    have hA1 : |∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G| ≤ E.Q * Mk :=
      setInt_bound E hS (by positivity) (fun ω => by
        rw [abs_mul, abs_of_pos hQ]; exact mul_le_mul_of_nonneg_left (hMk c hc ω) hQ.le) _
    have hcabs : |c| ≤ |E.clo| + |E.chi| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le E.clo, le_abs_self E.chi, abs_nonneg E.clo,
        abs_nonneg E.chi, hc.1, hc.2]
    have hP1 : |E.H c * (c + ∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G)| ≤
        |E.clo| + |E.chi| + E.Q * Mk := by
      rw [abs_mul, abs_of_nonneg H0]
      calc E.H c * |c + ∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G|
          ≤ 1 * (|c| + |∫ ω in E.contSet c, E.Q * E.k c ω ∂E.G|) :=
            mul_le_mul H1 (abs_add_le _ _) (abs_nonneg _) zero_le_one
        _ ≤ _ := by linarith
    have hP2 : |∫ s in c..E.cStar1, E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G)| ≤
        (E.chi - E.clo) * (1 + E.Q * E.K) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := c) (b := E.cStar1)
        (C := 1 + E.Q * E.K)
        (f := fun s => E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G))
        (fun s hs => by
          rw [uIoc_of_le h1] at hs
          have hsI : s ∈ Icc E.clo E.chi := ⟨hc.1.trans hs.1.le, hs.2.trans hc1I.2⟩
          obtain ⟨h0', h1'⟩ := H_bounds E hS hsI
          obtain ⟨g0, g1⟩ := setkc_bounds E hS hsI (E.contSet s)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0', abs_of_nonneg (by positivity)]
          calc E.H s * (1 + E.Q * ∫ ω in E.contSet s, E.kc s ω ∂E.G) ≤ 1 * (1 + E.Q * E.K) :=
                mul_le_mul h1' (by nlinarith) (by positivity) zero_le_one
            _ = _ := one_mul _)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h1)] at this
      have : (E.cStar1 - c) * (1 + E.Q * E.K) ≤ (E.chi - E.clo) * (1 + E.Q * E.K) :=
        mul_le_mul_of_nonneg_right (by linarith [hc1I.2, hc.1]) (by positivity)
      linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hP1 hP2
  · rw [abs_zero]
    have : 0 ≤ (E.chi - E.clo) * (1 + E.Q * E.K) :=
      mul_nonneg (by linarith) (by positivity)
    positivity

open Classical in
theorem optAdm (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    E.optMech.Admissible E := by
  have hc1I := cStar1_mem E hS.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _
    refine ⟨fun i => by simp only [Env.optMech]; split_ifs <;> norm_num, ?_⟩
    simp only [Env.optMech]
    rw [Finset.sum_boole]
    exact_mod_cast Finset.card_le_one.mpr (fun i hi j hj => by
      simp only [Finset.mem_filter] at hi hj; exact lowest_unique hi.2.2 hj.2.2)
  · intro C _ ω
    refine ⟨fun i => by simp only [Env.optMech]; split_ifs <;> norm_num, ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp only [Env.optMech]
    split_ifs with h1 h2 <;> norm_num
    exact h2 ⟨h1.1, h1.2.1⟩
  · intro i
    simp only [Env.optMech]
    exact Measurable.ite (show MeasurableSet {C : Fin E.n → ℝ | C i ≤ E.cStar1 ∧ isLowest C i} from
      (measurableSet_le (measurable_pi_apply i) measurable_const).inter (isLowest_meas i))
      measurable_const measurable_const
  · intro i
    simp only [Env.optMech]
    have hset : {p : (Fin E.n → ℝ) × Ω | p.1 i ≤ E.cStar1 ∧ isLowest p.1 i ∧ E.clo ≤ p.1 i ∧
        E.k (p.1 i) p.2 ≤ E.k (E.cStar2 p.2) p.2} =
        {p : (Fin E.n → ℝ) × Ω | p.1 i ≤ E.cStar1 ∧ isLowest p.1 i ∧ E.clo ≤ p.1 i ∧
        E.k (max E.clo (min (p.1 i) E.chi)) p.2 ≤ E.k (E.cStar2 p.2) p.2} := by
      ext p
      simp only [mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, h3, by rwa [clamp_eq E ⟨h3, h1.trans hc1I.2⟩]⟩
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, h3, by rwa [clamp_eq E ⟨h3, h1.trans hc1I.2⟩] at h4⟩
    have hm : MeasurableSet {p : (Fin E.n → ℝ) × Ω | p.1 i ≤ E.cStar1 ∧ isLowest p.1 i ∧
        E.clo ≤ p.1 i ∧ E.k (max E.clo (min (p.1 i) E.chi)) p.2 ≤ E.k (E.cStar2 p.2) p.2} := by
      have hp1 : Measurable (fun p : (Fin E.n → ℝ) × Ω => p.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      have hk1 : Measurable (fun p : (Fin E.n → ℝ) × Ω =>
          E.k (max E.clo (min (p.1 i) E.chi)) p.2) := by
        have := (k_clamp_meas E hS).comp (hp1.prodMk measurable_snd)
        exact this
      have hk2 : Measurable (fun p : (Fin E.n → ℝ) × Ω => E.k (E.cStar2 p.2) p.2) := by
        have hsnd : Measurable (fun p : (Fin E.n → ℝ) × Ω => p.2) := measurable_snd
        have := (kc2_meas E hS hA).comp hsnd
        exact this
      exact (measurableSet_le hp1 measurable_const).inter
        (((isLowest_meas i).preimage measurable_fst).inter
        ((measurableSet_le measurable_const hp1).inter (measurableSet_le hk1 hk2)))
    exact Measurable.ite (hset ▸ hm) measurable_const measurable_const
  · intro i
    obtain ⟨BT, hBT⟩ := optTransfer_bound E hS hA
    have hν := nu_prob E hS
    have hpl := profileLaw_eq E hS
    have := profile_prob E hS
    simp only [Env.optMech]
    have hae : ∀ᵐ C ∂E.profileLaw, C i ∈ Ico E.clo E.chi := by
      rw [hpl]; exact ae_pi_Ico E hS i
    refine bdd_int ?_ BT (hae.mono fun C hC => hBT (C i) (Ico_subset_Icc_self hC))
    rw [hpl]
    exact ((optTransfer_aesm E hS hA).mono_ac
      (show nu E ≪ volume.restrict (Icc E.clo E.chi) from withDensity_absolutelyContinuous _ _)
      ).comp_measurePreserving (measurePreserving_eval (μ := fun _ : Fin E.n => nu E) i)

theorem psi2max_int (E : Env Ω) (hS : E.Standing) {c : ℝ} (hc : c ∈ Icc E.clo E.chi) :
    Integrable (fun ω => E.Q * max 0 (E.R - E.Psi2 c ω)) E.G := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hQ := hS.2.1
  have hR := hS.2.2.1
  obtain ⟨P2, hP2⟩ := Psi2_bound E hS
  have hm : Measurable (fun ω => E.Psi2 c ω) := by
    unfold Env.Psi2
    exact (hS.2.2.2.2.2.2.2.2.2.2.2.2.1 c).add
      (measurable_const.mul (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 c))
  refine bdd_int (measurable_const.mul (measurable_const.max
    (measurable_const.sub hm))).aestronglyMeasurable (E.Q * (E.R + P2)) (ae_of_all _ fun ω => ?_)
  have hp := hP2 c hc ω
  rw [abs_mul, abs_of_pos hQ, abs_of_nonneg (le_max_left _ _)]
  apply mul_le_mul_of_nonneg_left _ hQ.le
  apply max_le (by linarith [abs_nonneg (E.Psi2 c ω)])
  linarith [neg_abs_le (E.Psi2 c ω)]

theorem g_sign (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) {c : ℝ}
    (hc : c ∈ Icc E.clo E.chi) :
    (c < E.cStar1 → 0 ≤ E.R - E.Psi1 c + ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G) ∧
    (E.cStar1 < c → E.R - E.Psi1 c + ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G < 0) := by
  have hlt := hS.2.2.2.1
  have hQ := hS.2.1
  set S1 := insert E.clo {c ∈ Icc E.clo E.chi |
      E.Psi1 c ≤ E.R + ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G} with hS1
  have hbdd : BddAbove S1 := by
    refine ⟨E.chi, ?_⟩
    rintro y (rfl | ⟨hy, _⟩)
    · exact hlt.le
    · exact hy.2
  have hc1 : E.cStar1 = sSup S1 := rfl
  constructor
  · intro h
    obtain ⟨y, hyS, hcy⟩ := exists_lt_of_lt_csSup (⟨_, mem_insert _ _⟩ : S1.Nonempty) (hc1 ▸ h)
    rcases hyS with rfl | ⟨hyI, hyR⟩
    · exact absurd hc.1 (not_le.mpr hcy)
    · have h1 : E.Psi1 c ≤ E.Psi1 y := hA.1 hc hyI hcy.le
      have h2 : ∫ ω, E.Q * max 0 (E.R - E.Psi2 y ω) ∂E.G ≤
          ∫ ω, E.Q * max 0 (E.R - E.Psi2 c ω) ∂E.G := by
        apply integral_mono (psi2max_int E hS hyI) (psi2max_int E hS hc)
        intro ω
        have := hA.2 ω hc hyI hcy.le
        exact mul_le_mul_of_nonneg_left (max_le_max le_rfl (by linarith)) hQ.le
      linarith
  · intro h
    by_contra hcon
    push Not at hcon
    have : c ∈ S1 := Or.inr ⟨hc, by linarith⟩
    exact absurd (le_csSup hbdd this) (not_le.mpr h)

theorem lowest_le {n : ℕ} {C : Fin n → ℝ} {j : Fin n} (hj : isLowest C j) (i : Fin n) :
    C j ≤ C i := by
  rcases lt_trichotomy i j with h | h | h
  · exact (hj.1 i h).le
  · rw [h]
  · exact hj.2 i h

theorem x2sec_meas {n : ℕ} (M : Mech n Ω) (hm : ∀ i, Measurable fun p : (Fin n → ℝ) × Ω => M.x2 p.1 p.2 i)
    (C : Fin n → ℝ) (i : Fin n) : Measurable (fun ω => M.x2 C ω i) :=
  (hm i).comp (measurable_const.prodMk measurable_id)

theorem c2_facts (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) {c : ℝ}
    (hc : c ∈ Icc E.clo E.chi) (ω : Ω) :
    (c < E.cStar2 ω → E.Psi2 c ω ≤ E.R) ∧ (E.cStar2 ω < c → E.R < E.Psi2 c ω) := by
  have hlt := hS.2.2.2.1
  have hbdd := cStar2_bdd E hlt ω
  have hc2 : E.cStar2 ω = sSup (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}) := rfl
  constructor
  · intro h
    obtain ⟨y, hyS, hcy⟩ := exists_lt_of_lt_csSup (⟨_, mem_insert _ _⟩ :
      (insert E.clo {c ∈ Icc E.clo E.chi | E.Psi2 c ω ≤ E.R}).Nonempty) (hc2 ▸ h)
    rcases hyS with rfl | ⟨hyI, hyR⟩
    · exact absurd hc.1 (not_le.mpr hcy)
    · exact le_trans (hA.2 ω hc hyI hcy.le) hyR
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (le_csSup hbdd (Or.inr ⟨hc, hcon⟩)) (not_le.mpr h)

open Classical in
theorem pt_bound (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (M : Mech E.n Ω)
    (hM : M.Admissible E) {C : Fin E.n → ℝ} (hC : C ∈ E.cube)
    (hc1 : ∀ i, C i ≠ E.cStar1) (hc2 : ∀ i, ∀ᵐ ω ∂E.G, E.cStar2 ω ≠ C i) :
    ∑ i, (M.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ≤
      ∑ i, (E.optMech.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * E.optMech.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) := by
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have hQ := hS.2.1
  have hR := hS.2.2.1
  have hkmono := hS.2.2.2.2.2.2.2.2.2.1
  obtain ⟨P2, hP2⟩ := Psi2_bound E hS
  obtain ⟨j, hj⟩ := exists_lowest hS.1 C
  have hcI : C j ∈ Icc E.clo E.chi := hC j (mem_univ _)
  have hlow := lowest_le hj
  have hc2I : ∀ ω, E.cStar2 ω ∈ Icc E.clo E.chi := cStar2_mem E hS.2.2.2.1
  -- the optimal side
  have hopt : ∑ i, (E.optMech.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * E.optMech.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) =
      max 0 (E.R - E.Psi1 (C j) + ∫ ω, E.Q * max 0 (E.R - E.Psi2 (C j) ω) ∂E.G) := by
    rw [Finset.sum_eq_single j]
    · simp only [Env.optMech]
      by_cases h1 : C j ≤ E.cStar1
      · have hlt1 : C j < E.cStar1 := lt_of_le_of_ne h1 (hc1 j)
        rw [max_eq_right ((g_sign E hS hA hcI).1 hlt1)]
        rw [if_pos ⟨h1, hj⟩, one_mul]
        congr 1
        apply integral_congr_ae
        filter_upwards [hc2 j] with ω hω
        rcases lt_or_gt_of_ne hω with h | h
        · have hk : ¬ E.k (C j) ω ≤ E.k (E.cStar2 ω) ω :=
            not_le.mpr (hkmono ω (hc2I ω) hcI h)
          have hP := (c2_facts E hS hA hcI ω).2 h
          rw [if_neg (fun hh => hk hh.2.2.2), max_eq_left (by linarith)]
          ring
        · have hk : E.k (C j) ω ≤ E.k (E.cStar2 ω) ω :=
            (hkmono ω).monotoneOn hcI (hc2I ω) h.le
          have hP := (c2_facts E hS hA hcI ω).1 h
          rw [if_pos ⟨h1, hj, hcI.1, hk⟩, max_eq_right (by linarith)]
          ring
      · have h1' : E.cStar1 < C j := lt_of_not_ge h1
        rw [max_eq_left ((g_sign E hS hA hcI).2 h1').le]
        rw [if_neg (fun hh => h1 hh.1)]
        have : ∀ ω, (if C j ≤ E.cStar1 ∧ isLowest C j ∧ E.clo ≤ C j ∧
            E.k (C j) ω ≤ E.k (E.cStar2 ω) ω then (1 : ℝ) else 0) = 0 :=
          fun ω => if_neg (fun hh => h1 hh.1)
        simp [this]
    · intro i _ hij
      have hnl : ¬ isLowest C i := fun hi => hij (lowest_unique hi hj)
      simp only [Env.optMech]
      rw [if_neg (fun hh => hnl hh.2)]
      have : ∀ ω, (if C i ≤ E.cStar1 ∧ isLowest C i ∧ E.clo ≤ C i ∧
          E.k (C i) ω ≤ E.k (E.cStar2 ω) ω then (1 : ℝ) else 0) = 0 :=
        fun ω => if_neg (fun hh => hnl hh.2.1)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- the mechanism side
  have hs := hM.1 C hC
  have hsx0 : 0 ≤ ∑ i, M.x1 C i := Finset.sum_nonneg (fun i _ => hs.1 i)
  have hM1 : ∑ i, M.x1 C i * (E.R - E.Psi1 (C i)) ≤ (∑ i, M.x1 C i) * (E.R - E.Psi1 (C j)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (by linarith [hA.1 hcI (hC i (mem_univ _)) (hlow i)])
      (hs.1 i)
  have hint_i : ∀ i, Integrable (fun ω => E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω)) E.G := by
    intro i
    have hm : Measurable (fun ω => E.Psi2 (C i) ω) := by
      unfold Env.Psi2
      exact (hS.2.2.2.2.2.2.2.2.2.2.2.2.1 _).add
        (measurable_const.mul (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _))
    refine bdd_int ((measurable_const.mul (x2sec_meas M hM.2.2.2.1 C i)).mul
      (measurable_const.sub hm)).aestronglyMeasurable (E.Q * (E.R + P2))
      (ae_of_all _ fun ω => ?_)
    have hb := cube_b2 E M hM i hC ω
    have hp := hP2 (C i) (hC i (mem_univ _)) ω
    have : |E.R - E.Psi2 (C i) ω| ≤ E.R + P2 := by
      calc |E.R - E.Psi2 (C i) ω| ≤ |E.R| + |E.Psi2 (C i) ω| := abs_sub _ _
        _ ≤ E.R + P2 := by rw [abs_of_pos hR]; linarith
    rw [abs_mul, abs_mul, abs_of_pos hQ, abs_of_nonneg hb.1]
    calc E.Q * M.x2 C ω i * |E.R - E.Psi2 (C i) ω| ≤ E.Q * 1 * (E.R + P2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hb.2 hQ.le) this (abs_nonneg _) (by linarith)
      _ = E.Q * (E.R + P2) := by ring
  have hM2 : ∑ i, ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G ≤
      (∑ i, M.x1 C i) * ∫ ω, E.Q * max 0 (E.R - E.Psi2 (C j) ω) ∂E.G := by
    rw [← integral_finset_sum _ (fun i _ => hint_i i), ← integral_const_mul]
    apply integral_mono (integrable_finsetSum _ (fun i _ => hint_i i))
      ((psi2max_int E hS hcI).const_mul _)
    intro ω
    have h2 := hM.2.1 C hC ω
    have hmx : 0 ≤ E.Q * max 0 (E.R - E.Psi2 (C j) ω) :=
      mul_nonneg hQ.le (le_max_left _ _)
    calc ∑ i, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω)
        ≤ ∑ i, M.x2 C ω i * (E.Q * max 0 (E.R - E.Psi2 (C j) ω)) := by
          apply Finset.sum_le_sum
          intro i _
          have hmono2 : E.Psi2 (C j) ω ≤ E.Psi2 (C i) ω := hA.2 ω hcI (hC i (mem_univ _)) (hlow i)
          have : E.R - E.Psi2 (C i) ω ≤ max 0 (E.R - E.Psi2 (C j) ω) :=
            le_trans (show E.R - E.Psi2 (C i) ω ≤ E.R - E.Psi2 (C j) ω by linarith)
              (le_max_right _ _)
          have hx := h2.1 i
          calc E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω)
              ≤ E.Q * M.x2 C ω i * max 0 (E.R - E.Psi2 (C j) ω) :=
                mul_le_mul_of_nonneg_left this (mul_nonneg hQ.le hx)
            _ = M.x2 C ω i * (E.Q * max 0 (E.R - E.Psi2 (C j) ω)) := by ring
      _ = (∑ i, M.x2 C ω i) * (E.Q * max 0 (E.R - E.Psi2 (C j) ω)) := by rw [Finset.sum_mul]
      _ ≤ (∑ i, M.x1 C i) * (E.Q * max 0 (E.R - E.Psi2 (C j) ω)) :=
          mul_le_mul_of_nonneg_right h2.2 hmx
  rw [hopt, Finset.sum_add_distrib]
  set g := E.R - E.Psi1 (C j) + ∫ ω, E.Q * max 0 (E.R - E.Psi2 (C j) ω) ∂E.G with hg
  have hfin : (∑ i, M.x1 C i) * g ≤ max 0 g := by
    rcases le_total 0 g with h | h
    · rw [max_eq_right h]; nlinarith [hs.2]
    · rw [max_eq_left h]; nlinarith
  calc _ ≤ (∑ i, M.x1 C i) * (E.R - E.Psi1 (C j)) +
        (∑ i, M.x1 C i) * ∫ ω, E.Q * max 0 (E.R - E.Psi2 (C j) ω) ∂E.G := add_le_add hM1 hM2
    _ = (∑ i, M.x1 C i) * g := by rw [hg]; ring
    _ ≤ max 0 g := hfin

theorem hc1ae (E : Env Ω) (hS : E.Standing) :
    ∀ᵐ C ∂E.profileLaw, ∀ i, C i ≠ E.cStar1 := by
  have := nu_prob E hS
  rw [ae_all_iff]
  intro i
  have h : ∀ᵐ c ∂(nu E), c ≠ E.cStar1 := by
    rw [ae_iff]; simpa using nu_singleton E E.cStar1
  rw [profileLaw_eq E hS]
  exact (measurePreserving_eval (μ := fun _ : Fin E.n => nu E) i).quasiMeasurePreserving.ae h

theorem hc2ae (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) :
    ∀ᵐ C ∂E.profileLaw, ∀ i, ∀ᵐ ω ∂E.G, E.cStar2 ω ≠ C i := by
  have := nu_prob E hS
  have hG : IsProbabilityMeasure E.G := hS.2.2.2.2.2.2.2.2.1
  have := profile_prob E hS
  rw [ae_all_iff]
  intro i
  refine Measure.ae_ae_of_ae_prod (p := fun z : (Fin E.n → ℝ) × Ω => E.cStar2 z.2 ≠ z.1 i) ?_
  rw [ae_iff]
  have hp1 : Measurable (fun p : (Fin E.n → ℝ) × Ω => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hc2m : Measurable (fun p : (Fin E.n → ℝ) × Ω => E.cStar2 p.2) :=
    (cStar2_meas E hS hA).comp measurable_snd
  have hs : MeasurableSet {p : (Fin E.n → ℝ) × Ω | ¬ E.cStar2 p.2 ≠ p.1 i} := by
    simp only [not_not]
    exact measurableSet_eq_fun hc2m hp1
  rw [Measure.prod_apply_symm hs]
  have hz : ∀ ω, E.profileLaw ((fun C => (C, ω)) ⁻¹'
      {p : (Fin E.n → ℝ) × Ω | ¬ E.cStar2 p.2 ≠ p.1 i}) = 0 := by
    intro ω
    have hpre : ((fun C => (C, ω)) ⁻¹' {p : (Fin E.n → ℝ) × Ω | ¬ E.cStar2 p.2 ≠ p.1 i}) =
        (Function.eval i : (Fin E.n → ℝ) → ℝ) ⁻¹' ({E.cStar2 ω} : Set ℝ) := by
      ext C; simp [eq_comm]
    rw [hpre, profileLaw_eq E hS,
      (measurePreserving_eval (μ := fun _ : Fin E.n => nu E) i).measure_preimage
        (measurableSet_singleton _).nullMeasurableSet]
    exact nu_singleton E _
  rw [lintegral_congr hz, lintegral_zero]

theorem upper_bound (E : Env Ω) (hS : E.Standing) (hA : E.Assumption1) (M : Mech E.n Ω)
    (hM : M.Admissible E) (hIC : M.IsIC E) (hIR : M.IsIR E) :
    M.buyerSurplus E ≤ E.optMech.buyerSurplus E := by
  have hlt := hS.2.2.2.1
  have hc1I := cStar1_mem E hlt
  have hadm := optAdm E hS hA
  rw [virtual_surplus E hS hA M hM hIC, virtual_surplus E hS hA E.optMech hadm (optIC E hS hA)]
  have hU0 : ∀ i, E.optMech.U E i E.chi E.chi = 0 := by
    intro i
    rw [Uopt E hS hA i ⟨hlt.le, le_rfl⟩ ⟨hlt.le, le_rfl⟩]
    split_ifs with h
    · have : E.cStar1 = E.chi := le_antisymm hc1I.2 h
      rw [this]; simp
    · rfl
  have hUM : 0 ≤ ∑ i, M.U E i E.chi E.chi :=
    Finset.sum_nonneg (fun i _ => hIR i E.chi ⟨hlt.le, le_rfl⟩)
  simp only [hU0, Finset.sum_const_zero, sub_zero]
  have hV : (∫ C, ∑ i, (M.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * M.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ∂E.profileLaw) ≤
      ∫ C, ∑ i, (E.optMech.x1 C i * (E.R - E.Psi1 (C i)) +
        ∫ ω, E.Q * E.optMech.x2 C ω i * (E.R - E.Psi2 (C i) ω) ∂E.G) ∂E.profileLaw := by
    apply integral_mono_ae (integrable_finsetSum _ (fun i _ => int_b E hS M hM i))
      (integrable_finsetSum _ (fun i _ => int_b E hS E.optMech hadm i))
    filter_upwards [ae_cube E, hc1ae E hS, hc2ae E hS hA] with C hC h1 h2
    exact pt_bound E hS hA M hM hC h1 h2
  linarith

end IncProcP1Aux

open IncompleteProc.English IncProcP1Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    E.optMech.Admissible E ∧ E.optMech.IsIC E ∧ E.optMech.IsIR E ∧
      IsGreatest E.feasibleSurplus (E.optMech.buyerSurplus E) := by
  refine ⟨optAdm E hS hA, optIC E hS hA, optIR E hS hA,
    ⟨⟨E.optMech, optAdm E hS hA, optIC E hS hA, optIR E hS hA, rfl⟩, ?_⟩⟩
  rintro s ⟨M, hM, hIC, hIR, rfl⟩
  exact upper_bound E hS hA M hM hIC hIR
