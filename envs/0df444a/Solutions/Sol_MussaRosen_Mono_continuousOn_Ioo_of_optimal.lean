-- Prove2me | solution 1 for MussaRosen.Mono.continuousOn_Ioo_of_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:50:53.009975+00:00
-- url     : https://prove2.me/submissions/f1d944cf-a53c-4b0c-a429-ae57d51017c3

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology


namespace MussaRosen.Mono

theorem aux_int_comp {a b : ℝ} (hab : a ≤ b) {q : ℝ → ℝ} (hq : MonotoneOn q (Set.Icc a b))
    {K : ℝ → ℝ} (hK : Continuous K) : IntervalIntegrable (fun θ => K (q θ)) MeasureTheory.volume a b := by
  have hq' : IntervalIntegrable q MeasureTheory.volume a b :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hab])
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => K (q θ))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hK.comp_aestronglyMeasurable hq'.1.aestronglyMeasurable
  have hcomp : IsCompact (Set.Icc (q a) (q b)) := isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hK.continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ⟨hmeas, MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := M) (by simp) ?_⟩
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun θ hθ => ?_)
  have h1 : q a ≤ q θ := hq ⟨le_rfl, hab⟩ ⟨hθ.1.le, hθ.2⟩ hθ.1.le
  have h2 : q θ ≤ q b := hq ⟨hθ.1.le, hθ.2⟩ ⟨hab, le_rfl⟩ hθ.2
  exact hM _ ⟨h1, h2⟩

theorem aux_Fc_hasDeriv {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) {x : ℝ} (hx : x ∈ Set.Ioo θlo θhi) :
    HasDerivAt (fun u => ∫ s in θlo..u, D.f s) (D.f x) x := by
  have hc : ContinuousOn D.f (Set.Icc θlo θhi) := hfd.continuousOn
  apply intervalIntegral.integral_hasDerivAt_right
  · exact D.f_integrable.mono_set (by
      rw [Set.uIcc_of_le hx.1.le, Set.uIcc_of_le D.lo_lt_hi.le]
      exact Set.Icc_subset_Icc le_rfl hx.2.le)
  · exact (hc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  · exact hc.continuousAt (Icc_mem_nhds hx.1 hx.2)

theorem aux_Fc_cont {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) :
    ContinuousOn (fun u => ∫ s in θlo..u, D.f s) (Set.Icc θlo θhi) := by
  have := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
    (a := θlo) (b₁ := θlo) (b₂ := θhi) (f := D.f) D.f_integrable Set.left_mem_uIcc
  rwa [Set.uIcc_of_le D.lo_lt_hi.le] at this

theorem mu_eq_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ∀ t ∈ Set.Icc θlo θhi,
      mu D C q t = ∫ θ in t..θhi, (virtualValuation D θ - deriv C (q θ)) * D.f θ := by
  intro t ht
  have hle : θlo ≤ θhi := D.lo_lt_hi.le
  have hsub : Set.uIcc t θhi ⊆ Set.Icc θlo θhi := by
    rw [Set.uIcc_of_le ht.2]; exact Set.Icc_subset_Icc ht.1 le_rfl
  have hsub' : Set.uIcc t θhi ⊆ Set.uIcc θlo θhi := by
    rw [Set.uIcc_of_le hle]; exact hsub
  have hfc : ContinuousOn D.f (Set.Icc θlo θhi) := hfd.continuousOn
  have hgi : IntervalIntegrable (fun θ => deriv C (q θ)) MeasureTheory.volume t θhi :=
    (aux_int_comp hle hq.1 hCd2.continuous).mono_set hsub'
  have hFc := aux_Fc_cont D
  have key : ∫ θ in t..θhi, ((θ - t) * D.f θ - (1 - ∫ s in θlo..θ, D.f s)) = 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := t) (b := θhi)
      (f := fun θ => -(θ - t) * (1 - ∫ s in θlo..θ, D.f s))
      (f' := fun θ => (θ - t) * D.f θ - (1 - ∫ s in θlo..θ, D.f s)) ht.2
      (by
        apply ContinuousOn.mul
        · exact (continuousOn_id.sub continuousOn_const).neg
        · exact continuousOn_const.sub (hFc.mono (Set.Icc_subset_Icc ht.1 le_rfl)))
      (by
        intro x hx
        have hx' : x ∈ Set.Ioo θlo θhi := ⟨ht.1.trans_lt hx.1, hx.2⟩
        have h1 := aux_Fc_hasDeriv D hfd hx'
        have h2 : HasDerivAt (fun θ : ℝ => -(θ - t)) (-1) x :=
          ((hasDerivAt_id x).sub_const t).neg
        have h3 := h2.mul ((hasDerivAt_const x (1:ℝ)).sub h1)
        refine h3.congr_deriv ?_
        simp only [Pi.sub_apply]
        ring)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le ht.2]
        apply ContinuousOn.sub
        · exact (continuousOn_id.sub continuousOn_const).mul (hfc.mono (Set.Icc_subset_Icc ht.1 le_rfl))
        · exact continuousOn_const.sub (hFc.mono (Set.Icc_subset_Icc ht.1 le_rfl)))
    rw [this]
    have hF1 : (∫ s in θlo..θhi, D.f s) = 1 := D.f_total
    simp [hF1]
  unfold mu
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have hint1 : IntervalIntegrable (fun θ => (θ - (θ - t) - deriv C (q θ)) * D.f θ)
      MeasureTheory.volume t θhi := by
    have : IntervalIntegrable (fun θ => (θ - (θ - t) - deriv C (q θ))) MeasureTheory.volume t θhi :=
      (intervalIntegral.intervalIntegrable_id.sub (intervalIntegral.intervalIntegrable_id.sub
        intervalIntegrable_const)).sub hgi
    exact this.mul_continuousOn (hfc.mono hsub)
  have hint2 : IntervalIntegrable (fun θ => (θ - t) * D.f θ - (1 - ∫ s in θlo..θ, D.f s))
      MeasureTheory.volume t θhi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht.2]
    apply ContinuousOn.sub
    · exact (continuousOn_id.sub continuousOn_const).mul (hfc.mono (Set.Icc_subset_Icc ht.1 le_rfl))
    · exact continuousOn_const.sub (hFc.mono (Set.Icc_subset_Icc ht.1 le_rfl))
  have hcongr : ∫ θ in t..θhi, (virtualValuation D θ - deriv C (q θ)) * D.f θ =
      ∫ θ in t..θhi, ((θ - (θ - t) - deriv C (q θ)) * D.f θ +
        ((θ - t) * D.f θ - (1 - ∫ s in θlo..θ, D.f s))) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' := hsub hθ
    have hfθ := (D.f_pos θ hθ').ne'
    simp only [virtualValuation]
    rw [D.F_eq θ hθ']
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_add hint1 hint2, key, add_zero]

theorem aux_sub_uIcc {θlo θhi θ : ℝ} (hθ : θ ∈ Set.Icc θlo θhi) :
    Set.uIcc θlo θ ⊆ Set.uIcc θlo θhi := by
  rw [Set.uIcc_of_le hθ.1, Set.uIcc_of_le (hθ.1.trans hθ.2)]
  exact Set.Icc_subset_Icc le_rfl hθ.2

theorem aux_surplus_cont {θlo θhi : ℝ} (hle : θlo ≤ θhi) {r : ℝ → ℝ}
    (hr : IntervalIntegrable r MeasureTheory.volume θlo θhi) :
    ContinuousOn (fun θ => ∫ s in θlo..θ, r s) (Set.Icc θlo θhi) := by
  have := intervalIntegral.continuousOn_primitive_interval' (μ := MeasureTheory.volume)
    hr (Set.left_mem_uIcc : θlo ∈ Set.uIcc θlo θhi)
  rwa [Set.uIcc_of_le hle] at this

theorem aux_lin_int {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) {r : ℝ → ℝ}
    (hr : IntervalIntegrable r MeasureTheory.volume θlo θhi) :
    IntervalIntegrable (fun θ => (θ * r θ - ∫ s in θlo..θ, r s) * D.f θ)
      MeasureTheory.volume θlo θhi := by
  have hle := D.lo_lt_hi.le
  have h1 : IntervalIntegrable (fun θ => θ * r θ) MeasureTheory.volume θlo θhi :=
    hr.continuousOn_mul (g := fun θ : ℝ => θ) continuousOn_id
  have h2 : IntervalIntegrable (fun θ => ∫ s in θlo..θ, r s) MeasureTheory.volume θlo θhi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]; exact aux_surplus_cont hle hr
  exact (h1.sub h2).mul_continuousOn (by rw [Set.uIcc_of_le hle]; exact hfd.continuousOn)

theorem aux_cst_int {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) {C : ℝ → ℝ} (hC : Continuous C) {r : ℝ → ℝ}
    (hr : MonotoneOn r (Set.Icc θlo θhi)) :
    IntervalIntegrable (fun θ => C (r θ) * D.f θ) MeasureTheory.volume θlo θhi := by
  have hle := D.lo_lt_hi.le
  exact (aux_int_comp hle hr hC).mul_continuousOn (by rw [Set.uIcc_of_le hle]; exact hfd.continuousOn)

theorem aux_profit_split {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) {C : ℝ → ℝ} (hC : Continuous C) {r : ℝ → ℝ}
    (hr : MonotoneOn r (Set.Icc θlo θhi)) :
    profit D C r = (∫ θ in θlo..θhi, (θ * r θ - ∫ s in θlo..θ, r s) * D.f θ) -
      ∫ θ in θlo..θhi, C (r θ) * D.f θ := by
  have hle := D.lo_lt_hi.le
  have hri : IntervalIntegrable r MeasureTheory.volume θlo θhi :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hle])
  rw [← intervalIntegral.integral_sub (aux_lin_int D hfd hri) (aux_cst_int D hfd hC hr)]
  unfold profit surplus
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

theorem aux_dir {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q h : ℝ → ℝ) (M : ℝ)
    (hqm : MonotoneOn q (Set.Icc θlo θhi))
    (hum : MonotoneOn (fun θ => q θ + h θ) (Set.Icc θlo θhi))
    (hq0 : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ ∧ q θ ≤ M)
    (hu0 : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ + h θ ∧ q θ + h θ ≤ M) :
    Tendsto (fun t : ℝ => (profit D C (fun θ => q θ + t * h θ) - profit D C q) / t)
      (𝓝[>] 0) (𝓝 (firstVariation D C q h)) := by
  have hle := D.lo_lt_hi.le
  have hfc : ContinuousOn D.f (Set.Icc θlo θhi) := hfd.continuousOn
  have hfc' : ContinuousOn D.f (Set.uIcc θlo θhi) := by rw [Set.uIcc_of_le hle]; exact hfc
  have hC : Continuous C := hCd.continuous
  have hqi : IntervalIntegrable q MeasureTheory.volume θlo θhi :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hle])
  have hui : IntervalIntegrable (fun θ => q θ + h θ) MeasureTheory.volume θlo θhi :=
    MonotoneOn.intervalIntegrable (by rwa [Set.uIcc_of_le hle])
  have hhi : IntervalIntegrable h MeasureTheory.volume θlo θhi := by
    have := hui.sub hqi
    simpa using this
  -- monotonicity of the deformation
  have hmono : ∀ t ∈ Set.Icc (0:ℝ) 1, MonotoneOn (fun θ => q θ + t * h θ) (Set.Icc θlo θhi) := by
    intro t ht x hx y hy hxy
    have h1 := hqm hx hy hxy
    have h2 := hum hx hy hxy
    simp only at h2 ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h1), mul_nonneg ht.1 (sub_nonneg.2 h2)]
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ θ ∈ Set.Icc θlo θhi, q θ + t * h θ ∈ Set.Icc (0:ℝ) M := by
    intro t ht θ hθ
    obtain ⟨a1, a2⟩ := hq0 θ hθ
    obtain ⟨b1, b2⟩ := hu0 θ hθ
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 ht.2) a1, mul_nonneg ht.1 b1,
      mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 a2), mul_nonneg ht.1 (sub_nonneg.2 b2)]
  have hhb : ∀ θ ∈ Set.Icc θlo θhi, |h θ| ≤ M := by
    intro θ hθ
    obtain ⟨a1, a2⟩ := hq0 θ hθ
    obtain ⟨b1, b2⟩ := hu0 θ hθ
    rw [abs_le]; constructor <;> linarith
  -- the cost-derivative bound
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M)).exists_bound_of_continuousOn
    hCd2.continuous.continuousOn
  -- Step 1: identity for difference quotients
  have hlin_h := aux_lin_int D hfd hhi
  have hident : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      (profit D C (fun θ => q θ + t * h θ) - profit D C q) / t =
      (∫ θ in θlo..θhi, (θ * h θ - ∫ s in θlo..θ, h s) * D.f θ) -
        ∫ θ in θlo..θhi, t⁻¹ * (C (q θ + t * h θ) - C (q θ)) * D.f θ := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htne : t ≠ 0 := ht.1.ne'
    have hmt := hmono t ht'
    rw [aux_profit_split D hfd hC hmt, aux_profit_split D hfd hC hqm]
    have hlin : ∫ θ in θlo..θhi, (θ * (q θ + t * h θ) - ∫ s in θlo..θ, (q s + t * h s)) * D.f θ =
        (∫ θ in θlo..θhi, (θ * q θ - ∫ s in θlo..θ, q s) * D.f θ) +
          t * ∫ θ in θlo..θhi, (θ * h θ - ∫ s in θlo..θ, h s) * D.f θ := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (aux_lin_int D hfd hqi) (hlin_h.const_mul t)]
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc θlo θhi := by
        rw [Set.uIcc_of_le hle] at hθ; exact hθ
      have hsub := aux_sub_uIcc hθ'
      simp only
      rw [intervalIntegral.integral_add (hqi.mono_set hsub) ((hhi.mono_set hsub).const_mul t),
        intervalIntegral.integral_const_mul]
      ring
    have hcst_int := aux_cst_int D hfd hC hmt
    have hcst0 := aux_cst_int D hfd hC hqm
    have : ∫ θ in θlo..θhi, t⁻¹ * (C (q θ + t * h θ) - C (q θ)) * D.f θ =
        t⁻¹ * ((∫ θ in θlo..θhi, C (q θ + t * h θ) * D.f θ) - ∫ θ in θlo..θhi, C (q θ) * D.f θ) := by
      rw [← intervalIntegral.integral_sub hcst_int hcst0, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only
      ring
    rw [this, hlin]
    field_simp
    ring
  have hKnn : 0 ≤ K := by
    have := hK 0 ⟨le_rfl, by
      have := (hq0 θlo ⟨le_rfl, hle⟩); linarith [this.1, this.2]⟩
    exact (norm_nonneg _).trans this
  have hmeas : ∀ r : ℝ → ℝ, IntervalIntegrable r MeasureTheory.volume θlo θhi →
      MeasureTheory.AEStronglyMeasurable r
        (MeasureTheory.volume.restrict (Set.uIoc θlo θhi)) := by
    intro r hr; rw [Set.uIoc_of_le hle]; exact hr.1.aestronglyMeasurable
  have hdq : IntervalIntegrable (fun θ => deriv C (q θ)) MeasureTheory.volume θlo θhi :=
    aux_int_comp hle hqm hCd2.continuous
  have hint3 : IntervalIntegrable (fun θ => deriv C (q θ) * h θ * D.f θ)
      MeasureTheory.volume θlo θhi := by
    refine IntervalIntegrable.mono_fun' (g := fun θ => K * M * D.f θ)
      (D.f_integrable.const_mul _) ?_ ?_
    · exact ((hmeas _ hdq).mul (hmeas _ hhi)).mul (hmeas _ D.f_integrable)
    · rw [Set.uIoc_of_le hle]
      rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hθ' : θ ∈ Set.Icc θlo θhi := ⟨hθ.1.le, hθ.2⟩
      have hf0 := (D.f_pos θ hθ').le
      have h1 : ‖deriv C (q θ)‖ ≤ K := hK _ ⟨(hq0 θ hθ').1, (hq0 θ hθ').2⟩
      have h2 := hhb θ hθ'
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hf0] at h1 ⊢
      have h3 : |deriv C (q θ)| * |h θ| ≤ K * M :=
        mul_le_mul h1 h2 (abs_nonneg _) hKnn
      exact mul_le_mul_of_nonneg_right h3 hf0
  have hfv : firstVariation D C q h = (∫ θ in θlo..θhi, (θ * h θ - ∫ s in θlo..θ, h s) * D.f θ) -
      ∫ θ in θlo..θhi, deriv C (q θ) * h θ * D.f θ := by
    unfold firstVariation
    rw [← intervalIntegral.integral_sub hlin_h hint3]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    ring
  have hlim : Tendsto (fun t : ℝ => ∫ θ in θlo..θhi, t⁻¹ * (C (q θ + t * h θ) - C (q θ)) * D.f θ)
      (𝓝[>] 0) (𝓝 (∫ θ in θlo..θhi, deriv C (q θ) * h θ * D.f θ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => K * M * D.f θ) ?_ ?_ (D.f_integrable.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      have h1 := ((aux_int_comp hle (hmono t ht') hC).sub (aux_int_comp hle hqm hC)).const_mul t⁻¹
      have h2 := h1.mul_continuousOn hfc'
      exact hmeas _ h2
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      rw [Set.uIoc_of_le hle] at hθ
      have hθ' : θ ∈ Set.Icc θlo θhi := ⟨hθ.1.le, hθ.2⟩
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
      have hf0 := (D.f_pos θ hθ').le
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := C) (C := K)
        (s := Set.Icc (0:ℝ) M) (x := q θ) (y := q θ + t * h θ)
        (fun x _ => hCd.differentiableAt) (fun x hx => hK x hx) (convex_Icc _ _)
        ⟨(hq0 θ hθ').1, (hq0 θ hθ').2⟩ (hbd t ht' θ hθ')
      have hh := hhb θ hθ'
      have : ‖q θ + t * h θ - q θ‖ = t * |h θ| := by
        rw [Real.norm_eq_abs, add_sub_cancel_left, abs_mul, abs_of_pos ht.1]
      rw [this] at hmv
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hf0, abs_inv, abs_of_pos ht.1]
      rw [Real.norm_eq_abs] at hmv
      calc t⁻¹ * |C (q θ + t * h θ) - C (q θ)| * D.f θ
          ≤ t⁻¹ * (K * (t * |h θ|)) * D.f θ := by
            apply mul_le_mul_of_nonneg_right _ hf0
            exact mul_le_mul_of_nonneg_left hmv (inv_nonneg.2 ht.1.le)
        _ = K * |h θ| * D.f θ := by
            have htne : t ≠ 0 := ht.1.ne'
            field_simp
        _ ≤ K * M * D.f θ := by
            apply mul_le_mul_of_nonneg_right _ hf0
            exact mul_le_mul_of_nonneg_left hh hKnn
    · refine Filter.Eventually.of_forall (fun θ _ => ?_)
      have hin : HasDerivAt (fun t : ℝ => q θ + t * h θ) (h θ) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).mul_const (h θ)).const_add (q θ)
      have hC' : HasDerivAt C (deriv C (q θ)) (q θ + 0 * h θ) := by
        simpa using (hCd (q θ)).hasDerivAt
      have hcomp := hC'.comp (0:ℝ) hin
      have hs := hasDerivAt_iff_tendsto_slope_zero.1 hcomp
      have hs' : Tendsto (fun t : ℝ => t⁻¹ * (C (q θ + t * h θ) - C (q θ))) (𝓝[>] 0)
          (𝓝 (deriv C (q θ) * h θ)) := by
        have := hs.mono_left (nhdsWithin_mono (0:ℝ) (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => ne_of_gt hx))
        refine this.congr (fun t => ?_)
        simp
      exact hs'.mul_const (D.f θ)
  have hres := (tendsto_const_nhds (x := ∫ θ in θlo..θhi, (θ * h θ - ∫ s in θlo..θ, h s) * D.f θ)).sub hlim
  rw [← hfv] at hres
  refine hres.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  exact (hident t ht).symm

theorem aux_adm_convex {θlo θhi : ℝ} {q u : ℝ → ℝ} (hq : IsAdmissible θlo θhi q)
    (hu : IsAdmissible θlo θhi u) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    IsAdmissible θlo θhi (fun θ => (1 - t) * q θ + t * u θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 := hq.1 hx hy hxy
    have h2 := hu.1 hx hy hxy
    simp only
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) (sub_nonneg.2 h1), mul_nonneg ht.1 (sub_nonneg.2 h2)]
  · intro θ hθ
    have h1 := hq.2.1 θ hθ
    have h2 := hu.2.1 θ hθ
    simp only
    nlinarith [mul_nonneg (sub_nonneg.2 ht.2) h1, mul_nonneg ht.1 h2]
  · obtain ⟨s1, hs1⟩ := hq.2.2
    obtain ⟨s2, hs2⟩ := hu.2.2
    refine ⟨s1 ∪ s2, fun θ hθ hθs => ?_⟩
    rw [Finset.mem_union, not_or] at hθs
    exact ((hs1 θ hθ hθs.1).const_mul (1 - t)).add ((hs2 θ hθ hθs.2).const_mul t)

theorem firstVariation_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (h : ℝ → ℝ) (hh : IsAdmissible θlo θhi (q + h)) :
    firstVariation D C q h ≤ 0 := by
  have hle := D.lo_lt_hi.le
  have hhi' : θhi ∈ Set.Icc θlo θhi := ⟨hle, le_rfl⟩
  have hqa := hq.1
  have hua : IsAdmissible θlo θhi (fun θ => q θ + h θ) := hh
  set M := max (q θhi) (q θhi + h θhi) with hM
  have hlim := aux_dir D hfd C hCd hCd2 q h M hqa.1 hua.1
    (fun θ hθ => ⟨hqa.2.1 θ hθ, (hqa.1 hθ hhi' hθ.2).trans (le_max_left _ _)⟩)
    (fun θ hθ => ⟨hua.2.1 θ hθ, (hua.1 hθ hhi' hθ.2).trans (le_max_right _ _)⟩)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hadm := aux_adm_convex hqa hua ht'
  have hfun : (fun θ => (1 - t) * q θ + t * (q θ + h θ)) = fun θ => q θ + t * h θ := by
    funext θ; ring
  rw [hfun] at hadm
  have := hq.2 _ hadm
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) ht.1.le

theorem aux_step {a b t : ℝ} (g : ℝ → ℝ) (hab : a ≤ b) (hat : a ≤ t) :
    ∫ x in a..b, (if t < x then g x else 0) = if t ≤ b then ∫ x in t..b, g x else 0 := by
  have h1 : ∀ x, (if t < x then g x else 0) = Set.indicator (Set.Ioi t) g x := by
    intro x; simp [Set.indicator_apply]
  simp_rw [h1]
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  split_ifs with hb
  · rw [intervalIntegral.integral_of_le hb]
    have : Set.Ioc a b ∩ Set.Ioi t = Set.Ioc t b := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩; exact ⟨⟨hat.trans_lt h3, h2⟩, h3⟩
    rw [this]
  · have : Set.Ioc a b ∩ Set.Ioi t = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro ⟨_, h2⟩ h3; exact hb (h3.le.trans h2)
    rw [this]; simp

theorem aux_adm_step {θlo θhi : ℝ} {q : ℝ → ℝ} (hq : IsAdmissible θlo θhi q) (t : ℝ) :
    IsAdmissible θlo θhi (q + fun θ => if t < θ then (1:ℝ) else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 := hq.1 hx hy hxy
    simp only [Pi.add_apply]
    have : (if t < x then (1:ℝ) else 0) ≤ (if t < y then 1 else 0) := by
      by_cases hx' : t < x
      · simp [hx', hx'.trans_le hxy]
      · simp only [hx', if_false]; split_ifs <;> norm_num
    linarith
  · intro θ hθ
    have h1 := hq.2.1 θ hθ
    simp only [Pi.add_apply]
    split_ifs <;> linarith
  · obtain ⟨s, hs⟩ := hq.2.2
    refine ⟨insert t s, fun θ hθ hθs => ?_⟩
    rw [Finset.mem_insert, not_or] at hθs
    have hq' := hs θ hθ hθs.2
    have hh : DifferentiableAt ℝ (fun θ : ℝ => if t < θ then (1:ℝ) else 0) θ := by
      rcases lt_or_gt_of_ne hθs.1 with h | h
      · have : (fun θ : ℝ => if t < θ then (1:ℝ) else 0) =ᶠ[𝓝 θ] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds h] with x hx
          simp [not_lt.2 (le_of_lt (Set.mem_Iio.1 hx))]
        exact (differentiableAt_const _).congr_of_eventuallyEq this
      · have : (fun θ : ℝ => if t < θ then (1:ℝ) else 0) =ᶠ[𝓝 θ] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds h] with x hx
          simp [Set.mem_Ioi.1 hx]
        exact (differentiableAt_const _).congr_of_eventuallyEq this
    exact hq'.add hh

theorem mu_nonpos_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ t ∈ Set.Icc θlo θhi, mu D C q t ≤ 0 := by
  intro t ht
  have hle := D.lo_lt_hi.le
  have hv := firstVariation_core D hfd C hCd hCd2 q hq _ (aux_adm_step hq.1 t)
  have hfv : firstVariation D C q (fun θ => if t < θ then (1:ℝ) else 0) = mu D C q t := by
    unfold firstVariation mu
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
    have hpt : ∀ θ ∈ Set.uIcc θlo θhi,
        (θ * (if t < θ then (1:ℝ) else 0) - (∫ s in θlo..θ, (if t < s then (1:ℝ) else 0)) -
          deriv C (q θ) * (if t < θ then (1:ℝ) else 0)) * D.f θ =
        if t < θ then (θ - (θ - t) - deriv C (q θ)) * D.f θ else 0 := by
      intro θ hθ
      rw [Set.uIcc_of_le hle] at hθ
      have := aux_step (fun _ => (1:ℝ)) hθ.1 ht.1 (b := θ) (t := t)
      rw [this]
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
      by_cases h1 : t < θ
      · simp [h1, h1.le]
      · have : θ ≤ t := not_lt.1 h1
        by_cases h2 : t ≤ θ
        · have : θ = t := le_antisymm ‹θ ≤ t› h2
          subst this; simp
        · simp [h1, h2]
    rw [intervalIntegral.integral_congr hpt]
    rw [aux_step (fun θ => (θ - (θ - t) - deriv C (q θ)) * D.f θ) hle ht.1]
    rw [if_pos ht.2]
  rw [hfv] at hv
  exact hv

theorem aux_step2 {a b t : ℝ} (g : ℝ → ℝ) (hat : a ≤ t) (htb : t ≤ b) :
    ∫ x in a..b, (if x < t then g x else 0) = ∫ x in a..t, g x := by
  have h1 : ∀ x, (if x < t then g x else 0) = Set.indicator (Set.Iio t) g x := by
    intro x; simp [Set.indicator_apply]
  simp_rw [h1]
  rw [intervalIntegral.integral_of_le (hat.trans htb), MeasureTheory.setIntegral_indicator measurableSet_Iio,
    intervalIntegral.integral_of_le hat]
  have : Set.Ioc a b ∩ Set.Iio t = Set.Ioo a t := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3.le.trans htb⟩, h3⟩
  rw [this, MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem aux_fub1 {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) {h : ℝ → ℝ} (hhm : Measurable h)
    {B : ℝ} (hB : ∀ s, |h s| ≤ B) :
    ∫ θ in θlo..θhi, (∫ s in θlo..θ, h s) * D.f θ =
      ∫ s in θlo..θhi, h s * (1 - ∫ r in θlo..s, D.f r) := by
  have hle := D.lo_lt_hi.le
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc θlo θhi) with hμ
  have hfi : MeasureTheory.Integrable D.f μ := D.f_integrable.1
  have hint : MeasureTheory.Integrable
      (Function.uncurry fun θ s => (if s < θ then h s else 0) * D.f θ) (μ.prod μ) := by
    refine MeasureTheory.Integrable.mono' (g := fun z : ℝ × ℝ => ‖D.f z.1‖ * B)
      (hfi.norm.mul_prod (MeasureTheory.integrable_const B)) ?_ ?_
    · have h1 : Measurable fun z : ℝ × ℝ => if z.2 < z.1 then h z.2 else 0 :=
        Measurable.ite (measurableSet_lt measurable_snd measurable_fst) (hhm.comp measurable_snd)
          measurable_const
      exact h1.aestronglyMeasurable.mul (hfi.1.comp_fst)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      split_ifs
      · exact hB _
      · simp only [norm_zero]; exact (abs_nonneg _).trans (hB 0)
  have e1 : ∫ θ in θlo..θhi, (∫ s in θlo..θ, h s) * D.f θ =
      ∫ θ, ∫ s, (if s < θ then h s else 0) * D.f θ ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hle]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ
    simp only
    rw [MeasureTheory.integral_mul_const]
    congr 1
    have := aux_step2 h (a := θlo) (b := θhi) (t := θ) hθ.1.le hθ.2
    rw [← this, intervalIntegral.integral_of_le hle]
  rw [e1, MeasureTheory.integral_integral_swap hint, intervalIntegral.integral_of_le hle]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  simp only
  have e2 : ∀ θ : ℝ, (if s < θ then h s else 0) * D.f θ = h s * (if s < θ then D.f θ else 0) := by
    intro θ; split_ifs <;> simp
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have h3 : ∫ θ, (if s < θ then D.f θ else 0) ∂μ = ∫ θ in s..θhi, D.f θ := by
    rw [hμ, ← intervalIntegral.integral_of_le hle, aux_step D.f hle hs.1.le, if_pos hs.2]
  rw [h3]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (D.f_integrable.mono_set (by
      rw [Set.uIcc_of_le hs.1.le, Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc le_rfl hs.2)) (D.f_integrable.mono_set (by
      rw [Set.uIcc_of_le hs.2, Set.uIcc_of_le hle]
      exact Set.Icc_subset_Icc hs.1.le le_rfl))
  rw [D.f_total] at hsplit
  linarith

theorem aux_meas_int {a b : ℝ} (hab : a ≤ b) {h : ℝ → ℝ} (hhm : Measurable h) {B : ℝ}
    (hB : ∀ s, |h s| ≤ B) : IntervalIntegrable h MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine ⟨hhm.aestronglyMeasurable, MeasureTheory.HasFiniteIntegral.restrict_of_bounded (C := B) (by simp) ?_⟩
  exact Filter.Eventually.of_forall (fun s => by simpa using hB s)

theorem aux_int3 {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) (C : ℝ → ℝ)
    (hCd2 : Differentiable ℝ (deriv C)) (q : ℝ → ℝ) (M : ℝ)
    (hqm : MonotoneOn q (Set.Icc θlo θhi))
    (hq0 : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ ∧ q θ ≤ M)
    {h : ℝ → ℝ} (hhi : IntervalIntegrable h MeasureTheory.volume θlo θhi) {B : ℝ}
    (hB : ∀ s, |h s| ≤ B) :
    IntervalIntegrable (fun θ => deriv C (q θ) * h θ * D.f θ) MeasureTheory.volume θlo θhi := by
  have hle := D.lo_lt_hi.le
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M)).exists_bound_of_continuousOn
    hCd2.continuous.continuousOn
  have hKnn : 0 ≤ K := by
    have := hK 0 ⟨le_rfl, by
      have := (hq0 θlo ⟨le_rfl, hle⟩); linarith [this.1, this.2]⟩
    exact (norm_nonneg _).trans this
  have hmeas : ∀ r : ℝ → ℝ, IntervalIntegrable r MeasureTheory.volume θlo θhi →
      MeasureTheory.AEStronglyMeasurable r
        (MeasureTheory.volume.restrict (Set.uIoc θlo θhi)) := by
    intro r hr; rw [Set.uIoc_of_le hle]; exact hr.1.aestronglyMeasurable
  have hdq : IntervalIntegrable (fun θ => deriv C (q θ)) MeasureTheory.volume θlo θhi :=
    aux_int_comp hle hqm hCd2.continuous
  refine IntervalIntegrable.mono_fun' (g := fun θ => K * B * D.f θ)
    (D.f_integrable.const_mul _) ?_ ?_
  · exact ((hmeas _ hdq).mul (hmeas _ hhi)).mul (hmeas _ D.f_integrable)
  · rw [Set.uIoc_of_le hle]
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun θ hθ => ?_)
    have hθ' : θ ∈ Set.Icc θlo θhi := ⟨hθ.1.le, hθ.2⟩
    have hf0 := (D.f_pos θ hθ').le
    have h1 : ‖deriv C (q θ)‖ ≤ K := hK _ ⟨(hq0 θ hθ').1, (hq0 θ hθ').2⟩
    have h2 := hB θ
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hf0] at h1 ⊢
    have h3 : |deriv C (q θ)| * |h θ| ≤ K * B :=
      mul_le_mul h1 h2 (abs_nonneg _) hKnn
    exact mul_le_mul_of_nonneg_right h3 hf0

theorem aux_fv_rep {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi)) (C : ℝ → ℝ)
    (hCd2 : Differentiable ℝ (deriv C)) (q : ℝ → ℝ) (M : ℝ)
    (hqm : MonotoneOn q (Set.Icc θlo θhi))
    (hq0 : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ ∧ q θ ≤ M)
    {h : ℝ → ℝ} (hhm : Measurable h) {B : ℝ} (hB : ∀ s, |h s| ≤ B) :
    firstVariation D C q h = ∫ s in θlo..θhi,
      h s * ((s - deriv C (q s)) * D.f s - (1 - ∫ r in θlo..s, D.f r)) := by
  have hle := D.lo_lt_hi.le
  have hfc : ContinuousOn D.f (Set.Icc θlo θhi) := hfd.continuousOn
  have hfc' : ContinuousOn D.f (Set.uIcc θlo θhi) := by rw [Set.uIcc_of_le hle]; exact hfc
  have hhi := aux_meas_int hle hhm hB (a := θlo) (b := θhi)
  have hi3 := aux_int3 D hfd C hCd2 q M hqm hq0 hhi hB
  have hFc := aux_surplus_cont hle (D.f_integrable)
  have hP1 : IntervalIntegrable (fun θ => θ * h θ * D.f θ) MeasureTheory.volume θlo θhi :=
    (hhi.continuousOn_mul (g := fun θ : ℝ => θ) continuousOn_id).mul_continuousOn hfc'
  have hP2 : IntervalIntegrable (fun θ => (∫ s in θlo..θ, h s) * D.f θ) MeasureTheory.volume θlo θhi := by
    have hS : IntervalIntegrable (fun θ => ∫ s in θlo..θ, h s) MeasureTheory.volume θlo θhi :=
      (aux_surplus_cont hle hhi).intervalIntegrable_of_Icc hle
    exact hS.mul_continuousOn hfc'
  have hP4 : IntervalIntegrable (fun θ => h θ * (1 - ∫ r in θlo..θ, D.f r))
      MeasureTheory.volume θlo θhi := by
    refine hhi.mul_continuousOn ?_
    rw [Set.uIcc_of_le hle]
    exact continuousOn_const.sub hFc
  unfold firstVariation
  have e1 : ∫ θ in θlo..θhi, (θ * h θ - (∫ s in θlo..θ, h s) - deriv C (q θ) * h θ) * D.f θ =
      ∫ θ in θlo..θhi, ((θ * h θ * D.f θ - (∫ s in θlo..θ, h s) * D.f θ) -
        deriv C (q θ) * h θ * D.f θ) := by
    apply intervalIntegral.integral_congr; intro θ _; simp only; ring
  have e2 : ∫ s in θlo..θhi, h s * ((s - deriv C (q s)) * D.f s - (1 - ∫ r in θlo..s, D.f r)) =
      ∫ θ in θlo..θhi, ((θ * h θ * D.f θ - deriv C (q θ) * h θ * D.f θ) -
        h θ * (1 - ∫ r in θlo..θ, D.f r)) := by
    apply intervalIntegral.integral_congr; intro θ _; simp only; ring
  rw [e1, e2, intervalIntegral.integral_sub (hP1.sub hP2) hi3,
    intervalIntegral.integral_sub hP1 hP2, intervalIntegral.integral_sub (hP1.sub hi3) hP4,
    intervalIntegral.integral_sub hP1 hi3, aux_fub1 D hhm hB]
  ring

theorem aux_layer {θlo θhi H : ℝ} (hle : θlo ≤ θhi) (hH : 0 ≤ H) {ψ m : ℝ → ℝ}
    (hψm : Monotone ψ) (hψ0 : ∀ s, 0 ≤ ψ s) (hψH : ∀ s, ψ s ≤ H)
    (hm : IntervalIntegrable m MeasureTheory.volume θlo θhi) :
    ∫ s in θlo..θhi, ψ s * m s =
      ∫ y in (0:ℝ)..H, ∫ s in θlo..θhi, (if y < ψ s then m s else 0) := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc θlo θhi) with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 H) with hν
  have e1 : ∀ s, ψ s * m s = ∫ y, (if y < ψ s then m s else 0) ∂ν := by
    intro s
    have h0 := aux_step2 (fun _ => (1:ℝ)) (a := 0) (b := H) (t := ψ s) (hψ0 s) (hψH s)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at h0
    rw [intervalIntegral.integral_of_le hH] at h0
    have h1 : ∀ y : ℝ, (if y < ψ s then m s else 0) = (if y < ψ s then (1:ℝ) else 0) * m s := by
      intro y; split_ifs <;> simp
    simp_rw [h1]
    rw [MeasureTheory.integral_mul_const]
    rw [hν, h0]
  have hint : MeasureTheory.Integrable
      (Function.uncurry fun s y => if y < ψ s then m s else 0) (μ.prod ν) := by
    have hmi : MeasureTheory.Integrable m μ := hm.1
    refine MeasureTheory.Integrable.mono' (g := fun z : ℝ × ℝ => ‖m z.1‖ * 1)
      (hmi.norm.mul_prod (MeasureTheory.integrable_const (1:ℝ))) ?_ ?_
    · have hs : MeasurableSet {z : ℝ × ℝ | z.2 < ψ z.1} :=
        measurableSet_lt measurable_snd (hψm.measurable.comp measurable_fst)
      have := (hmi.1.comp_fst (β := ℝ) (ν := ν)).indicator hs
      refine this.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp [Set.indicator_apply, Function.uncurry]
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, mul_one]
      split_ifs
      · exact le_rfl
      · simp
  have := MeasureTheory.integral_integral_swap hint
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hH]
  calc ∫ s in Set.Ioc θlo θhi, ψ s * m s
      = ∫ s, ∫ y, (if y < ψ s then m s else 0) ∂ν ∂μ := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro s _; exact e1 s
    _ = ∫ y, ∫ s, (if y < ψ s then m s else 0) ∂μ ∂ν := this
    _ = _ := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro y _
        simp only
        rw [hμ, intervalIntegral.integral_of_le hle]

noncomputable def aux_phi (qa qb x : ℝ) : ℝ := min (max x qa) qb - qa

theorem aux_phi_mono {qa qb x y : ℝ} (h : x ≤ y) : aux_phi qa qb x ≤ aux_phi qa qb y := by
  unfold aux_phi
  have := max_le_max h (le_refl qa)
  have := min_le_min this (le_refl qb)
  linarith

theorem aux_phi_lip {qa qb x y : ℝ} (h : x ≤ y) :
    aux_phi qa qb y - aux_phi qa qb x ≤ y - x := by
  unfold aux_phi
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem aux_phi_nonneg {qa qb x : ℝ} (h : qa ≤ qb) : 0 ≤ aux_phi qa qb x := by
  unfold aux_phi
  have : qa ≤ min (max x qa) qb := le_min (le_max_right _ _) h
  linarith

theorem aux_phi_le {qa qb x : ℝ} : aux_phi qa qb x ≤ qb - qa := by
  unfold aux_phi
  have : min (max x qa) qb ≤ qb := min_le_right _ _
  linarith

theorem aux_phi_of_le {qa qb x : ℝ} (h : x ≤ qa) (hab : qa ≤ qb) : aux_phi qa qb x = 0 := by
  unfold aux_phi
  have : max x qa = qa := max_eq_right h
  rw [this, min_eq_left hab]; ring

theorem aux_phi_of_ge {qa qb x : ℝ} (h : qb ≤ x) (hab : qa ≤ qb) : aux_phi qa qb x = qb - qa := by
  unfold aux_phi
  have : max x qa = x := max_eq_left (hab.trans h)
  rw [this, min_eq_right h]

theorem aux_phi_mid {qa qb x : ℝ} (h1 : qa ≤ x) (h2 : x ≤ qb) : aux_phi qa qb x = x - qa := by
  unfold aux_phi
  rw [max_eq_left h1, min_eq_left h2]

noncomputable def aux_Q (θlo θhi : ℝ) (q : ℝ → ℝ) (s : ℝ) : ℝ := q (max θlo (min s θhi))

theorem aux_Q_eq {θlo θhi : ℝ} {q : ℝ → ℝ} {s : ℝ} (hs : s ∈ Set.Icc θlo θhi) :
    aux_Q θlo θhi q s = q s := by
  unfold aux_Q
  rw [min_eq_left hs.2, max_eq_right hs.1]

theorem aux_Q_mono {θlo θhi : ℝ} (hle : θlo ≤ θhi) {q : ℝ → ℝ}
    (hq : MonotoneOn q (Set.Icc θlo θhi)) : Monotone (aux_Q θlo θhi q) := by
  intro x y hxy
  unfold aux_Q
  apply hq
  · exact ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  · exact ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  · exact max_le_max le_rfl (min_le_min hxy le_rfl)

theorem aux_phi_abs {qa qb x y : ℝ} : |aux_phi qa qb x - aux_phi qa qb y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have h1 := aux_phi_mono (qa := qa) (qb := qb) h
    have h2 := aux_phi_lip (qa := qa) (qb := qb) h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := aux_phi_mono (qa := qa) (qb := qb) h
    have h2 := aux_phi_lip (qa := qa) (qb := qb) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

theorem aux_deriv_zero_left {q : ℝ → ℝ} {d a θ : ℝ} (hd : HasDerivAt q d θ) (haθ : a < θ)
    (hc : ∀ s ∈ Set.Icc a θ, q s = q θ) : d = 0 := by
  have h1 : HasDerivWithinAt q d (Set.Icc a θ) θ := hd.hasDerivWithinAt
  have h0 : HasDerivWithinAt q 0 (Set.Icc a θ) θ :=
    (hasDerivWithinAt_const θ (Set.Icc a θ) (q θ)).congr (fun s hs => hc s hs) (hc θ ⟨haθ.le, le_rfl⟩)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc haθ θ (Set.right_mem_Icc.2 haθ.le)) h1 h0

theorem aux_deriv_zero_right {q : ℝ → ℝ} {d b θ : ℝ} (hd : HasDerivAt q d θ) (hθb : θ < b)
    (hc : ∀ s ∈ Set.Icc θ b, q s = q θ) : d = 0 := by
  have h1 : HasDerivWithinAt q d (Set.Icc θ b) θ := hd.hasDerivWithinAt
  have h0 : HasDerivWithinAt q 0 (Set.Icc θ b) θ :=
    (hasDerivWithinAt_const θ (Set.Icc θ b) (q θ)).congr (fun s hs => hc s hs) (hc θ ⟨le_rfl, hθb.le⟩)
  exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hθb θ (Set.left_mem_Icc.2 hθb.le)) h1 h0

theorem aux_psi_deriv_zero {θlo θhi : ℝ} {q : ℝ → ℝ} {qa qb θ : ℝ}
    (hθ : θ ∈ Set.Ioo θlo θhi) (hd : HasDerivAt q 0 θ) :
    HasDerivAt (fun s => aux_phi qa qb (aux_Q θlo θhi q s)) 0 θ := by
  have hlo := hasDerivAt_iff_isLittleO.1 hd
  apply hasDerivAt_iff_isLittleO.2
  have hbig : (fun x' => aux_phi qa qb (aux_Q θlo θhi q x') - aux_phi qa qb (aux_Q θlo θhi q θ) -
      (x' - θ) • (0:ℝ)) =O[𝓝 θ] (fun x' => q x' - q θ - (x' - θ) • (0:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with x' hx'
    simp only [smul_zero, sub_zero, Real.norm_eq_abs, one_mul]
    rw [aux_Q_eq ⟨hx'.1.le, hx'.2.le⟩, aux_Q_eq ⟨hθ.1.le, hθ.2.le⟩]
    exact aux_phi_abs
  exact hbig.trans_isLittleO hlo

theorem aux_psi_diff {θlo θhi : ℝ} {q : ℝ → ℝ} (hq : MonotoneOn q (Set.Icc θlo θhi))
    {a b : ℝ} (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi) {θ : ℝ} (hθ : θ ∈ Set.Ioo θlo θhi)
    (hθa : θ ≠ a) (hθb : θ ≠ b) (hd : DifferentiableAt ℝ q θ) :
    DifferentiableAt ℝ (fun s => aux_phi (q a) (q b) (aux_Q θlo θhi q s)) θ := by
  have hle : θlo ≤ θhi := ha.trans (hab.le.trans hb)
  have haI : a ∈ Set.Icc θlo θhi := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Set.Icc θlo θhi := ⟨ha.trans hab.le, hb⟩
  have hqab : q a ≤ q b := hq haI hbI hab.le
  have hθI : θ ∈ Set.Icc θlo θhi := ⟨hθ.1.le, hθ.2.le⟩
  rcases lt_or_gt_of_ne hθa with h1 | h1
  · -- θ < a
    have : (fun s => aux_phi (q a) (q b) (aux_Q θlo θhi q s)) =ᶠ[𝓝 θ] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      apply aux_phi_of_le _ hqab
      unfold aux_Q
      exact hq ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩ haI
        (max_le ha ((min_le_left _ _).trans (le_of_lt hs)))
    exact (differentiableAt_const _).congr_of_eventuallyEq this
  rcases lt_or_gt_of_ne hθb with h2 | h2
  · -- a < θ < b
    have hqθ1 : q a ≤ q θ := hq haI hθI h1.le
    have hqθ2 : q θ ≤ q b := hq hθI hbI h2.le
    rcases hqθ1.lt_or_eq with c1 | c1
    · rcases hqθ2.lt_or_eq with c2 | c2
      · have hcont := hd.continuousAt
        have : (fun s => aux_phi (q a) (q b) (aux_Q θlo θhi q s)) =ᶠ[𝓝 θ] fun s => q s - q a := by
          filter_upwards [hcont.eventually (Ioo_mem_nhds c1 c2), Ioo_mem_nhds hθ.1 hθ.2] with s hs hs'
          rw [aux_Q_eq ⟨hs'.1.le, hs'.2.le⟩]
          exact aux_phi_mid hs.1.le hs.2.le
        exact (hd.sub_const _).congr_of_eventuallyEq this
      · -- q θ = q b
        have hder : HasDerivAt q (deriv q θ) θ := hd.hasDerivAt
        have h0 : deriv q θ = 0 := by
          apply aux_deriv_zero_right hder h2 (b := b)
          intro s hs
          have := hq hθI ⟨hθ.1.le.trans hs.1, hs.2.trans hb⟩ hs.1
          have := hq ⟨hθ.1.le.trans hs.1, hs.2.trans hb⟩ hbI hs.2
          linarith
        rw [h0] at hder
        exact (aux_psi_deriv_zero (qa := q a) (qb := q b) hθ hder).differentiableAt
    · have hder : HasDerivAt q (deriv q θ) θ := hd.hasDerivAt
      have h0 : deriv q θ = 0 := by
        apply aux_deriv_zero_left hder h1 (a := a)
        intro s hs
        have := hq haI ⟨ha.trans hs.1, hs.2.trans hθ.2.le⟩ hs.1
        have := hq ⟨ha.trans hs.1, hs.2.trans hθ.2.le⟩ hθI hs.2
        linarith
      rw [h0] at hder
      exact (aux_psi_deriv_zero (qa := q a) (qb := q b) hθ hder).differentiableAt
  · -- θ > b
    have : (fun s => aux_phi (q a) (q b) (aux_Q θlo θhi q s)) =ᶠ[𝓝 θ] fun _ => q b - q a := by
      filter_upwards [Ioi_mem_nhds h2] with s hs
      apply aux_phi_of_ge _ hqab
      unfold aux_Q
      exact hq hbI ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
        (le_max_of_le_right (le_min hs.le hb))
    exact (differentiableAt_const _).congr_of_eventuallyEq this

theorem aux_adm_psi {θlo θhi : ℝ} {q : ℝ → ℝ} (hq : IsAdmissible θlo θhi q)
    {a b : ℝ} (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi) :
    IsAdmissible θlo θhi
      (q + fun s => -(aux_phi (q a) (q b) (aux_Q θlo θhi q s))) := by
  have haI : a ∈ Set.Icc θlo θhi := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Set.Icc θlo θhi := ⟨ha.trans hab.le, hb⟩
  have hqab : q a ≤ q b := hq.1 haI hbI hab.le
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have h1 := hq.1 hx hy hxy
    have h2 := aux_phi_lip (qa := q a) (qb := q b) h1
    simp only [Pi.add_apply]
    rw [aux_Q_eq hx, aux_Q_eq hy]
    linarith
  · intro θ hθ
    have h0 := hq.2.1 θ hθ
    have ha0 := hq.2.1 a haI
    simp only [Pi.add_apply]
    rw [aux_Q_eq hθ]
    rcases le_total (q θ) (q a) with c | c
    · rw [aux_phi_of_le c hqab]; linarith
    · rcases le_total (q θ) (q b) with d | d
      · rw [aux_phi_mid c d]; linarith
      · rw [aux_phi_of_ge d hqab]; linarith
  · obtain ⟨s, hs⟩ := hq.2.2
    refine ⟨insert a (insert b s), fun θ hθ hθs => ?_⟩
    simp only [Finset.mem_insert, not_or] at hθs
    have hq' := hs θ hθ hθs.2.2
    have hψ := aux_psi_diff hq.1 ha hab hb hθ hθs.1 hθs.2.1 hq'
    exact hq'.add hψ.neg

theorem aux_layer_int {θlo θhi H : ℝ} (hle : θlo ≤ θhi) (hH : 0 ≤ H) {ψ m : ℝ → ℝ}
    (hψm : Monotone ψ)
    (hm : IntervalIntegrable m MeasureTheory.volume θlo θhi) :
    IntervalIntegrable (fun y => ∫ s in θlo..θhi, (if y < ψ s then m s else 0))
      MeasureTheory.volume 0 H := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc θlo θhi) with hμ
  set ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 H) with hν
  have hint : MeasureTheory.Integrable
      (Function.uncurry fun s y => if y < ψ s then m s else 0) (μ.prod ν) := by
    have hmi : MeasureTheory.Integrable m μ := hm.1
    refine MeasureTheory.Integrable.mono' (g := fun z : ℝ × ℝ => ‖m z.1‖ * 1)
      (hmi.norm.mul_prod (MeasureTheory.integrable_const (1:ℝ))) ?_ ?_
    · have hs : MeasurableSet {z : ℝ × ℝ | z.2 < ψ z.1} :=
        measurableSet_lt measurable_snd (hψm.measurable.comp measurable_fst)
      have := (hmi.1.comp_fst (β := ℝ) (ν := ν)).indicator hs
      refine this.congr (Filter.Eventually.of_forall (fun z => ?_))
      simp [Set.indicator_apply, Function.uncurry]
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, mul_one]
      split_ifs
      · exact le_rfl
      · simp
  have h2 := hint.integral_prod_right
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hH]
  refine h2.congr (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  rw [hμ, intervalIntegral.integral_of_le hle]
  rfl

theorem aux_upset {θlo θhi H : ℝ} (hle : θlo ≤ θhi) {m ψ : ℝ → ℝ} (hψm : Monotone ψ)
    {a b : ℝ} (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi)
    (hψa : ∀ s, s ≤ a → ψ s = 0) (hψb : ∀ s, b ≤ s → ψ s = H)
    {y : ℝ} (hy0 : 0 ≤ y) (hyH : y < H) :
    ∃ τ ∈ Set.Icc a b,
      ∫ s in θlo..θhi, (if y < ψ s then m s else 0) = ∫ s in τ..θhi, m s := by
  set U : Set ℝ := {s | s ∈ Set.Icc a b ∧ y < ψ s} with hU
  have hbU : b ∈ U := ⟨⟨hab.le, le_rfl⟩, by rw [hψb b le_rfl]; exact hyH⟩
  have hne : U.Nonempty := ⟨b, hbU⟩
  have hbdd : BddBelow U := ⟨a, fun s hs => hs.1.1⟩
  set τ := sInf U with hτ
  have hτa : a ≤ τ := le_csInf hne (fun s hs => hs.1.1)
  have hτb : τ ≤ b := csInf_le hbdd hbU
  have key1 : ∀ s, y < ψ s → τ ≤ s := by
    intro s hs
    by_cases hsb : b ≤ s
    · exact hτb.trans hsb
    · push_neg at hsb
      have has : a < s := by
        by_contra hcon
        push_neg at hcon
        rw [hψa s hcon] at hs
        linarith
      exact csInf_le hbdd ⟨⟨has.le, hsb.le⟩, hs⟩
  have key2 : ∀ s, τ < s → y < ψ s := by
    intro s hs
    obtain ⟨u, hu, hus⟩ := exists_lt_of_csInf_lt hne hs
    exact lt_of_lt_of_le hu.2 (hψm hus.le)
  refine ⟨τ, ⟨hτa, hτb⟩, ?_⟩
  have hτ0 : θlo ≤ τ := ha.trans hτa
  have hae : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), s ∉ ({τ} : Set ℝ) :=
    (Set.countable_singleton τ).ae_notMem _
  have e1 : ∫ s in θlo..θhi, (if y < ψ s then m s else 0) =
      ∫ s in θlo..θhi, (if τ < s then m s else 0) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with s hs _
    have hsτ : s ≠ τ := by simpa using hs
    by_cases h1 : y < ψ s
    · have : τ < s := lt_of_le_of_ne (key1 s h1) (Ne.symm hsτ)
      simp [h1, this]
    · have : ¬ τ < s := fun h => h1 (key2 s h)
      simp [h1, this]
  rw [e1, aux_step m hle hτ0, if_pos (hτb.trans hb)]

noncomputable def aux_m {θlo θhi : ℝ} (D : TypeDistribution θlo θhi) (C q : ℝ → ℝ) (s : ℝ) : ℝ :=
  (s - deriv C (q s)) * D.f s - (1 - ∫ r in θlo..s, D.f r)

theorem aux_m_int {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : MonotoneOn q (Set.Icc θlo θhi)) :
    IntervalIntegrable (aux_m D C q) MeasureTheory.volume θlo θhi := by
  have hle := D.lo_lt_hi.le
  have hfc' : ContinuousOn D.f (Set.uIcc θlo θhi) := by
    rw [Set.uIcc_of_le hle]; exact hfd.continuousOn
  have hdq : IntervalIntegrable (fun θ => deriv C (q θ)) MeasureTheory.volume θlo θhi :=
    aux_int_comp hle hq hCd2.continuous
  have h1 := ((intervalIntegral.intervalIntegrable_id (a := θlo) (b := θhi)).sub hdq).mul_continuousOn hfc'
  have h2 : IntervalIntegrable (fun s => 1 - ∫ r in θlo..s, D.f r) MeasureTheory.volume θlo θhi := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact continuousOn_const.sub (aux_Fc_cont D)
  exact h1.sub h2

theorem aux_mu_eq {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ∀ t ∈ Set.Icc θlo θhi, mu D C q t = ∫ s in t..θhi, aux_m D C q s := by
  intro t ht
  rw [mu_eq_core D hfd C hCd hCd2 q hq t ht]
  have hle := D.lo_lt_hi.le
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc θlo θhi := by
    rw [Set.uIcc_of_le ht.2] at hθ; exact ⟨ht.1.trans hθ.1, hθ.2⟩
  have hfθ := (D.f_pos θ hθ').ne'
  simp only [virtualValuation, aux_m]
  rw [D.F_eq θ hθ']
  field_simp
  ring

theorem aux_mu_cont {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ContinuousOn (mu D C q) (Set.Icc θlo θhi) := by
  have hle := D.lo_lt_hi.le
  have hmi := aux_m_int D hfd C hCd2 q hq.1
  have h1 := intervalIntegral.continuousOn_primitive_interval_left (μ := MeasureTheory.volume)
    (f := aux_m D C q) (a := θlo) (b := θhi) (by
      rw [Set.uIcc_of_le hle, ← intervalIntegrable_iff_integrableOn_Icc_of_le hle]; exact hmi)
  rw [Set.uIcc_of_le hle] at h1
  exact h1.congr (fun t ht => aux_mu_eq D hfd C hCd hCd2 q hq t ht)

theorem aux_KL {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    {a b : ℝ} (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi) (hqab : q a < q b) :
    ∃ τ ∈ Set.Icc a b, 0 ≤ mu D C q τ := by
  by_contra hcon
  push_neg at hcon
  have hle := D.lo_lt_hi.le
  have haI : a ∈ Set.Icc θlo θhi := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Set.Icc θlo θhi := ⟨ha.trans hab.le, hb⟩
  have hhiI : θhi ∈ Set.Icc θlo θhi := ⟨hle, le_rfl⟩
  have hqa := hq.1
  have hcont := (aux_mu_cont D hfd C hCd hCd2 q hqa).mono (Set.Icc_subset_Icc ha hb)
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab.le) hcont
  set δ := -mu D C q x with hδ
  have hδpos : 0 < δ := by have := hcon x hx; linarith
  have hμδ : ∀ τ ∈ Set.Icc a b, mu D C q τ ≤ -δ := by
    intro τ hτ; have := hxmax hτ; simp only [Set.mem_setOf_eq] at this; linarith
  have hH : 0 < q b - q a := sub_pos.2 hqab
  set ψ : ℝ → ℝ := fun s => aux_phi (q a) (q b) (aux_Q θlo θhi q s) with hψ
  have hψm : Monotone ψ := fun x y hxy => aux_phi_mono (aux_Q_mono hle hqa.1 hxy)
  have hψ0 : ∀ s, 0 ≤ ψ s := fun s => aux_phi_nonneg hqab.le
  have hψH : ∀ s, ψ s ≤ q b - q a := fun s => aux_phi_le
  have hclamp : ∀ s, max θlo (min s θhi) ∈ Set.Icc θlo θhi :=
    fun s => ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  have hψa : ∀ s, s ≤ a → ψ s = 0 := by
    intro s hs
    apply aux_phi_of_le _ hqab.le
    unfold aux_Q
    exact hqa.1 (hclamp s) haI (max_le ha ((min_le_left _ _).trans hs))
  have hψb : ∀ s, b ≤ s → ψ s = q b - q a := by
    intro s hs
    apply aux_phi_of_ge _ hqab.le
    unfold aux_Q
    exact hqa.1 hbI (hclamp s) (le_max_of_le_right (le_min hs hb))
  have hadm := aux_adm_psi hqa ha hab hb
  have hv := firstVariation_core D hfd C hCd hCd2 q hq _ hadm
  have hq0 : ∀ θ ∈ Set.Icc θlo θhi, 0 ≤ q θ ∧ q θ ≤ q θhi :=
    fun θ hθ => ⟨hqa.2.1 θ hθ, hqa.1 hθ hhiI hθ.2⟩
  have hnegm : Measurable (fun s => -ψ s) := hψm.measurable.neg
  have hrep := aux_fv_rep D hfd C hCd2 q (q θhi) hqa.1 hq0 (h := fun s => -ψ s) hnegm
    (B := q b - q a) (fun s => by rw [abs_neg, abs_of_nonneg (hψ0 s)]; exact hψH s)
  have hmi := aux_m_int D hfd C hCd2 q hqa.1
  have e : ∫ s in θlo..θhi, (fun s => -ψ s) s * ((s - deriv C (q s)) * D.f s -
      (1 - ∫ r in θlo..s, D.f r)) = -∫ s in θlo..θhi, ψ s * aux_m D C q s := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    simp only [aux_m]
    ring
  have hnn : 0 ≤ ∫ s in θlo..θhi, ψ s * aux_m D C q s := by
    rw [hrep, e] at hv; linarith
  rw [aux_layer hle hH.le hψm hψ0 hψH hmi] at hnn
  have hinner : ∀ y ∈ Set.Ioo (0:ℝ) (q b - q a),
      ∫ s in θlo..θhi, (if y < ψ s then aux_m D C q s else 0) ≤ -δ := by
    intro y hy
    obtain ⟨τ, hτ, he⟩ := aux_upset hle (m := aux_m D C q) hψm ha hab hb hψa hψb hy.1.le hy.2
    rw [he, ← aux_mu_eq D hfd C hCd hCd2 q hqa τ ⟨ha.trans hτ.1, hτ.2.trans hb⟩]
    exact hμδ τ hτ
  have hint := aux_layer_int hle hH.le hψm hmi
  rw [intervalIntegral.integral_of_le hH.le, MeasureTheory.integral_Ioc_eq_integral_Ioo] at hnn
  have hle2 : ∫ y in Set.Ioo (0:ℝ) (q b - q a), ∫ s in θlo..θhi, (if y < ψ s then aux_m D C q s else 0)
      ≤ ∫ y in Set.Ioo (0:ℝ) (q b - q a), (-δ) := by
    apply MeasureTheory.setIntegral_mono_on
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hH.le] at hint
      exact hint.mono_set Set.Ioo_subset_Ioc_self
    · exact MeasureTheory.integrableOn_const (by simp)
    · exact measurableSet_Ioo
    · exact hinner
  rw [MeasureTheory.setIntegral_const] at hle2
  simp only [Real.volume_real_Ioo, sub_zero, smul_eq_mul] at hle2
  rw [max_eq_left hH.le] at hle2
  nlinarith

theorem aux_mu_neg_nbhd {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) {θ : ℝ} (hθ : θ ∈ Set.Ioo θlo θhi)
    (hneg : mu D C q θ < 0) :
    ∃ ε > 0, ∀ s, |s - θ| < ε → s ∈ Set.Ioo θlo θhi ∧ mu D C q s < 0 := by
  have hc := (aux_mu_cont D hfd C hCd hCd2 q hq).continuousAt (Icc_mem_nhds hθ.1 hθ.2)
  have h1 : ∀ᶠ s in 𝓝 θ, mu D C q s < 0 := hc.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ s in 𝓝 θ, s ∈ Set.Ioo θlo θhi := Ioo_mem_nhds hθ.1 hθ.2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and h2)
  refine ⟨ε, hε, fun s hs => ?_⟩
  have := hball (y := s) (by rwa [Real.dist_eq])
  exact ⟨this.2, this.1⟩

theorem mu_eq_zero_of_deriv_pos_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ θ ∈ Set.Ioo θlo θhi, ∀ d : ℝ, 0 < d → HasDerivAt q d θ → mu D C q θ = 0 := by
  intro θ hθ d hd hder
  have hle := D.lo_lt_hi.le
  have hnp := mu_nonpos_core D hfd C hCd hCd2 q hq θ ⟨hθ.1.le, hθ.2.le⟩
  by_contra hne
  have hneg : mu D C q θ < 0 := lt_of_le_of_ne hnp hne
  obtain ⟨ε, hε, hball⟩ := aux_mu_neg_nbhd D hfd C hCd hCd2 q hq.1 hθ hneg
  have hslope := (hasDerivAt_iff_tendsto_slope.1 hder).eventually (lt_mem_nhds hd)
  have hslope' := eventually_nhdsWithin_iff.1 hslope
  obtain ⟨ε', hε', hball'⟩ := Metric.eventually_nhds_iff.1 hslope'
  set η := min ε ε' / 2 with hη
  have hηpos : 0 < η := by positivity
  have hηε : η < ε := by
    have : min ε ε' ≤ ε := min_le_left _ _
    linarith
  have hηε' : η < ε' := by
    have : min ε ε' ≤ ε' := min_le_right _ _
    linarith
  have hsa := hball' (y := θ - η) (by rw [Real.dist_eq]; simp [abs_of_pos hηpos, hηε'])
  have hsb := hball' (y := θ + η) (by rw [Real.dist_eq]; simp [abs_of_pos hηpos, hηε'])
  have hna : θ - η ∈ ({θ}ᶜ : Set ℝ) := by simp; linarith
  have hnb : θ + η ∈ ({θ}ᶜ : Set ℝ) := by simp; linarith
  have h1 := hsa hna
  have h2 := hsb hnb
  rw [slope_def_field] at h1 h2
  have qa_lt : q (θ - η) < q θ := by
    have : θ - η - θ < 0 := by linarith
    have := (div_pos_iff.1 h1)
    rcases this with ⟨_, h⟩ | ⟨h, h'⟩
    · linarith
    · linarith
  have qb_gt : q θ < q (θ + η) := by
    have : 0 < θ + η - θ := by linarith
    have := (div_pos_iff.1 h2)
    rcases this with ⟨h, _⟩ | ⟨_, h'⟩
    · linarith
    · linarith
  have hθa : θlo ≤ θ - η := (hball (θ - η) (by simp [abs_of_pos hηpos, hηε])).1.1.le
  have hθb : θ + η ≤ θhi := (hball (θ + η) (by simp [abs_of_pos hηpos, hηε])).1.2.le
  obtain ⟨τ, hτ, hτ0⟩ := aux_KL D hfd C hCd hCd2 q hq hθa (by linarith) hθb (qa_lt.trans qb_gt)
  have := (hball τ (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])).2
  linarith

theorem mu_eq_zero_of_not_continuousAt_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ θ ∈ Set.Ioo θlo θhi, ¬ ContinuousAt q θ → mu D C q θ = 0 := by
  intro θ hθ hnc
  have hle := D.lo_lt_hi.le
  have hnp := mu_nonpos_core D hfd C hCd hCd2 q hq θ ⟨hθ.1.le, hθ.2.le⟩
  by_contra hne
  have hneg : mu D C q θ < 0 := lt_of_le_of_ne hnp hne
  obtain ⟨ε, hε, hball⟩ := aux_mu_neg_nbhd D hfd C hCd hCd2 q hq.1 hθ hneg
  have hmono := hq.1.1
  have hex : ∃ a b, θ - ε < a ∧ a < θ ∧ θ < b ∧ b < θ + ε ∧ q a < q b := by
    by_contra hcon
    push_neg at hcon
    apply hnc
    have hconst : ∀ s, |s - θ| < ε → q s = q θ := by
      intro s hs
      rw [abs_lt] at hs
      have hsI : s ∈ Set.Icc θlo θhi := (hball s (abs_lt.2 hs)).1 |> fun h => ⟨h.1.le, h.2.le⟩
      have hθI : θ ∈ Set.Icc θlo θhi := ⟨hθ.1.le, hθ.2.le⟩
      rcases lt_trichotomy s θ with h | h | h
      · have hbI : θ + ε / 2 ∈ Set.Icc θlo θhi :=
          (hball (θ + ε/2) (by rw [abs_lt]; constructor <;> linarith)).1 |> fun h => ⟨h.1.le, h.2.le⟩
        have h1 := hcon s (θ + ε/2) (by linarith) h (by linarith) (by linarith)
        have h2 := hmono hsI hθI h.le
        have h3 := hmono hθI hbI (by linarith)
        linarith
      · rw [h]
      · have haI : θ - ε / 2 ∈ Set.Icc θlo θhi :=
          (hball (θ - ε/2) (by rw [abs_lt]; constructor <;> linarith)).1 |> fun h => ⟨h.1.le, h.2.le⟩
        have h1 := hcon (θ - ε/2) s (by linarith) (by linarith) h (by linarith)
        have h2 := hmono haI hθI (by linarith)
        have h3 := hmono hθI hsI h.le
        linarith
    refine (continuousAt_const (y := q θ)).congr ?_
    filter_upwards [Metric.ball_mem_nhds θ hε] with s hs
    exact (hconst s (by simpa [Real.dist_eq] using hs)).symm
  obtain ⟨a, b, h1, h2, h3, h4, hab⟩ := hex
  have hA := (hball a (by rw [abs_lt]; constructor <;> linarith)).1
  have hB := (hball b (by rw [abs_lt]; constructor <;> linarith)).1
  obtain ⟨τ, hτ, hτ0⟩ := aux_KL D hfd C hCd hCd2 q hq hA.1.le (h2.trans h3) hB.2.le hab
  have := (hball τ (by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2])).2
  linarith

theorem aux_left_nonpos {a θ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc a θ)) (haθ : a < θ)
    (hcon : ContinuousAt g θ)
    (h : ∀ s ∈ Set.Ico a θ, ∫ r in s..θ, g r ≤ 0) : g θ ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcon.eventually (lt_mem_nhds hpos))
  set s := max a (θ - ε / 2) with hs
  have hsθ : s < θ := max_lt haθ (by linarith)
  have has : a ≤ s := le_max_left _ _
  have hint : IntervalIntegrable g MeasureTheory.volume s θ :=
    (hg.mono (Set.Icc_subset_Icc has le_rfl)).intervalIntegrable_of_Icc hsθ.le
  have := intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun r hr => by
    have := hball (y := r) (by
      rw [Real.dist_eq, abs_lt]
      have h1 : θ - ε / 2 ≤ s := le_max_right _ _
      constructor <;> linarith [hr.1, hr.2])
    linarith) hsθ
  linarith [h s ⟨has, hsθ⟩]

theorem aux_right_nonneg {b θ : ℝ} {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc θ b)) (hθb : θ < b)
    (hcon : ContinuousAt g θ)
    (h : ∀ s ∈ Set.Ioc θ b, 0 ≤ ∫ r in θ..s, g r) : 0 ≤ g θ := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcon.eventually (gt_mem_nhds hneg))
  set s := min b (θ + ε / 2) with hs
  have hsθ : θ < s := lt_min hθb (by linarith)
  have hsb : s ≤ b := min_le_left _ _
  have hint : IntervalIntegrable (fun r => -g r) MeasureTheory.volume θ s :=
    ((hg.mono (Set.Icc_subset_Icc le_rfl hsb)).neg).intervalIntegrable_of_Icc hsθ.le
  have := intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun r hr => by
    have := hball (y := r) (by
      rw [Real.dist_eq, abs_lt]
      have h1 : s ≤ θ + ε / 2 := min_le_right _ _
      constructor <;> linarith [hr.1, hr.2])
    linarith) hsθ
  rw [intervalIntegral.integral_neg] at this
  linarith [h s ⟨hsθ, hsb⟩]

theorem aux_strictMono_Cp {C : ℝ → ℝ} (hCd2 : Differentiable ℝ (deriv C))
    (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q) : StrictMonoOn (deriv C) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hCd2.continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  exact hC2 x (le_of_lt hx)

theorem aux_int_m_sub {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) {s θ : ℝ} (hs : θlo ≤ s) (hsθ : s ≤ θ) (hθ : θ ≤ θhi) :
    ∫ r in s..θ, aux_m D C q r = mu D C q s - mu D C q θ := by
  have hle := D.lo_lt_hi.le
  have hmi := aux_m_int D hfd C hCd2 q hq.1
  rw [aux_mu_eq D hfd C hCd hCd2 q hq s ⟨hs, hsθ.trans hθ⟩, aux_mu_eq D hfd C hCd hCd2 q hq θ ⟨hs.trans hsθ, hθ⟩]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hmi.mono_set (by rw [Set.uIcc_of_le hsθ, Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hs hθ) :
      IntervalIntegrable (aux_m D C q) MeasureTheory.volume s θ)
    (hmi.mono_set (by rw [Set.uIcc_of_le hθ, Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc (hs.trans hsθ) le_rfl) :
      IntervalIntegrable (aux_m D C q) MeasureTheory.volume θ θhi)
  linarith

theorem continuousOn_Ioo_core {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ContinuousOn q (Set.Ioo θlo θhi) := by
  intro θ hθ
  apply ContinuousAt.continuousWithinAt
  by_contra hnc
  have hle := D.lo_lt_hi.le
  have hμ0 := mu_eq_zero_of_not_continuousAt_core D hfd C hCd hCd2 q hq θ hθ hnc
  have hnp := mu_nonpos_core D hfd C hCd hCd2 q hq
  have hqa := hq.1
  set Q := aux_Q θlo θhi q with hQ
  have hQm : Monotone Q := aux_Q_mono hle hqa.1
  have hQeq : ∀ s ∈ Set.Icc θlo θhi, Q s = q s := fun s hs => aux_Q_eq hs
  set L := sSup (Q '' Set.Iio θ) with hL
  set R := sInf (Q '' Set.Ioi θ) with hR
  have hne1 : (Q '' Set.Iio θ).Nonempty := ⟨Q (θ-1), θ-1, by simp, rfl⟩
  have hne2 : (Q '' Set.Ioi θ).Nonempty := ⟨Q (θ+1), θ+1, by simp, rfl⟩
  have hbdd1 : BddAbove (Q '' Set.Iio θ) := ⟨Q θ, by rintro _ ⟨s, hs, rfl⟩; exact hQm (le_of_lt hs)⟩
  have hbdd2 : BddBelow (Q '' Set.Ioi θ) := ⟨Q θ, by rintro _ ⟨s, hs, rfl⟩; exact hQm (le_of_lt hs)⟩
  have hQL : ∀ s < θ, Q s ≤ L := fun s hs => le_csSup hbdd1 ⟨s, hs, rfl⟩
  have hQR : ∀ s > θ, R ≤ Q s := fun s hs => csInf_le hbdd2 ⟨s, hs, rfl⟩
  have hLθ : L ≤ Q θ := csSup_le hne1 (by rintro _ ⟨s, hs, rfl⟩; exact hQm hs.le)
  have hθR : Q θ ≤ R := le_csInf hne2 (by rintro _ ⟨s, hs, rfl⟩; exact hQm hs.le)
  have hLR : L < R := by
    by_contra hge
    push_neg at hge
    have hLe : L = Q θ := le_antisymm hLθ (hθR.trans hge)
    have hRe : R = Q θ := le_antisymm (hge.trans hLθ) hθR
    apply hnc
    have hqQ : q =ᶠ[𝓝 θ] Q := by
      filter_upwards [Ioo_mem_nhds hθ.1 hθ.2] with s hs
      exact (hQeq s ⟨hs.1.le, hs.2.le⟩).symm
    refine ContinuousAt.congr ?_ hqQ.symm
    rw [ContinuousAt, tendsto_order]
    constructor
    · intro a' ha'
      obtain ⟨_, ⟨s0, hs0, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne1 (show a' < L by rw [hLe]; exact ha')
      filter_upwards [Ioi_mem_nhds (show s0 < θ from hs0)] with x hx
      exact lt_of_lt_of_le hlt (hQm (le_of_lt hx))
    · intro b' hb'
      obtain ⟨_, ⟨s1, hs1, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne2 (show R < b' by rw [hRe]; exact hb')
      filter_upwards [Iio_mem_nhds (show θ < s1 from hs1)] with x hx
      exact lt_of_le_of_lt (hQm (le_of_lt hx)) hlt
  have hL0 : 0 ≤ L := by
    have h1 : Q θlo ≤ L := hQL θlo hθ.1
    have h2 : Q θlo = q θlo := hQeq θlo ⟨le_rfl, hle⟩
    have h3 := hqa.2.1 θlo ⟨le_rfl, hle⟩
    linarith
  have hmonoCp := aux_strictMono_Cp hCd2 hC2
  have hCLR : deriv C L < deriv C R :=
    hmonoCp (Set.mem_Ici.2 hL0) (Set.mem_Ici.2 (hL0.trans hLR.le)) hLR
  have hmi := aux_m_int D hfd C hCd2 q hqa.1
  have hgc : ∀ c : ℝ, ContinuousOn (fun r => (r - c) * D.f r - (1 - ∫ x in θlo..r, D.f x))
      (Set.Icc θlo θhi) := fun c =>
    ((continuousOn_id.sub continuousOn_const).mul hfd.continuousOn).sub
      (continuousOn_const.sub (aux_Fc_cont D))
  have hmL : ∀ r ∈ Set.Ico θlo θ, (r - deriv C L) * D.f r - (1 - ∫ x in θlo..r, D.f x) ≤
      aux_m D C q r := by
    intro r hr
    have hrI : r ∈ Set.Icc θlo θhi := ⟨hr.1, hr.2.le.trans hθ.2.le⟩
    have h1 : q r ≤ L := by rw [← hQeq r hrI]; exact hQL r hr.2
    have h2 : deriv C (q r) ≤ deriv C L :=
      hmonoCp.monotoneOn (Set.mem_Ici.2 (hqa.2.1 r hrI)) (Set.mem_Ici.2 hL0) h1
    have h3 := (D.f_pos r hrI).le
    unfold aux_m
    nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]
  have hmR : ∀ r ∈ Set.Ioc θ θhi, aux_m D C q r ≤
      (r - deriv C R) * D.f r - (1 - ∫ x in θlo..r, D.f x) := by
    intro r hr
    have hrI : r ∈ Set.Icc θlo θhi := ⟨hθ.1.le.trans hr.1.le, hr.2⟩
    have h1 : R ≤ q r := by rw [← hQeq r hrI]; exact hQR r hr.1
    have h2 : deriv C R ≤ deriv C (q r) :=
      hmonoCp.monotoneOn (Set.mem_Ici.2 (hL0.trans hLR.le)) (Set.mem_Ici.2 (hqa.2.1 r hrI)) h1
    have h3 := (D.f_pos r hrI).le
    unfold aux_m
    nlinarith [mul_nonneg (sub_nonneg.2 h2) h3]
  have hleft : (θ - deriv C L) * D.f θ - (1 - ∫ x in θlo..θ, D.f x) ≤ 0 := by
    apply aux_left_nonpos (a := θlo) (g := fun r => (r - deriv C L) * D.f r - (1 - ∫ x in θlo..r, D.f x))
    · exact (hgc _).mono (Set.Icc_subset_Icc le_rfl hθ.2.le)
    · exact hθ.1
    · exact ((hgc _).continuousAt (Icc_mem_nhds hθ.1 hθ.2))
    · intro s hs
      have hsI : s ∈ Set.Icc θlo θhi := ⟨hs.1, hs.2.le.trans hθ.2.le⟩
      have hint1 : IntervalIntegrable (fun r => (r - deriv C L) * D.f r - (1 - ∫ x in θlo..r, D.f x))
          MeasureTheory.volume s θ :=
        ((hgc _).mono (Set.Icc_subset_Icc hs.1 hθ.2.le)).intervalIntegrable_of_Icc hs.2.le
      have hint2 : IntervalIntegrable (aux_m D C q) MeasureTheory.volume s θ :=
        hmi.mono_set (by rw [Set.uIcc_of_le hs.2.le, Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hs.1 hθ.2.le)
      have h1 := intervalIntegral.integral_mono_on_of_le_Ioo hs.2.le hint1 hint2
        (fun r hr => hmL r ⟨hs.1.trans hr.1.le, hr.2⟩)
      rw [aux_int_m_sub D hfd C hCd hCd2 q hqa hs.1 hs.2.le hθ.2.le, hμ0] at h1
      have := hnp s hsI
      linarith
  have hright : 0 ≤ (θ - deriv C R) * D.f θ - (1 - ∫ x in θlo..θ, D.f x) := by
    apply aux_right_nonneg (b := θhi) (g := fun r => (r - deriv C R) * D.f r - (1 - ∫ x in θlo..r, D.f x))
    · exact (hgc _).mono (Set.Icc_subset_Icc hθ.1.le le_rfl)
    · exact hθ.2
    · exact ((hgc _).continuousAt (Icc_mem_nhds hθ.1 hθ.2))
    · intro s hs
      have hsI : s ∈ Set.Icc θlo θhi := ⟨hθ.1.le.trans hs.1.le, hs.2⟩
      have hint1 : IntervalIntegrable (fun r => (r - deriv C R) * D.f r - (1 - ∫ x in θlo..r, D.f x))
          MeasureTheory.volume θ s :=
        ((hgc _).mono (Set.Icc_subset_Icc hθ.1.le hs.2)).intervalIntegrable_of_Icc hs.1.le
      have hint2 : IntervalIntegrable (aux_m D C q) MeasureTheory.volume θ s :=
        hmi.mono_set (by rw [Set.uIcc_of_le hs.1.le, Set.uIcc_of_le hle]; exact Set.Icc_subset_Icc hθ.1.le hs.2)
      have h1 := intervalIntegral.integral_mono_on_of_le_Ioo hs.1.le hint2 hint1
        (fun r hr => hmR r ⟨hr.1, hr.2.le.trans hs.2⟩)
      rw [aux_int_m_sub D hfd C hCd hCd2 q hqa hθ.1.le hs.1.le hs.2, hμ0] at h1
      have := hnp s hsI
      linarith
  have hfθ := D.f_pos θ ⟨hθ.1.le, hθ.2.le⟩
  nlinarith [mul_pos (sub_pos.2 hCLR) hfθ]

end MussaRosen.Mono

open MussaRosen.Mono


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ContinuousOn q (Set.Ioo θlo θhi) := by
  exact continuousOn_Ioo_core D hfd C hCd hCd2 hC2 q hq
