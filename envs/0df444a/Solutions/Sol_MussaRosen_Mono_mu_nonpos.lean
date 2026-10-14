-- Prove2me | solution 1 for MussaRosen.Mono.mu_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:33:22.971157+00:00
-- url     : https://prove2.me/submissions/d42f63c9-1329-40d4-a318-e3ac89a3da10

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

end MussaRosen.Mono

open MussaRosen.Mono


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q) :
    ∀ t ∈ Set.Icc θlo θhi, mu D C q t ≤ 0 := by
  exact mu_nonpos_core D hfd C hCd hCd2 q hq
