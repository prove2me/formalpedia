-- Prove2me | solution 1 for MussaRosen.Mono.mu_eq_integral_MR_sub_MC
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:27:23.327163+00:00
-- url     : https://prove2.me/submissions/589a7810-0355-4f4c-be4b-6a0063f40a5e

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

end MussaRosen.Mono

open MussaRosen.Mono


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (q : ℝ → ℝ) (hq : IsAdmissible θlo θhi q) :
    ∀ t ∈ Set.Icc θlo θhi,
      mu D C q t = ∫ θ in t..θhi, (virtualValuation D θ - deriv C (q θ)) * D.f θ := by
  exact mu_eq_core D hfd C hCd hCd2 q hq
