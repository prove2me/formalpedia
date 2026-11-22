-- Prove2me | solution 1 for MasulloAudit.real_place_term_eq_realTraceIntegral
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:31:05.723575+00:00
-- url     : https://prove2.me/submissions/1575d2df-1fd8-4187-98f5-f7dd5c368d0a

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology ContDiff

namespace RealPlaceAux

/-- Pointwise algebra on `(1,∞)`. -/
lemma w_pos_side (t : ℝ) (ht : 1 < t) :
    (|t| ^ (1/2 : ℝ) / |1 - t| * (1 / |t|)) + (|-t| ^ (1/2 : ℝ) / |1 - -t| * (1 / |-t|))
      = 2 * (Real.sqrt t / (t ^ 2 - 1)) := by
  have h0 : 0 < t := by linarith
  rw [abs_neg, abs_of_pos h0, abs_of_neg (by linarith : 1 - t < 0),
    abs_of_pos (by linarith : (0:ℝ) < 1 - -t), ← Real.sqrt_eq_rpow]
  obtain ⟨s, hs1, rfl⟩ : ∃ s, 1 < s ∧ t = s ^ 2 := by
    refine ⟨Real.sqrt t, ?_, (Real.sq_sqrt h0.le).symm⟩
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one ht
  have hs : 0 < s := by linarith
  rw [Real.sqrt_sq hs.le]
  have h1 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (s ^ 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : 1 - s ^ 2 ≠ 0 := by nlinarith
  have h4 : 1 - -s ^ 2 ≠ 0 := by nlinarith
  have e : (s ^ 2) ^ 2 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by ring
  have h5 : s ^ 2 + 1 ≠ 0 := by positivity
  rw [e]
  field_simp
  ring

lemma w_neg_side (t : ℝ) (ht : 1 < t) :
    |-(t ^ 2)⁻¹| * ((|t⁻¹| ^ (1/2 : ℝ) / |1 - t⁻¹| * (1 / |t⁻¹|)) +
      (|-t⁻¹| ^ (1/2 : ℝ) / |1 - -t⁻¹| * (1 / |-t⁻¹|)))
      = 2 * (Real.sqrt t / (t ^ 2 - 1)) := by
  have h0 : 0 < t := by linarith
  have hi : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hi0 : 0 < t⁻¹ := inv_pos.2 h0
  rw [abs_neg, abs_neg, abs_of_pos hi0, abs_of_pos (by linarith : 0 < 1 - t⁻¹),
    abs_of_pos (by linarith : (0:ℝ) < 1 - -t⁻¹), abs_of_pos (by positivity : 0 < (t ^ 2)⁻¹),
    ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  obtain ⟨s, hs1, rfl⟩ : ∃ s, 1 < s ∧ t = s ^ 2 := by
    refine ⟨Real.sqrt t, ?_, (Real.sq_sqrt h0.le).symm⟩
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt zero_le_one ht
  have hs : 0 < s := by linarith
  rw [Real.sqrt_sq hs.le]
  have h1 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : (s ^ 2) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : 1 - (s ^ 2)⁻¹ ≠ 0 := by
    rw [sub_ne_zero]; intro h; field_simp at h; nlinarith
  have h4 : 1 - -(s ^ 2)⁻¹ ≠ 0 := by
    have : 0 < (s^2)⁻¹ := by positivity
    linarith
  have h6 : 1 + s ^ 2 ≠ 0 := by positivity
  have e : (s ^ 2) ^ 2 - 1 = (s ^ 2 - 1) * (s ^ 2 + 1) := by ring
  have h5 : s ^ 2 + 1 ≠ 0 := by positivity
  have e1 : 1 - (s ^ 2)⁻¹ = (s ^ 2 - 1) / s ^ 2 := by field_simp
  have e2 : 1 - -(s ^ 2)⁻¹ = (s ^ 2 + 1) / s ^ 2 := by field_simp; ring
  rw [e, e1, e2]
  field_simp
  ring

end RealPlaceAux

open RealPlaceAux in
theorem solution (φ : ℝ → ℂ) (hφ : MasulloRH.IsRationalTraceTest φ) :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (1/2 : ℂ) * ∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ) =
      ∫ t in Ioi (1:ℝ), MasulloRH.realTraceIntegrand φ t := by
  obtain ⟨hsmooth, hcpt, hsupp, h1⟩ := hφ
  set w : ℝ → ℝ := fun x => |x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) with hw
  set f : ℝ → ℂ := fun x => φ |x| * (w x : ℂ) with hf
  -- support bounds
  have hK : IsCompact (tsupport φ) := hcpt
  obtain ⟨ε, hε, hεball⟩ : ∃ ε > 0, Metric.ball (0:ℝ) ε ⊆ (tsupport φ)ᶜ := by
    have : (tsupport φ)ᶜ ∈ 𝓝 (0:ℝ) := by
      apply (isClosed_tsupport φ).isOpen_compl.mem_nhds
      intro h; exact lt_irrefl (0:ℝ) (hsupp h)
    exact Metric.mem_nhds_iff.1 this
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hzero : ∀ y, φ y ≠ 0 → ε ≤ |y| ∧ |y| ≤ R := by
    intro y hy
    have hy' : y ∈ tsupport φ := subset_tsupport _ hy
    refine ⟨?_, ?_⟩
    · by_contra hlt; push Not at hlt
      exact hεball (by simpa [Metric.mem_ball] using hlt) hy'
    · simpa [Metric.mem_closedBall] using hR hy'
  obtain ⟨C, hC⟩ := hsmooth.lipschitzWith_of_hasCompactSupport hcpt (by simp)
  have hlip : ∀ y, ‖φ y‖ ≤ C * |y - 1| := by
    intro y
    have := hC.dist_le_mul y 1
    simpa [h1, Real.dist_eq] using this
  -- f is bounded
  have hbound : ∀ x, ‖f x‖ ≤ C / Real.sqrt ε := by
    intro x
    by_cases hx : φ |x| = 0
    · simp only [hf, hx, zero_mul, norm_zero]; positivity
    obtain ⟨hεx, -⟩ := hzero _ hx
    rw [abs_abs] at hεx
    have hxpos : 0 < |x| := lt_of_lt_of_le hε hεx
    simp only [hf, hw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← Real.sqrt_eq_rpow]
    have hA : ‖φ |x|‖ ≤ C * |1 - x| := by
      refine (hlip _).trans (mul_le_mul_of_nonneg_left ?_ C.2)
      rw [abs_sub_comm 1 x]
      simpa using abs_abs_sub_abs_le x 1
    have hsq : 0 < Real.sqrt |x| := Real.sqrt_pos.2 hxpos
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt |x| / |1 - x|),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / |x|)]
    by_cases h1x : |1 - x| = 0
    · simp [h1x]; positivity
    have h1x' : 0 < |1 - x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h1x)
    calc ‖φ |x|‖ * (Real.sqrt |x| / |1 - x| * (1 / |x|))
        ≤ (C * |1 - x|) * (Real.sqrt |x| / |1 - x| * (1 / |x|)) := by
          gcongr
      _ = C / Real.sqrt |x| := by
          have : Real.sqrt |x| ^ 2 = |x| := Real.sq_sqrt hxpos.le
          field_simp
          rw [this]
      _ ≤ C / Real.sqrt ε := by
          gcongr
  have hmeas : AEStronglyMeasurable f volume := by
    have hc : Continuous φ := hsmooth.continuous
    apply AEStronglyMeasurable.mul
    · exact (hc.comp continuous_abs).aestronglyMeasurable
    · apply Measurable.aestronglyMeasurable
      apply Complex.measurable_ofReal.comp
      simp only [hw]; fun_prop
  have hfint : Integrable f := by
    have hsub : Function.support f ⊆ Metric.closedBall 0 R := by
      intro x hx
      have : φ |x| ≠ 0 := by
        intro h; apply hx; simp [hf, h]
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      simpa using (hzero _ this).2
    rw [← integrableOn_iff_integrable_of_support_subset hsub]
    exact Measure.integrableOn_of_bounded (measure_closedBall_lt_top).ne
      hmeas (Filter.Eventually.of_forall hbound)
  refine ⟨hfint.integrableOn, ?_⟩
  -- reduce to (0, ∞)
  have hset : ∫ x in {x : ℝ | x ≠ 0}, f x = ∫ x in Iic (0:ℝ) ∪ Ioi 0, f x := by
    apply setIntegral_congr_set
    rw [Iic_union_Ioi, ae_eq_univ]
    have : {x : ℝ | x ≠ 0}ᶜ = {0} := by ext; simp
    rw [this]; exact measure_singleton _
  have hsplit : ∫ x in {x : ℝ | x ≠ 0}, f x
      = (∫ y in Ioi (0:ℝ), f (-y)) + ∫ y in Ioi (0:ℝ), f y := by
    rw [hset, setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hfint.integrableOn hfint.integrableOn]
    have := integral_comp_neg_Ioi 0 f
    rw [neg_zero] at this
    rw [← this]
  set F : ℝ → ℂ := fun y => f (-y) + f y with hF
  have hFint : Integrable F := hfint.comp_neg.add hfint
  have hsplit2 : ∫ x in {x : ℝ | x ≠ 0}, f x = ∫ y in Ioi (0:ℝ), F y := by
    rw [hsplit, hF, integral_add hfint.comp_neg.integrableOn hfint.integrableOn]
  -- split (0,∞) = (0,1) ∪ [1,∞)
  have himg : (fun t : ℝ => t⁻¹) '' Ioi 1 = Ioo 0 1 := by
    ext y; constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨inv_pos.2 (by linarith [mem_Ioi.1 ht]), inv_lt_one_of_one_lt₀ ht⟩
    · rintro ⟨hy0, hy1⟩
      exact ⟨y⁻¹, (one_lt_inv₀ hy0).2 hy1, inv_inv y⟩
  have hderiv : ∀ t ∈ Ioi (1:ℝ), HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) (Ioi 1) t :=
    fun t ht => (hasDerivAt_inv (by linarith [mem_Ioi.1 ht] : t ≠ 0)).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => t⁻¹) (Ioi 1) := inv_injective.injOn
  have hcov : ∫ y in Ioo (0:ℝ) 1, F y = ∫ t in Ioi (1:ℝ), |-(t ^ 2)⁻¹| • F t⁻¹ := by
    rw [← himg]
    exact integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
  have hcovint : IntegrableOn (fun t : ℝ => |-(t ^ 2)⁻¹| • F t⁻¹) (Ioi 1) := by
    rw [← integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj F,
      himg]
    exact hFint.integrableOn
  have hsplit3 : ∫ y in Ioi (0:ℝ), F y
      = ∫ t in Ioi (1:ℝ), (|-(t ^ 2)⁻¹| • F t⁻¹ + F t) := by
    rw [← Ioo_union_Ici_eq_Ioi zero_lt_one, setIntegral_union ((Iio_disjoint_Ici le_rfl).mono_left Ioo_subset_Iio_self)
      measurableSet_Ici hFint.integrableOn hFint.integrableOn, integral_Ici_eq_integral_Ioi,
      hcov, integral_add hcovint hFint.integrableOn]
  rw [hsplit2, hsplit3, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht1 : 1 < t := ht
  have ht0 : 0 < t := by linarith
  have hA := w_pos_side t ht1
  have hB := w_neg_side t ht1
  have hA' : (w (-t) : ℂ) + (w t : ℂ) = 2 * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ) := by
    rw [add_comm]; exact_mod_cast hA
  have hB' : ((|-(t ^ 2)⁻¹| : ℝ) : ℂ) * ((w (-t⁻¹) : ℂ) + (w t⁻¹ : ℂ))
      = 2 * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ) := by
    rw [add_comm (w (-t⁻¹) : ℂ)]; exact_mod_cast hB
  rw [abs_neg] at hB'
  simp only [hF, hf, MasulloRH.realTraceIntegrand, Complex.real_smul, abs_neg,
    abs_of_pos ht0, abs_of_pos (inv_pos.2 ht0)]
  linear_combination (1/2 : ℂ) * φ t * hA' + (1/2 : ℂ) * φ t⁻¹ * hB'

