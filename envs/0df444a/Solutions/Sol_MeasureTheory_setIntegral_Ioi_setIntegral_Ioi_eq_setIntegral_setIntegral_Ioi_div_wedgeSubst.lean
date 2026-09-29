-- Prove2me | solution 1 for MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6ff5909e-07ba-5fa0-9765-c57d46b17be2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst

set_option autoImplicit false

open MeasureTheory Set

theorem solution
    (H : ℝ → ℝ → ℂ) (hHm : Measurable (Function.uncurry H))
    (hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (v : ℝ) (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w) := by
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ

  have img1 : ∀ u : ℝ, 0 < u → (fun σ : ℝ => u * (σ - u)) '' Ioi u = Ioi 0 := by
    intro u hu
    ext t
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact mul_pos hu (sub_pos.2 hσ)
    · intro ht
      refine ⟨t / u + u, ?_, ?_⟩
      · show u < t / u + u
        linarith [div_pos (show (0:ℝ) < t from ht) hu]
      · show u * (t / u + u - u) = t
        field_simp
        ring
  have hder1 : ∀ u : ℝ, ∀ x ∈ Ioi u, HasDerivWithinAt (fun σ : ℝ => u * (σ - u)) u (Ioi u) x := by
    intro u x _
    have h := ((hasDerivAt_id x).sub_const u).const_mul u
    simp only [id, mul_one] at h
    exact h.hasDerivWithinAt
  have hinj1 : ∀ u : ℝ, 0 < u → InjOn (fun σ : ℝ => u * (σ - u)) (Ioi u) := by
    intro u hu a _ b _ h
    have := mul_left_cancel₀ hu.ne' h
    linarith
  have img2 : ∀ σ : ℝ, 0 < σ → (fun w : ℝ => v / w) '' Ioi (v / σ) = Ioo 0 σ := by
    intro σ hσ
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw0 : 0 < w := lt_trans (div_pos hv hσ) hw
      refine ⟨div_pos hv hw0, ?_⟩
      rw [div_lt_iff₀ hw0]
      have := (div_lt_iff₀ hσ).1 hw
      linarith [mul_comm σ w]
    · rintro ⟨hu0, huσ⟩
      refine ⟨v / u, ?_, ?_⟩
      · show v / σ < v / u
        exact div_lt_div_of_pos_left hv hu0 huσ
      · show v / (v / u) = u
        field_simp
  have hder2 : ∀ σ : ℝ, 0 < σ → ∀ x ∈ Ioi (v / σ),
      HasDerivWithinAt (fun w : ℝ => v / w) (-(v / x ^ 2)) (Ioi (v / σ)) x := by
    intro σ hσ x hx
    have hx0 : 0 < x := lt_trans (div_pos hv hσ) hx
    have h := (hasDerivAt_const x v).div (hasDerivAt_id x) hx0.ne'
    simp only [id, zero_mul, mul_one, zero_sub] at h
    have e : -v / x ^ 2 = -(v / x ^ 2) := by ring
    rw [e] at h
    exact h.hasDerivWithinAt
  have hinj2 : ∀ σ : ℝ, 0 < σ → InjOn (fun w : ℝ => v / w) (Ioi (v / σ)) := by
    intro σ hσ a ha b hb h
    have ha0 : 0 < a := lt_trans (div_pos hv hσ) ha
    have hb0 : 0 < b := lt_trans (div_pos hv hσ) hb
    have h' : v / a = v / b := h
    field_simp at h'
    nlinarith [h', hv]

  have sub1 : ∀ u : ℝ, 0 < u → ∀ G : ℝ → ℂ,
      ∫ t in Ioi (0 : ℝ), G t = ∫ σ in Ioi u, u • G (u * (σ - u)) := by
    intro u hu G
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (hder1 u) (hinj1 u hu) G
    rw [img1 u hu] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun σ _ => ?_
    rw [abs_of_pos hu]

  obtain ⟨Kp, hKp⟩ : ∃ Kp : ℝ × ℝ → ℂ,
      Kp = Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p => p.1 • H (p.1 * (p.2 - p.1)) p.1) := ⟨_, rfl⟩
  have hKu : ∀ u : ℝ, (fun σ => Kp (u, σ)) = (Ioi u).indicator (fun σ => u • H (u * (σ - u)) u) := by
    intro u; funext σ
    rw [hKp]
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioi]
  have hKσ : ∀ σ : ℝ, (fun u => Kp (u, σ)) = (Iio σ).indicator (fun u => u • H (u * (σ - u)) u) := by
    intro σ; funext u
    rw [hKp]
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio]
  have hKm : Measurable Kp := by
    rw [hKp]
    refine Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    exact measurable_fst.smul (hHm.comp (by measurability : Measurable fun p : ℝ × ℝ => (p.1 * (p.2 - p.1), p.1)))

  have hKslice : ∀ u : ℝ, 0 < u → ∫⁻ σ in Ioi (0 : ℝ), ‖Kp (u, σ)‖ₑ = ∫⁻ t in Ioi (0 : ℝ), ‖H t u‖ₑ := by
    intro u hu
    have e1 : (fun σ => ‖Kp (u, σ)‖ₑ) = (Ioi u).indicator (fun σ => ENNReal.ofReal |u| * ‖H (u * (σ - u)) u‖ₑ) := by
      funext σ
      have := congrFun (hKu u) σ
      rw [this, Set.indicator_apply, Set.indicator_apply]
      split_ifs
      · rw [enorm_smul, Real.enorm_eq_ofReal_abs]
      · simp
    rw [e1, setLIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hu.le]
    have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi (hder1 u) (hinj1 u hu)
      (fun t => ‖H t u‖ₑ)
    rw [img1 u hu] at h
    rw [h]
  have hKint : Integrable Kp (μ.prod μ) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hfin := hHi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    calc ∫⁻ p, ‖Kp p‖ₑ ∂(μ.prod μ) = ∫⁻ u, ∫⁻ σ, ‖Kp (u, σ)‖ₑ ∂μ ∂μ :=
          lintegral_prod _ hKm.enorm.aemeasurable
      _ = ∫⁻ u, ∫⁻ t, ‖H t u‖ₑ ∂μ ∂μ := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
          exact hKslice u hu
      _ = ∫⁻ p, ‖Function.uncurry H p‖ₑ ∂(μ.prod μ) :=
          (lintegral_prod_symm (fun p : ℝ × ℝ => ‖Function.uncurry H p‖ₑ) hHm.enorm.aemeasurable).symm
      _ < ⊤ := hfin

  calc ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u
      = ∫ u in Ioi (0 : ℝ), ∫ σ in Ioi (0 : ℝ), Kp (u, σ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        rw [sub1 u hu0 (fun t => H t u)]
        show ∫ σ in Ioi u, u • H (u * (σ - u)) u = ∫ σ in Ioi (0 : ℝ), (fun σ => Kp (u, σ)) σ
        rw [hKu u, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hu0.le]
    _ = ∫ σ in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), Kp (u, σ) :=
        integral_integral_swap (f := fun u σ => Kp (u, σ)) hKint
    _ = ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
          ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_
        have hσ0 : (0 : ℝ) < σ := hσ
        show ∫ u in Ioi (0 : ℝ), (fun u => Kp (u, σ)) u = _
        rw [hKσ σ, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← img2 σ hσ0,
          integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi (hder2 σ hσ0) (hinj2 σ hσ0)]
        refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
        have hw0 : 0 < w := lt_trans (div_pos hv hσ0) hw
        rw [abs_neg, abs_of_pos (div_pos hv (pow_pos hw0 2)), smul_smul, Complex.real_smul]
        have e1 : v / w ^ 2 * (v / w) = v ^ 2 / w ^ 3 := by field_simp
        have e2 : v / w * (σ - v / w) = v * (σ * w - v) / w ^ 2 := by field_simp
        rw [e1, e2]

end S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
end P2MW
export P2MW.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst (solution)
