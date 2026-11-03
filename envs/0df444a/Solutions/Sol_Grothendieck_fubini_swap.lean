-- Prove2me | solution 1 for Grothendieck.fubini_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T04:53:50.933944+00:00
-- url     : https://prove2.me/submissions/ba7f5d5b-6dfc-4aa8-8ffb-c8a1533bab1e

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Fubini

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

instance (r : ℕ) (τ : ℝ) : SFinite (reducedLaw r τ) := by
  unfold reducedLaw
  infer_instance

end Grothendieck

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The one-dimensional Laplace identity `∫_0^∞ u^{-1/2} e^{-Cu} du = √π/√C`. -/
theorem integral_rpow_neg_half_exp_mul {C : ℝ} (hC : 0 < C) :
    (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
      = Real.sqrt Real.pi / Real.sqrt C := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1/2:ℝ)) (r := C) (by norm_num) hC
  have h1 : ((1/2:ℝ) - 1) = -(1/2) := by norm_num
  rw [h1, Real.Gamma_one_half_eq] at h
  rw [h, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.div_rpow zero_le_one (le_of_lt hC), Real.one_rpow, one_div, div_eq_mul_inv]
  ring_nf

/-- **The Laplace step.** For `A, B > 0`,
`1/(√A √B) = π⁻¹ ∫∫_{(0,∞)²} (st)^{-1/2} e^{-(sA+tB)} ds dt`. -/
theorem laplace_inv_sqrt_mul_inv_sqrt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (Real.sqrt A * Real.sqrt B)⁻¹
      = Real.pi⁻¹ * ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)) := by
  have hI : ∀ C : ℝ, 0 < C →
      (∫ u in Set.Ioi (0:ℝ), u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
        = Real.sqrt Real.pi / Real.sqrt C := fun C hC => integral_rpow_neg_half_exp_mul hC
  have hinner : ∀ s ∈ Set.Ioi (0:ℝ),
      (∫ t in Set.Ioi (0:ℝ), (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B)))
        = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (Real.sqrt Real.pi / Real.sqrt B) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hpt : ∀ t ∈ Set.Ioi (0:ℝ),
        (s * t) ^ (-(1/2) : ℝ) * Real.exp (-(s * A + t * B))
          = (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))) * (t ^ (-(1/2) : ℝ) * Real.exp (-(B * t))) := by
      intro t ht
      have ht0 : (0:ℝ) < t := ht
      have e1 : -(s * A + t * B) = -(A * s) + -(B * t) := by ring
      rw [Real.mul_rpow (le_of_lt hs0) (le_of_lt ht0), e1, Real.exp_add]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hI B hB]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_mul_const, hI A hA]
  have hsq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    rw [← sq, Real.sq_sqrt (le_of_lt Real.pi_pos)]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hA0 : Real.sqrt A ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hA)
  have hB0 : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp
  rw [Real.sq_sqrt (le_of_lt Real.pi_pos)]

end Grothendieck

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The reduced integrand as a ratio: `reducedIntegrand r W = ⟨X,Y⟩/(‖X‖‖Y‖)` with `X`, `Y` the two
columns of `W`. -/
theorem reducedIntegrand_eq_inner_div (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = inner ℝ (colFun r 0 W) (colFun r 1 W)
        * (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by
  unfold reducedIntegrand normalize
  rw [inner_smul_left, inner_smul_right]
  simp only [conj_trivial, RCLike.real_smul_eq_coe_smul, smul_eq_mul]
  ring

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Laplace form of the rounding integrand.** Away from the null set where a column vanishes,
the integrand of Lemma 2.1 equals `π⁻¹` times the inner product times the double Laplace integral of
`exp(-(s‖X‖² + t‖Y‖²))`. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by
  rw [reducedIntegrand_eq_inner_div]
  have hA : (0:ℝ) < ‖colFun r 0 W‖ ^ 2 := by positivity
  have hB : (0:ℝ) < ‖colFun r 1 W‖ ^ 2 := by positivity
  have hden : (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹
      = (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2))⁻¹ := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hden, laplace_inv_sqrt_mul_inv_sqrt hA hB]
  ring

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Laplace form of the rounding integrand, unconditionally.** Lean's convention `(0)⁻¹ = 0`
makes both sides vanish when a column vanishes, so no hypothesis is needed. -/
theorem reducedIntegrand_eq_pi_inv_mul_integral_all (r : ℕ)
    (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) := by
  by_cases hX : colFun r 0 W = 0
  · have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0 := by simp [hX]
    rw [hinner]
    simp [reducedIntegrand, normalize, hX]
  · by_cases hY : colFun r 1 W = 0
    · have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0 := by simp [hY]
      rw [hinner]
      simp [reducedIntegrand, normalize, hY]
    · exact reducedIntegrand_eq_pi_inv_mul_integral r W hX hY

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- **The Fubini majorant.** For a nonzero pair of columns, `‖X‖‖Y‖` times the double Laplace
integral of `e^{-(s‖X‖²+t‖Y‖²)}` is exactly `π`. -/
theorem laplace_integral_mul_norm_eq_pi {r : ℕ} (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hX : colFun r 0 W ≠ 0) (hY : colFun r 1 W ≠ 0) :
    (‖colFun r 0 W‖ * ‖colFun r 1 W‖) *
        (∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
          (s * t) ^ (-(1/2) : ℝ) *
            Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)))
      = Real.pi := by
  have hA : (0:ℝ) < ‖colFun r 0 W‖ ^ 2 := by positivity
  have hB : (0:ℝ) < ‖colFun r 1 W‖ ^ 2 := by positivity
  have hden : (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2))⁻¹
      = (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have hpi := laplace_inv_sqrt_mul_inv_sqrt hA hB
  rw [hden] at hpi
  have hpos : (0:ℝ) < ‖colFun r 0 W‖ * ‖colFun r 1 W‖ :=
    mul_pos (norm_pos_iff.mpr hX) (norm_pos_iff.mpr hY)
  field_simp at hpi ⊢
  linarith [hpi]

end Grothendieck

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

noncomputable def fubiniFactor (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (p : ℝ × ℝ) : ℝ :=
  (p.1 * p.2) ^ (-(1/2) : ℝ) *
    Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))

lemma fubiniFactor_apply (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) (s t : ℝ) :
    fubiniFactor r W (s, t) = (s * t) ^ (-(1/2) : ℝ) *
      Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := rfl

lemma fubiniIntegrand_eq_mul (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) (p : ℝ × ℝ) :
    fubiniIntegrand r W p = inner ℝ (colFun r 0 W) (colFun r 1 W) * fubiniFactor r W p := rfl

lemma integrable_fubiniFactor_of_ne_zero (r : ℕ) {W : Fin r → EuclideanSpace ℝ (Fin 2)}
    (hc : inner ℝ (colFun r 0 W) (colFun r 1 W) ≠ 0)
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    Integrable (fubiniFactor r W) planeMeasure := by
  have h1 : Integrable (fun p => (inner ℝ (colFun r 0 W) (colFun r 1 W))⁻¹ *
      fubiniIntegrand r W p) planeMeasure := hW.const_mul _
  refine h1.congr ?_
  filter_upwards with p
  rw [fubiniIntegrand_eq_mul]
  field_simp

theorem integral_fubiniIntegrand_eq_mul (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    ∫ p, fubiniIntegrand r W p ∂planeMeasure
      = inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := by
  by_cases hc : inner ℝ (colFun r 0 W) (colFun r 1 W) = 0
  · have hzero : ∀ p, fubiniIntegrand r W p = 0 := by
      intro p
      rw [fubiniIntegrand_eq_mul, hc, zero_mul]
    rw [hc, zero_mul]
    simp [hzero]
  · have hg : Integrable (fubiniFactor r W) planeMeasure :=
      integrable_fubiniFactor_of_ne_zero r hc hW
    have hprod : ∫ p, fubiniFactor r W p ∂planeMeasure
        = ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2)) := by
      rw [planeMeasure] at hg ⊢
      rw [integral_prod (f := fubiniFactor r W) hg]
      simp [fubiniFactor_apply]
    calc ∫ p, fubiniIntegrand r W p ∂planeMeasure
        = ∫ p, inner ℝ (colFun r 0 W) (colFun r 1 W) * fubiniFactor r W p ∂planeMeasure := by
          simp [fubiniIntegrand_eq_mul]
      _ = inner ℝ (colFun r 0 W) (colFun r 1 W) * ∫ p, fubiniFactor r W p ∂planeMeasure :=
          integral_const_mul _ _
      _ = _ := by rw [hprod]

theorem reducedIntegrand_eq_pi_inv_mul_integral_section (r : ℕ)
    (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (hW : Integrable (fun p => fubiniIntegrand r W p) planeMeasure) :
    reducedIntegrand r W = Real.pi⁻¹ * ∫ p, fubiniIntegrand r W p ∂planeMeasure := by
  rw [reducedIntegrand_eq_pi_inv_mul_integral_all, integral_fubiniIntegrand_eq_mul r W hW]

theorem fubini_swap_of_integrable (r : ℕ) {τ : ℝ}
    (hInt : Integrable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure)) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure := by
  have hsec : ∀ᵐ W ∂(reducedLaw r τ),
      Integrable (fun p => fubiniIntegrand r W p) planeMeasure :=
    hInt.prod_right_ae
  have hpoint : ∀ᵐ W ∂(reducedLaw r τ), reducedIntegrand r W
      = Real.pi⁻¹ * ∫ p, fubiniIntegrand r W p ∂planeMeasure := by
    filter_upwards [hsec] with W hW
    exact reducedIntegrand_eq_pi_inv_mul_integral_section r W hW
  calc ∫ W, reducedIntegrand r W ∂(reducedLaw r τ)
      = ∫ W, Real.pi⁻¹ * (∫ p, fubiniIntegrand r W p ∂planeMeasure)
          ∂(reducedLaw r τ) := integral_congr_ae hpoint
    _ = Real.pi⁻¹ * ∫ W, (∫ p, fubiniIntegrand r W p ∂planeMeasure)
          ∂(reducedLaw r τ) := integral_const_mul _ _
    _ = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ))
          ∂planeMeasure := by
        rw [integral_integral_swap hInt]

theorem measurable_colFun_apply (r : ℕ) (j : Fin 2) :
    Measurable (fun W : Fin r → EuclideanSpace ℝ (Fin 2) => colFun r j W) := by
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp j) := by
    have h : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin 2) → (Fin 2 → ℝ)) :=
      WithLp.measurable_ofLp (p := 2) (X := Fin 2 → ℝ)
    exact (measurable_pi_apply j).comp h
  unfold colFun
  refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
  exact measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

theorem measurable_uncurry_fubiniIntegrand (r : ℕ) :
    Measurable (Function.uncurry (fubiniIntegrand r)) := by
  have h0 : Measurable (fun a : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
      colFun r 0 a.1) := (measurable_colFun_apply r 0).comp measurable_fst
  have h1 : Measurable (fun a : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
      colFun r 1 a.1) := (measurable_colFun_apply r 1).comp measurable_fst
  unfold fubiniIntegrand Function.uncurry
  measurability

theorem integrable_fubiniIntegrand_of_bound (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure))
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    Integrable (Function.uncurry (fubiniIntegrand r)) ((reducedLaw r τ).prod planeMeasure) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hpi : ENNReal.ofReal Real.pi < (⊤ : ENNReal) := ENNReal.ofReal_lt_top
  refine lt_of_le_of_lt ?_ hpi
  simpa only [ofReal_norm] using hbound

theorem fubini_swap_of_bound (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure))
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_integrable r (integrable_fubiniIntegrand_of_bound r hmeas hbound)

theorem fubini_swap_of_lintegral_bound (r : ℕ) {τ : ℝ}
    (hbound : (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_bound r (measurable_uncurry_fubiniIntegrand r).aestronglyMeasurable hbound

noncomputable def fubiniMajorant (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2))
    (p : ℝ × ℝ) : ℝ :=
  ‖colFun r 0 W‖ * ‖colFun r 1 W‖ *
    ((p.1 * p.2) ^ (-(1/2) : ℝ) *
      Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)))

lemma planeMeasure_eq_prod :
    planeMeasure = (volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ))) :=
  rfl

lemma ae_planeMeasure_pos : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
  rw [ae_iff]
  have h : planeMeasure
      = (volume.prod volume).restrict (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) := by
    rw [planeMeasure_eq_prod, Measure.prod_restrict]
  rw [h, Measure.restrict_apply' (μ := volume.prod volume)
      (s := Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ))
      (t := {p : ℝ × ℝ | ¬ (0 < p.1 ∧ 0 < p.2)})
      (MeasurableSet.prod measurableSet_Ioi measurableSet_Ioi)]
  have hempty : {p : ℝ × ℝ | ¬ (0 < p.1 ∧ 0 < p.2)} ∩ (Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)) = ∅ := by
    ext p
    simp
  rw [hempty, measure_empty]

lemma lintegral_rpow_neg_half_exp_mul {C : ℝ} (hC : 0 < C) :
    (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))))
      = ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt C) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))
      (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      (fun u : ℝ => u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_pos_of_pos hu _).le (Real.exp_pos _).le
  have h := integral_eq_lintegral_of_nonneg_ae hnn hmeas
  rw [integral_rpow_neg_half_exp_mul hC] at h
  have hpos : (0:ℝ) < Real.sqrt Real.pi / Real.sqrt C :=
    div_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.sqrt_pos.mpr hC)
  have hne : (∫⁻ u in Set.Ioi (0:ℝ),
      ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    linarith
  calc (∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u))))
      = ENNReal.ofReal ((∫⁻ u in Set.Ioi (0:ℝ),
          ENNReal.ofReal (u ^ (-(1/2) : ℝ) * Real.exp (-(C * u)))).toReal) :=
        (ENNReal.ofReal_toReal hne).symm
    _ = ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt C) := by rw [← h]

lemma lintegral_laplace_kernel {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * A + p.2 * B))) ∂planeMeasure)
      = ENNReal.ofReal (Real.pi / (Real.sqrt A * Real.sqrt B)) := by
  have hgem : ∀ p : ℝ × ℝ, 0 < p.1 → 0 < p.2 →
      ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * Real.exp (-(p.1 * A + p.2 * B)))
        = ENNReal.ofReal (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          ENNReal.ofReal (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) := by
    intro p h1 h2
    have hg1 : 0 ≤ p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1)) :=
      mul_nonneg (Real.rpow_pos_of_pos h1 _).le (Real.exp_pos _).le
    have hg2 : 0 ≤ p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2)) :=
      mul_nonneg (Real.rpow_pos_of_pos h2 _).le (Real.exp_pos _).le
    have hval : (p.1 * p.2) ^ (-(1/2) : ℝ) * Real.exp (-(p.1 * A + p.2 * B))
        = (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) := by
      rw [Real.mul_rpow h1.le h2.le,
        show -(p.1 * A + p.2 * B) = -(A * p.1) + -(B * p.2) by ring, Real.exp_add]
      ring
    rw [hval, ENNReal.ofReal_mul hg1]
  have h1 : (∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * A + p.2 * B))) ∂planeMeasure)
      = ∫⁻ p, ENNReal.ofReal (p.1 ^ (-(1/2) : ℝ) * Real.exp (-(A * p.1))) *
          ENNReal.ofReal (p.2 ^ (-(1/2) : ℝ) * Real.exp (-(B * p.2))) ∂planeMeasure := by
    apply lintegral_congr_ae
    filter_upwards [ae_planeMeasure_pos] with p hp
    exact hgem p hp.1 hp.2
  rw [h1, planeMeasure_eq_prod,
    lintegral_prod_mul (f := fun s => ENNReal.ofReal (s ^ (-(1/2) : ℝ) * Real.exp (-(A * s))))
      (g := fun t => ENNReal.ofReal (t ^ (-(1/2) : ℝ) * Real.exp (-(B * t))))
      (by fun_prop) (by fun_prop),
    lintegral_rpow_neg_half_exp_mul hA, lintegral_rpow_neg_half_exp_mul hB,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.sqrt Real.pi / Real.sqrt A)]
  congr 1
  rw [div_mul_div_comm, Real.mul_self_sqrt Real.pi_pos.le]

lemma norm_fubiniIntegrand_le (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) {p : ℝ × ℝ}
    (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ‖fubiniIntegrand r W p‖ ≤ fubiniMajorant r W p := by
  have hfac_pos : 0 < (p.1 * p.2) ^ (-(1/2) : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos h1 h2) _
  have hexp_pos : 0 < Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)) :=
    Real.exp_pos _
  have hfac : ‖(p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))‖
      = (p.1 * p.2) ^ (-(1/2) : ℝ) *
        Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2)) := by
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos hfac_pos hexp_pos)]
  rw [fubiniIntegrand, fubiniMajorant, norm_mul, hfac]
  exact mul_le_mul_of_nonneg_right (norm_inner_le_norm (colFun r 0 W) (colFun r 1 W))
    (mul_nonneg hfac_pos.le hexp_pos.le)

lemma lintegral_majorant_W_le (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
      ≤ ENNReal.ofReal Real.pi := by
  by_cases hX : colFun r 0 W = 0
  · have hzero : ∀ p, fubiniMajorant r W p = 0 := by
      intro p
      simp [fubiniMajorant, hX]
    simp only [hzero]
    simp
  by_cases hY : colFun r 1 W = 0
  · have hzero : ∀ p, fubiniMajorant r W p = 0 := by
      intro p
      simp [fubiniMajorant, hY]
    simp only [hzero]
    simp
  have hXp : 0 < ‖colFun r 0 W‖ := norm_pos_iff.mpr hX
  have hYp : 0 < ‖colFun r 1 W‖ := norm_pos_iff.mpr hY
  have hc : 0 < ‖colFun r 0 W‖ * ‖colFun r 1 W‖ := mul_pos hXp hYp
  have hfac : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (fubiniMajorant r W p)
        = ENNReal.ofReal (‖colFun r 0 W‖ * ‖colFun r 1 W‖) *
          ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
            Real.exp (-(p.1 * ‖colFun r 0 W‖ ^ 2 + p.2 * ‖colFun r 1 W‖ ^ 2))) := by
    intro p
    rw [fubiniMajorant, ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hkey : ‖colFun r 0 W‖ * ‖colFun r 1 W‖ *
      (Real.pi / (Real.sqrt (‖colFun r 0 W‖ ^ 2) * Real.sqrt (‖colFun r 1 W‖ ^ 2)))
      = Real.pi := by
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    exact mul_div_cancel₀ _ (ne_of_gt hc)
  have hval : (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
      = ENNReal.ofReal Real.pi := by
    rw [lintegral_congr hfac, lintegral_const_mul _ (by fun_prop),
      lintegral_laplace_kernel (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)), hkey]
  exact hval.le

theorem lintegral_norm_fubiniIntegrand_le_pi (r : ℕ) {τ : ℝ} :
    (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure)) ≤ ENNReal.ofReal Real.pi := by
  have : SFinite planeMeasure := by
    rw [planeMeasure_eq_prod]
    infer_instance
  have hmeas : AEMeasurable
      (fun z : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) =>
        ENNReal.ofReal (fubiniMajorant r z.1 z.2))
      ((reducedLaw r τ).prod planeMeasure) := by
    apply Measurable.aemeasurable
    simp only [fubiniMajorant, colFun]
    fun_prop
  have hae : ∀ᵐ z ∂((reducedLaw r τ).prod planeMeasure), 0 < z.2.1 ∧ 0 < z.2.2 := by
    have hset : MeasurableSet
        {z : (Fin r → EuclideanSpace ℝ (Fin 2)) × (ℝ × ℝ) | 0 < z.2.1 ∧ 0 < z.2.2} := by
      measurability
    have h := (Measure.ae_prod_mem_iff_ae_ae_mem (μ := reducedLaw r τ) (ν := planeMeasure)
      hset).mpr (Filter.Eventually.of_forall fun _ => ae_planeMeasure_pos)
    simpa using h
  calc (∫⁻ z, ENNReal.ofReal ‖Function.uncurry (fubiniIntegrand r) z‖
        ∂((reducedLaw r τ).prod planeMeasure))
      ≤ ∫⁻ z, ENNReal.ofReal (fubiniMajorant r z.1 z.2)
          ∂((reducedLaw r τ).prod planeMeasure) := by
        apply lintegral_mono_ae
        filter_upwards [hae] with z hz
        exact ENNReal.ofReal_le_ofReal (norm_fubiniIntegrand_le r z.1 hz.1 hz.2)
    _ = ∫⁻ W, (∫⁻ p, ENNReal.ofReal (fubiniMajorant r W p) ∂planeMeasure)
          ∂(reducedLaw r τ) := by
        rw [lintegral_lintegral]
        exact hmeas
    _ ≤ ∫⁻ _W, ENNReal.ofReal Real.pi ∂(reducedLaw r τ) :=
        lintegral_mono fun W => lintegral_majorant_W_le r W
    _ = ENNReal.ofReal Real.pi := by
        rw [lintegral_const]
        have : IsProbabilityMeasure (reducedLaw r τ) := by
          unfold reducedLaw
          infer_instance
        simp

lemma integrable_fubiniIntegrand (r : ℕ) {τ : ℝ}
    (hmeas : AEStronglyMeasurable (Function.uncurry (fubiniIntegrand r))
      ((reducedLaw r τ).prod planeMeasure)) :
    Integrable (Function.uncurry (fubiniIntegrand r)) ((reducedLaw r τ).prod planeMeasure) := by
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact lt_of_le_of_lt (lintegral_norm_fubiniIntegrand_le_pi r) ENNReal.ofReal_lt_top

theorem fubini_swap_proof (r : ℕ) (τ : ℝ) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_lintegral_bound r (lintegral_norm_fubiniIntegrand_le_pi r)

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (τ : ℝ) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_proof r τ
