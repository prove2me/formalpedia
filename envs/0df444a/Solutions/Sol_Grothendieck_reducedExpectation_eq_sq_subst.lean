-- Prove2me | solution 1 for Grothendieck.reducedExpectation_eq_sq_subst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T20:58:15.706623+00:00
-- url     : https://prove2.me/submissions/2cd03d1e-772e-4341-8b04-b0e9c59ceb74

import Mathlib
import Definitions.Def_Grothendieck_Reduced
import Definitions.Def_Grothendieck_Fubini

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators Real Topology

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

theorem fubini_swap_proved (r : ℕ) (τ : ℝ) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure :=
  fubini_swap_of_lintegral_bound r (lintegral_norm_fubiniIntegrand_le_pi r)

end Grothendieck

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace

namespace Grothendieck

lemma isHermitian_corrMat (t : ℝ) : (corrMat t).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

lemma corrMat_posSemidef {t : ℝ} (ht : |t| ≤ 1) : (corrMat t).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_corrMat t) fun x => ?_
  simp only [star_trivial, Matrix.mulVec, dotProduct, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  have h1 : (0:ℝ) ≤ 1 - t^2 := by
    have := abs_le.mp ht
    nlinarith
  nlinarith [sq_nonneg (x 0 + t * x 1), sq_nonneg (x 1), h1, mul_nonneg h1 (sq_nonneg (x 1))]

/-- The one-dimensional Gaussian integral of a complex exponential. -/
lemma integral_gaussian_exp (c : ℝ) :
    ∫ t : ℝ, Complex.exp (↑(t * c) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-↑(c ^ 2) / 2) := by
  simp only [← Real.inner_apply]
  rw [← charFun_apply, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.ofReal_pow]
  ring

lemma measurable_normalize (r : ℕ) : Measurable (normalize r) := by
  unfold normalize
  fun_prop

lemma measurable_colFun (r : ℕ) (j : Fin 2) : Measurable (colFun r j) := by
  unfold colFun
  fun_prop

lemma measurable_reducedIntegrand (r : ℕ) : Measurable (reducedIntegrand r) := by
  unfold reducedIntegrand
  exact Measurable.inner (measurable_normalize r |>.comp (measurable_colFun r 0))
    (measurable_normalize r |>.comp (measurable_colFun r 1))

/-- The reduced integrand in coordinates: the cosine of the angle between the two columns. -/
lemma reducedIntegrand_eq (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = (∑ i, (W i).ofLp 0 * (W i).ofLp 1) /
        (Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) * Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2)) := by
  have hinner : inner ℝ (colFun r 0 W) (colFun r 1 W)
      = ∑ i, (W i).ofLp 0 * (W i).ofLp 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial, colFun, WithLp.ofLp_toLp]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hn0 : ‖colFun r 0 W‖ = Real.sqrt (∑ i, ((W i).ofLp 0) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  have hn1 : ‖colFun r 1 W‖ = Real.sqrt (∑ i, ((W i).ofLp 1) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.real_norm_sq_eq]
    simp [colFun]
  unfold reducedIntegrand normalize
  rw [real_inner_smul_left, real_inner_smul_right, hinner, hn0, hn1]
  rw [inv_mul_eq_div, inv_mul_eq_div, div_div, mul_comm]

lemma measurable_cholMap (t : ℝ) : Measurable (cholMap t) := by
  unfold cholMap
  refine (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp ?_
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> simp <;> fun_prop

lemma inner_cholMap (t : ℝ) (y z : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (cholMap t y) z = inner ℝ y (cholAdj t z) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, cholMap, cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  ring

lemma norm_sq_cholAdj {t : ℝ} (ht : |t| ≤ 1) (z : EuclideanSpace ℝ (Fin 2)) :
    ‖cholAdj t z‖ ^ 2 = z.ofLp ⬝ᵥ (corrMat t).mulVec z.ofLp := by
  have h1 : (0:ℝ) ≤ 1 - t ^ 2 := by
    have := abs_le.mp ht
    nlinarith
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [cholAdj, WithLp.ofLp_toLp, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one]
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, corrMat_apply_zero_zero,
    corrMat_apply_zero_one, corrMat_apply_one_zero, corrMat_apply_one_one]
  rw [mul_pow, Real.sq_sqrt h1]
  ring

/-- **The correlation law in Cholesky form**: the two-dimensional Gaussian with covariance
`!![1,t;t,1]` is the law of `(y₀, t y₀ + √(1-t²) y₁)` for a standard Gaussian `y ∈ ℝ²`. -/
lemma map_cholMap_stdGaussian {t : ℝ} (ht : |t| ≤ 1) :
    Measure.map (cholMap t) (stdGaussian (EuclideanSpace ℝ (Fin 2)))
      = multivariateGaussian 0 (corrMat t) := by
  have hS : (corrMat t).PosSemidef := corrMat_posSemidef ht
  apply Measure.ext_of_charFun
  ext z
  rw [charFun_multivariateGaussian hS]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero]
  rw [charFun_apply]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) =>
      Complex.exp (↑⟪y, z⟫ * Complex.I) := by fun_prop
  rw [integral_map (measurable_cholMap t).aemeasurable hcont.aestronglyMeasurable]
  simp only [inner_cholMap]
  rw [← charFun_apply, charFun_stdGaussian]
  congr 1
  rw [← Complex.ofReal_pow, norm_sq_cholAdj ht]
  push_cast
  ring

theorem integral_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-c * x ^ 2)) = Real.sqrt (Real.pi / c) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ) hc
  rw [Module.finrank_self] at h
  simp only [Nat.cast_one, one_div] at h
  have h' : (∫ x : ℝ, Real.exp (-c * x ^ 2)) = ∫ x : ℝ, Real.exp (-c * ‖x‖ ^ 2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  rw [h', h, show (2:ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]

theorem integral_sq_mul_exp_neg_mul_sq_half {c : ℝ} (hc : 0 < c) :
    (∫ x in Set.Ioi (0:ℝ), x ^ 2 * Real.exp (-(c * x ^ 2)))
      = Real.sqrt Real.pi / (4 * c ^ ((3:ℝ)/2)) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := c)
    (by norm_num) (by norm_num) hc
  have e1 : (-(2 + 1) / 2 : ℝ) = -(3/2) := by norm_num
  have e2 : ((2 + 1) / 2 : ℝ) = 3/2 := by norm_num
  rw [e1, e2] at h
  have hΓ : Real.Gamma (3/2 : ℝ) = Real.sqrt Real.pi / 2 := by
    have h1 := Real.Gamma_add_one (s := (1/2 : ℝ)) (by norm_num)
    rw [show (1/2 : ℝ) + 1 = 3/2 by norm_num, Real.Gamma_one_half_eq] at h1
    linarith
  rw [hΓ] at h
  have h' : (∫ x in Set.Ioi (0:ℝ), x ^ 2 * Real.exp (-(c * x ^ 2)))
      = c ^ (-(3/2) : ℝ) * (1/2) * (Real.sqrt Real.pi / 2) := by
    simpa only [Real.rpow_two, neg_mul] using h
  rw [h', Real.rpow_neg (le_of_lt hc)]
  have hc32 : (0:ℝ) < c ^ ((3:ℝ)/2) := Real.rpow_pos_of_pos hc _
  field_simp
  ring

/-- `∫_ℝ x² e^{-c x²} dx = √π/(2 c^{3/2})`. -/
theorem integral_sq_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-(c * x ^ 2)))
      = Real.sqrt Real.pi / (2 * c ^ ((3:ℝ)/2)) := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2)))
  rw [integral_sq_mul_exp_neg_mul_sq_half hc] at h
  have h' : (∫ x : ℝ, (fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2))) |x|)
      = ∫ x : ℝ, x ^ 2 * Real.exp (-(c * x ^ 2)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sq_abs]
  rw [h'] at h
  rw [h]
  ring

/-- `∫_ℝ x e^{-c x²} dx = 0` (`c > 0`): the integrand is odd. -/
theorem integral_x_mul_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, x * Real.exp (-(c * x ^ 2))) = 0 := by
  have hInt : Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq hc (s := (1:ℝ)) (by norm_num)
    simpa only [Real.rpow_one, neg_mul] using h
  have hsplit := integral_add_compl (μ := volume) (s := Set.Ioi (0:ℝ)) measurableSet_Ioi hInt
  have hneg : (∫ x in (Set.Ioi (0:ℝ))ᶜ, x * Real.exp (-(c * x ^ 2)))
      = -(∫ x in Set.Ioi (0:ℝ), x * Real.exp (-(c * x ^ 2))) := by
    have hc' : (Set.Ioi (0:ℝ))ᶜ = Set.Iic 0 := by rw [Set.compl_Ioi]
    rw [hc']
    have h := integral_comp_neg_Iic (c := 0) (f := fun x : ℝ => x * Real.exp (-(c * x ^ 2)))
    simp only [neg_zero] at h
    rw [← h]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Iic (fun x _ => ?_)
    simp only [neg_sq]
    ring
  rw [hneg] at hsplit
  linarith

end Grothendieck

set_option maxHeartbeats 2000000

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace NNReal

namespace Grothendieck

theorem integral_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-(c * x ^ 2))) = Real.sqrt (Real.pi / c) := by
  simpa only [neg_mul] using integral_exp_neg_mul_sq hc

theorem integrable_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * x ^ 2))) volume := by
  simpa only [neg_mul] using integrable_exp_neg_mul_sq hc

theorem integrable_mul_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) volume := by
  simpa only [neg_mul, Real.rpow_one] using
    integrable_rpow_mul_exp_neg_mul_sq hc (s := (1:ℝ)) (by norm_num)

/-- The row map `p ↦ cholMap τ (p.1, p.2)`: the Cholesky parametrisation of one row. -/
def rowMap (t : ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  cholMap t (WithLp.toLp 2 ![p.1, p.2])

@[simp] lemma rowMap_ofLp_zero (t : ℝ) (p : ℝ × ℝ) : (rowMap t p).ofLp 0 = p.1 := rfl
@[simp] lemma rowMap_ofLp_one (t : ℝ) (p : ℝ × ℝ) :
    (rowMap t p).ofLp 1 = t * p.1 + Real.sqrt (1 - t ^ 2) * p.2 := rfl

lemma measurable_toLp_pair : Measurable (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2]) := by
  fun_prop

/-- The standard Gaussian on `ℝ²` as the law of a pair of independent standard Gaussians. -/
lemma stdGaussian_fin_two_eq_map_prod :
    stdGaussian (EuclideanSpace ℝ (Fin 2))
      = Measure.map (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hm1 := Measure.map_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g := WithLp.toLp 2)
    (f := fun p : ℝ × ℝ => (MeasurableEquiv.finTwoArrow (α := ℝ)).symm p)
    (WithLp.measurable_toLp 2 (Fin 2 → ℝ)) (MeasurableEquiv.measurable _)
  have hfun : (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
      = (WithLp.toLp 2) ∘ fun p : ℝ × ℝ => (MeasurableEquiv.finTwoArrow (α := ℝ)).symm p := by
    funext p
    simp only [Function.comp_apply]
    congr 1
  rw [hfun]
  rw [← hm1]
  rw [(measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.map_eq]
  rw [map_pi_eq_stdGaussian (ι := Fin 2)]

lemma measurable_rowMap (t : ℝ) : Measurable (rowMap t) :=
  (measurable_cholMap t).comp measurable_toLp_pair

/-- **The single row law**: the two-dimensional Gaussian with covariance `!![1,t;t,1]` is the
law of `(p.1, t p.1 + √(1-t²) p.2)` for a pair of independent standard Gaussians. -/
theorem rowLaw_eq {t : ℝ} (ht : |t| ≤ 1) :
    Measure.map (rowMap t) ((gaussianReal 0 1).prod (gaussianReal 0 1))
      = multivariateGaussian 0 (corrMat t) := by
  have h := Measure.map_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (g := cholMap t) (f := fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])
    (measurable_cholMap t) measurable_toLp_pair
  change Measure.map ((cholMap t) ∘
    (fun p : ℝ × ℝ => WithLp.toLp 2 ![p.1, p.2])) _ = _
  rw [← h, ← stdGaussian_fin_two_eq_map_prod, map_cholMap_stdGaussian ht]

lemma gaussianPDFReal_zero_one_apply (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  norm_num

/-- Integration against the standard Gaussian, written through its Lebesgue density. -/
lemma integral_gaussianReal_zero_one_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * f x := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top) f]
  simp only [ProbabilityTheory.gaussianPDF.eq_1,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]

/-- The standard Gaussian weight is a bounded factor: `gaussianPDFReal 0 1 x * e^{-c x²}` is a
constant times `e^{-(c+1/2)x²}`. -/
lemma gaussianPDFReal_zero_one_mul_exp (c x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-(c * x ^ 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((c + 1 / 2) * x ^ 2)) := by
  rw [gaussianPDFReal_zero_one_apply, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- `x ↦ e^{-c x²}` is integrable against the standard Gaussian as soon as `c > -1/2`. -/
theorem integrable_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-((c + 1 / 2) * x ^ 2))) volume := by
    have h := (integrable_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)).const_mul
      ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- `x ↦ x * e^{-c x²}` is integrable against the standard Gaussian when `c > -1/2`. -/
theorem integrable_mul_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => x * Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (x * Real.exp (-((c + 1 / 2) * x ^ 2)))) volume := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)
      (s := (1:ℝ)) (by norm_num)).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul, Real.rpow_one] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- `x ↦ x² * e^{-c x²}` is integrable against the standard Gaussian when `c > -1/2`. -/
theorem integrable_sq_mul_exp_neg_mul_sq_gaussianReal {c : ℝ} (hc : -(1 / 2 : ℝ) < c) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(c * x ^ 2))) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  have hbase : Integrable (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      (x ^ 2 * Real.exp (-((c + 1 / 2) * x ^ 2)))) volume := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq (by linarith : (0:ℝ) < c + 1 / 2)
      (s := (2:ℝ)) (by norm_num)).const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
    simpa only [neg_mul, Real.rpow_two] using h
  refine hbase.congr (Filter.Eventually.of_forall fun x => ?_)
  have hexp : Real.exp (-((c + 1 / 2) * x ^ 2))
      = Real.exp (-x ^ 2 / 2) * Real.exp (-(c * x ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [ProbabilityTheory.gaussianPDF.eq_1, smul_eq_mul, gaussianPDFReal_zero_one_apply]
  rw [ENNReal.toReal_ofReal (by positivity), hexp]
  ring

/-- **Two-dimensional integration against `γ × γ` as an iterated Lebesgue integral.** -/
theorem integral_prod_gaussianReal_eq (G : ℝ × ℝ → ℝ)
    (hG : Integrable G ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    ∫ z, G z ∂((gaussianReal 0 1).prod (gaussianReal 0 1))
      = ∫ p, ∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) * G (p, q) := by
  rw [integral_prod _ hG]
  simp_rw [integral_gaussianReal_zero_one_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  ring

/-- `∫ q, e^{-(D q² + 2 B p q)} = √(π/D) e^{B²p²/D}` for `D > 0`. -/
theorem integral_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    (∫ q : ℝ, Real.exp (-(D * q ^ 2 + 2 * B * p * q)))
      = Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D) := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have key2 : ∀ q : ℝ, Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) * Real.exp (-(D * (q + B * p / D) ^ 2)) := by
    intro q
    rw [key q, Real.exp_add, mul_comm]
  simp_rw [key2]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add_right_eq_self (μ := volume)
      (f := fun u : ℝ => Real.exp (-(D * u ^ 2))) (B * p / D),
    integral_exp_neg_mul_sq_norm hD]
  ring

/-- `∫ q, q e^{-(D q² + 2 B p q)} = -(Bp/D) √(π/D) e^{B²p²/D}` for `D > 0`. -/
theorem integral_mul_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    (∫ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))
      = -(B * p / D) * Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D) := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have key2 : ∀ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) *
        ((fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)
          - (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) := by
    intro q
    rw [key q]
    simp only
    rw [Real.exp_add]
    field_simp
    ring
  simp_rw [key2]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub]
  · rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add_right_eq_self (μ := volume)
        (f := fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (B * p / D),
      MeasureTheory.integral_add_right_eq_self (μ := volume)
        (f := fun u : ℝ => Real.exp (-(D * u ^ 2))) (B * p / D),
      integral_x_mul_exp_neg_mul_sq hD, integral_exp_neg_mul_sq_norm hD]
    ring
  · have h := (integrable_mul_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  · have h := ((integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))).const_mul
      (B * p / D)
    simpa only [sub_neg_eq_add, smul_eq_mul] using h

/-- `x² e^{-a x²} ≤ 2/a` for `a > 0`. -/
lemma sq_mul_exp_neg_le {a x : ℝ} (ha : 0 < a) :
    x ^ 2 * Real.exp (-(a * x ^ 2)) ≤ 2 / a := by
  have hpos : 0 < Real.exp (-(a * x ^ 2)) := Real.exp_pos _
  have hpos2 : 0 < Real.exp (a * x ^ 2 / 2) := Real.exp_pos _
  have h2a : (0:ℝ) < 2 / a := by positivity
  have key : x ^ 2 ≤ (2 / a) * Real.exp (a * x ^ 2 / 2) := by
    have h1 := Real.add_one_le_exp (a * x ^ 2 / 2)
    have h3 : (2 / a) * (a * x ^ 2 / 2 + 1) ≤ (2 / a) * Real.exp (a * x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left h1 h2a.le
    have h4 : (2 / a) * (a * x ^ 2 / 2 + 1) = x ^ 2 + 2 / a := by field_simp; try ring
    rw [h4] at h3
    linarith
  have hexp : Real.exp (a * x ^ 2 / 2) * Real.exp (-(a * x ^ 2))
      = Real.exp (-(a * x ^ 2 / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle1 : Real.exp (-(a * x ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x, ha.le]
  calc x ^ 2 * Real.exp (-(a * x ^ 2))
      ≤ ((2 / a) * Real.exp (a * x ^ 2 / 2)) * Real.exp (-(a * x ^ 2)) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ = (2 / a) * (Real.exp (a * x ^ 2 / 2) * Real.exp (-(a * x ^ 2))) := by ring
    _ = (2 / a) * Real.exp (-(a * x ^ 2 / 2)) := by rw [hexp]
    _ ≤ (2 / a) * 1 := mul_le_mul_of_nonneg_left hle1 h2a.le
    _ = 2 / a := by ring

/-- The moment integrand of one row is bounded by `(1/a + 1/b)/2`. -/
lemma abs_mul_le_exp_bound {a b τ σ p q : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |p * (τ * p + σ * q)| * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
      ≤ 1 / a + 1 / b := by
  set s := τ * p + σ * q with hs
  have hfac : Real.exp (-(a * p ^ 2 + b * s ^ 2))
      = Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2)) := by
    rw [show -(a * p ^ 2 + b * s ^ 2) = -(a * p ^ 2) + -(b * s ^ 2) by ring, Real.exp_add]
  have hp2 : p ^ 2 * Real.exp (-(a * p ^ 2)) ≤ 2 / a := sq_mul_exp_neg_le ha
  have hsq2 : s ^ 2 * Real.exp (-(b * s ^ 2)) ≤ 2 / b := sq_mul_exp_neg_le hb
  have h1 : |p * s| ≤ (p ^ 2 + s ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|p| - |s|), abs_nonneg p, abs_nonneg s, sq_abs p, sq_abs s]
  have hlea : Real.exp (-(a * p ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg p, ha.le]
  have hleb : Real.exp (-(b * s ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg s, hb.le]
  have hEa : (0:ℝ) ≤ Real.exp (-(a * p ^ 2)) := (Real.exp_pos _).le
  have hEb : (0:ℝ) ≤ Real.exp (-(b * s ^ 2)) := (Real.exp_pos _).le
  have e1 : (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) ≤ (2 / a) * 1 :=
    mul_le_mul hp2 hleb hEb (by positivity)
  have e2 : (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) ≤ (2 / b) * 1 :=
    mul_le_mul hsq2 hlea hEa (by positivity)
  have hsplit : ((p ^ 2 + s ^ 2) / 2) * (Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2)))
      = (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) / 2
        + (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) / 2 := by ring
  calc |p * s| * Real.exp (-(a * p ^ 2 + b * s ^ 2))
      ≤ ((p ^ 2 + s ^ 2) / 2) * (Real.exp (-(a * p ^ 2)) * Real.exp (-(b * s ^ 2))) :=
        mul_le_mul h1 (le_of_eq hfac) (Real.exp_pos (-(a * p ^ 2 + b * s ^ 2))).le (by positivity)
    _ = (p ^ 2 * Real.exp (-(a * p ^ 2))) * Real.exp (-(b * s ^ 2)) / 2
        + (s ^ 2 * Real.exp (-(b * s ^ 2))) * Real.exp (-(a * p ^ 2)) / 2 := hsplit
    _ ≤ (2 / a) * 1 / 2 + (2 / b) * 1 / 2 := by linarith [e1, e2]
    _ = 1 / a + 1 / b := by field_simp

/-- **The mass of the tilted two-dimensional Gaussian.** For `a, b > 0` and `|τ| < 1`,
`E[e^{-a ξ² - b η²}] = ((1+2a)(1+2b) - 4τ²ab)^{-1/2}` for `(ξ,η) ~ N(0, !![1,τ;τ,1])`. -/
theorem integral_rowLaw_mass {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : τ ^ 2 < 1) :
    (∫ w : EuclideanSpace ℝ (Fin 2),
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
        ∂(multivariateGaussian 0 (corrMat τ)))
      = ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(1 / 2) : ℝ) := by
  set σ := Real.sqrt (1 - τ ^ 2) with hσdef
  have hσ2 : σ ^ 2 = 1 - τ ^ 2 := by
    rw [hσdef]; exact Real.sq_sqrt (by linarith)
  set D := 1 / 2 + b * σ ^ 2 with hDdef
  set B := b * τ * σ with hBdef
  set A₁ := a + b * τ ^ 2 - B ^ 2 / D with hA₁def
  set A₂ := A₁ + 1 / 2 with hA₂def
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDA : D * A₂ = K / 4 := by
    have hDne : D ≠ 0 := hDpos.ne'
    have hB2 : B ^ 2 = b ^ 2 * τ ^ 2 * (1 - τ ^ 2) := by
      rw [hBdef, mul_pow, mul_pow, hσ2]
    have hexp : D * A₂ = D * (a + b * τ ^ 2 + 1 / 2) - B ^ 2 := by
      rw [hA₂def, hA₁def]; field_simp; ring
    rw [hexp, hB2, hKdef, hDdef, hσ2]; ring
  have hKpos : 0 < K := by
    have hab : 0 < a * b := mul_pos ha hb
    have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
    rw [hKdef]; nlinarith [h1, ha, hb]
  have hA₂pos : 0 < A₂ := by
    have h4 : (0:ℝ) < K / 4 := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [hDA, hDpos, mul_nonpos_of_nonneg_of_nonpos hDpos.le hcon]
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  -- 1. the row law is the Cholesky image of `γ × γ`
  rw [← rowLaw_eq hτ1]
  rw [integral_map (measurable_rowMap τ).aemeasurable]
  simp only [rowMap_ofLp_zero, rowMap_ofLp_one, ← hσdef]
  · -- 2. iterated Lebesgue form
    rw [integral_prod_gaussianReal_eq _ ?hInt]
    · -- 3. the inner integral
      have hinner : ∀ p : ℝ,
          (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
          = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2)) := by
        intro p
        have hpoint : ∀ q : ℝ, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
            Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
            = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
          intro q
          have h1 : gaussianPDFReal 0 1 q
              = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2) := by
            rw [gaussianPDFReal_zero_one_apply]
          rw [h1]
          have hexp : Real.exp (-(q ^ 2) / 2) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            simp only [hDdef, hBdef]
            ring
          rw [show gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2)) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                (Real.exp (-(q ^ 2) / 2) *
                  Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))) by ring]
          rw [hexp]
          ring
        calc (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
            = ∫ q, (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
              exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                ∫ q, Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
              rw [MeasureTheory.integral_const_mul]
          _ = (gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-((a + b * τ ^ 2) * p ^ 2)))) *
                (Real.sqrt (Real.pi / D) * Real.exp (B ^ 2 * p ^ 2 / D)) := by
              rw [integral_exp_neg_quadratic_linear hDpos]
          _ = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
                Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2)) := by
              rw [hA₁def]
              have hE : Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (B ^ 2 * p ^ 2 / D)
                  = Real.exp (-((a + b * τ ^ 2 - B ^ 2 / D) * p ^ 2)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [← hE]; ring
      -- 4. the outer integral
      have houter : (∫ p, gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2)))
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂) := by
        have h1 : ∀ p : ℝ, gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2))
            = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(A₂ * p ^ 2)) := by
          intro p
          rw [gaussianPDFReal_zero_one_apply, mul_assoc, ← Real.exp_add]
          congr 2
          rw [hA₂def]; ring
        simp only [h1]
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_sq_norm hA₂pos]
      have h2 : ∀ p : ℝ, gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi / D) * Real.exp (-(A₁ * p ^ 2))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D)) *
            (gaussianPDFReal 0 1 p * Real.exp (-(A₁ * p ^ 2))) := by
        intro p; ring
      simp only [hinner, h2]
      rw [MeasureTheory.integral_const_mul, houter]
      -- 5. the constant
      have hsq : Real.sqrt (Real.pi / D) * Real.sqrt (Real.pi / A₂)
          = Real.pi / Real.sqrt (D * A₂) := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show Real.pi / D * (Real.pi / A₂) = Real.pi ^ 2 / (D * A₂) by field_simp]
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq Real.pi_pos.le]
      have hconst : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂))
          = 1 / (2 * Real.sqrt (D * A₂)) := by
        have hsq2 : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
          Real.mul_self_sqrt (by positivity)
        have hD2 : Real.sqrt (D * A₂) * Real.sqrt (D * A₂) = D * A₂ :=
          Real.mul_self_sqrt (by positivity)
        have hne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        have hne2 : Real.sqrt (D * A₂) ≠ 0 :=
          (Real.sqrt_pos.mpr (mul_pos hDpos hA₂pos)).ne'
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        rw [show (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / A₂))
            = (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.sqrt (Real.pi / D) * Real.sqrt (Real.pi / A₂)) by
              rw [mul_inv]; ring]
        rw [hsq2, hsq]
        field_simp
      rw [hconst]
      have hK4' : Real.sqrt K = 2 * Real.sqrt (D * A₂) := by
        rw [show K = 4 * (D * A₂) by rw [hDA]; ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
      rw [← hK4']
      rw [Real.rpow_neg hKpos.le, ← Real.sqrt_eq_rpow]
      norm_num
    · -- integrability of the composite mass integrand
      refine Integrable.mono (integrable_const (1:ℝ))
        (by fun_prop : Measurable (fun z : ℝ × ℝ =>
          Real.exp (-(a * z.1 ^ 2 + b * (τ * z.1 + σ * z.2) ^ 2)))).aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_one]
      exact Real.exp_le_one_iff.mpr
        (by nlinarith [sq_nonneg z.1, sq_nonneg (τ * z.1 + σ * z.2), ha.le, hb.le])
  · exact (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable

/-- Integrability of `q ↦ e^{-(Dq²+2Bpq)}` on the line. -/
theorem integrable_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    Integrable (fun q : ℝ => Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D := by
    intro q; field_simp; ring
  have hbase : Integrable (fun q : ℝ => Real.exp (-(D * (q + B * p / D) ^ 2))) volume := by
    have h := (integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  refine (hbase.const_mul (Real.exp (B ^ 2 * p ^ 2 / D))).congr ?_
  filter_upwards with q
  rw [key q, Real.exp_add]
  ring

/-- Integrability of `q ↦ q e^{-(Dq²+2Bpq)}` on the line. -/
theorem integrable_mul_exp_neg_quadratic_linear {D B p : ℝ} (hD : 0 < D) :
    Integrable (fun q : ℝ => q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume := by
  have hDne : D ≠ 0 := hD.ne'
  have key : ∀ q : ℝ, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))
      = Real.exp (B ^ 2 * p ^ 2 / D) *
        ((fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)
          - (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) := by
    intro q
    rw [show -(D * q ^ 2 + 2 * B * p * q)
      = -(D * (q + B * p / D) ^ 2) + B ^ 2 * p ^ 2 / D by field_simp; ring]
    simp only
    rw [Real.exp_add]
    field_simp
    ring
  have h1 : Integrable (fun q : ℝ =>
      (fun u : ℝ => u * Real.exp (-(D * u ^ 2))) (q + B * p / D)) volume := by
    have h := (integrable_mul_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))
    simpa only [sub_neg_eq_add] using h
  have h2 : Integrable (fun q : ℝ =>
      (B * p / D) * (fun u : ℝ => Real.exp (-(D * u ^ 2))) (q + B * p / D)) volume := by
    have h := ((integrable_exp_neg_mul_sq_norm hD).comp_sub_right (-(B * p / D))).const_mul
      (B * p / D)
    simpa only [sub_neg_eq_add, smul_eq_mul] using h
  refine ((h1.sub h2).const_mul (Real.exp (B ^ 2 * p ^ 2 / D))).congr ?_
  filter_upwards with q
  exact (key q).symm

/-- **The first moment of the tilted two-dimensional Gaussian.** For `a, b > 0`, `|τ| < 1`,
`E[ξη e^{-a ξ² - b η²}] = τ ((1+2a)(1+2b) - 4τ²ab)^{-3/2}`. -/
theorem integral_rowLaw_moment {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : τ ^ 2 < 1) :
    (∫ w : EuclideanSpace ℝ (Fin 2),
        (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
        ∂(multivariateGaussian 0 (corrMat τ)))
      = τ * ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(3 / 2) : ℝ) := by
  set σ := Real.sqrt (1 - τ ^ 2) with hσdef
  have hσ2 : σ ^ 2 = 1 - τ ^ 2 := by
    rw [hσdef]; exact Real.sq_sqrt (by linarith)
  set D := 1 / 2 + b * σ ^ 2 with hDdef
  set B := b * τ * σ with hBdef
  set A₁ := a + b * τ ^ 2 - B ^ 2 / D with hA₁def
  set A₂ := A₁ + 1 / 2 with hA₂def
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDA : D * A₂ = K / 4 := by
    have hDne : D ≠ 0 := hDpos.ne'
    have hB2 : B ^ 2 = b ^ 2 * τ ^ 2 * (1 - τ ^ 2) := by
      rw [hBdef, mul_pow, mul_pow, hσ2]
    have hexp : D * A₂ = D * (a + b * τ ^ 2 + 1 / 2) - B ^ 2 := by
      rw [hA₂def, hA₁def]; field_simp; ring
    rw [hexp, hB2, hKdef, hDdef, hσ2]; ring
  have hKpos : 0 < K := by
    have hab : 0 < a * b := mul_pos ha hb
    have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
    rw [hKdef]; nlinarith [h1, ha, hb]
  have hA₂pos : 0 < A₂ := by
    have h4 : (0:ℝ) < K / 4 := by linarith
    by_contra hcon
    push_neg at hcon
    nlinarith [hDA, hDpos, mul_nonpos_of_nonneg_of_nonpos hDpos.le hcon]
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  rw [← rowLaw_eq hτ1]
  rw [integral_map (measurable_rowMap τ).aemeasurable]
  simp only [rowMap_ofLp_zero, rowMap_ofLp_one, ← hσdef]
  · rw [integral_prod_gaussianReal_eq _ ?hInt]
    · have hinner : ∀ p : ℝ,
          (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))))
          = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))) := by
        intro p
        have hpt : ∀ q : ℝ,
            Real.exp (-(q ^ 2) / 2) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))
              = Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (-(D * q ^ 2 + 2 * B * p * q)) := by
          intro q
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          simp only [hDdef, hBdef]
          ring
        have hpoint : ∀ q : ℝ, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
            ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
            = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              ((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  Real.exp (-(D * q ^ 2 + 2 * B * p * q))
               + (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) := by
          intro q
          have h1 : gaussianPDFReal 0 1 q
              = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2) := by
            rw [gaussianPDFReal_zero_one_apply]
          rw [h1,
            show gaussianPDFReal 0 1 p * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(q ^ 2) / 2)) *
                ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))
              = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
                ((p * (τ * p + σ * q)) * (Real.exp (-(q ^ 2) / 2) *
                  Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2)))) by ring,
            hpt q]
          ring
        have hInt1 : Integrable (fun q : ℝ =>
            (p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
              Real.exp (-(D * q ^ 2 + 2 * B * p * q))) volume :=
          (integrable_exp_neg_quadratic_linear hDpos).const_mul _
        have hInt2 : Integrable (fun q : ℝ =>
            (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
              (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) volume :=
          (integrable_mul_exp_neg_quadratic_linear hDpos).const_mul _
        calc (∫ q, (gaussianPDFReal 0 1 p * gaussianPDFReal 0 1 q) *
              ((p * (τ * p + σ * q)) * Real.exp (-(a * p ^ 2 + b * (τ * p + σ * q) ^ 2))))
            = ∫ q, (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              ((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  Real.exp (-(D * q ^ 2 + 2 * B * p * q))
               + (p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (q * Real.exp (-(D * q ^ 2 + 2 * B * p * q)))) :=
              integral_congr_ae (Filter.Eventually.of_forall hpoint)
          _ = (gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹) *
              (((p ^ 2 * τ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (∫ q, Real.exp (-(D * q ^ 2 + 2 * B * p * q))))
               + ((p * σ * Real.exp (-((a + b * τ ^ 2) * p ^ 2))) *
                  (∫ q, q * Real.exp (-(D * q ^ 2 + 2 * B * p * q))))) := by
              rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hInt1 hInt2,
                MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          _ = gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
              Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))) := by
              have hE : Real.exp (-((a + b * τ ^ 2) * p ^ 2)) * Real.exp (B ^ 2 * p ^ 2 / D)
                  = Real.exp (-(A₁ * p ^ 2)) := by
                rw [hA₁def, ← Real.exp_add]; congr 1; ring
              rw [integral_exp_neg_quadratic_linear hDpos,
                integral_mul_exp_neg_quadratic_linear hDpos, ← hE]
              ring
      have h2 : ∀ p : ℝ, gaussianPDFReal 0 1 p * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.sqrt (Real.pi / D) * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / D)) *
            (gaussianPDFReal 0 1 p * (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))) := by
        intro p; ring
      simp only [hinner, h2]
      have houter : (∫ p, gaussianPDFReal 0 1 p *
            (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2))))
          = (τ - σ * B / D) * ((Real.sqrt (2 * Real.pi))⁻¹ *
              (Real.sqrt Real.pi / (2 * A₂ ^ ((3:ℝ)/2)))) := by
        have h1 : ∀ p : ℝ, gaussianPDFReal 0 1 p *
            (p ^ 2 * (τ - σ * B / D) * Real.exp (-(A₁ * p ^ 2)))
            = (τ - σ * B / D) * ((Real.sqrt (2 * Real.pi))⁻¹ *
                (p ^ 2 * Real.exp (-(A₂ * p ^ 2)))) := by
          intro p
          have hE : Real.exp (-(p ^ 2) / 2) * Real.exp (-(A₁ * p ^ 2))
              = Real.exp (-(A₂ * p ^ 2)) := by
            rw [← Real.exp_add]; congr 1; rw [hA₂def]; ring
          rw [gaussianPDFReal_zero_one_apply, ← hE]
          ring
        simp only [h1]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          integral_sq_mul_exp_neg_mul_sq hA₂pos]
      rw [MeasureTheory.integral_const_mul, houter]
      -- the constant
      have hτB : τ - σ * B / D = τ / (2 * D) := by
        rw [hBdef, hDdef]
        have hDne : (1/2 + b * σ ^ 2) ≠ 0 := by positivity
        field_simp
        nlinarith [hσ2]
      rw [hτB]
      have hsqrt_div : Real.sqrt (Real.pi / D) = Real.sqrt Real.pi / Real.sqrt D :=
        Real.sqrt_div Real.pi_pos.le D
      have hA23 : A₂ ^ ((3:ℝ)/2) = A₂ * Real.sqrt A₂ := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hA₂pos, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have h1pi : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
        Real.mul_self_sqrt (by positivity)
      have h2pi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
        Real.mul_self_sqrt Real.pi_pos.le
      have h3D : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
      have h4A : Real.sqrt A₂ * Real.sqrt A₂ = A₂ := Real.mul_self_sqrt hA₂pos.le
      have h4pos : (0:ℝ) < 4 * (D * A₂) := by positivity
      have hK4 : K = 4 * (D * A₂) := by rw [hDA]; ring
      rw [hK4]
      -- substitute the square roots by atoms
      set sd := Real.sqrt D with hsd
      set sa := Real.sqrt A₂ with hsa
      set sv := Real.sqrt Real.pi with hsv
      set su := Real.sqrt (2 * Real.pi) with hsu
      have hDeq : D = sd * sd := by
        rw [hsd]; exact (Real.mul_self_sqrt hDpos.le).symm
      have hAeq : A₂ = sa * sa := by
        rw [hsa]; exact (Real.mul_self_sqrt hA₂pos.le).symm
      have hA23 : A₂ ^ ((3:ℝ)/2) = A₂ * sa := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add hA₂pos, Real.rpow_one, hsa,
          Real.sqrt_eq_rpow]
      have hseq : (D * A₂) ^ ((3:ℝ)/2) = D * sd * (A₂ * sa) := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num,
          Real.rpow_add (by positivity : (0:ℝ) < D * A₂), Real.rpow_one,
          Real.mul_rpow hDpos.le hA₂pos.le, hsd, hsa, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        ring
      have h4pow : (4:ℝ) ^ ((3:ℝ)/2) = 8 := by
        rw [show ((3:ℝ)/2) = 1 + 1/2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
          show (4:ℝ) ^ ((1:ℝ)/2) = 2 by rw [← Real.sqrt_eq_rpow]; norm_num]
        norm_num
      have h4pos : (0:ℝ) < 4 * (D * A₂) := by positivity
      rw [Real.rpow_neg h4pos.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (le_of_lt (mul_pos hDpos hA₂pos)), h4pow, hseq,
        hsqrt_div, hA23]
      rw [hDeq, hAeq]
      have hsvv : sv * sv = Real.pi := by rw [hsv]; exact Real.mul_self_sqrt Real.pi_pos.le
      have hsuu : su * su = 2 * Real.pi := by rw [hsu]; exact Real.mul_self_sqrt (by positivity)
      have hsdne : sd ≠ 0 := by
        rw [hsd]; exact (Real.sqrt_pos.mpr hDpos).ne'
      have hsane : sa ≠ 0 := by
        rw [hsa]; exact (Real.sqrt_pos.mpr hA₂pos).ne'
      have hsvne : sv ≠ 0 := by
        rw [hsv]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
      have hsune : su ≠ 0 := by
        rw [hsu]; exact (Real.sqrt_pos.mpr (by positivity)).ne'
      have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
      have hsvv' : sv ^ 2 = Real.pi := by rw [sq, hsvv]
      have hsuu' : su ^ 2 = 2 * Real.pi := by rw [sq, hsuu]
      field_simp
      rw [hsvv', hsuu']
      ring
    · refine Integrable.mono (integrable_const (1 / a + 1 / b))
        (by fun_prop : Measurable (fun z : ℝ × ℝ =>
          (z.1 * (τ * z.1 + σ * z.2)) *
            Real.exp (-(a * z.1 ^ 2 + b * (τ * z.1 + σ * z.2) ^ 2)))).aestronglyMeasurable ?_
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
        abs_of_pos (by positivity : (0:ℝ) < 1 / a + 1 / b)]
      exact abs_mul_le_exp_bound ha hb
  · exact (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) *
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable

end Grothendieck

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace NNReal

namespace Grothendieck

theorem isProb_multivariateGaussian (μ : EuclideanSpace ℝ (Fin 2))
    (S : Matrix (Fin 2) (Fin 2) ℝ) :
    IsProbabilityMeasure (multivariateGaussian μ S) :=
  (inferInstance : IsGaussian (multivariateGaussian μ S)).toIsProbabilityMeasure

/-- Integrability of the row mass factor against the row law. -/
theorem integrable_row_exp {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
      (multivariateGaussian 0 (corrMat τ)) := by
  haveI := isProb_multivariateGaussian 0 (corrMat τ)
  refine Integrable.mono (integrable_const (1:ℝ))
    (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_one]
  exact Real.exp_le_one_iff.mpr
    (by nlinarith [sq_nonneg (w.ofLp 0), sq_nonneg (w.ofLp 1), ha.le, hb.le])

/-- Integrability of the row moment factor against the row law. -/
theorem integrable_row_moment {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
      (multivariateGaussian 0 (corrMat τ)) := by
  haveI := isProb_multivariateGaussian 0 (corrMat τ)
  refine Integrable.mono (integrable_const (1 / a + 1 / b))
    (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin 2) =>
      (w.ofLp 0 * w.ofLp 1) *
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))).aestronglyMeasurable ?_
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / a + 1 / b)]
  have h := abs_mul_le_exp_bound (a := a) (b := b) (τ := 0) (σ := 1)
    (p := w.ofLp 0) (q := w.ofLp 1) ha hb
  simpa using h

/-- **The row Fubini (step (i) of Leaf 1).** For `r ≥ 1`, `|τ| < 1`, `a, b > 0`,
`∫ W, ⟨col W 0, col W 1⟩ e^{-(a‖col W 0‖² + b‖col W 1‖²)} ∂(reducedLaw r τ)`
`= r · A · C^{r-1} = r τ C^{r+2}` with `C = ((1+2a)(1+2b) - 4τ²ab)^{-1/2}`. -/
theorem integral_reducedLaw_row {r : ℕ} {τ a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hτ : τ ^ 2 < 1) :
    (∫ W : Fin r → EuclideanSpace ℝ (Fin 2),
        (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
          Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
        ∂(reducedLaw r τ))
      = r * τ * ((1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b) ^ (-(((r : ℝ) + 2) / 2) : ℝ) := by
  classical
  set K := (1 + 2 * a) * (1 + 2 * b) - 4 * τ ^ 2 * a * b with hKdef
  have hτ1 : |τ| ≤ 1 := by
    have h : |τ| < 1 := by rw [abs_lt]; constructor <;> nlinarith [hτ]
    linarith
  have hμ : reducedLaw r τ = Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ)) :=
    rfl
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [reducedLaw]
  · -- pointwise decomposition
    have hpoint : ∀ W : Fin r → EuclideanSpace ℝ (Fin 2),
        (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
          Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
        = ∑ i, ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
            Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2)) := by
      intro W
      have hsum : a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2
          = ∑ i, (a * (W i).ofLp 0 ^ 2 + b * (W i).ofLp 1 ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
      have hexp : Real.exp (-(a * ∑ i, ((W i).ofLp 0) ^ 2 + b * ∑ i, ((W i).ofLp 1) ^ 2))
          = ∏ i, Real.exp (-(a * (W i).ofLp 0 ^ 2 + b * (W i).ofLp 1 ^ 2)) := by
        rw [hsum, ← Finset.sum_neg_distrib, ← Real.exp_sum]
      rw [hexp, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : (∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1))
          = (W i).ofLp 0 * (W i).ofLp 1 := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hji; simp [hji]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [Finset.prod_mul_distrib, h1]
    -- integrability of each summand
    have hφ : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
        (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (multivariateGaussian 0 (corrMat τ)) := integrable_row_moment ha hb
    have hψ : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (multivariateGaussian 0 (corrMat τ)) := integrable_row_exp ha hb
    have hInt : ∀ i : Fin r, Integrable (fun W : Fin r → EuclideanSpace ℝ (Fin 2) =>
        ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
          Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2)))
        (Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ))) := by
      intro i
      have h := Integrable.fintype_prod
        (μ := fun _ : Fin r => multivariateGaussian 0 (corrMat τ))
        (f := fun (j : Fin r) (w : EuclideanSpace ℝ (Fin 2)) =>
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
        (fun j => by
          by_cases hji : j = i
          · subst hji; simpa using hφ
          · simpa [hji] using hψ)
      simpa using h
    rw [hμ]
    simp only [hpoint]
    rw [MeasureTheory.integral_finset_sum]
    swap
    · intro i _
      exact hInt i
    -- each summand is a product integral
    have hval : ∀ i : Fin r,
        (∫ W : Fin r → EuclideanSpace ℝ (Fin 2),
          ∏ j, (if j = i then (W j).ofLp 0 * (W j).ofLp 1 else 1) *
            Real.exp (-(a * (W j).ofLp 0 ^ 2 + b * (W j).ofLp 1 ^ 2))
          ∂(Measure.pi (fun _ : Fin r => multivariateGaussian 0 (corrMat τ))))
        = τ * K ^ (-(3/2) : ℝ) * (K ^ (-(1/2) : ℝ)) ^ (r - 1) := by
      intro i
      rw [integral_fintype_prod_eq_prod
        (μ := fun _ : Fin r => multivariateGaussian 0 (corrMat τ))
        (f := fun (j : Fin r) (w : EuclideanSpace ℝ (Fin 2)) =>
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))]
      have hstep : ∀ j : Fin r, (∫ w : EuclideanSpace ℝ (Fin 2),
          (if j = i then (w.ofLp 0 * w.ofLp 1) else 1) *
            Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))
          ∂(multivariateGaussian 0 (corrMat τ)))
          = (if j = i then τ * K ^ (-(3/2) : ℝ) else K ^ (-(1/2) : ℝ)) := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp only [if_true]
          rw [show (fun w : EuclideanSpace ℝ (Fin 2) =>
              (w.ofLp 0 * w.ofLp 1) * Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2)))
              = (fun w => (w.ofLp 0 * w.ofLp 1) *
                Real.exp (-(a * (w.ofLp 0) ^ 2 + b * (w.ofLp 1) ^ 2))) from rfl,
            integral_rowLaw_moment ha hb hτ, hKdef]
        · subst_vars
          simp only [if_false, one_mul, hji]
          rw [integral_rowLaw_mass ha hb hτ, hKdef]
      simp only [hstep]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      have h1 : ∏ j ∈ Finset.univ.erase i, (if j = i then τ * K ^ (-(3/2) : ℝ) else K ^ (-(1/2) : ℝ))
          = ∏ _j ∈ Finset.univ.erase i, K ^ (-(1/2) : ℝ) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.ne_of_mem_erase hj)]
      rw [h1, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, if_pos rfl]
      ring
    simp only [hval]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- the constant
    have hKpos : 0 < K := by
      have hab : 0 < a * b := mul_pos ha hb
      have h1 : τ ^ 2 * (a * b) < 1 * (a * b) := mul_lt_mul_of_pos_right hτ hab
      rw [hKdef]; nlinarith [h1, ha, hb]
    have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      have : 1 ≤ r := hr
      push_cast [Nat.cast_sub this]
      ring
    rw [show (K ^ (-(1/2) : ℝ)) ^ (r - 1) = K ^ (-(1/2) * ((r - 1 : ℕ) : ℝ)) from by
      rw [← Real.rpow_natCast (K ^ (-(1/2) : ℝ)) (r - 1), ← Real.rpow_mul hKpos.le]]
    have hKadd := Real.rpow_add hKpos (-(3/2:ℝ)) (-(1/2) * ((r - 1 : ℕ) : ℝ))
    rw [mul_assoc τ, ← hKadd]
    have hexp : -(3/2 : ℝ) + -(1/2) * ((r : ℝ) - 1) = -(((r : ℝ) + 2) / 2) := by ring
    rw [hcast, hexp]
    ring

end Grothendieck

#print axioms Grothendieck.integral_reducedLaw_row

open MeasureTheory
open scoped BigOperators Real Topology

namespace Grothendieck

/-- The inner product of the two columns is the sum of coordinatewise products. -/
theorem inner_colFun (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (colFun r 0 W) (colFun r 1 W) = ∑ i, (W i).ofLp 0 * (W i).ofLp 1 := by
  simp [colFun, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- The squared norm of a column is the sum of the squares of its coordinates. -/
theorem norm_sq_colFun (r : ℕ) (j : Fin 2) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    ‖colFun r j W‖ ^ 2 = ∑ i, ((W i).ofLp j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [colFun]

/-- The positive quadrant is almost all of `planeMeasure`. -/
theorem ae_pos_planeMeasure : ∀ᵐ p ∂planeMeasure, 0 < p.1 ∧ 0 < p.2 := by
  unfold planeMeasure
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0:ℝ))), 0 < s := ae_restrict_mem measurableSet_Ioi
  have h2 : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0:ℝ))), 0 < t := ae_restrict_mem measurableSet_Ioi
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  rw [Measure.ae_prod_iff_ae_ae hset]
  filter_upwards [h1] with a ha
  filter_upwards [h2] with b hb
  exact ⟨ha, hb⟩

/-- **The kernel form of the rounding expectation.** The expectation is `π⁻¹ r τ` times the double
Laplace integral of the kernel `(st)^{-1/2} C^{r+2}`. -/
theorem reducedExpectation_eq_kernel_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, ((p.1 * p.2) ^ (-(1/2) : ℝ) *
          ((r : ℝ) * τ *
            ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^ (-(((r : ℝ) + 2) / 2) : ℝ)))
          ∂planeMeasure := by
  rw [fubini_swap_proved r τ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_planeMeasure] with p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hinner : (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ))
      = (p.1 * p.2) ^ (-(1/2) : ℝ) *
          ∫ W, (∑ i, (W i).ofLp 0 * (W i).ofLp 1) *
            Real.exp (-(p.1 * ∑ i, ((W i).ofLp 0) ^ 2 + p.2 * ∑ i, ((W i).ofLp 1) ^ 2))
            ∂(reducedLaw r τ) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W => ?_)
    simp only [fubiniIntegrand, inner_colFun, norm_sq_colFun]
    ring
  rw [hinner, integral_reducedLaw_row (a := p.1) (b := p.2) hp1 hp2 hτ]

end Grothendieck

/-
Target B: the two-dimensional substitution `Grothendieck.reducedExpectation_eq_sq_subst`.

Route: no integrability whatsoever.  Everything is done at the level of `ℝ≥0∞`-valued
(Lebesgue) integrals, where Tonelli needs no hypotheses beyond measurability, and the
one-dimensional change of variables `MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`
has no integrability hypothesis either.  The final passage back to Bochner integrals uses
`MeasureTheory.integral_eq_lintegral_of_nonneg_ae`, which is valid *without* integrability
(both sides are then `0`), together with the unconditional `ENNReal.toReal_mul`.
-/

open MeasureTheory
open scoped BigOperators Real Topology ENNReal

namespace Grothendieck

theorem measurable_rpow_const_real (y : ℝ) : Measurable fun x : ℝ => x ^ y := by
  refine measurable_of_measurable_on_compl_singleton 0 ?_
  exact Continuous.measurable (continuousOn_iff_continuous_domRestrict.1 (fun x hx =>
    (Real.continuousAt_rpow_const x y (Or.inl hx)).continuousWithinAt))

attribute [fun_prop] measurable_rpow_const_real

/-- `(√(2s))⁻¹ ds = du` under `s = u²/2`, in the form that a factor `c` is carried along.
No measurability or integrability hypothesis on `F`. -/
theorem lintegral_const_sqrt_inv_mul_eq (c : ℝ≥0∞) (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0:ℝ), c * (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * F t)
      = ∫⁻ u in Set.Ioi (0:ℝ), c * F (u ^ 2 / 2) := by
  have himg : (fun u : ℝ => u ^ 2 / 2) '' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
    ext s
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu0 : (0:ℝ) < u := hu
      show (0:ℝ) < u ^ 2 / 2
      positivity
    · intro hs
      have hs0 : (0:ℝ) < s := hs
      refine ⟨Real.sqrt (2 * s), ?_, ?_⟩
      · show (0:ℝ) < Real.sqrt (2 * s)
        positivity
      · show Real.sqrt (2 * s) ^ 2 / 2 = s
        rw [Real.sq_sqrt (by positivity)]
        ring
  have hinj : Set.InjOn (fun u : ℝ => u ^ 2 / 2) (Set.Ioi (0:ℝ)) := by
    intro a ha b hb hab
    have ha0 : (0:ℝ) < a := ha
    have hb0 : (0:ℝ) < b := hb
    simp only at hab
    have : a ^ 2 = b ^ 2 := by linarith
    nlinarith [ha0, hb0, this]
  conv_lhs => rw [← himg]
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun u : ℝ => u ^ 2 / 2) (f' := fun u : ℝ => u)
    (fun u _ => ?_) hinj]
  swap
  · have hd : HasDerivAt (fun u : ℝ => u ^ 2 / 2) u u := by
      have h := (hasDerivAt_pow 2 u).div_const 2
      refine HasDerivAt.congr_deriv h ?_
      ring
    exact hd.hasDerivWithinAt
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : (0:ℝ) < u := hu
  have habs : |u| = u := abs_of_pos hu0
  have hsq : Real.sqrt (2 * (u ^ 2 / 2)) = u := by
    rw [show 2 * (u ^ 2 / 2) = u ^ 2 by ring, Real.sqrt_sq hu0.le]
  have hone : ENNReal.ofReal u * ENNReal.ofReal u⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (le_of_lt hu0), mul_inv_cancel₀ hu0.ne', ENNReal.ofReal_one]
  simp only [habs, hsq]
  rw [show ENNReal.ofReal u * (c * (ENNReal.ofReal u⁻¹ * F (u ^ 2 / 2)))
      = c * ((ENNReal.ofReal u * ENNReal.ofReal u⁻¹) * F (u ^ 2 / 2)) by ring, hone, one_mul]

/-- `(√(2s))⁻¹ ds = du` under `s = u²/2`, as an identity of Lebesgue integrals of
`ℝ≥0∞`-valued functions (no measurability or integrability hypothesis). -/
theorem lintegral_sqrt_inv_mul_eq (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * F t
      = ∫⁻ u in Set.Ioi (0:ℝ), F (u ^ 2 / 2) := by
  simpa using lintegral_const_sqrt_inv_mul_eq 1 F

/-- The substitution `s = u²/2`, `t = v²/2` for a general kernel `κ`, with
`κ' u v = κ (u²/2) (v²/2)`.  The weight `(s t)^{-1/2} ds dt` becomes `2 du dv`. -/
theorem lintegral_kernel_subst_general (κ κ' : ℝ → ℝ → ℝ) (c : ℝ)
    (hκpos : ∀ s t : ℝ, 0 < s → 0 < t → 0 < κ s t)
    (hsub : ∀ u v : ℝ, κ' u v = κ (u ^ 2 / 2) (v ^ 2 / 2))
    (hκm : ∀ s : ℝ, Measurable fun t : ℝ => ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))
    (hF : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)))
    (hG : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ))) :
    ∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)) ∂planeMeasure
      = 2 * ∫⁻ p, ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ)) ∂planeMeasure := by
  have hst : ∀ s t : ℝ, 0 < s → 0 < t →
      (s * t) ^ (-(1/2) : ℝ) = 2 * (Real.sqrt (2 * s))⁻¹ * (Real.sqrt (2 * t))⁻¹ := by
    intro s t hs ht
    have h4 : (4:ℝ) ^ (-(1/2) : ℝ) = 1/2 := by
      have h4' : Real.sqrt (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), ← Real.sqrt_eq_rpow, h4']
      norm_num
    have h1 : (Real.sqrt (2 * s))⁻¹ = (2 * s) ^ (-(1/2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * s)]
    have h2 : (Real.sqrt (2 * t))⁻¹ = (2 * t) ^ (-(1/2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * t)]
    rw [h1, h2, mul_assoc, ← Real.mul_rpow (by positivity : (0:ℝ) ≤ 2 * s)
      (by positivity : (0:ℝ) ≤ 2 * t)]
    rw [show (2:ℝ) * s * (2 * t) = 4 * (s * t) by ring]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ s * t), h4]
    ring
  -- the pointwise identity `(s t)^{-1/2} κ^{-c} = 2 (√(2s))⁻¹ (√(2t))⁻¹ κ^{-c}`
  have hpt : ∀ s t : ℝ, 0 < s → 0 < t →
      ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
        = 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))) := by
    intro s t hs0 ht0
    have ha : (0:ℝ) ≤ (Real.sqrt (2 * s))⁻¹ := by positivity
    have hb : (0:ℝ) ≤ (Real.sqrt (2 * t))⁻¹ := by positivity
    have hk : (0:ℝ) ≤ (κ s t) ^ (-c : ℝ) :=
      (Real.rpow_pos_of_pos (hκpos s t hs0 ht0) _).le
    rw [hst s t hs0 ht0]
    conv_rhs => rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul ha,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  -- the inner substitution, for fixed `s > 0`
  have step2 : ∀ s ∈ Set.Ioi (0:ℝ),
      ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
        = (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)) := by
    intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hmeas : Measurable fun t : ℝ =>
        ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) * ENNReal.ofReal ((κ s t) ^ (-c : ℝ)) := by
      have h1 : Measurable fun t : ℝ => ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) := by fun_prop
      exact h1.mul (hκm s)
    have hae : (fun t => ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ)))
        =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
        (fun t => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ))))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hpt s t hs0 ht
    rw [lintegral_congr_ae hae]
    rw [show (fun t : ℝ => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))))
          = (fun t : ℝ => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            (ENNReal.ofReal ((Real.sqrt (2 * t))⁻¹) *
              ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))) from by
      funext t; ring]
    rw [lintegral_const_mul _ hmeas]
    rw [lintegral_sqrt_inv_mul_eq (fun t => ENNReal.ofReal ((κ s t) ^ (-c : ℝ)))]
  -- the outer substitution
  have step3 : ∫⁻ s in Set.Ioi (0:ℝ), ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ))
      = ∫⁻ u in Set.Ioi (0:ℝ), 2 * ∫⁻ v in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)) := by
    have hae : (fun s => ∫⁻ t in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((s * t) ^ (-(1/2) : ℝ) * (κ s t) ^ (-c : ℝ)))
        =ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
        (fun s => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact step2 s hs
    rw [lintegral_congr_ae hae]
    rw [show (fun s : ℝ => (2 * ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹)) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))
          = (fun s : ℝ => 2 * (ENNReal.ofReal ((Real.sqrt (2 * s))⁻¹) *
            ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))) from by
      funext s; ring]
    rw [lintegral_const_sqrt_inv_mul_eq 2
      (fun s => ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ s (v ^ 2 / 2)) ^ (-c : ℝ)))]
  -- Tonelli again, and the constant `2`
  have step4 : (∫⁻ u in Set.Ioi (0:ℝ), 2 * ∫⁻ v in Set.Ioi (0:ℝ),
          ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)))
      = 2 * ∫⁻ p, ENNReal.ofReal ((κ' p.1 p.2) ^ (-c : ℝ)) ∂
          ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    have hf : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal ((κ (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) ^ (-c : ℝ)) := by
      have h := hG
      simpa only [hsub] using h
    have hGm : Measurable fun u : ℝ =>
        ∫⁻ v in Set.Ioi (0:ℝ), ENNReal.ofReal ((κ (u ^ 2 / 2) (v ^ 2 / 2)) ^ (-c : ℝ)) :=
      hf.lintegral_prod_right'
    rw [lintegral_const_mul 2 hGm]
    congr 1
    have hTon := MeasureTheory.lintegral_prod (μ := volume.restrict (Set.Ioi (0:ℝ)))
      (ν := volume.restrict (Set.Ioi (0:ℝ)))
      (fun p : ℝ × ℝ => ENNReal.ofReal ((κ (p.1 ^ 2 / 2) (p.2 ^ 2 / 2)) ^ (-c : ℝ)))
      hf.aemeasurable
    rw [← hTon]
    exact lintegral_congr fun p => by rw [hsub]
  have step1 := MeasureTheory.lintegral_prod (μ := volume.restrict (Set.Ioi (0:ℝ)))
    (ν := volume.restrict (Set.Ioi (0:ℝ)))
    (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) * (κ p.1 p.2) ^ (-c : ℝ)))
    hF.aemeasurable
  unfold planeMeasure
  rw [step1, step3, step4]

/-- The two-dimensional substitution for the concrete Laplace kernel of Lemma 2.1. -/
theorem lintegral_kernel_eq (r : ℕ) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    ∫⁻ p, ENNReal.ofReal ((p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure
      = 2 * ∫⁻ p, ENNReal.ofReal
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  refine lintegral_kernel_subst_general
    (fun s t => (1 + 2 * s) * (1 + 2 * t) - 4 * τ ^ 2 * s * t)
    (fun u v => (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2)
    (((r : ℝ) + 2) / 2) ?_ ?_ ?_ ?_ ?_
  · intro s t hs ht
    have h1 : (0:ℝ) < s * t := mul_pos hs ht
    have h2 : (0:ℝ) < 1 - τ ^ 2 := by linarith
    have h3 : (0:ℝ) < s * t * (1 - τ ^ 2) := mul_pos h1 h2
    nlinarith [h3, hs, ht]
  · intro u v
    ring
  · intro s
    fun_prop
  · fun_prop
  · fun_prop

/-- The positivity of the kernel `(1+2s)(1+2t) - 4τ²st` on the positive quadrant. -/
theorem kernel_pos {τ : ℝ} (hτ : τ ^ 2 < 1) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    0 < (1 + 2 * s) * (1 + 2 * t) - 4 * τ ^ 2 * s * t := by
  have h1 : (0:ℝ) < s * t := mul_pos hs ht
  have h2 : (0:ℝ) < 1 - τ ^ 2 := by linarith
  have h3 : (0:ℝ) < s * t * (1 - τ ^ 2) := mul_pos h1 h2
  nlinarith [h3, hs, ht]

/-- The base of the substituted kernel is nonnegative everywhere. -/
theorem sq_kernel_nonneg {τ : ℝ} (hτ : τ ^ 2 < 1) (u v : ℝ) :
    0 ≤ (1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2 := by
  have h2 : (0:ℝ) ≤ 1 - τ ^ 2 := by linarith
  nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v),
    mul_nonneg (mul_nonneg (sq_nonneg u) (sq_nonneg v)) h2]

/-- The real identity behind the substitution: no integrability is needed at any point. -/
theorem integral_kernel_eq (r : ℕ) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure)
      = 2 * ∫ p, (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  have hg_nn : 0 ≤ᵐ[planeMeasure] (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) := by
    filter_upwards [ae_pos_planeMeasure] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt (mul_pos hp1 hp2)) _)
      (le_of_lt (Real.rpow_pos_of_pos (kernel_pos hτ hp1 hp2) _))
  have hH_nn : 0 ≤ᵐ[planeMeasure] (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) := by
    filter_upwards with p
    exact Real.rpow_nonneg (sq_kernel_nonneg hτ p.1 p.2) _
  have hg_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
      ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
    have h : Measurable fun p : ℝ × ℝ => (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) := by fun_prop
    exact h.aestronglyMeasurable
  have hH_meas : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
        (-(((r : ℝ) + 2) / 2) : ℝ)) planeMeasure := by
    have h : Measurable fun p : ℝ × ℝ =>
        ((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) := by fun_prop
    exact h.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hg_nn hg_meas,
    integral_eq_lintegral_of_nonneg_ae hH_nn hH_meas, lintegral_kernel_eq r hτ,
    ENNReal.toReal_mul]
  norm_num

/-- **Step 4b: the substitutions `s = p²/2`, `t = q²/2`.** -/
theorem reducedExpectation_eq_sq_subst_proof (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = 2 * (r : ℝ) * τ * Real.pi⁻¹ * ∫ p,
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure := by
  rw [reducedExpectation_eq_kernel_proof r hr hτ]
  have hA : (∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((r : ℝ) * τ * ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure)
      = ((r : ℝ) * τ) * ∫ p, (p.1 * p.2) ^ (-(1/2) : ℝ) *
        ((1 + 2 * p.1) * (1 + 2 * p.2) - 4 * τ ^ 2 * p.1 * p.2) ^
          (-(((r : ℝ) + 2) / 2) : ℝ) ∂planeMeasure := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
  rw [hA, integral_kernel_eq r hτ]
  ring

end Grothendieck

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = 2 * (r : ℝ) * τ * Real.pi⁻¹ * ∫ p,
          (((1 + p.1 ^ 2) * (1 + p.2 ^ 2) - τ ^ 2 * p.1 ^ 2 * p.2 ^ 2) ^
            (-(((r : ℝ) + 2) / 2) : ℝ)) ∂planeMeasure :=
  reducedExpectation_eq_sq_subst_proof r hr hτ
