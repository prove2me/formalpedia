-- Prove2me | solution 1 for Grothendieck.reducedIntegrand_eq_pi_inv_mul_integral_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:13:46.609998+00:00
-- url     : https://prove2.me/submissions/48b21689-ab4a-424d-89b8-28f7d61e3eee

import Mathlib
import Definitions.Def_Grothendieck_Reduced

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
theorem reducedIntegrand_eq_pi_inv_mul_integral_all_proof (r : ℕ)
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

open MeasureTheory in
open Grothendieck in
theorem solution (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = Real.pi⁻¹ * (inner ℝ (colFun r 0 W) (colFun r 1 W) *
          ∫ s in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ),
            (s * t) ^ (-(1/2) : ℝ) *
              Real.exp (-(s * ‖colFun r 0 W‖ ^ 2 + t * ‖colFun r 1 W‖ ^ 2))) :=
  reducedIntegrand_eq_pi_inv_mul_integral_all_proof r W
