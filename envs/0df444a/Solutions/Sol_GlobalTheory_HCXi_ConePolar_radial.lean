-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:09.968718+00:00
-- url     : https://prove2.me/submissions/4c953249-09d1-4e82-9eb7-e1d698db4e68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar
namespace GlobalTheory.HCXi.ConePolar
theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) (F H : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Set.Ioi (Real.sqrt a), ENNReal.ofReal ρ * (F (ρ ^ 2 - a) * H ρ)
      = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ), F τ * H (Real.sqrt (a + τ)) := by
  have himg : (fun ρ : ℝ => ρ ^ 2 - a) '' Set.Ioi (Real.sqrt a) = Set.Ioi 0 := by
    ext τ
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have h0 := Real.sqrt_nonneg a
      have h1 := Real.sq_sqrt ha
      nlinarith
    · intro hτ
      refine ⟨Real.sqrt (a + τ), Real.sqrt_lt_sqrt ha (by linarith), ?_⟩
      rw [Real.sq_sqrt (by linarith)]; ring
  have hinj : Set.InjOn (fun ρ : ℝ => ρ ^ 2 - a) (Set.Ioi (Real.sqrt a)) := by
    intro x hx y hy hxy
    have h0 := Real.sqrt_nonneg a
    simp only [Set.mem_Ioi] at hx hy
    have : x ^ 2 = y ^ 2 := by simpa using hxy
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 this
  have hder : ∀ x ∈ Set.Ioi (Real.sqrt a), HasDerivWithinAt (fun ρ : ℝ => ρ ^ 2 - a) (2 * x)
      (Set.Ioi (Real.sqrt a)) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).sub_const a).hasDerivWithinAt (s := Set.Ioi (Real.sqrt a))
    simpa using this
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj,
    ← lintegral_const_mul' _ _ (by simp)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (Real.sqrt_nonneg a).trans (le_of_lt hx)
  rw [show a + (x ^ 2 - a) = x ^ 2 by ring, Real.sqrt_sq hx0, abs_of_nonneg (by positivity),
    ENNReal.ofReal_mul (by norm_num), ← mul_assoc (1 / 2 : ℝ≥0∞), ← mul_assoc (1 / 2 : ℝ≥0∞)]
  have : (1 / 2 : ℝ≥0∞) * ENNReal.ofReal 2 = 1 := by
    rw [ENNReal.ofReal_ofNat, one_div, ENNReal.inv_mul_cancel (by simp) (by simp)]
  rw [this, one_mul]
end GlobalTheory.HCXi.ConePolar
