-- Prove2me | solution 1 for GlobalTheory.WeilM.norm_eq_one_of_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.912201+00:00
-- url     : https://prove2.me/submissions/ab812be5-034c-436b-a7ca-e9ce172785bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] {G : Type} [Group G]
namespace GlobalTheory.WeilM
theorem _root_.solution {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} {a : ℂ}
    (h : ∫⁻ x, ‖(a • f) x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) (h0 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ 0)
    (h1 : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤) : ‖a‖ = 1 := by
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at h
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])] at h
  have h2 : ‖a‖ₑ ^ 2 = 1 := (ENNReal.mul_left_inj h0 h1).mp (h.trans (one_mul _).symm)
  rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_eq_one, pow_eq_one_iff_of_nonneg zero_le' two_ne_zero] at h2
  exact congrArg NNReal.toReal h2
end GlobalTheory.WeilM
