-- Prove2me | solution 1 for GlobalTheory.RiemannThetaModel.norm_sq_riemannTheta_mul_exp_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:51.554737+00:00
-- url     : https://prove2.me/submissions/d481d1d2-47a8-439e-9cfe-e88f9a06417e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_NormSqRiemannThetaMulExpPeriodic
import Theorems.Thm_GlobalTheory_RiemannThetaModel_norm_riemannTheta_real_coords

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.RiemannThetaModel
variable {ι : Type*} [Fintype ι]
namespace GlobalTheory.RiemannThetaModel
theorem _root_.solution {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm)
    (a b x y : ι → ℝ) (m k : ι → ℤ) :
    ‖riemannTheta a b Ω ((fun i => ((x + fun i => (m i : ℝ)) i : ℂ)) +
        Ω *ᵥ fun i => ((y + fun i => (k i : ℝ)) i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * ((y + fun i => (k i : ℝ)) ⬝ᵥ
        (Ω.map Complex.im *ᵥ (y + fun i => (k i : ℝ))))) =
    ‖riemannTheta a b Ω ((fun i => (x i : ℂ)) + Ω *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * (y ⬝ᵥ (Ω.map Complex.im *ᵥ y))) := by
  have key (t r : ℝ) : (Real.exp (π * t) * r) ^ 2 * Real.exp (-2 * π * t) = r ^ 2 := by
    rw [mul_pow, mul_right_comm, sq, ← Real.exp_add, ← Real.exp_add]
    simp only [show π * t + π * t + -2 * π * t = 0 by ring, Real.exp_zero, one_mul]
  rw [norm_riemannTheta_real_coords h, norm_riemannTheta_real_coords h, key, key, ← add_assoc,
    ← add_assoc, riemannTheta_char_add_intCast_left, riemannTheta_char_add_intCast_right,
    norm_mul, Complex.norm_exp]
  simp [dotProduct]
end GlobalTheory.RiemannThetaModel
