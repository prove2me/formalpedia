-- Prove2me | solution 1 for GlobalTheory.JacobiDeriv.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:37.453032+00:00
-- url     : https://prove2.me/submissions/990285f7-6611-4379-86e0-6f1a67590425

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero
import Theorems.Thm_GlobalTheory_JacobiDeriv_norm_term_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
open GlobalTheory GlobalTheory.JacobiDeriv
namespace GlobalTheory.JacobiDeriv
theorem _root_.solution {T : ℝ} (hT : 0 < T) (n : ℤ) {τ : ℂ} (hτ : T ≤ τ.im) :
    ‖jacobiTheta₂'_term n ((τ + 1) / 2) τ‖ ≤
      2 * π * (|(n : ℝ)| ^ 1 * Real.exp (-π * (T * n ^ 2 - 2 * (T / 2) * |(n : ℝ)|))) := by
  rw [norm_term_eq, pow_one, mul_assoc]
  have h0 : (0 : ℝ) ≤ n * (n + 1) := by
    have : 0 ≤ n * (n + 1) := by
      rcases le_or_gt 0 n with h | h
      · positivity
      · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
    exact_mod_cast this
  gcongr
  have h1 := neg_abs_le (n : ℝ)
  have h2 : π * (n * (n + 1)) * T ≤ π * (n * (n + 1)) * τ.im :=
    mul_le_mul_of_nonneg_left hτ (mul_nonneg Real.pi_pos.le h0)
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_pos Real.pi_pos hT).le]
end GlobalTheory.JacobiDeriv
