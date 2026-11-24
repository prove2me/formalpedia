-- Prove2me | solution 1 for GlobalTheory.JacobiDeriv.norm_term_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:08.931294+00:00
-- url     : https://prove2.me/submissions/8b326c4b-9510-46b4-8ef9-d915fbcf66e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DifferentiableAtDerivAtZero

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
theorem _root_.solution (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂'_term n ((τ + 1) / 2) τ‖ =
      2 * π * |(n : ℝ)| * Real.exp (-(π * (n * (n + 1)) * τ.im)) := by
  rw [jacobiTheta₂'_term, norm_mul, norm_jacobiTheta₂_term]
  congr 1
  · simp [abs_of_pos Real.pi_pos]
  · congr 1
    simp
    ring
end GlobalTheory.JacobiDeriv
