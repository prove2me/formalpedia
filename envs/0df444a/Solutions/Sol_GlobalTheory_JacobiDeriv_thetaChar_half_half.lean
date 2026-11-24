-- Prove2me | solution 1 for GlobalTheory.JacobiDeriv.thetaChar_half_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:21:09.685021+00:00
-- url     : https://prove2.me/submissions/54d9fc09-984c-4522-bc21-09ede8ead208

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
open Complex Filter
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold Topology Real
namespace GlobalTheory.JacobiDeriv
namespace _root_.GlobalTheory.JacobiDeriv
theorem _root_.solution (τ z : ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar (g := 1) !![τ] ![1 / 2] ![1 / 2] ![z] =
      cexp (π * I * (τ / 4 + z + 1 / 2)) * jacobiTheta₂ (z + (τ + 1) / 2) τ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar jacobiTheta₂
  rw [← tsum_mul_left]
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  congr 1
  ext n
  simp [jacobiTheta₂_term, dotProduct, Matrix.mulVec, ← Complex.exp_add]
  congr 1
  ring
end _root_.GlobalTheory.JacobiDeriv
end GlobalTheory.JacobiDeriv
