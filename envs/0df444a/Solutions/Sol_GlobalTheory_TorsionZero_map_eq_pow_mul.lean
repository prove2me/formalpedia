-- Prove2me | solution 1 for GlobalTheory.TorsionZero.map_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:32:58.38686+00:00
-- url     : https://prove2.me/submissions/bf932293-ef64-494b-9162-e39d7eff8934

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_mul_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K R : Type} [Field K] [CommRing R] [Algebra K R]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {σ : Type} {x : σ → R} {φ ψ : R →ₐ[K] K} {c : K}
    (h : ∀ j, φ (x j) = ψ (x j) * c) {i : σ} (hi : φ (x i) ≠ 0) {y : R} {e n : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous (n + e)) (hy : y * x i ^ n = aeval x G) :
    φ y = c ^ e * ψ y := by
  have h1 := congrArg φ hy
  have h2 := congrArg ψ hy
  rw [map_mul, map_pow, comp_aeval_apply] at h1 h2
  rw [show (fun j => φ (x j)) = fun j => ψ (x j) * c from funext h,
    aeval_mul_of_isHomogeneous _ _ hG, ← h2] at h1
  refine mul_right_cancel₀ (pow_ne_zero n hi) ?_
  rw [h1, h i]
  ring
end GlobalTheory.TorsionZero
