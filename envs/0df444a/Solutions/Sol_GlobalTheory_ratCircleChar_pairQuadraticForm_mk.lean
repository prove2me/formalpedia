-- Prove2me | solution 1 for GlobalTheory.ratCircleChar_pairQuadraticForm_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:39.231506+00:00
-- url     : https://prove2.me/submissions/7fa5f244-dfcd-413b-a2a2-ace2044ac934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_pairQuadraticForm_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {n : Type*} [Fintype n]
variable [DecidableEq n] {b d : Matrix n n ℤ}
namespace GlobalTheory
theorem _root_.solution (hd : d.det ≠ 0) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (ν : n → ℤ) :
    ratCircleChar (pairQuadraticForm hd hs he (Submodule.Quotient.mk ν)) =
      Complex.exp (Real.pi * Complex.I *
        ((fun i => (ν i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (ν i : ℂ))) := by
  have hinv : (d.map ((↑) : ℤ → ℂ))⁻¹ = (d.map ((↑) : ℤ → ℚ))⁻¹.map (Rat.castHom ℂ) := by
    refine inv_eq_right_inv ?_
    have : d.map ((↑) : ℤ → ℂ) = (d.map ((↑) : ℤ → ℚ)).map (Rat.castHom ℂ) := by ext; simp
    rw [this, ← Matrix.map_mul, mul_nonsing_inv _ (isUnit_det_map_ratCast hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [pairQuadraticForm_mk, ratCircleChar_coe, hinv]
  congr 1
  simp only [dotProduct, mulVec, mul_apply, map_apply, Rat.coe_castHom]
  push_cast
  ring
end GlobalTheory
