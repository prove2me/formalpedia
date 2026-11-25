-- Prove2me | solution 1 for GlobalTheory.sq_sum_exp_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:15.212513+00:00
-- url     : https://prove2.me/submissions/702eb8e2-9b13-495d-84c7-4ca7311d4f49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_ratCircleChar_pairQuadraticForm_mk
import Theorems.Thm_GlobalTheory_sq_sum_pairQuadraticForm

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
theorem _root_.solution (hodd : Odd d.det) (hs : (dᵀ * b).IsSymm)
    (he : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∃ u v : Matrix n n ℤ, u * b + v * d = 1)
    {ι : Type*} [Fintype ι] (r : ι → n → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (n → ℤ) ⧸ LinearMap.range d.mulVecLin)) :
    (∑ k, Complex.exp (Real.pi * Complex.I *
        ((fun i => (r k i : ℂ)) ⬝ᵥ (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ
          fun i => (r k i : ℂ)))) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  letI := Fintype.ofBijective _ hr
  rw [← sq_sum_pairQuadraticForm hodd hs he hc]
  congr 1
  exact Fintype.sum_bijective _ hr _ _ fun k => (ratCircleChar_pairQuadraticForm_mk _ hs he _).symm
end GlobalTheory
