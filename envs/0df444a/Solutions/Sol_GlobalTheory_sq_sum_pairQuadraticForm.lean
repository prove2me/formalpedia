-- Prove2me | solution 1 for GlobalTheory.sq_sum_pairQuadraticForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:08.694807+00:00
-- url     : https://prove2.me/submissions/841a2707-821a-4e8c-b717-0804776c959e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Theorems.Thm_GlobalTheory_sq_quadraticGaussSum
import Theorems.Thm_GlobalTheory_pairQuadraticForm_nondegenerate
import Theorems.Thm_GlobalTheory_natCard_quotient_range_mulVecLin
import Theorems.Thm_GlobalTheory_chi_four_natAbs_mul

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
    [Fintype ((n → ℤ) ⧸ LinearMap.range d.mulVecLin)] :
    (∑ x, ratCircleChar (pairQuadraticForm (by rintro h; simp [h] at hodd) hs he x)) ^ 2 =
      (ZMod.χ₄ (d.det : ZMod 4) : ℤ) * (d.det : ℂ) := by
  have hd : d.det ≠ 0 := by rintro h; simp [h] at hodd
  have hcard := natCard_quotient_range_mulVecLin hd
  rw [Nat.card_eq_fintype_card] at hcard
  rw [sq_quadraticGaussSum (by rw [hcard]; exact hodd.natAbs) _
    (pairQuadraticForm_nondegenerate hd hs he hc), hcard]
  rw [← Int.cast_natCast (R := ℂ), ← Int.cast_mul, chi_four_natAbs_mul, Int.cast_mul]
end GlobalTheory
