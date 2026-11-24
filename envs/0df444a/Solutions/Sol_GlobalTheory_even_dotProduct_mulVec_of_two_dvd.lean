-- Prove2me | solution 1 for GlobalTheory.even_dotProduct_mulVec_of_two_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:37:57.12196+00:00
-- url     : https://prove2.me/submissions/04d8aa0b-e3c8-4089-9266-181fecf1e428

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

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
omit [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution (hb : ∀ i j, 2 ∣ b i j) (d : Matrix n n ℤ) (μ : n → ℤ) :
    Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ) := by
  rw [even_iff_two_dvd]
  simp only [dotProduct, mulVec, mul_apply]
  exact dvd_sum fun i _ => Dvd.dvd.mul_left (dvd_sum fun j _ => Dvd.dvd.mul_right
    (dvd_sum fun k _ => (hb k j).mul_left _) _) _
end GlobalTheory
