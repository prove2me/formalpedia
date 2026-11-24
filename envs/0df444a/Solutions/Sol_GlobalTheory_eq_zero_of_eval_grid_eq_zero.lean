-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_eval_grid_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:44.740159+00:00
-- url     : https://prove2.me/submissions/3390f321-5f13-4d77-a952-16da2bb75f0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Theorems.Thm_GlobalTheory_eq_zero_of_eval_box_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]
namespace GlobalTheory
theorem _root_.solution (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP
end GlobalTheory
