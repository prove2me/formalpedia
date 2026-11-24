-- Prove2me | solution 1 for GlobalTheory.DiffVanish.eval_diffTopPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:04:37.919549+00:00
-- url     : https://prove2.me/submissions/8fbf039d-e3f9-4d55-b798-a772a05c6b8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
import Theorems.Thm_GlobalTheory_DiffVanish_form_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]
omit [CharZero K]
namespace GlobalTheory
namespace DiffVanish
theorem _root_.solution {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) (n : ι → ℤ) :
    MvPolynomial.eval (fun i ↦ (n i : K)) (diffTopPoly d g φ x) =
      (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by
  rw [MultilinearMap.map_sum, mul_sum, diffTopPoly, map_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [MultilinearMap.map_smul_univ, ← h.form_apply]
  simp [Function.comp_def]
  ring
end DiffVanish
end GlobalTheory
