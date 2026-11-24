-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_diffTopPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:36.633866+00:00
-- url     : https://prove2.me/submissions/d9a5e396-79df-46df-9f8e-fd38d059ec7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

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
theorem _root_.solution (d : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G)
    (φ : G → K) (x : G) : (diffTopPoly d g φ x).IsHomogeneous d := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ ↦ MvPolynomial.IsHomogeneous.C_mul ?_ _
  simpa using MvPolynomial.IsHomogeneous.prod univ (fun j : Fin d ↦ (MvPolynomial.X (a j) :
    MvPolynomial ι K)) (fun _ ↦ 1) fun j _ ↦ MvPolynomial.isHomogeneous_X K (a j)
end GlobalTheory
