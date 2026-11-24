-- Prove2me | solution 1 for GlobalTheory.FormalInv.coeff_substInv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:50.945051+00:00
-- url     : https://prove2.me/submissions/684ce697-34a4-4741-8f38-a52542e44662

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsInDeg
import Theorems.Thm_GlobalTheory_FormalInv_approxLimit_mem_coeffsInDeg
import Theorems.Thm_GlobalTheory_FormalInv_higherPart_mem_coeffsInDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0) {S : Subring R} {g : ℕ}
    (hB : ∀ i j, (linearPart u)⁻¹ i j ∈ S)
    (huS : ∀ i (d : σ →₀ ℕ), d.degree < g → coeff d (u i) ∈ S) (i : σ) (d : σ →₀ ℕ)
    (hd : d.degree < g) : coeff d (substInv u i) ∈ S :=
  mem_coeffsInDeg.1 (approxLimit_mem_coeffsInDeg hu hB
    (fun i => higherPart_mem_coeffsInDeg (hu i) (mem_coeffsInDeg.2 (huS i))) i) d hd
end GlobalTheory.FormalInv
