-- Prove2me | solution 1 for GlobalTheory.FormalInv.smul_mem_coeffsIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:07.214581+00:00
-- url     : https://prove2.me/submissions/890bcd5d-3be9-4783-95df-16592068c4a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder

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
namespace GlobalTheory.FormalInv
theorem _root_.solution {κ : Type*} {S : Subring R} {w : κ → σ → ℕ} {g : κ → ℕ}
    {r : R} (hr : r ∈ S) {f : MvPowerSeries σ R} (hf : f ∈ coeffsIn S w g) :
    r • f ∈ coeffsIn S w g := fun d hd => by
  rw [map_smul, smul_eq_mul]; exact S.mul_mem hr (hf d hd)
end GlobalTheory.FormalInv
