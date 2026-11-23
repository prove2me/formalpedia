-- Prove2me | solution 1 for GlobalTheory.FormalInv.mem_coeffsIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:16.213998+00:00
-- url     : https://prove2.me/submissions/b38cda3b-14ac-498c-ac47-b0593cc9a18c

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
    {f : MvPowerSeries σ R} :
    f ∈ coeffsIn S w g ↔ ∀ d, (∀ k, weight (w k) d < g k) → coeff d f ∈ S := Iff.rfl
end GlobalTheory.FormalInv
