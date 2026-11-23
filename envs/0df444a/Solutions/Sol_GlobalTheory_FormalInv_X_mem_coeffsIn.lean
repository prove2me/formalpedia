-- Prove2me | solution 1 for GlobalTheory.FormalInv.X_mem_coeffsIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:14.701948+00:00
-- url     : https://prove2.me/submissions/14d63dbe-2d35-4e37-9600-ddad95f6c9c3

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
theorem _root_.solution {κ : Type*} {S : Subring R} {w : κ → σ → ℕ} {g : κ → ℕ} (s : σ) :
    (X s : MvPowerSeries σ R) ∈ coeffsIn S w g := fun d _ => by
  classical
  rw [coeff_X]; split_ifs <;> simp
end GlobalTheory.FormalInv
