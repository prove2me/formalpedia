-- Prove2me | solution 1 for GlobalTheory.FormalInv.sumFamily_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:14.567606+00:00
-- url     : https://prove2.me/submissions/08c5a990-acb6-4f4a-9d41-5c29edb4e713

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
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite τ] [Finite τ'] (a : σ → MvPowerSeries τ R)
    (a' : σ' → MvPowerSeries τ' R) (i : σ) :
    sumFamily a a' (Sum.inl i) = rename Sum.inl (a i) := rfl
end GlobalTheory.FormalInv
