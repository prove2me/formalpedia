-- Prove2me | solution 1 for GlobalTheory.FormalInv.substAlgEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:14.291871+00:00
-- url     : https://prove2.me/submissions/1351522c-bc69-4a95-b88b-a1200ac7841e

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
variable [Fintype σ] [DecidableEq σ]
variable {u v : σ → MvPowerSeries σ R}
namespace GlobalTheory.FormalInv
theorem _root_.solution (hu : ∀ i, constantCoeff (u i) = 0)
    (hA : IsUnit (linearPart u)) (f : MvPowerSeries σ R) :
    substAlgEquiv hu hA f = f.subst u := by simp [substAlgEquiv]
end GlobalTheory.FormalInv
