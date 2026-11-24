-- Prove2me | solution 1 for GlobalTheory.BruhatRep.t_mxh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:39.851657+00:00
-- url     : https://prove2.me/submissions/7f71e359-7362-49ce-8fb8-28c3915f41e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_t_mx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution (htm : ∀ s, t * m s = m s⁻¹ * t) {x : K} (hx : x ≠ 0) (X : M) :
    X * t * mx m x = X * mx m x⁻¹ * t := by
  simpa only [mul_assoc] using congrArg (X * ·) (t_mx m t htm hx)
end GlobalTheory.BruhatRep
