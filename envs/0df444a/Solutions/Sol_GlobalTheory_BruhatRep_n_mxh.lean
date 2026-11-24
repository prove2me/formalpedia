-- Prove2me | solution 1 for GlobalTheory.BruhatRep.n_mxh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:38.792204+00:00
-- url     : https://prove2.me/submissions/bdef3c56-fb91-44d9-9f70-53475c2cb2aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_n_mx

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
theorem _root_.solution (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (y : K) (X : M) :
    X * n y * mx m x = X * mx m x * n (y / x ^ 2) := by
  simpa only [mul_assoc] using congrArg (X * ·) (n_mx n m hmn hx y)
end GlobalTheory.BruhatRep
