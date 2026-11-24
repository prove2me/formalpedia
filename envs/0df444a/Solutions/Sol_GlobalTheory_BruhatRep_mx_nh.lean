-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_nh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:57.989138+00:00
-- url     : https://prove2.me/submissions/7925d7ae-260a-497d-925f-be7170167570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_n

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
theorem _root_.solution (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (z : K) (X : M) :
    X * mx m x * n z = X * n (x ^ 2 * z) * mx m x := by
  simpa only [mul_assoc] using congrArg (X * ·) (mx_n n m hmn hx z)
end GlobalTheory.BruhatRep
