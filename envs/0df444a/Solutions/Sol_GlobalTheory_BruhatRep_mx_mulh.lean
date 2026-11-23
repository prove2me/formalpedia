-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_mulh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:41.980069+00:00
-- url     : https://prove2.me/submissions/92370e5d-748d-4adc-87f0-e020f92f6f06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_mul

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
theorem _root_.solution (hm : ∀ a b, m (a * b) = m a * m b) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (X : M) :
    X * mx m x * mx m y = X * mx m (x * y) := by
  rw [mul_assoc, mx_mul m hm hx hy]
end GlobalTheory.BruhatRep
