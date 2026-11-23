-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:07.891806+00:00
-- url     : https://prove2.me/submissions/99184136-7c62-4d27-859c-487cc40c17f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_ne

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
theorem _root_.solution (hm : ∀ a b, m (a * b) = m a * m b) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    mx m x * mx m y = mx m (x * y) := by
  rw [mx_ne m hx, mx_ne m hy, mx_ne m (mul_ne_zero hx hy), ← hm]; congr 1; ext; simp
end GlobalTheory.BruhatRep
