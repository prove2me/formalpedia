-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_n
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:06.736143+00:00
-- url     : https://prove2.me/submissions/7ec9cc78-94cd-4d9d-8328-b38af8032e70

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
theorem _root_.solution (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (z : K) :
    mx m x * n z = n (x ^ 2 * z) * mx m x := by
  rw [mx_ne m hx]; have := hmn (Units.mk0 x hx) z; rwa [Units.val_mk0] at this
end GlobalTheory.BruhatRep
