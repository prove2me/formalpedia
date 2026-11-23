-- Prove2me | solution 1 for GlobalTheory.UnitLemma.valsAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:40.840352+00:00
-- url     : https://prove2.me/submissions/9eae6894-9144-4ed3-87ee-aa41341123d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValsAtApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ}
    (e : Fin r → ι) (x : G) (j : Fin r) :
    Multiplicative.toAdd (valsAt w e x) j = Multiplicative.toAdd (w (e j) x) := rfl
end GlobalTheory.UnitLemma
