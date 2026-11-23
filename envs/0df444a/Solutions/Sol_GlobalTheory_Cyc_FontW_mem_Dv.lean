-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.mem_Dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:48.61894+00:00
-- url     : https://prove2.me/submissions/bae573cb-8404-4497-baf4-5e0219fbe684

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution {l r : ℕ} {M : Type*} [AddCommGroup M] {x : M} :
    x ∈ Dv l r M ↔ ∃ y, l ^ r • y = x := Iff.rfl
end GlobalTheory.Cyc.FontW
