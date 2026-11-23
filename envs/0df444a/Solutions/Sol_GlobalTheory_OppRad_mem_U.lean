-- Prove2me | solution 1 for GlobalTheory.OppRad.mem_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:32.224707+00:00
-- url     : https://prove2.me/submissions/9100497a-f732-45b9-93d6-c0fea898f6b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]
namespace GlobalTheory.OppRad
theorem _root_.solution {p q : R} {u : Rˣ} : u ∈ U p q ↔ p * (u.val - 1) = u.val - 1 ∧ (u.val - 1) * q = u.val - 1 := Iff.rfl
end GlobalTheory.OppRad
