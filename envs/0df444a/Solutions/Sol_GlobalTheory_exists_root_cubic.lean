-- Prove2me | solution 1 for GlobalTheory.exists_root_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:33.205963+00:00
-- url     : https://prove2.me/submissions/8abc64c3-768b-47a1-974f-2a5a44847804

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {L : Type*} [Field L] [IsAlgClosed L]
namespace GlobalTheory
theorem _root_.solution {a : L} (ha : a ≠ 0) (b c d : L) :
    ∃ x : L, a * x ^ 3 + b * x ^ 2 + c * x + d = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : L[X])
    (by rw [degree_cubic ha]; decide)
  exact ⟨x, by simpa using hx⟩
end GlobalTheory
