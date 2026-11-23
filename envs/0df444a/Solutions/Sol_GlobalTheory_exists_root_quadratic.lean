-- Prove2me | solution 1 for GlobalTheory.exists_root_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:33.649559+00:00
-- url     : https://prove2.me/submissions/520d31d2-f696-4c34-8a3e-858159673653

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
theorem _root_.solution (b c : L) : ∃ x : L, x ^ 2 + b * x + c = 0 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 2 + C b * X + C c : L[X])
    (by rw [show (X ^ 2 + C b * X + C c : L[X]).degree = 2 by compute_degree!]; decide)
  exact ⟨x, by simpa using hx⟩
end GlobalTheory
