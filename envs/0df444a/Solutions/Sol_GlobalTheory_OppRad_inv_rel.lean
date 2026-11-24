-- Prove2me | solution 1 for GlobalTheory.OppRad.inv_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:28.1142+00:00
-- url     : https://prove2.me/submissions/8cef292b-bc03-4e7d-bd26-b4531890c60e

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
theorem _root_.solution {p p' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) : (w⁻¹).val * p = p' * (w⁻¹).val := by
  rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hp, Units.mul_inv_cancel_right]
end GlobalTheory.OppRad
