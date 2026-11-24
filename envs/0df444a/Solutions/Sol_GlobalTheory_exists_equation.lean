-- Prove2me | solution 1 for GlobalTheory.exists_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:41:31.362872+00:00
-- url     : https://prove2.me/submissions/20d462b5-6405-40ca-8190-56fbc5928934

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_exists_root_quadratic

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
theorem _root_.solution (W : WeierstrassCurve L) (x : L) : ∃ y, W.toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := exists_root_quadratic (W.a₁ * x + W.a₃)
    (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  exact ⟨y, (equation_iff ..).mpr (by linear_combination hy)⟩
end GlobalTheory
