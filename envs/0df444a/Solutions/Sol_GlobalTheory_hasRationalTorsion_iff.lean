-- Prove2me | solution 1 for GlobalTheory.hasRationalTorsion_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:16.214915+00:00
-- url     : https://prove2.me/submissions/80d9f001-8780-4c66-b1bb-d6f12608091d

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
variable {K : Type*} [Field K]
variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}
namespace GlobalTheory
theorem _root_.solution [DecidableEq L] : HasRationalTorsion W L n ↔
    ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y), n • Point.some x y h = 0 →
      x ∈ (algebraMap K L).range ∧ y ∈ (algebraMap K L).range := by
  unfold HasRationalTorsion
  convert Iff.rfl
end GlobalTheory
