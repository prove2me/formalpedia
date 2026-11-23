-- Prove2me | solution 1 for GlobalTheory.transvection_isUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:25.90881+00:00
-- url     : https://prove2.me/submissions/67bf91b4-54d2-4824-acc0-c883110b8854

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] {m : ℕ}
namespace GlobalTheory
theorem _root_.solution {i j : Fin m} (hji : j < i) (x : k) :
    (transvection j i x).BlockTriangular id := by
  intro a b hba
  simp only [id] at hba
  simp only [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hba), single_apply, zero_add]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hba (not_lt.mpr hji.le)
  · rfl
end GlobalTheory
