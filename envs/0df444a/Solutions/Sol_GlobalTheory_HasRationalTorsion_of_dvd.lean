-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:02.516811+00:00
-- url     : https://prove2.me/submissions/e6a812f1-9aa9-4905-91f3-5a8917bea8b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff

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
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L n) (hmn : m ∣ n) :
    HasRationalTorsion W L m := by
  classical
  obtain ⟨k, rfl⟩ := hmn
  rw [hasRationalTorsion_iff] at h ⊢
  intro x y hP h0
  exact h x y hP (by rw [mul_nsmul, h0, nsmul_zero])
end HasRationalTorsion
end GlobalTheory
