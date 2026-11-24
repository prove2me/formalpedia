-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.mem_range_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:23.069845+00:00
-- url     : https://prove2.me/submissions/d712cbbf-d2ad-4274-884d-151267aadb02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff
import Theorems.Thm_GlobalTheory_nonsingular_baseChange_iff

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
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
omit [CharZero K] [IsAlgClosed L]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L 2) (h₁ : W.a₁ = 0)
    (h₃ : W.a₃ = 0) {x : L} (hx : x ^ 3 + algebraMap K L W.a₂ * x ^ 2 + algebraMap K L W.a₄ * x
      + algebraMap K L W.a₆ = 0) : x ∈ (algebraMap K L).range := by
  classical
  have hy : (W.baseChange L).toAffine.Equation x 0 := by
    rw [equation_iff]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
    linear_combination -hx
  refine (hasRationalTorsion_iff.mp h x 0 (nonsingular_baseChange_iff.mpr hy) ?_).1
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  simp [WeierstrassCurve.baseChange, h₁, h₃]
end HasRationalTorsion
end GlobalTheory
