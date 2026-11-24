-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.exists_point_of_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:50:05.231235+00:00
-- url     : https://prove2.me/submissions/e6f7c997-1b62-497c-811b-775820a1ca23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_hasRationalTorsion_iff
import Theorems.Thm_GlobalTheory_nonsingular_baseChange_iff
import Theorems.Thm_GlobalTheory_exists_equation
import Theorems.Thm_GlobalTheory_three_nsmul_eq_zero_iff

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
omit [CharZero K]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L 3) {x : L}
    (hx : (W.baseChange L).Ψ₃.eval x = 0) :
    ∃ x₀ y₀ : K, algebraMap K L x₀ = x ∧ W.toAffine.Nonsingular x₀ y₀ ∧ W.Ψ₃.eval x₀ = 0 := by
  classical
  obtain ⟨y, hy⟩ := exists_equation (W.baseChange L) x
  have hy' : (W.baseChange L).toAffine.Nonsingular x y := nonsingular_baseChange_iff.mpr hy
  obtain ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩ :=
    hasRationalTorsion_iff.mp h x y hy' ((three_nsmul_eq_zero_iff hy').mpr hx)
  refine ⟨x₀, y₀, rfl, (W.toAffine.map_nonsingular (algebraMap K L).injective x₀ y₀).mp hy', ?_⟩
  rw [WeierstrassCurve.baseChange, map_Ψ₃, eval_map_apply] at hx
  exact (map_eq_zero _).mp hx
end HasRationalTorsion
end GlobalTheory
