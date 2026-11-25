-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_mem_dualMonoid_eq_exposedFace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:35.26563+00:00
-- url     : https://prove2.me/submissions/ddff6880-9371-4f55-bcfe-dc9e2416f6b5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Lattice
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ToricFaces
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_of_isFaceOf
import Theorems.Thm_GroundTheory_Arith_Toric_exists_separating_rational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone TensorProduct
variable {N : Type*} [AddCommGroup N]
variable [Module.Free ℤ N] [Module.Finite ℤ N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hτ : τ.IsFaceOf σ) :
    ∃ u ∈ dualMonoid σ, τ = exposedFace σ (toRealDual N u) := by
  have hστ : σ ⊓ τ = τ := inf_eq_right.2 hτ.le
  obtain ⟨u, hu, -, hE, -⟩ := exists_separating_rational hσ (hσ.of_isFaceOf hτ)
    (by rw [hστ]; exact hτ) (by rw [hστ])
  exact ⟨u, hu, by rw [hE, hστ]⟩
end GroundTheory.Arith.Toric
