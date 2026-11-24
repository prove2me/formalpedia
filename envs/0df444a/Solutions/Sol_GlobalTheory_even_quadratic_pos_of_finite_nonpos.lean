-- Prove2me | solution 1 for GlobalTheory.even_quadratic_pos_of_finite_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:41.381799+00:00
-- url     : https://prove2.me/submissions/95bdf167-0549-439d-a2f1-0c36cddd82a1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvenQuadraticPosOfFiniteNonpos
import Theorems.Thm_GlobalTheory_cubeRel_even_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (φ : X → ℤ), (∀ a b c, φ (a + b + c) + φ a + φ b + φ c = φ (a + b) + φ (a + c) + φ (b + c)) → (∀ a, φ (-a) = φ a) → {a | φ a ≤ 0}.Finite → ∀ a, a ≠ 0 → 0 < φ a := by
  intro X _ _ φ h he hfin a ha
  by_contra hle
  rw [not_lt] at hle
  have hinj : Function.Injective (fun n : ℕ => n • a) := by
    intro m n hmn
    have h1 : ((m : ℤ) - (n : ℤ)) • a = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul]
      exact sub_eq_zero.mpr hmn
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact_mod_cast sub_eq_zero.mp h2
    · exact absurd h2 ha
  refine Set.infinite_of_injective_forall_mem hinj ?_ hfin
  intro n
  show φ (n • a) ≤ 0
  rw [cubeRel_even_nsmul φ h he a n]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
end GlobalTheory
