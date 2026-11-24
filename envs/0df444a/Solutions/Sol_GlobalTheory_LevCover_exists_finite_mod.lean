-- Prove2me | solution 1 for GlobalTheory.LevCover.exists_finite_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:43.201907+00:00
-- url     : https://prove2.me/submissions/38fcd119-71b2-4280-a50e-393111daee09

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevCover
variable {S : Scheme.{0}}
namespace GlobalTheory.LevCover
theorem _root_.solution (M : Type) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    ∃ (κ : Type) (_ : Finite κ) (q : M → κ), ∀ a a', q a = q a' → ∃ c, a' = a + n • c := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let b := Module.Free.chooseBasis ℤ M
  refine ⟨Module.Free.ChooseBasisIndex ℤ M → ZMod n, inferInstance, fun a i => (b.repr a i : ZMod n),
    fun a a' h => ?_⟩
  have h1 : ∀ i, ∃ c : ℤ, b.repr a' i - b.repr a i = n * c := fun i =>
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (congrFun h i)
  choose c hc using h1
  refine ⟨b.equivFun.symm c, b.equivFun.injective (funext fun i => ?_)⟩
  rw [map_add, map_nsmul, LinearEquiv.apply_symm_apply]
  simp only [Module.Basis.equivFun_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  linarith [hc i]
end GlobalTheory.LevCover
