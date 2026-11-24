-- Prove2me | solution 1 for GlobalTheory.LevCover.RepTors.clopenCond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:42.350296+00:00
-- url     : https://prove2.me/submissions/1f692172-865b-4d32-848b-2b0eb30cedfc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RangeSubsetOfGeom
import Theorems.Thm_GlobalTheory_LevCover_ClopenCond_congr
import Theorems.Thm_GlobalTheory_LevCover_clopenCond_eq
import Theorems.Thm_GlobalTheory_LevCover_RepTors_ext

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
namespace RepTors
theorem _root_.solution {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S}
    {et : La → (Z ⟶ G)} (R : RepTors G n La Z et) {T : Over S} (x y : La → (T ⟶ G))
    (hx : ∀ a c, x (a + c) = x a * x c) (hx' : ∀ a, x a ^ n = 1)
    (hy : ∀ a c, y (a + c) = y a * y c) (hy' : ∀ a, y a ^ n = 1) :
    ClopenCond T fun _ h => ∀ a, h ≫ x a = h ≫ y a := by
  obtain ⟨u, hu, -⟩ := R.2.2.2.2 T x hx hx'
  obtain ⟨u', hu', -⟩ := R.2.2.2.2 T y hy hy'
  have := R.1
  have := R.2.1
  refine (clopenCond_eq u u').congr fun T' h => ⟨fun H => R.ext fun a => ?_, fun H a => ?_⟩
  · rw [Category.assoc, Category.assoc, hu, hu', H]
  · rw [← hu, ← hu', ← Category.assoc, H, Category.assoc]
end RepTors
end GlobalTheory.LevCover
