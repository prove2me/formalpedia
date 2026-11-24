-- Prove2me | solution 1 for GlobalTheory.FlatPoints.eq_zero_of_forall_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:42.821555+00:00
-- url     : https://prove2.me/submissions/e9074d5f-578a-4450-95b0-85e76784453d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Theorems.Thm_GlobalTheory_tensor_eq_zero_of_forall_geometric_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FlatPoints
namespace GlobalTheory.FlatPoints
theorem _root_.solution (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F]
    (hinj : Function.Injective (algebraMap O F)) (A : Type) [CommRing A] [Algebra O A]
    [Module.Finite O A] [Module.Flat O A] [_root_.IsReduced (TensorProduct O F A)] (a : A)
    (ha : ∀ φ : A →ₐ[O] F, φ a = 0) : a = 0 := by
  have := tensor_eq_zero_of_forall_geometric_point O F hinj A O (a ⊗ₜ 1) (fun φ => by simp [ha φ])
  simpa using congrArg (TensorProduct.rid O A) this
end GlobalTheory.FlatPoints
