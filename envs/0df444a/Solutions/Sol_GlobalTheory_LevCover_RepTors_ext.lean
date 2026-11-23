-- Prove2me | solution 1 for GlobalTheory.LevCover.RepTors.ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:18.752313+00:00
-- url     : https://prove2.me/submissions/178a0727-c464-4663-ab76-d4d10ff2d90b

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
namespace RepTors
theorem _root_.solution {G : Over S} [GrpObj G] {n : ℕ} {La : Type} [AddCommGroup La] {Z : Over S} {et : La → (Z ⟶ G)}
    (R : RepTors G n La Z et) {T : Over S} {u u' : T ⟶ Z} (h : ∀ a, u ≫ et a = u' ≫ et a) : u = u' :=
  (R.2.2.2.2 T (fun a => u' ≫ et a) (fun a c => by rw [R.2.2.1, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, R.2.2.2.1, MonObj.comp_one])).unique h fun _ => rfl
end RepTors
end GlobalTheory.LevCover
