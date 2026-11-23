-- Prove2me | solution 1 for GlobalTheory.SharpRel.push_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:22:05.720266+00:00
-- url     : https://prove2.me/submissions/6d106b85-8192-4fb8-9108-1b7a2598438f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.SharpRel
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
namespace GlobalTheory.SharpRel
theorem _root_.solution (h : IsGrpPullback A' A f φ) {p : A ⟶ A} {p' : A' ⟶ A'}
    (e : p'.left ≫ φ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h T (x ≫ p') = pushHom h T x ≫ p := by
  ext1
  change (x ≫ p').left ≫ φ = (x.left ≫ φ) ≫ p.left
  rw [Over.comp_left, Category.assoc, Category.assoc, e]
end GlobalTheory.SharpRel
