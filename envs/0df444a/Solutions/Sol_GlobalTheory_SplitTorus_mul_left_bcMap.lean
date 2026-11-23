-- Prove2me | solution 1 for GlobalTheory.SplitTorus.mul_left_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:13.101076+00:00
-- url     : https://prove2.me/submissions/20e573a3-0152-4e1a-a619-8f1f5da538bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_bcIso_hom_fst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.SplitTorus.bcIso_hom_fst

set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S S' : Scheme.{u}} (f : S' ⟶ S) (X Y : Type u) [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.SplitTorus
theorem _root_.solution (T : Over S') (x y : T ⟶ splitTorus S' X)
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ splitTorus S X) (hx : x₀.left = x.left ≫ bcMap f X)
    (hy : y₀.left = y.left ≫ bcMap f X) : (x₀ * y₀).left = (x * y).left ≫ bcMap f X := by
  have h := mul_left_comp_fst (splitTorus S X) f (x ≫ (bcIso f X).hom) (y ≫ (bcIso f X).hom) x₀ y₀
    (by rw [hx, Over.comp_left, Category.assoc, bcIso_hom_fst])
    (by rw [hy, Over.comp_left, Category.assoc, bcIso_hom_fst])
  rw [h, ← MonObj.mul_comp, Over.comp_left, Category.assoc, bcIso_hom_fst]
end GlobalTheory.SplitTorus
