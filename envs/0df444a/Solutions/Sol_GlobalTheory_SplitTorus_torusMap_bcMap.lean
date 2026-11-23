-- Prove2me | solution 1 for GlobalTheory.SplitTorus.torusMap_bcMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:49.343802+00:00
-- url     : https://prove2.me/submissions/9360bbdd-c365-4b32-8957-bb1848d048d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_torusMap_appTop_chi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
variable {X Y}
namespace GlobalTheory.SplitTorus
theorem _root_.solution (φ : Y →+ X) :
    (torusMap S' φ).left ≫ bcMap f Y = bcMap f X ≫ (torusMap S φ).left := by
  let p : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S Y :=
    Over.homMk ((torusMap S' φ).left ≫ bcMap f Y) (by
      rw [Category.assoc, bcMap_hom, ← Category.assoc, Over.w]; rfl)
  let q : Over.mk ((splitTorus S' X).hom ≫ f) ⟶ splitTorus S Y :=
    Over.homMk (bcMap f X ≫ (torusMap S φ).left) (by
      rw [Category.assoc, Over.w, bcMap_hom]; rfl)
  have : p = q := hom_ext fun b => by
    rw [val_eq, val_eq]
    change ((torusMap S' φ).left ≫ bcMap f Y).appTop.hom _ =
      (bcMap f X ≫ (torusMap S φ).left).appTop.hom _
    rw [appTop_comp_apply, appTop_comp_apply, bcMap_appTop_chi, torusMap_appTop_chi,
      torusMap_appTop_chi, bcMap_appTop_chi]
  exact congrArg (·.left) this
end GlobalTheory.SplitTorus
