-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.exists_eq_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:44.429512+00:00
-- url     : https://prove2.me/submissions/0663b00a-6a35-4c4c-9eee-6ffb1db3da8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}
namespace GlobalTheory.TorsorUnit
theorem _root_.solution (hU : IsAffineOpen U) (g : Z ⟶ Y) (e : ⊤ ≤ g ⁻¹ᵁ U) :
    ∃ θ, g = pt hU θ := by
  have hr : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact e trivial
  let l := IsOpenImmersion.lift hU.fromSpec g hr
  refine ⟨((Scheme.ΓSpecIso _).inv ≫ l.appTop).hom, ?_⟩
  rw [pt, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp_assoc,
    Iso.inv_hom_id, Spec.map_id]
  exact (IsOpenImmersion.lift_fac _ _ hr).symm.trans (congrArg (l ≫ ·) (Category.id_comp _).symm)
end GlobalTheory.TorsorUnit
