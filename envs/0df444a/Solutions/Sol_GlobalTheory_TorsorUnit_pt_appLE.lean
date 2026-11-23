-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.pt_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:14:57.231097+00:00
-- url     : https://prove2.me/submissions/fa88755a-5fd9-42a4-afd9-3ff501fa3c16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_toSpec_appTop

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
theorem _root_.solution (hU : IsAffineOpen U) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) (e : ⊤ ≤ pt hU θ ⁻¹ᵁ U) :
    ((pt hU θ).appLE U ⊤ e).hom = θ := by
  have h1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans (Category.comp_id _)
  have h2 := Scheme.Hom.appLE_comp_appLE (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec
    U ⊤ ⊤ hU.fromSpec_preimage_self.ge le_rfl
  rw [h1] at h2
  have h3 : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3] at h2
  exact (congrArg CommRingCat.Hom.hom h2).symm.trans (toSpec_appTop θ)
end GlobalTheory.TorsorUnit
