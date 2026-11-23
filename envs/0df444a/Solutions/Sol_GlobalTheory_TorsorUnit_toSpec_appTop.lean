-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.toSpec_appTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:45.013804+00:00
-- url     : https://prove2.me/submissions/32e65532-4c42-4a79-80a5-afeb19392375

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution {R : CommRingCat.{0}} (θ : R →+* Γ(Z, ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom =
      θ := by
  have := SplitTorusPoints.ΓSpecIso_inv_comp_specMap Z.toSpecΓ (CommRingCat.ofHom θ)
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id] at this
  exact congrArg CommRingCat.Hom.hom this
end GlobalTheory.TorsorUnit
