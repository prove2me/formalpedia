-- Prove2me | solution 1 for GlobalTheory.TorsorUnit.comp_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:09.277616+00:00
-- url     : https://prove2.me/submissions/f29f134b-dd39-4fc7-953e-b8144304a05d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Theorems.Thm_GlobalTheory_TorsorUnit_ev_single
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
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']
namespace GlobalTheory.TorsorUnit
theorem _root_.solution (f : R →+* R') (θ : C →+* R) (φ : Multiplicative X →* Rˣ) :
    f.comp (ev θ φ) = ev (f.comp θ) ((Units.map f.toMonoidHom).comp φ) := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro a <;> simp [ev_single]
end GlobalTheory.TorsorUnit
