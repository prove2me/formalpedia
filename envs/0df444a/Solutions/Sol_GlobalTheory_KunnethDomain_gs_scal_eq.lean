-- Prove2me | solution 1 for GlobalTheory.KunnethDomain.gs_scal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:11:03.836049+00:00
-- url     : https://prove2.me/submissions/54512697-4942-4efa-bc15-25163c3c6a43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqSumMulOfIsDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.KunnethDomain
open ReciprocityTheory.ChartRestriction.G.DVR
variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.KunnethDomain
theorem _root_.solution {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (ρ : T ⟶ Y) (z : T) (c : R) :
    gs ρ z ⊤ (scal p c) = cst (ρ ≫ p) z c := by
  rw [gs_eq ρ z ⊤ trivial]; rfl
end GlobalTheory.KunnethDomain
