-- Prove2me | solution 1 for GlobalTheory.AbLaw.bijective_appLE_of_le_opensRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:54:51.001607+00:00
-- url     : https://prove2.me/submissions/d813fc08-da56-4aaf-9764-91fba0d99bad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechLBPullIsoOfIsOpenImmersion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
theorem _root_.solution {Y Y' : Scheme.{0}} (e : Y' ⟶ Y) [IsOpenImmersion e]
    {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens} (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (e.appLE V V' h).hom := by
  obtain rfl : V' = e ⁻¹ᵁ V := le_antisymm h h'
  have := e.isIso_app V hV
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.app V)
end GlobalTheory.AbLaw
