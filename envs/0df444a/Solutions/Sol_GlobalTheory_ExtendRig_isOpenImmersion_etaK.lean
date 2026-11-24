-- Prove2me | solution 1 for GlobalTheory.ExtendRig.isOpenImmersion_etaK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:45.261434+00:00
-- url     : https://prove2.me/submissions/e72aef84-cc37-41da-923c-71948c7e836e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_ExtendRig_isLocalization_away_of_irreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtendRig
namespace GlobalTheory.ExtendRig
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] :
    IsOpenImmersion (etaK V K) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := isLocalization_away_of_irreducible V K hπ
  exact IsOpenImmersion.of_isLocalization π
end GlobalTheory.ExtendRig
