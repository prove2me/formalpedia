-- Prove2me | solution 1 for GlobalTheory.ExtendRig.isRegularRing_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:49.934858+00:00
-- url     : https://prove2.me/submissions/cc0b091f-39cf-49dc-bf00-09903d321aed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing

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
    [IsDiscreteValuationRing V] : IsRegularRing V :=
  have : IsDedekindDomain V := IsPrincipalIdealRing.isDedekindDomain V
  inferInstance
end GlobalTheory.ExtendRig
