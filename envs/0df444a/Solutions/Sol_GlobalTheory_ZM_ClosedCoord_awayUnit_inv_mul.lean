-- Prove2me | solution 1 for GlobalTheory.ZM.ClosedCoord.awayUnit_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:19.903377+00:00
-- url     : https://prove2.me/submissions/292e9af2-4404-46ba-b020-832b5c29cd7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProjectiveCoordinateRepresentationClosedSubsch
import Theorems.Thm_GlobalTheory_ZM_ClosedCoord_awayUnit_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ClosedCoord
open MvPolynomial
namespace GlobalTheory.ZM.ClosedCoord
theorem _root_.solution {R' : Type} [CommRing R'] (r : R') :
    ((awayUnit r)⁻¹ : (Localization.Away r)ˣ) * algebraMap R' (Localization.Away r) r = 1 := by
  rw [← awayUnit_coe]; exact Units.inv_mul _
end GlobalTheory.ZM.ClosedCoord
