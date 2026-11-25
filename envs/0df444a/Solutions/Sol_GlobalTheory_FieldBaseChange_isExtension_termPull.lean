-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.isExtension_termPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:07:14.779033+00:00
-- url     : https://prove2.me/submissions/05f91f70-59ee-49c4-b055-2e3bf0196e0e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Theorems.Thm_GlobalTheory_FieldBaseChange_isExtension_pullOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (E F : Type) [Field F] [Algebra (FractionRing R) F]
  [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (k : ℕ) (α : D.X) : IsExtension (termPull D E F k α) :=
  isExtension_pullOver (isPullback_famMap D E F) D.P.isLB _ _
end GlobalTheory.FieldBaseChange
