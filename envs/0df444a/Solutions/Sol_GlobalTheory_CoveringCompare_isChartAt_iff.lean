-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.isChartAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:47:59.891751+00:00
-- url     : https://prove2.me/submissions/e24bfaee-1ee9-4df4-9219-a69b04dd63e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoveringCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.CoveringCompare
theorem _root_.solution (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) :
    CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, f, g⟩, e⟩, fun ⟨⟨a, b, c, d, f, g⟩, e⟩ => ⟨a, b, c, d, e, f, g⟩⟩
end GlobalTheory.CoveringCompare
