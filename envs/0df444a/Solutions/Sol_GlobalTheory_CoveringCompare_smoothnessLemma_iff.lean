-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.smoothnessLemma_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:59.687294+00:00
-- url     : https://prove2.me/submissions/d280a10e-40b5-4f18-b145-c81156fefc29

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
namespace GlobalTheory.CoveringCompare
theorem _root_.solution : UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma := Iff.rfl
end GlobalTheory.CoveringCompare
