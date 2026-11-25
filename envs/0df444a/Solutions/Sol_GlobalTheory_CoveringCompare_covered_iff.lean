-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.covered_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:38.390012+00:00
-- url     : https://prove2.me/submissions/9adb3c01-d48a-45cd-86f8-797c2715223f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
import Theorems.Thm_GlobalTheory_CoveringCompare_isChartAt_iff

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
theorem _root_.solution (Y : Model Xo c β) (p : ℕ) : (∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p := by
  refine forall_congr' fun x => ⟨?_, ?_⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).2 (h₁ i),
      fun V C _ _ _ _ _ _ _ _ => h₂ C V⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).1 (h₁ i),
      fun C V _ _ _ _ _ _ _ _ => h₂ V C⟩
end GlobalTheory.CoveringCompare
