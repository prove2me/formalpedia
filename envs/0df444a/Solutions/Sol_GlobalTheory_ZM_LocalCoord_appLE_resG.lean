-- Prove2me | solution 1 for GlobalTheory.ZM.LocalCoord.appLE_resG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:14.46347+00:00
-- url     : https://prove2.me/submissions/feee59e5-edbf-4f43-8908-a013bf95dd84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocally

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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.LocalCoord
namespace GlobalTheory.ZM.LocalCoord
theorem _root_.solution {X Y : Scheme.{0}} (x : Y ⟶ X) {U U' : X.Opens} (hU : U' ≤ U) {V : Y.Opens} (h : V ≤ x ⁻¹ᵁ U')
    (a : Γ(X, U)) : (x.appLE U' V h).hom (resG X hU a) = (x.appLE U V (h.trans (x.preimage_mono hU))).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
end GlobalTheory.ZM.LocalCoord
