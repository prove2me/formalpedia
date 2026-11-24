-- Prove2me | solution 1 for GlobalTheory.ZM.LocalCoord.resG_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:15.319908+00:00
-- url     : https://prove2.me/submissions/f558cd81-f38e-4683-bc39-67b1e0617001

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
theorem _root_.solution {X Y : Scheme.{0}} (x : Y ⟶ X) {U : X.Opens} {V V' : Y.Opens} (h : V ≤ x ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(X, U)) : resG Y hV ((x.appLE U V h).hom a) = (x.appLE U V' (hV.trans h)).hom a := by
  unfold resG
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
end GlobalTheory.ZM.LocalCoord
