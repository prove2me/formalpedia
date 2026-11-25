-- Prove2me | solution 1 for GlobalTheory.isSemiAbelian_of_isAbelianScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:16.740821+00:00
-- url     : https://prove2.me/submissions/c7efe6c9-a5fb-4d8c-993b-f90dcd62dbf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeOfGenericallySurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Theorems.Thm_GlobalTheory_isAbelianScheme_pullback_obj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (h : IsAbelianScheme A) : IsSemiAbelian A where
  comm := h.comm
  smooth := h.smooth
  separated := by have := h.proper; infer_instance
  quasiCompact := by have := h.proper; infer_instance
  geomConnected := h.geomConnected
  fibres := fun _ _ _ p => ⟨torusExtensionOfAbelian _ (isAbelianScheme_pullback_obj p A h)⟩
end GlobalTheory
