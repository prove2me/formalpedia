-- Prove2me | solution 1 for GlobalTheory.ZJ.etale_mulN_and_isOpen_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:22.5162+00:00
-- url     : https://prove2.me/submissions/4d4ece1c-d41f-493b-a400-17c005cad41b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EtaleMulNAndIsOpenOmOfIsSemiAbelian
import Theorems.Thm_GlobalTheory_GrpTangent_etale_mulN


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
theorem _root_.solution (C : Core) (L : C.Law) (T : C.Theta) :
    letI := L.grp; Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left ∧ IsOpen (T.Om L) := by
  letI := L.grp
  letI := L.comm
  have := L.smooth
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have h : Etale (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left := GlobalTheory.GrpTangent.etale_mulN C.GG T.m_unit
  exact ⟨h, (ReciprocityTheory.ChartRestriction.G.Semi.mulN C.GG T.m).left.isOpenMap _ (Out.nonzeroLocus T.s).isOpen⟩
end GlobalTheory.ZJ
