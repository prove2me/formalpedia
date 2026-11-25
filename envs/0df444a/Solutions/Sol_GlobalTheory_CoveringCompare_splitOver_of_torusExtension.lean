-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.splitOver_of_torusExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:10.105027+00:00
-- url     : https://prove2.me/submissions/f735ecce-041f-4d9e-8657-af9c45520246

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
import Theorems.Thm_GlobalTheory_exists_splitExt_isGt_of_torusExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
namespace GlobalTheory.CoveringCompare
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩
end GlobalTheory.CoveringCompare
