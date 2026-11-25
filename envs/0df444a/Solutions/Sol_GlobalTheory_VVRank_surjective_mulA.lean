-- Prove2me | solution 1 for GlobalTheory.VVRank.surjective_mulA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:22.724828+00:00
-- url     : https://prove2.me/submissions/204c604f-89c8-4704-b423-884c6028fde1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_AbLaw_MulN_isMonHom_mulA
import Theorems.Thm_GlobalTheory_AbLaw_MulN_isPullback_baseChange
import Theorems.Thm_GlobalTheory_AbLaw_MulN_surjective_of_geomFibres
import Theorems.Thm_GlobalTheory_MulFinite_isFinite_of_relAmple
import Theorems.Thm_GlobalTheory_flat_and_surjective_of_isFinite_abelianEnd
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution (P : PolAV S) (n : ℕ) (hn : n ≠ 0)
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![((n ^ 2 : ℕ) : ℤ), -1]))
    (hα : α.IsGen) : Surjective (mulA P.A n).left := by
  have := P.isAb.proper
  have := P.isAb.comm
  have hf := MulFinite.isFinite_of_relAmple P.A P.L P.isLB P.ample _ (n ^ 2) (by positivity) α hα
  have hm := AbLaw.MulN.isMonHom_mulA P.A n
  exact AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t =>
    (flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
      (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (AbLaw.MulN.isPullback_baseChange t _) hf)).2
end GlobalTheory.VVRank
