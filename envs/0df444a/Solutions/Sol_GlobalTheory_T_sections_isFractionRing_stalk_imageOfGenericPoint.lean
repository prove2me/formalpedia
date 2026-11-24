-- Prove2me | solution 1 for GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:26.425273+00:00
-- url     : https://prove2.me/submissions/c779b40a-42f8-411f-925e-57ed09c9634a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
import Theorems.Thm_GlobalTheory_NormSheafDescent_sections_isDomain_isFractionRing_stalk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  first | exact @GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | exact GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | (intros; apply GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk <;> assumption)
end _root_.GlobalTheory.T
