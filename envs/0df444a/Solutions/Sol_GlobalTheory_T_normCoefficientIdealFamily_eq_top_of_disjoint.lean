-- Prove2me | solution 1 for GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:20.882942+00:00
-- url     : https://prove2.me/submissions/abd049aa-1be9-4dba-9042-63e122b13842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjointStatement
import Theorems.Thm_GlobalTheory_NormSheafDescent_famIdeal_eq_top_of_disjoint


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
theorem _root_.solution : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | exact GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint <;> assumption)
end _root_.GlobalTheory.T
