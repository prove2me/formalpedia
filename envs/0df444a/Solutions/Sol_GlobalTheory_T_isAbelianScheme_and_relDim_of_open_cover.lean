-- Prove2me | solution 1 for GlobalTheory.T.isAbelianScheme_and_relDim_of_open_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:49.38849+00:00
-- url     : https://prove2.me/submissions/e03f416b-fed5-4a5c-9583-b228f3fe9520

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCoverStatement
import Theorems.Thm_GlobalTheory_CoverGlue_isAbelianScheme_and_relDim_of_cover


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ((∀ i, IsAbelianScheme (G i)) → IsAbelianScheme A) ∧ ∀ g : ℕ, (∀ i, SmoothOfRelativeDimension g (G i).hom) → SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.CoverGlue.isAbelianScheme_and_relDim_of_cover | exact GlobalTheory.CoverGlue.isAbelianScheme_and_relDim_of_cover | (intros; apply GlobalTheory.CoverGlue.isAbelianScheme_and_relDim_of_cover <;> assumption)
end _root_.GlobalTheory.T
