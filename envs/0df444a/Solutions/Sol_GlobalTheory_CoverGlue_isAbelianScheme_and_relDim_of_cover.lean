-- Prove2me | solution 1 for GlobalTheory.CoverGlue.isAbelianScheme_and_relDim_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:02.824197+00:00
-- url     : https://prove2.me/submissions/4041be7a-0eb2-4883-a174-6f9c6ec0b53d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCover
import Theorems.Thm_GlobalTheory_CoverGlue_of_isPullback_cover
import Theorems.Thm_GlobalTheory_CoverGlue_isCommMonObj_of_cover

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
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ((∀ i, IsAbelianScheme (G i)) → IsAbelianScheme A) ∧ ∀ g : ℕ, (∀ i, SmoothOfRelativeDimension g (G i).hom) → SmoothOfRelativeDimension g A.hom := by
  intro S I U A _ G _ ψ hU h
  refine ⟨fun hab => ?_, fun g hg => ?_⟩
  · constructor
    · exact isCommMonObj_of_cover hU h fun i => (hab i).comm
    · exact @of_isPullback_cover @Smooth (HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth) _ _ _ _ hU _ _ _ _
        (fun i => (h i).1) fun i => (hab i).smooth
    · exact of_isPullback_cover @IsProper hU (fun i => (h i).1) fun i => (hab i).proper
    · refine ⟨?_⟩
      exact of_isPullback_cover (geometrically (ConnectedSpace ·)) hU (fun i => (h i).1)
        fun i => (hab i).geomConnected.geometrically_connectedSpace
  · exact @of_isPullback_cover (@SmoothOfRelativeDimension g)
      (HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension g)) _ _ _ _ hU _ _ _ _
      (fun i => (h i).1) hg
end GlobalTheory.CoverGlue
