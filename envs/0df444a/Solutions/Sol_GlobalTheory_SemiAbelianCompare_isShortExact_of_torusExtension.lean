-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.isShortExact_of_torusExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:41:27.828806+00:00
-- url     : https://prove2.me/submissions/33fdcaba-a466-48e9-ac12-c043ff09ece3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G
open GlobalTheory GlobalTheory.SemiAbelianCompare
variable {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
namespace GlobalTheory.SemiAbelianCompare
theorem _root_.solution (E : Semi.TorusExtension G) :
    letI := E.addCommGroup; letI := E.grpB
    IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsAbelianScheme E.B ∧ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsShortExact E.i E.q := by
  letI := E.addCommGroup; letI := E.grpB
  have := E.finite
  have := E.q_hom
  have := E.q_flat
  have := E.q_surjective
  exact ⟨(isAbelianScheme_iff _).1 E.isAbelian, E.i_hom, E.q_hom, E.isKernel, E.q_flat,
    E.q_surjective, (quasiCompact_iff_locallyOfFinitePresentation E.isKernel).1 E.q_quasiCompact⟩
end GlobalTheory.SemiAbelianCompare
