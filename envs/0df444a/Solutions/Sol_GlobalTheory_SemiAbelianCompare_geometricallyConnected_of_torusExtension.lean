-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.geometricallyConnected_of_torusExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:45.570565+00:00
-- url     : https://prove2.me/submissions/f77fc6db-cb98-47d1-b0bc-3062ebbf3b8a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_geometricallyConnected_quotient
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_isShortExact_of_torusExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
    GeometricallyConnected G.hom := by
  letI := E.addCommGroup; letI := E.grpB
  have := E.free
  have := E.q_hom
  have := E.q_flat
  have := E.q_surjective
  have := (isShortExact_of_torusExtension E).2.finitePresentation
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  have := geometricallyConnected_quotient E.isKernel
  rw [← Over.w E.q]
  exact GeometricallyConnected.comp _ _
end GlobalTheory.SemiAbelianCompare
