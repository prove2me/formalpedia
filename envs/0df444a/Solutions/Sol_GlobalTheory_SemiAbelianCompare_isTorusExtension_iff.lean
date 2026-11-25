-- Prove2me | solution 1 for GlobalTheory.SemiAbelianCompare.isTorusExtension_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:55:06.53979+00:00
-- url     : https://prove2.me/submissions/9421cd17-b1cc-4082-a753-3f0d1b182c66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuasiCompactIffLocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_SemiAbelianCompare_isShortExact_of_torusExtension

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
variable (G)
namespace GlobalTheory.SemiAbelianCompare
theorem _root_.solution :
    IsCommMonObj G ∧ Nonempty (Semi.TorusExtension G) ↔ IndefiniteRowSideFullHecke.SemiAbelianSchemes.IsTorusExtension G :=
  and_congr_right fun _ =>
    ⟨fun ⟨E⟩ => ⟨E.X, E.addCommGroup, E.free, E.finite, E.B, E.grpB, E.i, E.q,
      isShortExact_of_torusExtension E⟩,
    fun ⟨_, _, _, _, _, _, _, _, hB, h⟩ => ⟨torusExtensionOfIsShortExact hB h⟩⟩
end GlobalTheory.SemiAbelianCompare
