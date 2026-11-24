-- Prove2me | solution 1 for GlobalTheory.SS.IdemSplit.isMonHom_ret
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:00.583813+00:00
-- url     : https://prove2.me/submissions/6596c984-6fc6-43be-bee9-68a262a76fcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmConnIdempotentSplits

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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.IdemSplit
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] {G H : C} [GrpObj G]
  (i : H ⟶ G) (r : G ⟶ H) (hir : i ≫ r = 𝟙 H) [he : IsMonHom (r ≫ i)]
namespace GlobalTheory.SS.IdemSplit
theorem _root_.solution : letI := grpObj i r hir; IsMonHom r :=
  letI := grpObj i r hir
  { one_hom := rfl
    mul_hom := by
      haveI : Mono i := (SplitMono.mk r hir).mono
      change μ[G] ≫ r = (r ⊗ₘ r) ≫ (i ⊗ₘ i) ≫ μ[G] ≫ r
      rw [← cancel_mono i, Category.assoc, Category.assoc (r ⊗ₘ r), mul_comp i r hir,
        tensorHom_comp_tensorHom_assoc, IsMonHom.mul_hom] }
end GlobalTheory.SS.IdemSplit
