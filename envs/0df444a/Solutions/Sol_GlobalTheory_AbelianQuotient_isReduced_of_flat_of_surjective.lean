-- Prove2me | solution 1 for GlobalTheory.AbelianQuotient.isReduced_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:54.148801+00:00
-- url     : https://prove2.me/submissions/3e024f16-d723-49f0-9eba-c8b3a0e145da

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FormallyUnramifiedOfCompOfEtaleOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_QuotientIsAbelianSchemeOfQuotientScheme
import Theorems.Thm_GlobalTheory_faithfullyFlat_stalkMap_of_flat


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
open GlobalTheory
open GlobalTheory.AbelianQuotient
variable {S : Scheme.{0}}
namespace GlobalTheory.AbelianQuotient
theorem _root_.solution {X Y : Scheme.{0}} (p : X ⟶ Y) [Flat p] [Surjective p]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := p.surjective y
    exact isReduced_of_injective (p.stalkMap x).hom
      (faithfullyFlat_stalkMap_of_flat p x).injective
  exact isReduced_of_isReduced_stalk Y
end GlobalTheory.AbelianQuotient
