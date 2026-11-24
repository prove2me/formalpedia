-- Prove2me | solution 1 for GlobalTheory.TorusTrivial.cover_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:15.577196+00:00
-- url     : https://prove2.me/submissions/40afc9a3-da02-408e-9a91-b76a45826cc0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusTrivial
namespace GlobalTheory.TorusTrivial
theorem _root_.solution {P Y Z W : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback a b f g)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) b :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hf.1.1,
    MorphismProperty.of_isPullback (P := @Flat) h hf.1.2⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h hf.2⟩
end GlobalTheory.TorusTrivial
