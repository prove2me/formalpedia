-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.isClosedImmersion_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:53:16.491396+00:00
-- url     : https://prove2.me/submissions/a6c891bf-e98e-494a-a4d7-c63a30099a31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsClosedImmersionDescendsToSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.ClosedLimit
universe u
open GlobalTheory.Spread
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)
namespace GlobalTheory.ClosedLimit
theorem _root_.solution {X Y X' Y' : Scheme.{0}} {g : X ⟶ Y} {πX : X ⟶ X₀}
    {πY : Y ⟶ Y₀} {g' : X' ⟶ Y'} {πX' : X' ⟶ X₀} {πY' : Y' ⟶ Y₀}
    (h : IsPullback πX g g₀ πY) (h' : IsPullback πX' g' g₀ πY') (m : Y' ⟶ Y) (hm : m ≫ πY = πY')
    [IsClosedImmersion g] : IsClosedImmersion g' := by
  subst hm
  have : IsPullback (h.lift πX' (g' ≫ m) (by rw [Category.assoc, h'.w])) g' g m :=
    IsPullback.of_right (by rw [h.lift_fst]; exact h') (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback this inferInstance
end GlobalTheory.ClosedLimit
