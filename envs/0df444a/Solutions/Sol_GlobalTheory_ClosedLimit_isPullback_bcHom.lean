-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.isPullback_bcHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:14.610927+00:00
-- url     : https://prove2.me/submissions/c522e58f-c4b6-4c9b-b397-47aee514562b

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
import Theorems.Thm_GlobalTheory_ClosedLimit_bcHom_fst
import Theorems.Thm_GlobalTheory_ClosedLimit_bcHom_snd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.ClosedLimit.bcHom_fst
attribute [reassoc] GlobalTheory.ClosedLimit.bcHom_snd

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
theorem _root_.solution {T : Scheme.{0}} (t : T ⟶ Sp k) :
    IsPullback (pullback.fst (g₀ ≫ q) t) (bcHom g₀ q t) g₀ (pullback.fst q t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q t) (v₂₂ := q) (h₃₁ := t) ?_
    (bcHom_fst g₀ q t).symm (.of_hasPullback _ _)
  rw [bcHom_snd]
  exact .of_hasPullback _ _
end GlobalTheory.ClosedLimit
