-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.isPullback_bcMap_bcHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:41:05.592196+00:00
-- url     : https://prove2.me/submissions/942b21d2-ee5c-417f-8a64-196646671a0d

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
import Theorems.Thm_GlobalTheory_ClosedLimit_isPullback_bcHom
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
theorem _root_.solution {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) :
    IsPullback (bcMap (g₀ ≫ q) f) (bcHom g₀ q _) (bcHom g₀ q _) (bcMap q f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := g₀) (h₂₂ := pullback.fst _ _) ?_ ?_
    (isPullback_bcHom g₀ q _)
  · rw [bcMap_fst, bcMap_fst]
    exact isPullback_bcHom g₀ q _
  · apply pullback.hom_ext
    · rw [Category.assoc, bcHom_fst, bcMap_fst_assoc, Category.assoc, bcMap_fst, bcHom_fst]
    · rw [Category.assoc, bcHom_snd, bcMap_snd, Category.assoc, bcMap_snd, bcHom_snd_assoc]
end GlobalTheory.ClosedLimit
