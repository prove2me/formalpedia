-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.surjective_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:51.061666+00:00
-- url     : https://prove2.me/submissions/401b68d0-8942-495a-b15c-dc4eebda3827

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
namespace GlobalTheory.ClosedLimit
theorem _root_.solution {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {a : A ⟶ A'} {b : B ⟶ B'}
    {f' : A' ⟶ B'} (po : IsPushout f a b f') (s : Set B)
    (hs : Subring.closure (Set.range f.hom ∪ s) = ⊤) (h : ∀ x ∈ s, b.hom x ∈ f'.hom.range) :
    Function.Surjective f'.hom := by
  have h₁ : (⊤ : Subring B) ≤ f'.hom.range.comap b.hom := by
    rw [← hs, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | hx)
    · exact ⟨a.hom y, congr($(po.w.symm).hom y)⟩
    · exact h _ hx
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨y, rfl⟩ | hx)
  · exact h₁ (Subring.mem_top y)
  · exact hx
end GlobalTheory.ClosedLimit
