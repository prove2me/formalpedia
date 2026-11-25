-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.descends_of_isAffine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:32:38.426707+00:00
-- url     : https://prove2.me/submissions/1830adb7-5824-4a65-b0db-a5662d6cc041

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
import Theorems.Thm_GlobalTheory_ClosedLimit_isPullback_bcHom
import Theorems.Thm_GlobalTheory_ClosedLimit_isClosedImmersion_of_isPullback
import Theorems.Thm_GlobalTheory_ClosedLimit_exists_finset_bcHom

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
namespace GlobalTheory.ClosedLimit
theorem _root_.solution (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0})
    (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [IsAffine Y₀] [QuasiCompact g₀] [QuasiSeparated g₀]
    [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S)
    (hY : IsPullback πY p q (spMap R₀.subtype)) (hX : IsPullback πX g g₀ πY)
    (hg : IsClosedImmersion g) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁),
        πY₁ ≫ q = p₁ ≫ spMap (Subring.inclusion h) → IsPullback πX₁ g₁ g₀ πY₁ →
          IsClosedImmersion g₁ := by
  have hY' : IsPullback πY p q (spMap (algebraMap R₀ S)) := hY
  have := isClosedImmersion_of_isPullback g₀ hX (isPullback_bcHom g₀ q (spMap (algebraMap R₀ S)))
    hY'.isoPullback.inv hY'.isoPullback_inv_fst
  obtain ⟨s, hs'⟩ := exists_finset_bcHom g₀ q S
  refine ⟨s, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let i : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hi : spMap i ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact isClosedImmersion_of_isPullback g₀
    (isPullback_bcHom g₀ q (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))))) hX₁
    (pullback.lift πY₁ (p₁ ≫ spMap i) (by rw [Category.assoc, hi, hY₁])) (pullback.lift_fst _ _ _)
end GlobalTheory.ClosedLimit
