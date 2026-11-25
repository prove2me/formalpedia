-- Prove2me | solution 1 for GlobalTheory.ClosedLimit.exists_finset_bcHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:33.187259+00:00
-- url     : https://prove2.me/submissions/f9b54147-bc6b-4dc1-b324-885098379631

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
import Theorems.Thm_GlobalTheory_ClosedLimit_exists_isClosedImmersion_of_isLimit
import Theorems.Thm_GlobalTheory_ClosedLimit_isPullback_bcHom
import Theorems.Thm_GlobalTheory_ClosedLimit_isPullback_bcMap_bcHom
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
open GlobalTheory.Spread
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)
namespace GlobalTheory.ClosedLimit
theorem _root_.solution (A : Type) [CommRing A] [Algebra k A] [IsAffine Y₀]
    [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀]
    [IsClosedImmersion (bcHom g₀ q (spMap (algebraMap k A)))] :
    ∃ s : Finset A, IsClosedImmersion
      (bcHom g₀ q (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))) := by
  classical
  let α : bcDiagram (g₀ ≫ q) A ⟶ bcDiagram q A :=
    { app s := bcHom g₀ q _
      naturality s t f := (isPullback_bcMap_bcHom g₀ q _).w }
  have (s : (Finset A)ᵒᵖ) : IsAffine ((bcDiagram q A).obj s) :=
    inferInstanceAs (IsAffine (pullback q
      (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))))
  have (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (α.app s) :=
    MorphismProperty.of_isPullback (isPullback_bcHom g₀ q _) inferInstance
  have : @IsClosedImmersion (bcCone (g₀ ≫ q) A).pt (bcCone q A).pt
    (bcHom g₀ q (spMap (algebraMap k A))) := ‹_›
  obtain ⟨s, hs⟩ := exists_isClosedImmersion_of_isLimit _ _ α (bcCone (g₀ ≫ q) A) (bcCone q A)
    (isLimitBcCone _ _) (isLimitBcCone _ _) (fun f ↦ isPullback_bcMap_bcHom g₀ q _)
    (bcHom g₀ q (spMap (algebraMap k A))) (fun s ↦ (isPullback_bcMap_bcHom g₀ q _).w.symm)
  exact ⟨s.unop, hs⟩
end GlobalTheory.ClosedLimit
