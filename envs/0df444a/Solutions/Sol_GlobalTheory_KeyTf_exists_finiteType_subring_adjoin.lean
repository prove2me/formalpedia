-- Prove2me | solution 1 for GlobalTheory.KeyTf.exists_finiteType_subring_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:02.830881+00:00
-- url     : https://prove2.me/submissions/8ba4af5b-61ff-4116-9956-681899bd6e45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFiniteTypeSubringAdjoin

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
open GlobalTheory GlobalTheory.KeyTf
namespace GlobalTheory.KeyTf
namespace _root_.GlobalTheory.KeyTf
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (F : Finset S), Algebra.FiniteType ℤ R₀ →
      ∃ R₁ : Subring S, R₀ ≤ R₁ ∧ (F : Set S) ⊆ R₁ ∧ Algebra.FiniteType ℤ R₁ := by
  intro S _ R₀ F hR₀
  classical
  obtain ⟨s, hs⟩ := hR₀.out
  let T : Finset S := s.image (Subtype.val) ∪ F
  refine ⟨(Algebra.adjoin ℤ (T : Set S)).toSubring, ?_, ?_, ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : R₀) ∈ Algebra.adjoin ℤ (s : Set R₀) := hs ▸ Algebra.mem_top
    have h2 : x ∈ (Algebra.adjoin ℤ (s : Set R₀)).map R₀.subtype.toIntAlgHom :=
      Subalgebra.mem_map.2 ⟨_, hmem, rfl⟩
    rw [← Algebra.adjoin_image] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy)
  · intro x hx
    exact Algebra.subset_adjoin (Finset.mem_union_right _ hx)
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨T, rfl⟩
end _root_.GlobalTheory.KeyTf
end GlobalTheory.KeyTf
