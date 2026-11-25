-- Prove2me | solution 1 for GlobalTheory.mem_span_of_forall_germ_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:21:00.707538+00:00
-- url     : https://prove2.me/submissions/c860ba0e-2815-4d4a-9732-f04fff33eb12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemSpanOfForallGermMemSpan
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
namespace GlobalTheory
private theorem gs_id_eq_germ (X : Scheme.{0}) (V : X.Opens) (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = X.presheaf.germ V y hy a := by
  rw [gs_eq (𝟙 X) y V hy a]
  rfl
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X : Scheme.{0}) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (r : Γ(X, V)), IsAffineOpen V → (∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i))) → r ∈ Ideal.span (Set.range f) := by
  intro X V J f r hV h
  rw [hV.mem_ideal_iff]
  intro y hy
  rw [Ideal.map_span, ← Set.range_comp]
  by_cases hz : ∀ i, y ∉ X.basicOpen (f i)
  · have hr := h y hy hz
    simp only [gs_id_eq_germ X V y hy] at hr
    exact hr
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    rw [X.mem_basicOpen (f i) y hy] at hi
    have hmem : X.presheaf.germ V y hy (f i) ∈ Ideal.span (Set.range (⇑(X.presheaf.germ V y hy).hom ∘ f)) :=
      Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_of_isUnit_mem _ hmem hi]
    trivial
end GlobalTheory
