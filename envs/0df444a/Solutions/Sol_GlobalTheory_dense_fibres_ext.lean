-- Prove2me | solution 1 for GlobalTheory.dense_fibres_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:18.685028+00:00
-- url     : https://prove2.me/submissions/7dca5570-e24b-4040-9430-a9bab2ae1fb2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Theorems.Thm_GlobalTheory_hom_ext_of_geometricPoints_dense
import Theorems.Thm_GlobalTheory_exists_lift_closedImmersion_of_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X S : Scheme.{0}) [IsReduced X] (s : X ⟶ S) [Flat s] [LocallyOfFinitePresentation s]
      (Sg : Set S), Dense Sg → Dense (s ⁻¹' Sg) ∧
      (∀ (Y : Scheme.{0}) (t : Y ⟶ S) [IsSeparated t] (f g : X ⟶ Y), f ≫ t = s → g ≫ t = s →
        (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
          Set.range (x ≫ s) ⊆ Sg → x ≫ f = x ≫ g) → f = g) ∧
      (∀ (Y Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y),
        (∀ x : X, s x ∈ Sg → f x ∈ Set.range i) → ∃ f' : X ⟶ Z, f' ≫ i = f) := by
  intro X S _ s _ _ Sg hSg
  have hD : Dense (s ⁻¹' Sg) := hSg.preimage s.isOpenMap
  refine ⟨hD, fun Y t _ f g hf hg H ↦ ?_, fun Y Z i _ f H ↦ ?_⟩
  · refine hom_ext_of_geometricPoints_dense t f g (hf.trans hg.symm) _ hD fun K _ _ x hx ↦ ?_
    refine H K x ?_
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hx ⟨p, rfl⟩
  · exact exists_lift_closedImmersion_of_dense i f _ hD H
end GlobalTheory
