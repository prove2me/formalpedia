-- Prove2me | solution 1 for GlobalTheory.PsiSpread.exists_finite_cube_induction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:53.971504+00:00
-- url     : https://prove2.me/submissions/0d1669fe-9274-47fe-8300-771a37a14de7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction

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
noncomputable section
open GlobalTheory
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.PsiSpread
theorem _root_.solution (X : Type) [AddCommGroup X] [Module.Finite ℤ X] :
    ∃ S : Set X, S.Finite ∧ ∀ E : X → Prop, (∀ x ∈ S, E x) →
      (∀ a a' b, E a → E a' → E b → E (a + a') → E (a + b) → E (a' + b) → E (a + a' + b)) → ∀ x, E x := by
  have h : AddMonoid.FG X := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨G, hG⟩ := h.fg_top
  refine ⟨insert 0 ((G : Set X) ∪ Set.image2 (· + ·) (G : Set X) G),
    (G.finite_toSet.union (G.finite_toSet.image2 _ G.finite_toSet)).insert _, fun E hS hE x => ?_⟩
  have h₁ : ∀ g ∈ (G : Set X), E g := fun g hg => hS g (Or.inr (Or.inl hg))
  have key : E x ∧ ∀ g ∈ (G : Set X), E (g + x) := by
    refine AddSubmonoid.induction_of_closure_eq_top_left (motive := fun x => E x ∧ ∀ g ∈ (G : Set X), E (g + x))
      hG x ⟨hS 0 (Or.inl rfl), fun g hg => by rw [add_zero]; exact h₁ g hg⟩ fun g hg y hy => ⟨hy.2 g hg, fun g' hg' => ?_⟩
    rw [← add_assoc]
    exact hE g' g y (h₁ _ hg') (h₁ _ hg) hy.1 (hS _ (Or.inr (Or.inr ⟨g', hg', g, hg, rfl⟩))) (hy.2 _ hg') (hy.2 _ hg)
  exact key.1
end GlobalTheory.PsiSpread
