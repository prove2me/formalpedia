-- Prove2me | solution 1 for GlobalTheory.exists_common_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:43.424939+00:00
-- url     : https://prove2.me/submissions/98e542cb-49a0-487f-9f30-05310d338ea2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
namespace GlobalTheory
theorem _root_.solution {i : I} {A : Type} [Finite A] (P : A → ∀ j : I, (j ⟶ i) → Prop)
    (stable : ∀ a j (f : j ⟶ i) k (g : k ⟶ j), P a j f → P a k (g ≫ f))
    (h : ∀ a, ∃ j f, P a j f) : ∃ j f, ∀ a, P a j f := by
  classical
  have key : ∀ s : Finset A, ∃ j f, ∀ a ∈ s, P a j f := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert a s _ ih =>
      obtain ⟨j, f, hj⟩ := ih
      obtain ⟨j', f', hj'⟩ := h a
      obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
      refine ⟨k, g ≫ f, fun b hb => ?_⟩
      rcases Finset.mem_insert.1 hb with rfl | hb
      · rw [hg]; exact stable _ _ _ _ _ hj'
      · exact stable _ _ _ _ _ (hj b hb)
  have := Fintype.ofFinite A
  obtain ⟨j, f, hj⟩ := key Finset.univ
  exact ⟨j, f, fun a => hj a (Finset.mem_univ a)⟩
end GlobalTheory
