-- Prove2me | solution 1 for GlobalTheory.Retract.exists_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:37.863328+00:00
-- url     : https://prove2.me/submissions/e8d19ea6-5cb9-4626-8b9a-99df8f82309d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_section_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
namespace GlobalTheory.Retract
theorem _root_.solution (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) {T X' Y' : Scheme.{u}} {y : T ⟶ S}
    {a : X' ⟶ X} {f' : X' ⟶ T} (hX : IsPullback a f' f y)
    {b : Y' ⟶ Y} {g' : Y' ⟶ T} (hY : IsPullback b g' g y) :
    ∃ (i' : X' ⟶ Y') (r' : Y' ⟶ X'), i' ≫ r' = 𝟙 X' ∧ r' ≫ f' = g' ∧
      i' ≫ b = a ≫ i ∧ r' ≫ a = b ≫ r := by
  refine ⟨hY.lift (a ≫ i) f' (by rw [Category.assoc, section_comp hir hr, hX.w]),
    hX.lift (b ≫ r) g' (by rw [Category.assoc, hr, hY.w]), ?_, by simp, by simp, by simp⟩
  apply hX.hom_ext <;> simp [hir]
end GlobalTheory.Retract
