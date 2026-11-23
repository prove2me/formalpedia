-- Prove2me | solution 1 for GlobalTheory.bijective_restrictPoints_of_existsUnique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:46.161729+00:00
-- url     : https://prove2.me/submissions/a1b081b4-7af6-41e0-b307-7e46f9913470

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S)
    (i : T₀ ⟶ T)
    (H : ∀ g : T₀ ⟶ X, g ≫ f = i ≫ h → ∃! l : T ⟶ X, i ≫ l = g ∧ l ≫ f = h) :
    Function.Bijective (restrictPoints f h i) := by
  rw [Function.bijective_iff_existsUnique]
  rintro ⟨g, hg⟩
  obtain ⟨l, ⟨h₁, h₂⟩, h₃⟩ := H g hg
  exact ⟨⟨l, h₂⟩, Subtype.ext h₁, fun y hy ↦ Subtype.ext (h₃ _ ⟨congr(($hy).1), y.2⟩)⟩
end GlobalTheory
