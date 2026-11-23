-- Prove2me | solution 1 for GlobalTheory.Retract.geometrically
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:22.607611+00:00
-- url     : https://prove2.me/submissions/e458fc39-0c8b-4166-a6a5-4dc440b57cc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_exists_baseChange

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
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr
namespace GlobalTheory.Retract
theorem _root_.solution (P : ObjectProperty Scheme.{u})
    (hP : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ A), a ≫ b = 𝟙 A → P B → P A)
    (hg : AlgebraicGeometry.geometrically P g) : AlgebraicGeometry.geometrically P f := by
  intro K _ y Z fst snd h
  obtain ⟨i', r', h₁, -, -, -⟩ := exists_baseChange hir hr h (IsPullback.of_hasPullback g y)
  exact hP i' r' h₁ (pullback_of_geometrically hg K y)
end GlobalTheory.Retract
