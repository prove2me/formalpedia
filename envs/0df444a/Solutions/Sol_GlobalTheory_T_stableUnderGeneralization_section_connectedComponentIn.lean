-- Prove2me | solution 1 for GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:21.963455+00:00
-- url     : https://prove2.me/submissions/6d397ba3-b908-4bd8-83fa-3be17ffde5d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponents
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponentsStatement
import Theorems.Thm_GlobalTheory_stableUnderGeneralization_sectionComponents


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → StableUnderGeneralization {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.stableUnderGeneralization_sectionComponents | exact GlobalTheory.stableUnderGeneralization_sectionComponents | (intros; apply GlobalTheory.stableUnderGeneralization_sectionComponents <;> assumption)
end _root_.GlobalTheory.T
