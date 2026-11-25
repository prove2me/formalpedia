-- Prove2me | solution 1 for GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:15.499314+00:00
-- url     : https://prove2.me/submissions/1dc33283-2b6e-42ab-aae8-36eef010e613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Theorems.Thm_GlobalTheory_sectionComponents_preimage_of_isPullback


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
theorem _root_.solution : ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X) (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  first | exact @GlobalTheory.sectionComponents_preimage_of_isPullback | exact GlobalTheory.sectionComponents_preimage_of_isPullback | (intros; apply GlobalTheory.sectionComponents_preimage_of_isPullback <;> assumption)
end _root_.GlobalTheory.T
