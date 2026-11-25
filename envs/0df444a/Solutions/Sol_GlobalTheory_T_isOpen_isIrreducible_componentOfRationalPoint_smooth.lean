-- Prove2me | solution 1 for GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:38.511924+00:00
-- url     : https://prove2.me/submissions/7a0a29d7-23b9-4112-a842-7c09e01e29c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
import Theorems.Thm_GlobalTheory_isOpen_and_isIrreducible_sectionComponent_of_smooth_field


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
theorem _root_.solution : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
end _root_.GlobalTheory.T
