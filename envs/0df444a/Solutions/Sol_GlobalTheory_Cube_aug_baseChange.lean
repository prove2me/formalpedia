-- Prove2me | solution 1 for GlobalTheory.Cube.aug_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:27.013197+00:00
-- url     : https://prove2.me/submissions/1940264d-0839-41bb-9cbf-bf17aa10e5bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι R) (x : S ⊗[R] A.obj ∅) :
    Cube.aug (Cube.baseChange S A) x = Cube.termBaseChange S A 1 ((Cube.aug A).baseChange S x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (by simp only [map_zero])
  | add x y hx hy => exact (map_add _ _ _).trans (by simp only [map_add, hx, hy])
  | tmul c x => rfl
end Cube
end GlobalTheory
