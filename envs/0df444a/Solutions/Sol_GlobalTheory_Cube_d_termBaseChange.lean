-- Prove2me | solution 1 for GlobalTheory.Cube.d_termBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:38:39.659543+00:00
-- url     : https://prove2.me/submissions/857d8c36-7002-4ade-83e1-95a342dba532

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_Cube_termBaseChange_tmul

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
theorem _root_.solution [LinearOrder ι] (A : Cube.{v} ι R) (p : ℕ)
    (x : S ⊗[R] Cube.Term A p) :
    Cube.d (Cube.baseChange S A) p (Cube.termBaseChange S A p x) =
      Cube.termBaseChange S A (p + 1) ((Cube.d A p).baseChange S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    funext t
    rw [LinearMap.baseChange_tmul, Cube.termBaseChange_tmul, Cube.d_apply, Cube.d_apply,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (map_zsmul (TensorProduct.mk R S (A.obj t.1) c) _ _).symm
end Cube
end GlobalTheory
