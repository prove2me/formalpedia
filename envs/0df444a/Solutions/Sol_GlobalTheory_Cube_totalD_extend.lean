-- Prove2me | solution 1 for GlobalTheory.Cube.totalD_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:28.050612+00:00
-- url     : https://prove2.me/submissions/abf6d389-4e80-49e7-bdc5-9b554966d4b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_extend
import Theorems.Thm_GlobalTheory_Cube_ext_restrictDeg
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_succ
import Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_zero
import Theorems.Thm_GlobalTheory_Cube_extend_apply_of_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
variable [LinearOrder ι]
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) :
    totalD A (extend A p x) = extend A (p + 1) (d A p x) := by
  have key : ∀ (p q : ℕ) (x : Term A p), q ≠ p → restrictDeg A q (extend A p x) = 0 :=
    fun p q x h => funext fun s => extend_apply_of_ne A x (by rw [s.2]; exact h)
  refine ext_restrictDeg fun q => ?_
  cases q with
  | zero => rw [restrictDeg_totalD_zero, key _ _ _ (by omega)]
  | succ q =>
    rw [restrictDeg_totalD_succ]
    by_cases h : q = p
    · subst h
      rw [restrictDeg_extend, restrictDeg_extend]
    · rw [key _ _ _ h, key _ _ _ (by omega), map_zero]
end GlobalTheory.Cube
