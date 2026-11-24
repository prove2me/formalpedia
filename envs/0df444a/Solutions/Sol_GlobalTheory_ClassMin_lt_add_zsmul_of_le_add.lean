-- Prove2me | solution 1 for GlobalTheory.ClassMin.lt_add_zsmul_of_le_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:01.466394+00:00
-- url     : https://prove2.me/submissions/26fdd995-327c-499e-b54e-d64076a95d34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Theorems.Thm_GlobalTheory_ClassMin_map_add_zsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}
namespace GlobalTheory.ClassMin
theorem _root_.solution (hQ : Q.PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ) {a m : X} {n : ℤ}
    (hn : 2 ≤ n) (h : t * Q a + ν a ≤ t * Q (a + m) + ν (a + m)) (hm : m ≠ 0) :
    t * Q a + ν a < t * Q (a + n • m) + ν (a + n • m) := by
  have h1 := map_add_zsmul Q a m 1
  rw [one_smul] at h1
  rw [h1, map_add] at h
  rw [map_add_zsmul, map_add, map_zsmul, zsmul_eq_mul]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < t * Q m := mul_pos ht (hQ m hm)
  have h2 : 0 ≤ t * polar Q a m + t * Q m + ν m := by push_cast at h; linarith
  have h3 : 0 ≤ (n : ℝ) * (t * polar Q a m + t * Q m + ν m) := mul_nonneg (by linarith) h2
  have h4 : 0 < (n : ℝ) * (n - 1) * (t * Q m) := mul_pos (mul_pos (by linarith) (by linarith)) hp
  nlinarith
end GlobalTheory.ClassMin
