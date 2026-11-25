-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eq_principalPart_add_regularPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:49.921171+00:00
-- url     : https://prove2.me/submissions/f730577d-a543-46d4-98a6-01f42cd75624

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_sum_add_dslopeIter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (f : ℂ → ℂ) (p : ℂ) {z : ℂ} (hz : z ≠ p) :
    f z = principalPart f p z + regularPart f p z := by
  set n := meromorphicShift f p
  have h := eq_sum_add_dslopeIter p (laurentNumerator f p) (n + 1) z
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hz
  have hpow : (z - p) ^ (n + 1) ≠ 0 := pow_ne_zero _ hzp
  apply mul_left_cancel₀ hpow
  have e1 : (z - p) ^ (n + 1) * f z = laurentNumerator f p z := rfl
  rw [e1, h, mul_add, principalPart, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n + 1 := by simp only [Finset.mem_range] at hj; omega
  have e2 : (z - p) ^ (n + 1) = (z - p) ^ (n + 1 - j) * (z - p) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  have hpj : (z - p) ^ (n + 1 - j) ≠ 0 := pow_ne_zero _ hzp
  rw [laurentCoeff, e2]
  field_simp
  rfl
end GroundTheory.Global.Elliptic
