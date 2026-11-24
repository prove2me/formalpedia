-- Prove2me | solution 1 for GlobalTheory.DeformedSum.Bound.factor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:09:23.692917+00:00
-- url     : https://prove2.me/submissions/90a74ff4-246c-4ea8-aa1b-e1cd62ce265e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
import Theorems.Thm_GlobalTheory_DeformedSum_Bound_defCoord_lower
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Bound
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.DeformedSum.Bound
theorem _root_.solution (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) (hx : x ≠ 0) (i : I) {r : ℝ} (hr : r < 1)
    (hz : ‖z i‖ ≤ r) :
    ‖((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
        (defCoord φ z x i)⁻¹ ^ (k + m i)‖ ≤
      ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (k + m i) * (‖φ i x‖⁻¹) ^ k := by
  have hp : 0 < ‖φ i x‖ := by simpa using hx
  have hr' : 0 < 1 - r := by linarith
  have hl := defCoord_lower φ z x i hz
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  have hinv : ‖defCoord φ z x i‖⁻¹ ≤ (1 - r)⁻¹ * ‖φ i x‖⁻¹ := by
    rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv]
  rw [mul_assoc, mul_assoc]
  gcongr ‖_‖ * ?_
  calc ‖φ i x‖ ^ m i * ‖defCoord φ z x i‖⁻¹ ^ (k + m i)
      ≤ ‖φ i x‖ ^ m i * ((1 - r)⁻¹ * ‖φ i x‖⁻¹) ^ (k + m i) := by gcongr
    _ = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k := by
      rw [mul_pow, pow_add ‖φ i x‖⁻¹]
      have : ‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i = 1 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow]
      calc ‖φ i x‖ ^ m i * ((1 - r)⁻¹ ^ (k + m i) * (‖φ i x‖⁻¹ ^ k * ‖φ i x‖⁻¹ ^ m i))
          = (1 - r)⁻¹ ^ (k + m i) * ‖φ i x‖⁻¹ ^ k * (‖φ i x‖ ^ m i * ‖φ i x‖⁻¹ ^ m i) := by ring
        _ = _ := by rw [this, mul_one]
end GlobalTheory.DeformedSum.Bound
