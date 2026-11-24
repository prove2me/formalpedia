-- Prove2me | solution 1 for GlobalTheory.parsevalSep_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:27:55.953199+00:00
-- url     : https://prove2.me/submissions/ff67b430-f75d-4a33-922a-550d2dc5ffec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have h0 : ω ≠ 0 := hω.ne_zero hN.ne'
  rw [← Complex.inv_eq_conj h1]
  have hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  simp_rw [hz]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero k h0)]
  · have hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1 := by
      intro h'
      apply h
      apply hω.pow_inj hk hl
      field_simp at h'
      exact h'
    have hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    rw [geom_sum_eq hne, hp]
    simp
end GlobalTheory
