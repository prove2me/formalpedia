-- Prove2me | solution 1 for GlobalTheory.fourier_inv_sixtythree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:41.541672+00:00
-- url     : https://prove2.me/submissions/abdb3c61-6a28-4ab1-b656-5f48cfd4a8f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormTwelveOrderSixtythree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory
private theorem sum_range_63_primitiveRoot_pow_eq_ite (ω : ℂ) (hω : IsPrimitiveRoot ω 63) (n : ℕ) :
    ∑ j ∈ Finset.range 63, ω ^ (j * n) = if 63 ∣ n then (63 : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ω ^ (j * n) = (ω ^ n) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hn
  · rw [(hω.pow_eq_one_iff_dvd n).mpr hn]
    simp
  · have hne : ω ^ n ≠ 1 := fun h => hn ((hω.pow_eq_one_iff_dvd n).mp h)
    have h63 : (ω ^ n) ^ 63 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hg := geom_sum_mul (ω ^ n) 63
    rw [h63, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)
end GlobalTheory
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63) (m : ℕ)
    (hm : m < 63) :
    ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = 63 * (c m : ℂ) := by
  have hsum := sum_range_63_primitiveRoot_pow_eq_ite ω hω
  calc ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = ∑ k ∈ Finset.range 63, (c k : ℂ) * ∑ j ∈ Finset.range 63, ω ^ (j * (k + 62 * m)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_add, pow_add]
        ring
    _ = ∑ k ∈ Finset.range 63, (c k : ℂ) * (if 63 ∣ k + 62 * m then (63 : ℂ) else 0) := by
        simp_rw [hsum]
    _ = 63 * (c m : ℂ) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
          ring
        · intro k hk hkm
          have hk' := Finset.mem_range.mp hk
          rw [if_neg (by omega)]
          simp
        · intro hm'
          exact absurd (Finset.mem_range.mpr hm) hm'
end GlobalTheory
