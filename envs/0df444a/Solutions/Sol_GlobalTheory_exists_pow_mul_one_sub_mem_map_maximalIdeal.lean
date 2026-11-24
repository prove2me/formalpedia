-- Prove2me | solution 1 for GlobalTheory.exists_pow_mul_one_sub_mem_map_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:47.994373+00:00
-- url     : https://prove2.me/submissions/23428048-7617-435c-ac13-52be7e4b5e28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O H : Type) [CommRing O] [IsLocalRing O]
    [CommRing H] [Algebra O H] [Module.Finite O H] (u : H) :
    ∃ (N : ℕ) (y : H), u ^ N * (1 - y * u) ∈ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  set m := IsLocalRing.maximalIdeal O
  set J := m.map (algebraMap O H)
  letI : Field (O ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite (O ⧸ m) (H ⧸ J) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : IsArtinianRing (H ⧸ J) := IsArtinianRing.of_finite (O ⧸ m) _
  obtain ⟨N, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (R := H ⧸ J) (M := H ⧸ J)
    (Ideal.Quotient.mk J u) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨N, y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one, pow_succ] at hy
  simp only [map_mul, map_pow, map_sub, map_one]
  linear_combination -hy
end GlobalTheory
