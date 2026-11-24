-- Prove2me | solution 1 for GlobalTheory.NatMulIntegerMultiple.exists_nat_mul_eq_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:50.497979+00:00
-- url     : https://prove2.me/submissions/1c1660cd-661d-442e-81be-7b8e8c16723c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatMulEqInteger

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NatMulIntegerMultiple
open NumberField
namespace GlobalTheory.NatMulIntegerMultiple
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (k : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, (n : K) * k = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ k :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = (n : ℤ) • k := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hint
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = -((-(n : ℤ)) • k) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hint.neg
end GlobalTheory.NatMulIntegerMultiple
