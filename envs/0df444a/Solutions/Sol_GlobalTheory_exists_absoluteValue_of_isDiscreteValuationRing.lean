-- Prove2me | solution 1 for GlobalTheory.exists_absoluteValue_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:56.840262+00:00
-- url     : https://prove2.me/submissions/0e5c39a9-7f5e-43c9-8006-d8dd33d1b764

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
universe u
open IsDedekindDomain
namespace GlobalTheory
theorem _root_.solution (V K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    {a : V} (ha0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal V) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ∃ w : AbsoluteValue K ℝ, IsNonarchimedean w ∧
      (∀ x : K, w x ≤ 1 ↔ x ∈ (algebraMap V K).range) ∧ w (algebraMap V K a) = r := by
  let v := IsDiscreteValuationRing.maximalIdeal V
  have h0 : v.valuation K (algebraMap V K a) ≠ 0 := by
    simpa using ha0
  have h1 : v.valuation K (algebraMap V K a) < 1 := (v.valuation_lt_one_iff_mem a).2 ha
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero h0) with hm
  have hm0 : m < 0 := by
    rw [← WithZero.coe_unzero h0, ← WithZero.coe_one, WithZero.coe_lt_coe] at h1
    exact h1
  let b : NNReal := ⟨r ^ ((m : ℝ)⁻¹), by positivity⟩
  have hb : 1 < b := by
    rw [← NNReal.coe_lt_coe]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hr0 hr1 (inv_lt_zero.2 (by exact_mod_cast hm0))
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, fun x => ?_, ?_⟩
  · have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one, fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  · change ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap V K a)) :
      NNReal) : ℝ) = r
    rw [WithZeroMulInt.toNNReal_neg_apply _ h0, ← hm, NNReal.coe_zpow]
    change (r ^ ((m : ℝ)⁻¹)) ^ m = r
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, inv_mul_cancel₀ (by exact_mod_cast hm0.ne),
      Real.rpow_one]
end GlobalTheory
