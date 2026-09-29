-- Prove2me | solution 1 for LaurentSeries.exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f8e9f299-67cd-5957-9296-6482f596985e

import Mathlib
import Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one

set_option autoImplicit false

namespace P2M
namespace RootsConst

open Polynomial

theorem mem_valuationSubring_of_pow_eq_one {k₀ : Type*} [Field k₀] (A₀ : ValuationSubring k₀)
    {n : ℕ} (hn : n ≠ 0) {c : k₀} (hc : c ^ n = 1) : c ∈ A₀ := by
  rcases A₀.mem_or_inv_mem c with h | h
  · exact h
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hc
      exact zero_ne_one hc
    have : c = (c⁻¹) ^ (n - 1) := by
      have h1 : c * (c⁻¹) ^ (n - 1) * c⁻¹ = (c⁻¹) ^ (n - 1) := by
        rw [mul_assoc, mul_comm ((c⁻¹) ^ (n - 1)) c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      have h2 : (c⁻¹) ^ (n - 1) * c⁻¹ = (c⁻¹) ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
      rw [← h1, mul_assoc, h2, inv_pow, hc, inv_one, mul_one]
    rw [this]
    exact pow_mem h _

theorem coe_eq_C_of_pow_eq_one {k₀ : Type*} [Field k₀] (K : IntermediateField k₀ (LaurentSeries k₀))
    {n : ℕ} (hn : n ≠ 0) (ζ : K) (hζ : ζ ^ n = 1) :
    ((ζ : LaurentSeries k₀)) = HahnSeries.C ((ζ : LaurentSeries k₀).coeff 0) := by
  apply LaurentSeries.eq_C_coeff_zero_of_isAlgebraic
  have hζ' : ((ζ : LaurentSeries k₀)) ^ n = 1 := by
    have := congrArg (fun z : K => (z : LaurentSeries k₀)) hζ
    simpa using this
  refine IsIntegral.isAlgebraic ⟨X ^ n - 1, Polynomial.monic_X_pow_sub_C (1 : k₀) hn, ?_⟩
  simp [hζ']

end P2M.RootsConst

open P2M.RootsConst in
theorem solution
    {k₀ : Type*} [Field k₀] (K : IntermediateField k₀ (LaurentSeries k₀))
    (A₀ : ValuationSubring k₀) [Algebra A₀ K] [IsScalarTower A₀ k₀ K]
    {n : ℕ} (hn : n ≠ 0) (ζ : K) (hζ : ζ ^ n = 1) :
    ∃ a : A₀, a ^ n = 1 ∧ algebraMap A₀ K a = ζ := by
  set c : k₀ := (ζ : LaurentSeries k₀).coeff 0 with hc_def
  have hζC : ((ζ : LaurentSeries k₀)) = HahnSeries.C c := coe_eq_C_of_pow_eq_one K hn ζ hζ

  have hcn : c ^ n = 1 := by
    have h1 : ((ζ : LaurentSeries k₀)) ^ n = 1 := by
      have := congrArg (fun z : K => (z : LaurentSeries k₀)) hζ
      simpa using this
    rw [hζC, ← map_pow] at h1
    have h2 : (HahnSeries.C (c ^ n) : LaurentSeries k₀) = HahnSeries.C 1 := by rw [h1, map_one]
    exact HahnSeries.C_injective h2
  have hcA : c ∈ A₀ := mem_valuationSubring_of_pow_eq_one A₀ hn hcn
  refine ⟨⟨c, hcA⟩, ?_, ?_⟩
  · apply Subtype.ext
    show ((⟨c, hcA⟩ : A₀) ^ n : A₀).1 = 1
    rw [SubmonoidClass.mk_pow]
    exact hcn
  ·
    have h1 : algebraMap A₀ K ⟨c, hcA⟩ = algebraMap k₀ K c := by
      rw [IsScalarTower.algebraMap_apply A₀ k₀ K]
      rfl
    rw [h1]
    apply Subtype.ext
    rw [hζC]
    show ((algebraMap k₀ K c : K) : LaurentSeries k₀) = HahnSeries.C c
    have : ((algebraMap k₀ K c : K) : LaurentSeries k₀) = algebraMap k₀ (LaurentSeries k₀) c := rfl
    rw [this]
    have h1 : algebraMap k₀ (PowerSeries k₀) c = PowerSeries.C c := by simp
    rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

end S_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one
end P2MW
export P2MW.S_LaurentSeries_exists_valuationSubring_pow_eq_one_algebraMap_eq_of_pow_eq_one (solution)
