-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.exists_eq_pow_of_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:42.093985+00:00
-- url     : https://prove2.me/submissions/685da2ff-9392-4fcc-9aee-5dcf464b1acc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {L : Type*} [Field L] (w v : Valuation L ℤᵐ⁰)
    (h : ∀ f, w f ≤ 1 ↔ v f ≤ 1) {π : L} (hπ : v π = exp (-1)) :
    ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v f ^ e := by
  have key : ∀ (u : Valuation L ℤᵐ⁰) (f : L), f ≠ 0 → (u f < 1 ↔ ¬ u f⁻¹ ≤ 1) :=
    fun u f hf => by rw [not_le, Valuation.one_lt_val_iff u (inv_ne_zero hf), inv_inv]
  have hlt : ∀ f : L, f ≠ 0 → (w f < 1 ↔ v f < 1) := fun f hf => by
    rw [key w f hf, key v f hf, h f⁻¹]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hwπ : w π < 1 := (hlt π hπ0).mpr (by rw [hπ, ← exp_zero, exp_lt_exp]; norm_num)
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
  obtain ⟨c, hwπc⟩ : ∃ c : ℤ, w π = exp c := ⟨_, (exp_log hwπ0).symm⟩
  have hc0 : c < 0 := by
    have := hwπ
    rwa [hwπc, ← exp_zero, exp_lt_exp] at this
  refine ⟨c.natAbs, by omega, fun f => ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, map_zero, zero_pow (by omega)]
  have hvf0 : v f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  obtain ⟨l, hvf⟩ : ∃ l : ℤ, v f = exp l := ⟨_, (exp_log hvf0).symm⟩
  have hg : v (f * π ^ l) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hvf, ← exp_zsmul, ← exp_add, ← exp_zero]
    congr 1
    simp
  have hwg : w (f * π ^ l) = 1 := by
    have hg0 : f * π ^ l ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hπ0)
    refine le_antisymm ((h _).mpr hg.le) (not_lt.mp fun hl => ?_)
    have := (hlt _ hg0).mp hl
    rw [hg] at this
    exact lt_irrefl _ this
  rw [map_mul, map_zpow₀, hwπc, ← exp_zsmul] at hwg
  rw [eq_inv_of_mul_eq_one_left hwg, hvf, ← exp_nsmul, ← exp_neg]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [Int.ofNat_natAbs_of_nonpos hc0.le]
  ring
end GroundTheory.Arith.Abelian
