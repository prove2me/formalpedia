-- Prove2me | solution 1 for GroundTheory.Global.uniformizer_pow_succ_dvd_of_valuation_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:55.463308+00:00
-- url     : https://prove2.me/submissions/ac18f83e-2507-41aa-a503-7a2c4660194c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_ord_uniformizer_pow
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_ord_unit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    {z : 𝒪[K]} (h : valuation K (z : K) < valuation K ((ϖ : K) ^ k)) : ϖ ^ (k + 1) ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero _
  obtain ⟨m, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
  have hzK : (((w : 𝒪[K]) * ϖ ^ m : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast hz
  have hϖk : (ϖ : K) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [← normalizedValuation_lt_iff, normalizedValuation_eq_exp_ord hzK,
    normalizedValuation_eq_exp_ord hϖk, WithZero.exp_lt_exp, neg_lt_neg_iff,
    ord_uniformizer_pow hϖ] at h
  have hord : ord ((((w : 𝒪[K]) * ϖ ^ m : 𝒪[K])) : K) = m := by
    have hw : ((w : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast w.ne_zero
    have hϖm : (ϖ : K) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
    push_cast
    rw [ord_mul hw hϖm, ord_unit, ord_uniformizer_pow hϖ, zero_add]
  rw [hord] at h
  exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
end GroundTheory.Global
